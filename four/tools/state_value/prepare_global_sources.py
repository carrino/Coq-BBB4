"""Prepare an isolated, pinned Coq SOURCE tree; never compile or claim a proof.

Generator inputs may be copied from an explicit source pool. Ignored generated
sources and compiled artifacts are forbidden inputs. Every target .v must be
regenerated or copied from an explicit handwritten/core template, and must match
the independently frozen reference digest in the preparation manifest.
"""
import argparse
import builtins
import hashlib
import importlib
import importlib.machinery
import io
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time
import types

sys.dont_write_bytecode = True
# Isolated Python omits the script directory; restore only reviewed wrappers.
sys.path.insert(0, str(Path(__file__).resolve().parent))
WRAPPER_FILES = ('prepare_global_sources.py','public_renderers.py','late_renderers.py','foundation_renderers.py','lean_renderers.py','light_renderers.py')
RAW_OPEN = builtins.open
RAW_IO_OPEN = io.open
RAW_EXISTS = Path.exists
RAW_STAT = Path.stat
FORBIDDEN = {'.vo','.vos','.vok','.cmxs','.cmx','.cmo','.o','.a','.so','.pyc'}


def selected_source_records(spec):
    records=[]
    for path in spec['compile_order']:
        matches=[r for r in spec['load_paths']if path.startswith(r['path']+'/')]
        if len(matches)!=1:raise ValueError('Source must have exactly one selected namespace: '+path)
        row=matches[0]
        logical=row['namespace']+'.'+Path(path).relative_to(row['path']).with_suffix('').as_posix().replace('/','.')
        records.append(dict(path=path,logical_module=logical,
            sha256=spec['sources'][path]['sha256'],bytes=spec['sources'][path]['bytes'],
            direct_dependencies=spec['local_dependencies'][path],
            phase=spec['resource_policy']['source_phases'][path]))
    return records


def digest_bytes(data):
    return hashlib.sha256(data).hexdigest()


def read_raw(path):
    with RAW_OPEN(path, 'rb') as stream:
        return stream.read()


# Historical renderer bytes remain pinned by existing proof checkpoints. Correct
# only their invalid Python escape spelling in memory before compilation; their
# parsed programs and all generated Coq bytes must remain identical.
LEGACY_ESCAPE_RENDERERS = frozenset((
    'four/tools/check_weighted_closeout.py',
    'four/tools/check_burn21_s057_drift.py',
    'four/tools/check_burn10_state_replay_pilot.py',
))


def renderer_python_source(relative_path, data):
    if relative_path not in LEGACY_ESCAPE_RENDERERS:
        return data
    return data.replace(b' \\/ ', b' \\\\/ ').replace(b' /\\ ', b' /\\\\ ')


class Preparation:
    def __init__(self, source_pool, output, spec, extra_inputs=()):
        self.source_pool = source_pool.resolve()
        self.extra_inputs = [p.resolve() for p in extra_inputs]
        self.output = output.resolve()
        self.repo = self.output / 'tree'
        if RAW_EXISTS(self.repo) and any(self.repo.iterdir()):
            raise ValueError('Source preparation requires a fresh empty output tree: '+str(self.repo))
        self.repo.mkdir(parents=True, exist_ok=True)
        self.spec = spec
        self.targets = set(spec['sources'])
        self.inputs = {}
        self.generated = {}
        self.produced = set()
        self.module_names = set()
        self.actions = []
        self.phase = 'bootstrap'

    def rel(self, path):
        p = Path(path)
        if p.is_absolute():
            p = p.resolve().relative_to(self.repo)
        if '..' in p.parts or not p.parts:
            raise ValueError('Nonportable relative path: ' + str(path))
        return p.as_posix()

    def need(self, rel):
        return self.rel(rel) in self.targets

    def any_needed(self, prefix):
        prefix = self.rel(prefix).rstrip('/')
        return any(p == prefix or p.startswith(prefix + '/') for p in self.targets)

    @staticmethod
    def generated_path(rel):
        return rel.startswith(('four/build/','small/build/','build/'))

    def require_input(self, rel):
        rel = self.rel(rel)
        if self.spec.get('strict_input_set') and rel not in self.spec.get('input_sha256',{}):
            raise ValueError('Unexpected unreviewed input: '+rel)
        if self.generated_path(rel) or Path(rel).suffix in FORBIDDEN:
            raise ValueError('Generated/binary artifact forbidden as input: ' + rel)
        pool = next((p for p in [*self.extra_inputs,self.source_pool]
                     if RAW_EXISTS(p/rel)),None)
        src = None if pool is None else pool/rel
        if src is None:
            raise FileNotFoundError('Missing source-pool input: ' + rel)
        real = src.resolve()
        if not real.is_relative_to(pool):
            raise ValueError('Source input symlink escapes its pool: '+rel)
        if self.generated_path(real.relative_to(pool).as_posix()) or real.suffix in FORBIDDEN:
            raise ValueError('Source input symlink points to generated/binary artifact: '+rel)
        raw = read_raw(src)
        row = {'sha256': digest_bytes(raw), 'bytes': len(raw)}
        expected = self.spec.get('input_sha256', {}).get(rel)
        if expected and row['sha256'] != expected:
            raise ValueError('Changed frozen input: ' + rel)
        if rel in self.inputs and self.inputs[rel] != row:
            raise ValueError('Input changed during preparation: ' + rel)
        self.inputs[rel] = row
        dst = self.repo / rel
        dst.parent.mkdir(parents=True, exist_ok=True)
        if not RAW_EXISTS(dst):
            with RAW_OPEN(dst, 'wb') as stream:
                stream.write(raw)
        elif digest_bytes(read_raw(dst)) != row['sha256']:
            raise ValueError('Isolated input differs: ' + rel)
        return dst

    def path(self, rel):
        rel = self.rel(rel)
        p = self.repo / rel
        if self.generated_path(rel):
            return p
        return self.require_input(rel)

    def read_json(self, rel):
        return json.loads(self.path(rel).read_text())

    def emit(self, rel, content, producer='pure renderer'):
        rel = self.rel(rel)
        raw = content.encode() if isinstance(content, str) else bytes(content)
        if Path(rel).suffix in FORBIDDEN:
            raise ValueError('Compiled artifact output forbidden: ' + rel)
        if rel.endswith('.v') and rel not in self.targets:
            # Pure aggregate generators may emit a superset. Only the exact
            # frozen dependency graph belongs in the prepared workspace.
            return self.repo / rel
        expected = self.spec['sources'].get(rel)
        if expected and digest_bytes(raw) != expected['sha256']:
            raise ValueError('Regenerated Coq bytes differ: ' + rel +
                             ' expected=' + expected['sha256'] +
                             ' actual=' + digest_bytes(raw))
        dst = self.repo / rel
        dst.parent.mkdir(parents=True, exist_ok=True)
        with RAW_OPEN(dst, 'wb') as stream:
            stream.write(raw)
        self.generated[rel] = {'sha256': digest_bytes(raw), 'bytes': len(raw),
                               'producer': producer}
        self.produced.add(rel)
        return dst

    def module(self, name):
        self.module_names.add(name)
        module = importlib.import_module(name)
        file = getattr(module, '__file__', None)
        if file:
            p = Path(file).resolve()
            if not p.is_relative_to(self.repo):
                raise ValueError('Renderer imported outside isolated tree: ' + str(p))
        return module

    def bootstrap_python(self):
        # Import discovery needs files before importlib opens them. Only used
        # modules enter the input snapshot; unused candidates are pruned later.
        for pool in [self.source_pool,*reversed(self.extra_inputs)]:
            for folder in ('four/tools','tools'):
                src = pool / folder
                if not RAW_EXISTS(src):
                    continue
                for f in src.rglob('*.py'):
                    rel = f.relative_to(pool)
                    dst = self.repo / rel
                    dst.parent.mkdir(parents=True, exist_ok=True)
                    with RAW_OPEN(dst,'wb') as stream:
                        stream.write(read_raw(f))
        sys.path[:0] = [str(self.repo/'four/tools'), str(self.repo/'tools')]

    def guard_open(self, file, mode='r', *args, **kwargs):
        if isinstance(file, int):
            return RAW_OPEN(file, mode, *args, **kwargs)
        path = Path(file).resolve()
        writing = any(c in mode for c in 'wax+')
        if path.suffix in FORBIDDEN:
            raise ValueError('Compiled artifact read/write forbidden during preparation: '+str(path))
        if path.is_relative_to(self.repo):
            rel = path.relative_to(self.repo).as_posix()
            if writing:
                if Path(rel).suffix in FORBIDDEN or not self.generated_path(rel):
                    raise ValueError('Renderer writes outside generated source area: ' + rel)
                path.parent.mkdir(parents=True, exist_ok=True)
                self.produced.add(rel)
            elif not self.generated_path(rel):
                self.require_input(rel)
            elif not RAW_EXISTS(path) or rel not in self.produced:
                raise FileNotFoundError('Generated dependency not yet rendered: ' + rel)
            return RAW_OPEN(path, mode, *args, **kwargs)
        if path.is_relative_to(self.source_pool):
            raise ValueError('Renderer read source pool directly; use isolated paths: ' + str(path))
        # Only implementation Python and installed runtime resources may be
        # read outside the isolated tree. Private /tmp data is never a fallback.
        implementation=Path(__file__).resolve().parent
        runtime_roots=('/usr/','/lib/','/lib64/','/etc/','/proc/','/dev/','/opt/',
                       '/workspace/.opam/')
        allowed=(path.is_relative_to(implementation)and path.suffix=='.py')or str(path).startswith(runtime_roots)
        if writing or not allowed:
            raise ValueError('Renderer accessed outside isolated source tree: ' + str(path))
        return RAW_OPEN(path, mode, *args, **kwargs)

    def guard_exists(self, path):
        p = path.resolve()
        if p.is_relative_to(self.repo) and not RAW_EXISTS(p):
            rel = p.relative_to(self.repo).as_posix()
            if not self.generated_path(rel) and any(RAW_EXISTS(pool/rel)for pool in [*self.extra_inputs,self.source_pool]):
                self.require_input(rel)
        return RAW_EXISTS(p)

    def enter_guard(self):
        builtins.open = self.guard_open
        io.open = self.guard_open
        Path.exists = lambda path: self.guard_exists(path)
        self.old_loader_get_data=importlib.machinery.SourceFileLoader.get_data
        def loader_get_data(loader,path):
            p=Path(path).resolve()
            if p.suffix=='.py'and p.is_relative_to(self.repo):
                relative = p.relative_to(self.repo).as_posix()
                self.require_input(relative)
                return renderer_python_source(relative, self.old_loader_get_data(loader,path))
            return self.old_loader_get_data(loader,path)
        importlib.machinery.SourceFileLoader.get_data=loader_get_data
        def forbidden(*args, **kwargs):
            raise RuntimeError('External process forbidden during source-only preparation: ' +
                               repr(args[0] if args else kwargs.get('args')))
        self.old_subprocess = {name:getattr(subprocess,name) for name in
                               ('run','Popen','check_output','check_call','call')}
        for name in self.old_subprocess:
            setattr(subprocess,name,forbidden)
        self.old_os_process={name:getattr(os,name)for name in
                             ('system','fork','forkpty','posix_spawn','posix_spawnp')if hasattr(os,name)}
        for name in self.old_os_process:
            setattr(os,name,forbidden)

    def leave_guard(self):
        builtins.open = RAW_OPEN
        io.open = RAW_IO_OPEN
        Path.exists = RAW_EXISTS
        importlib.machinery.SourceFileLoader.get_data=self.old_loader_get_data
        for name,value in self.old_subprocess.items():
            setattr(subprocess,name,value)
        for name,value in self.old_os_process.items():
            setattr(os,name,value)

    def record_loaded_inputs(self):
        pending=list(sys.modules.values());seen=set()
        while pending:
            module=pending.pop()
            if not isinstance(module,types.ModuleType)or id(module)in seen:
                continue
            seen.add(id(module))
            pending.extend(value for value in list(vars(module).values())
                           if isinstance(value,types.ModuleType))
            name = getattr(module, '__file__', None)
            if not name:
                continue
            p = Path(name).resolve()
            if p.is_relative_to(self.repo) and p.suffix == '.py':
                self.require_input(p.relative_to(self.repo))

    def finish(self):
        self.record_loaded_inputs()
        missing=[]
        for rel,row in self.spec['sources'].items():
            path=self.repo/rel
            if not RAW_EXISTS(path) or (row['kind']=='generated'and rel not in self.produced):
                missing.append(rel)
            elif digest_bytes(read_raw(path)) != row['sha256']:
                raise ValueError('Prepared source digest differs: '+rel)
        for rel in self.produced:
            path=self.repo/rel
            if RAW_EXISTS(path) and path.is_file()and rel not in self.generated:
                raw=read_raw(path)
                self.generated[rel]={'sha256':digest_bytes(raw),'bytes':len(raw),
                                     'producer':'guarded pure helper write'}
        manifest={'scope':'Source preparation only; no compilation, kernel audit or mathematical credit.',
                  'complete':not missing, 'source_files':len(self.targets),
                  'source_bytes':sum(r['bytes']for r in self.spec['sources'].values()),
                  'input_files':self.inputs,'generated_files':self.generated,
                  'missing_sources':missing,'load_paths':self.spec['load_paths'],
                  'compile_order':self.spec['compile_order'],
                  'local_dependencies':self.spec['local_dependencies'],
                  'object_files_included':0,'fresh_source_compilation_executed':False,
                  'kernel_audit_executed':False,'new_state_families':0}
        implementation=Path(__file__).resolve().parent
        manifest['implementation_sha256']={name:digest_bytes(read_raw(implementation/name))
            for name in WRAPPER_FILES}
        self.output.mkdir(parents=True,exist_ok=True)
        (self.output/'preparation-result.json').write_text(json.dumps(manifest,indent=2)+'\n')
        frozen=dict(self.spec)
        frozen['input_sha256']={p:r['sha256']for p,r in self.inputs.items()}
        frozen['implementation_sha256']=manifest['implementation_sha256']
        (self.output/'frozen-prepare-manifest.json').write_text(json.dumps(frozen,indent=2)+'\n')
        plan={'scope':'Deferred compilation plan for this foundation source graph; NOT executed by preparation.',
              'working_directory':'tree','environment':{'COQPATH':''},
              'common_flags':[arg for row in self.spec['load_paths']for arg in('-Q',row['path'],row['namespace'])],
              'module_command_prefix':['coqc','-q','-noglob','-w',
                  '-abstract-large-number,+native-compiler-disabled','-native-compiler','ondemand'],
              'command_construction':'module_command_prefix + common_flags + [source]',
              'compile_order':self.spec['compile_order'],
              'local_dependencies':self.spec['local_dependencies'],
              'source_sha256':{p:r['sha256']for p,r in self.spec['sources'].items()},
              'default_workers':4,'per_worker_memory_mib':6144,
              'global_source_or_index_policy':{'workers':1,'address_space_mib':14336,'rss_guard_mib':12288},
              'project_object_files_included':0,'global_equality_claim_proved':False,
              'foundation_roots':self.spec.get('roots',[]),
              'pending_value_alias':self.spec.get('pending_value_alias'),
              'selected_project_policy':self.spec.get('selected_project_policy'),
              'resource_policy':self.spec.get('resource_policy'),
              'resume_policy':'No bare existing-object skip. Require current source/dependency/runtime/object records and checked audit receipts.',
              'fresh_compilation_executed':False,'kernel_audit_executed':False}
        (self.output/'compile-plan.json').write_text(json.dumps(plan,indent=2)+'\n')
        # A cold replay input pool contains only actually required source/data.
        snapshot=self.output/'inputs'
        for rel,row in self.inputs.items():
            dst=snapshot/rel;dst.parent.mkdir(parents=True,exist_ok=True)
            with RAW_OPEN(dst,'wb')as stream:stream.write(read_raw(self.repo/rel))
        for p in self.repo.rglob('*.py'):
            if p.relative_to(self.repo).as_posix()not in self.inputs:
                p.unlink()
        for suffix in FORBIDDEN:
            if any(self.repo.rglob('*'+suffix)):
                raise ValueError('Prepared workspace contains a binary artifact: '+suffix)
        # No pilot/diagnostic or generator superset may enter an active namespace.
        extras=[]
        for row in self.spec['load_paths']:
            for candidate in (self.repo/row['path']).rglob('*.v'):
                if candidate.relative_to(self.repo).as_posix()not in self.targets:
                    extras.append(candidate.relative_to(self.repo).as_posix())
        if extras:raise ValueError('Unselected Coq source under active namespace: '+repr(extras))
        lines=[]
        for row in self.spec['load_paths']:
            ns=json.dumps(row['namespace'])if not row['namespace']else row['namespace']
            lines.append('-Q '+row['path']+' '+ns)
        lines.extend(self.spec['compile_order'])
        (self.repo/'_CoqProject.prepared').write_text('\n'.join(lines)+'\n')
        if self.spec.get('source_records_output'):
            raw=(json.dumps(selected_source_records(self.spec),indent=2)+'\n').encode()
            if digest_bytes(raw)!=self.spec['selected_source_records_sha256']:
                raise ValueError('Selected source record digest changed')
            with RAW_OPEN(self.output/self.spec['source_records_output'],'wb')as stream:
                stream.write(raw)
        summary={k:manifest[k]for k in ('complete','source_files','source_bytes','object_files_included',
                                      'fresh_source_compilation_executed','kernel_audit_executed')}
        summary['missing_count']=len(missing)
        summary['missing_prefixes']=sorted({'/'.join(p.split('/')[:4])for p in missing})
        print(json.dumps(summary,indent=2))
        return 0 if not missing else 2


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--prepare-only',action='store_true',required=True)
    parser.add_argument('--source-input',type=Path,required=True)
    parser.add_argument('--manifest',type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--extra-input',type=Path,action='append',default=[])
    parser.add_argument('--only',choices=('public','late','foundation','all'),default='all')
    args=parser.parse_args()
    spec=json.loads(args.manifest.read_text())
    implementation=Path(__file__).resolve().parent
    for name,expected in spec.get('implementation_sha256',{}).items():
        if digest_bytes(read_raw(implementation/name))!=expected:
            raise ValueError('Preparation implementation changed: '+name)
    ctx=Preparation(args.source_input,args.output,spec,args.extra_input)
    ctx.bootstrap_python()
    # Direct core and handwritten sources are explicit non-generated inputs.
    for rel,row in spec['sources'].items():
        if row['kind']=='input':
            ctx.path(rel)
    ctx.enter_guard()
    try:
        for name in ([]if args.only=='foundation'else
                     ['public_renderers']if args.only=='public'else
                     ['late_renderers']if args.only=='late'else
                     ['public_renderers','late_renderers']):
            ctx.phase=name
            backend=importlib.import_module(name)
            backend.render(ctx)
        extra=importlib.import_module('foundation_renderers')
        ctx.phase='foundation_renderers'
        extra.render(ctx)
        ctx.record_loaded_inputs()
    finally:
        ctx.leave_guard()
    return ctx.finish()


if __name__=='__main__':
    sys.exit(main())
