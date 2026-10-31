# Version 2: memoize the pure path-to-logical-module mapping within each
# dependency snapshot, and accept mixed requested roots only when they appear
# in the current audit or are covered by validated exact-artifact receipts.
"""Exact-artifact receipts for full and incremental Coq kernel audits.

A recursive receipt is issued only after successful recursive coqchk. An
incremental audit may skip a dependency only when its source, compiled object,
runtime, and complete dependency closure match a prior receipt rooted in a
successful recursive audit. Every uncached module is explicitly checked with
coqchk -norec in one invocation; Coq 8.18 never skips explicitly named modules.
The verbose audit log is checked against the predicted dependency closure, so
an unexpected skipped compiled dependency prevents receipt publication.

Receipts are local build artifacts, not portable mathematical certificates.
Before publishing totals, audit the complete final dependency closure, either
freshly or through validated exact-artifact receipts and checks of every
remaining module. Bounded prerequisite phases may supply those receipts.
"""
import hashlib
from functools import lru_cache
import json
import re
import shutil
import subprocess
import time
from pathlib import Path


def digest(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as f:
        for block in iter(lambda:f.read(1024*1024),b''):
            h.update(block)
    return h.hexdigest()


def fresh_paths(directory, stem='audit'):
    """Preserve every prior receipt and its log when replaying a batch."""
    directory=Path(directory)
    for i in range(1000000):
        name=stem if i==0 else f'{stem}-{i:06}'
        receipt=directory/(name+'.json');log=directory/(name+'.log')
        if not receipt.exists() and not log.exists():return receipt,log
    raise ValueError('No unused audit receipt path')


def _runtime():
    paths = {name:str(Path(shutil.which(name)).resolve()) for name in ('coqchk','coqdep','coqc')}
    coqlib=Path(subprocess.check_output(['coqc','-where'],text=True).strip()).resolve()
    plugins=sorted((coqlib.parent/'coq-core/plugins').rglob('*.cmxs'))
    return dict(version=subprocess.check_output(['coqchk','--version'],text=True).strip(),
                executables={name:dict(path=path,sha256=digest(path)) for name,path in paths.items()},
                plugins={str(p):digest(p) for p in plugins})


def _loadargs(loadpaths):
    return [arg for path,module in loadpaths for arg in ('-Q',str(Path(path).resolve()),module)]


def snapshot(roots, loadpaths):
    """Include standard-library dependencies and implicit Init.Prelude too."""
    coqlib=Path(subprocess.check_output(['coqc','-where'],text=True).strip()).resolve()
    mappings=[(Path(path).resolve(),module) for path,module in loadpaths]
    mappings.append((coqlib/'theories','Coq'))
    mappings.sort(key=lambda pair:len(str(pair[0])),reverse=True)
    @lru_cache(maxsize=None)
    def module(path):
        for root,prefix in mappings:
            if path.is_relative_to(root):
                return prefix+'.'+'.'.join(path.relative_to(root).with_suffix('').parts)
        raise ValueError(f'No logical loadpath for dependency {path}')
    pending={Path(p).resolve() for p in roots}
    pending.add(coqlib/'theories/Init/Prelude.v')
    sources={};extras=set()
    plugin_dirs=sorted({p.parent for p in (coqlib.parent/'coq-core/plugins').rglob('*.cmxs')})
    args=['coqdep','-boot','-R',str(coqlib/'theories'),'Coq',
          *[arg for path in plugin_dirs for arg in ('-I',str(path))],*_loadargs(loadpaths)]
    while pending:
        batch=sorted(pending-sources.keys())
        if not batch:break
        output=subprocess.check_output([*args,*map(str,batch)],text=True)
        parsed={}
        for line in output.splitlines():
            if ': ' not in line or not line.split()[0].endswith('.vo'):continue
            source=Path(line.split()[0]).with_suffix('.v').resolve()
            deps=[]
            for token in line.split(': ',1)[1].split():
                if token.endswith('.vo'):
                    deps.append(Path(token).with_suffix('.v').resolve())
                elif token.endswith(('.cmxs','.cma','.cmxa')):
                    p=Path(token).resolve()
                    if not p.is_file():raise ValueError(f'Missing plugin artifact {token}')
                    extras.add(p)
            parsed[source]=deps
        if set(batch)-parsed.keys():raise ValueError('coqdep omitted an input source')
        for source in batch:
            if not source.is_file() or not source.with_suffix('.vo').is_file():
                raise ValueError(f'Compile dependency before auditing: {source}')
            sources[source]=parsed[source]
        pending={dep for deps in parsed.values() for dep in deps if dep not in sources}
    graph={}
    for source,deps in sorted(sources.items()):
        name=module(source)
        if name in graph:raise ValueError('Ambiguous logical module mapping')
        graph[name]=dict(source=str(source),source_sha256=digest(source),
                         object=str(source.with_suffix('.vo')),object_sha256=digest(source.with_suffix('.vo')),
                         dependencies=sorted(module(dep) for dep in deps))
    return dict(runtime=_runtime(),graph=graph,
                plugins={str(p):digest(p) for p in sorted(extras)})


def _load_receipt(path, seen=None):
    path=Path(path).resolve();seen=set() if seen is None else set(seen)
    if path in seen:raise ValueError('Cyclic audit receipt chain')
    seen.add(path);data=json.loads(path.read_text())
    if data.get('schema')!=1 or data.get('result')!='passed':raise ValueError('Invalid audit receipt')
    if data['kind'] not in {'recursive','incremental'}:raise ValueError('Unknown audit kind')
    parents=data.get('parents',[])
    if data['kind']=='incremental' and not parents:raise ValueError('Incremental receipt lacks recursive ancestry')
    parent_data=[]
    for parent in parents:
        if digest(parent['path'])!=parent['sha256']:raise ValueError('Parent receipt changed')
        parent_data.append(_load_receipt(parent['path'],seen))
    log=Path(data.get('log',path.with_suffix('.log')))
    if digest(log)!=data['log_sha256']:raise ValueError('Audit log changed')
    text=log.read_text()
    checked=re.findall(r'^Checking library: (\S+)\s*$',text,re.M)
    skipped=re.findall(r'^Admitting library: (\S+)\s*$',text,re.M)
    if checked!=data['checked_modules']:raise ValueError('Receipt checked-module list disagrees with log')
    if checked and 'Modules were successfully checked' not in text:
        raise ValueError('Receipt lacks a successful audit completion')
    if not set(checked+skipped)<=data['snapshot']['graph'].keys():
        raise ValueError('Receipt log names an unexpected dependency')
    if data['kind']=='recursive':
        if skipped or data['reused_modules'] or set(checked)!=set(data['snapshot']['graph']):
            raise ValueError('Recursive receipt did not check its entire dependency graph')
        if '-norec' in data['command'] or '-admit' in data['command']:
            raise ValueError('Recursive receipt used dependency-skipping flags')
    else:
        covered=_covered(data['snapshot'],parent_data)
        if not set(data['reused_modules'])<=covered:raise ValueError('Receipt reused an unverified dependency')
        if not set(data['snapshot']['graph'])<=set(checked)|covered:
            raise ValueError('Receipt leaves an unchecked module')
        if checked and skipped!=data['reused_modules']:
            raise ValueError('Receipt reused-module list disagrees with log')
    return data


def _covered(current, receipts):
    covered=set()
    for data in receipts:
        old=data['snapshot']
        if current['runtime']!=old['runtime']:
            continue
        if any(current['plugins'][p]!=old['plugins'][p]
               for p in current['plugins'].keys() & old['plugins'].keys()):
            continue
        memo={}
        def same(name, active=None):
            if name in memo:return memo[name]
            active=set() if active is None else set(active)
            if name in active:raise ValueError('Cyclic Coq dependency graph')
            active.add(name)
            result=(name in old['graph'] and current['graph'][name]==old['graph'][name]
                    and all(same(dep,active) for dep in current['graph'][name]['dependencies']))
            memo[name]=result;return result
        covered.update(name for name in current['graph'] if same(name))
    return covered


def audit(modules, roots, loadpaths, receipt, log, *, cache=(), recursive=False, timeout=36000):
    """Return an immutable local receipt after all checks and hash rechecks pass."""
    receipt=Path(receipt);log=Path(log);receipt.parent.mkdir(parents=True,exist_ok=True)
    if receipt.exists() or log.exists():
        raise ValueError('Audit receipts and logs are immutable; choose fresh output paths')
    if receipt.resolve()==log.resolve():raise ValueError('Receipt and log paths coincide')
    before=snapshot(roots,loadpaths)
    if not set(modules)<=before['graph'].keys():raise ValueError('Root module/source mismatch')
    parents=[dict(path=str(Path(p).resolve()),sha256=digest(p)) for p in cache]
    cached=[_load_receipt(p) for p in cache]
    covered=set() if recursive or not cached else _covered(before,cached)
    kind='recursive' if recursive or not covered else 'incremental'
    new=set(before['graph'])-covered
    command=['coqchk','-bytecode-compiler','yes',*_loadargs(loadpaths)]
    if kind=='recursive':
        command+=list(modules)
    else:
        command+=[arg for name in sorted(new) for arg in ('-norec',name)]
    start=time.monotonic()
    if kind=='incremental' and not new:
        log.write_text('All requested artifacts match previously successful audits.\n')
        checked=[];skipped=sorted(before['graph'])
    else:
        with log.open('w') as out:
            subprocess.run(command,stdout=out,stderr=subprocess.STDOUT,check=True,timeout=timeout)
        text=log.read_text()
        checked=re.findall(r'^Checking library: (\S+)\s*$',text,re.M)
        skipped=re.findall(r'^Admitting library: (\S+)\s*$',text,re.M)
        if 'Modules were successfully checked' not in text:raise ValueError('Incomplete coqchk log')
        actual=set(checked)|set(skipped)
        if not actual<=before['graph'].keys():
            raise ValueError(f'Unexpected compiled dependencies: {sorted(actual-before["graph"].keys())}')
        if kind=='recursive' and skipped:raise ValueError('Recursive audit skipped dependencies')
        if not set(skipped)<=covered:raise ValueError('Audit skipped an uncached dependency')
        if not set(modules)<=actual|covered:raise ValueError('Root module missing from audit')
        if kind=='incremental' and not new<=set(checked):raise ValueError('An uncached module was not checked')
    after=snapshot(roots,loadpaths)
    if before!=after:raise ValueError('Source/object/dependency artifacts changed during audit')
    # Recursive coqdep may conservatively list unused imports. Do not certify
    # those as kernel-checked merely because their sources were discovered.
    valid=set(checked)|set(skipped)
    if kind=='recursive':
        if not set(before['graph'])<=valid:
            raise ValueError('Source dependency graph exceeds actual checked libraries')
    result=dict(schema=1,result='passed',kind=kind,roots=list(modules),
                parents=parents if kind=='incremental' else [],snapshot=before,
                checked_modules=checked,reused_modules=skipped,
                command=command,log=str(log.resolve()),log_sha256=digest(log),
                elapsed_seconds=round(time.monotonic()-start,3))
    temp=receipt.with_suffix(receipt.suffix+'.tmp');temp.write_text(json.dumps(result,indent=2)+'\n');temp.replace(receipt)
    return result
