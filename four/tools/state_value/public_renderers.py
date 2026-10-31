"""Source-only backends for the original public four-symbol campaign.

Only pure source/data render functions are called. No original main, compiler,
native selector, historical object check or audit runner is invoked here.
"""
from collections import Counter, defaultdict
from contextlib import contextmanager
import csv
import hashlib
import io
import json
from pathlib import Path
import re
from types import SimpleNamespace


def _arg(command, flag, default=None):
    return command[command.index(flag)+1] if flag in command else default


def _mod(ctx, name):
    return ctx.module(name)


def _needed(ctx, prefix):
    return ctx.any_needed(prefix)


@contextmanager
def _capture(ctx, producer, rename=None, deferred=False):
    """Route writes from an existing pure generator through the source sink."""
    old_text, old_bytes = Path.write_text, Path.write_bytes
    old_read_text, old_read_bytes, old_rename = Path.read_text, Path.read_bytes, Path.rename
    pending = {}
    active = False
    def relative(path):
        return path.resolve().relative_to(ctx.repo.resolve()).as_posix()
    def emit(path, data):
        nonlocal active
        if active:
            return old_bytes(path, data if isinstance(data, bytes) else data.encode())
        rel = relative(path)
        if rename:
            rel = rename(rel)
        if deferred:
            # Some historical pure producers deliberately write a base shard,
            # read it back, then rewrite its checker. Only their final source
            # bytes belong to the frozen graph. Keep these intermediates in
            # memory; never present them to the verified source sink.
            pending[rel] = data if isinstance(data, bytes) else data.encode()
            return len(data)
        active = True
        try:
            ctx.emit(rel, data, producer)
        finally:
            active = False
        return len(data)
    def text(path, data, *args, **kwargs):
        return emit(path, data)
    def binary(path, data, *args, **kwargs):
        return emit(path, data)
    def read_binary(path, *args, **kwargs):
        try: rel = relative(path)
        except ValueError: return old_read_bytes(path, *args, **kwargs)
        return pending[rel] if rel in pending else old_read_bytes(path, *args, **kwargs)
    def read_text(path, *args, **kwargs):
        try: rel = relative(path)
        except ValueError: return old_read_text(path, *args, **kwargs)
        if rel not in pending:return old_read_text(path, *args, **kwargs)
        encoding = kwargs.get('encoding') or (args[0] if args else None) or 'utf-8'
        return pending[rel].decode(encoding)
    def move(path, target):
        source_rel = relative(path)
        if source_rel not in pending:return old_rename(path, target)
        target = Path(target)
        pending[relative(target)] = pending.pop(source_rel)
        return target
    Path.write_text, Path.write_bytes = text, binary
    if deferred:
        Path.read_text, Path.read_bytes, Path.rename = read_text, read_binary, move
    try:
        yield
        for rel, data in pending.items():
            ctx.emit(rel, data, producer)
    finally:
        Path.write_text, Path.write_bytes = old_text, old_bytes
        Path.read_text, Path.read_bytes, Path.rename = old_read_text, old_read_bytes, old_rename


def _csv(ctx, rel):
    return list(csv.DictReader(io.StringIO(ctx.path(rel).read_text()), delimiter='\t'))


def affine_foundations(ctx):
    if _needed(ctx, 'four/build/affine-batch/'):
        m = _mod(ctx, 'check_affine_batch')
        bundle = ctx.read_json('four/research/affine-batch-certs.json')
        old = _csv(ctx, 'four/research/affine-batch.tsv')
        outcomes = {r['machine']:r['status']=='coq_checked' for r in old}
        certs = []
        for machine, contents in sorted(bundle.items()):
            rel = 'four/build/affine-batch/certs/'+machine+'.cert'
            ctx.emit(rel, contents, 'affine-batch-certificate-text')
            certs.append(ctx.path(rel))
        for start in range(0, len(certs), m.SHARD_SIZE):
            parts = [m.generator.HEADER]
            for cert in certs[start:start+m.SHARD_SIZE]:
                if outcomes[cert.stem]:
                    parts.append(m.certificate(cert))
                else:
                    name = m.generator.shared.cname(cert.stem)
                    parts.append(m.definitions(cert)+'\nLemma rejected_'+name+' :\n  '+m.checker_term(cert)+' = false.\nProof. vm_compute. reflexivity. Qed.\n')
            ctx.emit(f'four/build/affine-batch/AffineBatch{start//m.SHARD_SIZE:03}.v', ''.join(parts), 'check_affine_batch.make_shards')
    if _needed(ctx, 'four/build/affine-closeout/'):
        accepted = {r['machine']:r for r in _csv(ctx, 'four/research/affine-batch.tsv') if r['status']=='coq_checked'}
        ctx.emit('four/build/affine-closeout/AffineCloseoutBatch.v', _mod(ctx, 'check_affine_closeout').generate(accepted), 'check_affine_closeout.generate')
    if _needed(ctx, 'four/build/closure-batch/'):
        m = _mod(ctx, 'check_closure_batch')
        d = ctx.read_json('four/research/closure-batch-input.json')
        rows = [dict(zip(d['columns'], values)) for values in d['rows']]
        modules = []
        for start in range(0, len(rows), m.SHARD_SIZE):
            name = f'ClosureBatch{start//m.SHARD_SIZE:03}'; modules.append(name)
            ctx.emit('four/build/closure-batch/'+name+'.v', m.generator.generate({'rows':rows[start:start+m.SHARD_SIZE]})+m.NONHALT, 'check_closure_batch.generator.generate')
        ctx.emit('four/build/closure-batch/ClosureBatchAll.v', m.aggregate(modules,len(rows)), 'check_closure_batch.aggregate')
    if _needed(ctx, 'four/build/family-transport/'):
        m = _mod(ctx, 'check_family_transport')
        config = ctx.read_json('four/research/transport-sources.json')
        data = ctx.read_json('four/research/family-transport-input.json')
        machines = []
        for source in config['sources']:
            for entry in source['machine_inputs']:
                p = 'four/'+entry['path']
                if entry['format']=='checked_affine_tsv':
                    machines.extend(r['machine'] for r in _csv(ctx,p) if r['status']=='coq_checked')
                else:
                    d = ctx.read_json(p)
                    machines.extend(r['machine'] for r in d['rows']) if entry['format']=='json_rows' else machines.extend(row[d['columns'].index('machine')] for row in d['rows'])
        with _capture(ctx, 'check_family_transport pure source functions'):
            m.source_module(config,len(machines));m.ready_module(data['ready_shadows'])
            images = m.image_shards(data['images'],'source_board','source_board_strong',4096,'ImageFamilies')
            shadows = m.image_shards(data['shadow_images'],'ready_board','ready_board_strong',4097,'ShadowFamilies')
            m.aggregate(images,shadows,len(data['images'])+len(data['shadow_images']))


def affine_wave(ctx, command):
    m = _mod(ctx, 'check_affine_wave')
    if Path(command[1]).name=='prepare_affine_templates.py':
        report = ctx.read_json(_arg(command,'--report'))
        name = report['module'].split('.')[1]
        rp = _arg(command,'--report')
        input_rel = rp[:-5]+'-input.json'
    else:
        name = _arg(command,'--name'); input_rel = _arg(command,'--input')
    prefix = 'four/build/affine-wave/proofs/'+name+'/'
    if not _needed(ctx,prefix):return
    with _capture(ctx, 'check_affine_wave.load_bundle'):
        data, paths = m.load_bundle(ctx.path(input_rel), ctx.path(prefix+'certs'))
    parts = []
    for start in range(0,len(paths),m.SHARD_SIZE):
        part = f'Part{start//m.SHARD_SIZE:04}';parts.append(part)
        if ctx.need(prefix+part+'.v'):
            ctx.emit(prefix+part+'.v',m.shard(paths[start:start+m.SHARD_SIZE],data['bound'],data['cfuel'],data['fuel']),'check_affine_wave.shard')
    ctx.emit(prefix+'All.v',m.aggregate(name,parts,data['bound'],len(paths)),'check_affine_wave.aggregate')


def weighted_portable(ctx, command):
    out = _arg(command,'--output-dir')+'/'
    if not _needed(ctx,out):return
    m = _mod(ctx,'replay_portable_weighted')
    report = ctx.read_json(_arg(command,'--report')); manifest = report['manifest']; namespace = manifest['namespace']
    checked = [r for r in report['results'] if r['status']=='coq_checked']
    certificates = _arg(command,'--certificates')
    if certificates:
        rows = [json.loads(s)for s in ctx.path(certificates).read_text().splitlines()]
        for i,row in enumerate(rows):
            name=f'Weighted{i:04d}.v'
            if ctx.need(out+name):ctx.emit(out+name,m.render(row),'replay_portable_weighted legacy.render')
        modules=[r['module']for r in checked]
        ctx.emit(out+'WeightedBoard.v',m.legacy.board_source(namespace,modules),'check_weighted.board_source')
    else:
        fields=('HEADER','unpack','render','sources','run','bundle_decode')
        if not hasattr(m,'_source_only_v2_baseline'):
            m._source_only_v2_baseline={k:getattr(m.v2,k)for k in fields}
        current={k:getattr(m.v2,k)for k in fields}
        old_decode=m.bundle_decode
        try:
            for k,v in m._source_only_v2_baseline.items():setattr(m.v2,k,v)
            m.bundle_decode=_mod(ctx,'weighted_codec_v2').bundle_decode
            registry_path=ctx.path(_arg(command,'--registry'));m.configure(manifest,registry_path)
            registry=json.loads(registry_path.read_text());rows=[]
            for b in registry['bundles']:
                p=ctx.path('four/'+b['path']);rows.extend(m.bundle_decode(p.read_text()))
            by_machine={r['machine']:r for r in rows};grouped={}
            for r in checked:grouped.setdefault(r['module'],[]).append(by_machine[r['machine']])
            for name,batch in grouped.items():
                if ctx.need(out+name+'.v'):ctx.emit(out+name+'.v',m.v2.shard_source(batch),'weighted_campaign_v2.shard_source')
            ctx.emit(out+'WeightedAll.v',m.v2.aggregate(namespace,list(grouped)),'weighted_campaign_v2.aggregate')
        finally:
            for k,v in current.items():setattr(m.v2,k,v)
            m.bundle_decode=old_decode


def weighted_closeout(ctx, command):
    out=_arg(command,'--proof-dir')+'/'
    if not _needed(ctx,out):return
    m=_mod(ctx,'replay_portable_weighted_closeout');r=ctx.read_json(_arg(command,'--weighted-report'))
    manifest=r['manifest'];namespace=manifest['namespace'];names=[x['machine']for x in r['results']if x['status']=='coq_checked']
    # The exact producer is kept in the immutable original helper module.
    ctx.emit(out+'WeightedCloseout.v',m.closeout.source(namespace),'check_weighted_closeout.source')
    ctx.emit(out+'WeightedPortableInventory.v',m.inventory_source(namespace,names),'replay_portable_weighted_closeout.inventory_source')


def pipeline(ctx, command):
    tool=Path(command[1]).name;out=_arg(command,'--output-dir','four/build/state-closure')+'/'
    if not _needed(ctx,out)and tool!='check_state_pipeline_cached.py':return
    repwl=tool in ('check_state_repwl_batch.py','check_state_repwl_recorded.py')
    base=_mod(ctx,'check_state_repwl_batch'if repwl else'check_state_pipeline_batch')
    inp=_arg(command,'--input','four/research/state-closure-input.json');ns=_arg(command,'--namespace','BBB24StateClosure')
    if tool=='check_state_pipeline_cached.py':
        kind=_arg(command,'--kind');target=_mod(ctx,{'prefix':'check_state_pipeline_prefix','selected':'check_state_pipeline_selected','history':'check_state_history_tail'}[kind])
        args=SimpleNamespace(input=ctx.path(inp))
        if kind=='prefix':
            desc,data,selected,_=target.load(args);orig='four/'+desc['original_output_dir']+'/'
            for s in selected:ctx.emit(orig+s['module']+'.v',base.shard_text(s['rows'],s['certificate'],data['state_bound']),'state pipeline prefix shard')
            ctx.emit(out+'StateClosurePrefixAll.v',base.aggregate([s['module']for s in selected],desc['selected_rows'],data['state_bound'],desc['original_namespace']),'state pipeline prefix aggregate')
        elif kind=='selected':
            data,full,groups,_=target.load(args);schedule=target.prefix.schedule(groups);limit=int(_arg(command,'--limit-shards',len(schedule)));selected=schedule[:limit];names=[]
            for i,s in enumerate(selected):
                n=f'StateSelected{i:03}';names.append(n);ctx.emit(out+n+'.v',base.shard_text(s['rows'],s['certificate'],data['state_bound']),'state pipeline selected shard')
            n='StateSelectedAll'if limit==len(schedule)else f'StateSelectedPrefix{limit:03}'
            ctx.emit(out+n+'.v',base.aggregate(names,sum(len(s['rows'])for s in selected),data['state_bound'],ns),'state pipeline selected aggregate')
        else:
            data,groups,_=target.load(args);names=[]
            for i,(g,rows)in enumerate(groups):
                n=f'HistoryCertificate{i:03}';names.append(n);ctx.emit(out+n+'.v',target.shard_text(rows,g['certificate'],data['state_bound']),'check_state_history_tail.shard_text')
            ctx.emit(out+'HistoryCertificateAll.v',base.aggregate(names,sum(len(rows)for _,rows in groups),data['state_bound'],ns),'state history aggregate')
        return
    data=ctx.read_json(inp);groups=data['groups'];bound=data['state_bound'];names=[];count=0
    for g in groups:
        for offset in range(0,len(g['rows']),base.SHARD_SIZE):
            rows=g['rows'][offset:offset+base.SHARD_SIZE];n=('StateRW'if repwl else'StateClosure')+f'{len(names):03}';names.append(n);count+=len(rows)
            ctx.emit(out+n+'.v',base.shard_text(rows,g['certificate'],bound),'state pipeline/repwl shard_text')
    ctx.emit(out+('StateRWAll.v'if repwl else'StateClosureAll.v'),base.aggregate(names,count,bound,ns),'state pipeline/repwl aggregate')


def simple(ctx, command):
    name=Path(command[1]).stem
    table={
      'check_marker_state':('four/research/state-marker-profile-v2.json','four/build/marker-state/MarkerBoard.v','generate'),
      'check_marker_potential':('four/research/state-marker-potential-v2.json','four/build/marker-potential/PotentialBoard.v','generate'),
      'check_marker_trail':('four/research/state-marker-trail-v2.json','four/build/marker-trail/TrailBoard.v','generate'),
      'check_marker_walls':('four/research/state-marker-walls-v2.json','four/build/marker-walls/WallsBoard.v','generate'),
      'check_state_branches':('four/research/state-branches-input.json','four/build/state-branches/StateBranches.v','generate'),
      'check_state_branch_cycles':('four/research/state-branch-cycles-input.json','four/build/state-branch-cycles/StateBranchCycles.v','generate'),
      'check_alphabet23':('four/research/alphabet23-families.json','four/build/alphabet23/AlphabetBoard.v','generate'),
      'check_alphabet_mask':('four/research/alphabet-mask-input.json','four/build/alphabet-mask/MaskBoard.v','source'),
      'check_state_quotients':('four/research/state-alphabet-quotient-input.json','four/build/state-alphabet-quotient/QuotientBoard.v','generate'),
    }
    if name in table:
        inp,out,fun=table[name]
        if not ctx.need(out):return
        m=_mod(ctx,name)
        # Prefer the module's authoritative frozen input constant.
        p=getattr(m,'INPUT',getattr(m,'BUNDLE',None))
        data=json.loads(p.read_text())if p is not None else ctx.read_json(inp)
        rows=data['rows']
        if name=='check_marker_potential':rows=[r for r in rows if not r['covered_by_v2']]
        if name in ('check_marker_trail','check_marker_walls'):rows=[r for r in rows if not r['covered_by_prior']]
        ctx.emit(out,getattr(m,fun)(rows),name+'.'+fun);return
    data_table={
      'check_state_marker_join':('INPUT','four/build/state-marker-branch/MarkerParent.v'),
      'check_state_b3_joins':('INPUT','four/build/state-b3-branches/B3Parents.v'),
      'check_late_marker_branch':('INPUT','four/build/late-marker-branch/LateMarkerBranch.v'),
    }
    if name in data_table:
        _,out=data_table[name]
        if ctx.need(out):
            m=_mod(ctx,name);data=json.loads(m.INPUT.read_text());ctx.emit(out,m.generate(data),name+'.generate')


def ordinary_boards(ctx, command):
    name=Path(command[1]).stem
    if name=='check_one_state_reach':
        out='four/build/one-state-reach/'
        if not _needed(ctx,out):return
        m=_mod(ctx,name);d=json.loads(m.INPUT.read_text());rows=d['rows'];names=[]
        for start in range(0,len(rows),m.SHARD_SIZE):
            n=f'StateReach{start//m.SHARD_SIZE:03}';names.append(n);ctx.emit(out+n+'.v',m.shard_text(rows[start:start+m.SHARD_SIZE]),name+'.shard_text')
        ctx.emit(out+'StateReachAll.v',m.aggregate(names,len(rows)),name+'.aggregate')
    elif name=='check_weighted_state':
        out=_arg(command,'--output-dir')+'/'
        if not _needed(ctx,out):return
        m=_mod(ctx,name);rows,_=m.load_input(ctx.path(_arg(command,'--input')));names=[]
        for start in range(0,len(rows),16):
            n=f'WeightedState{start//16:04}';names.append(n);ctx.emit(out+n+'.v',m.render_shard(rows[start:start+16]),name+'.render_shard')
        ctx.emit(out+'WeightedStateAll.v',m.aggregate(names,len(rows),4096,_arg(command,'--namespace')),name+'.aggregate')
    elif name=='replay_recorded_closure':
        out=_arg(command,'--build-dir')+'/'
        if not _needed(ctx,out):return
        m=_mod(ctx,'check_closure_wave');d,rows=m.load_input(ctx.path(_arg(command,'--input')));names=[]
        for start in range(0,len(rows),m.SHARD_SIZE):
            n=f'ClosureWave{start//m.SHARD_SIZE:04}';names.append(n);ctx.emit(out+n+'.v',m.shard_source(rows[start:start+m.SHARD_SIZE]),'check_closure_wave.shard_source')
        ctx.emit(out+'ClosureWaveAll.v',m.aggregate_source(names,_arg(command,'--namespace'),rows[0]['bound'],len(rows)),'check_closure_wave.aggregate_source')
    elif name=='check_late_cycles':
        stage=_arg(command,'--stage');out='four/build/late-cycle-proofs/'+stage+'/'
        if not _needed(ctx,out):return
        m=_mod(ctx,name);d=ctx.read_json('four/research/late-cycles-'+stage+'.json');rows=d['rows'];names=[]
        for start in range(0,len(rows),64):
            n=f'Cycle{start//64:03}';names.append(n);ctx.emit(out+n+'.v',m.shard_source(rows[start:start+64],d['bound']),name+'.shard_source')
        ctx.emit(out+'All.v',m.aggregate_source(stage,names,d['bound']),name+'.aggregate_source')
    elif name=='check_late_cycle_sources':
        stage=_arg(command,'--stage');out='four/build/late-cycle-proofs/'+stage+'/NonHalt.v'
        if ctx.need(out):
            m=_mod(ctx,name);d=ctx.read_json('four/research/late-cycles-'+stage+'.json');names=[f'Cycle{i:03}'for i in range((len(d['rows'])+63)//64)];ctx.emit(out,m.generate(stage,names,d['bound']),name+'.generate')


@contextmanager
def _attrs(module, **values):
    previous={name:getattr(module,name)for name in values}
    for name,value in values.items():setattr(module,name,value)
    try:yield
    finally:
        for name,value in previous.items():setattr(module,name,value)


def weighted_reuse(ctx, command):
    tool=Path(command[1]).stem
    if tool=='check_weighted_reuse':
        m=_mod(ctx,tool);name=_arg(command,'--name','pilot')
        out='four/build/weighted-reuse'+(''if name=='pilot'else'/'+name)+'/'
        if not _needed(ctx,out):return
        cert=_arg(command,'--certificates','four/research/weighted-pilot-certificates.jsonl')
        rows0=m.bundle_decode(ctx.path(cert).read_text());sources=[r if'graph'in r else m.unpack(r)for r in rows0 if'graph'in r or r.get('kind')=='weighted']
        data=ctx.read_json('four/research/weighted-reuse'+(''if name=='pilot'else'-'+name)+'-input.json')
        ns='BBB24WeightedReuse'+(''if name=='pilot'else name.capitalize())
        with _attrs(m,BUILD=ctx.path(out),NAMESPACE=ns),_capture(ctx,'check_weighted_reuse.generate'):
            m.generate(sources,data['rows'])
    elif tool=='check_weighted_suffix':
        m=_mod(ctx,tool);name=_arg(command,'--name','pilot');out='four/build/weighted-suffix/'+name+'/'
        if not _needed(ctx,out):return
        cert=_arg(command,'--certificates','four/research/weighted-pilot-certificates.jsonl')
        rows0=m.bundle_decode(ctx.path(cert).read_text());sources=[r if'graph'in r else m.unpack(r)for r in rows0 if'graph'in r or r.get('kind')=='weighted']
        data=ctx.read_json('four/research/weighted-suffix-'+name+'-input.json')
        with _attrs(m.direct,BUILD=m.direct.BUILD,NAMESPACE=m.direct.NAMESPACE),_capture(ctx,'check_weighted_suffix.generate',deferred=True):
            m.generate(sources,data['rows'],ctx.path(out),'BBB24WeightedSuffix'+name.capitalize())
    elif tool.startswith('check_weighted_stream_reuse'):
        name=_arg(command,'--name');out='four/build/weighted-stream/'+name+'/'
        if not _needed(ctx,out):return
        pipeline=_mod(ctx,'check_weighted_stream_reuse');wrapper=_mod(ctx,tool)
        pool,_,_=pipeline.sources(ctx.path(_arg(command,'--registry')))
        data=ctx.read_json('four/research/weighted-stream-reuse/'+name+'-input.json')
        values={}
        if tool.endswith('_v3'):
            values={'render':wrapper.render}
        elif tool.endswith(('_v7','_v8','_v9')):
            coq=_mod(ctx,'check_weighted_stream_reuse_v5')
            values={'template':wrapper.template if tool.endswith('_v9')else coq.template,
                    'COMMON':wrapper.COMMON if tool.endswith('_v9')else coq.COMMON}
            if tool.endswith(('_v8','_v9')):
                transform=_mod(ctx,'weighted_transform_v2').transform
                with _attrs(coq,transform=transform),_attrs(pipeline,**values),_capture(ctx,tool+' pure generate'):
                    pipeline.generate(pool,data['rows'],ctx.path(out),'BBB24WeightedStream'+name.capitalize(),True)
                return
        with _attrs(pipeline,**values),_capture(ctx,tool+' pure generate'):
            pipeline.generate(pool,data['rows'],ctx.path(out),'BBB24WeightedStream'+name.capitalize(),True)


def _ready_sources(ctx, module, registries):
    """Metadata-only source references; existing helper also demands old .v."""
    sources=[]
    for rel in registries:
        registry=ctx.read_json('four/'+rel);report=ctx.read_json('four/'+str(Path(rel).with_name('check.json')))
        ns=report['descriptor']['load_paths'][0]['namespace'];packed=[]
        for entry in registry['bundles']:
            packed.extend(module.bundle_decode(ctx.path('four/'+entry['path']).read_text()))
        count=Counter()
        for row,result in zip(packed,report['results']):
            assert row['machine']==result['machine']and result['status']=='coq_checked'
            name=result['module'];sub=count[name];count[name]+=1
            if row['kind']=='weighted':
                sources.append(dict(machine=row['machine'],mirror=row['mirror'],n=row['n'],t=row['t'],module=ns+'.'+name,proof=ns+'.'+name+f'.R{sub:04}'))
    return sources


def ready_reuse(ctx, command):
    tool=Path(command[1]).stem;name=_arg(command,'--name');out='four/build/ready-reuse/'+name+'/'
    if not _needed(ctx,out):return
    m=_mod(ctx,tool);base=_mod(ctx,'check_weighted_stream_reuse')
    data=ctx.read_json('four/research/ready-reuse/'+name+'-input.json')
    sources=_ready_sources(ctx,m,data['source_registries'])
    remap=lambda rel:rel[:-len('WeightedStreamAll.v')]+'ReadyReuseAll.v'if rel.endswith('/WeightedStreamAll.v')else rel
    with _attrs(base,COMMON=m.COMMON,template=m.template,groups=m.groups),_capture(ctx,tool+' pure generate',remap):
        base.generate(sources,data['rows'],ctx.path(out),'BBB24ReadyReuse'+name.capitalize(),True)


def conjugates(ctx, command):
    name=_arg(command,'--name','r000'if Path(command[1]).stem=='check_conjugate_batch'else'r001')
    out='four/build/conjugate/'+name+'/'
    if not _needed(ctx,out):return
    m=_mod(ctx,'check_conjugate_batch')
    config=ctx.read_json(_arg(command,'--config','four/research/conjugate-sources-'+name+'.json'))
    data=ctx.read_json(_arg(command,'--input','four/research/conjugate-input-'+name+'.json'))
    machines=[]
    for source in config['sources']:
        new=[]
        for entry in source['machine_inputs']:
            if entry['format']=='checked_affine_tsv':new.extend(r['machine']for r in _csv(ctx,'four/'+entry['path']))
            else:new.extend(m.machine_rows(entry))
        source['count']=len(new);machines.extend(new)
    with _capture(ctx,'check_conjugate_batch.generate'):
        m.generate(config,machines,data['rows'],ctx.path(out),'BBB24Conjugate'+name.capitalize())


def affine_children(ctx, command):
    name=_arg(command,'--name');out='four/build/affine-children/'+name+'/Children.v'
    if not ctx.need(out):return
    m=_mod(ctx,'check_affine_wave')
    with _capture(ctx,'affine child certificate texts'):
        data,paths=m.load_bundle(ctx.path(_arg(command,'--input')),ctx.path('four/build/affine-children/'+name+'/certificates'))
    text=m.shard(paths,data['bound'],data['cfuel'],data['fuel']).split('Lemma board_pending_checked',1)[0]
    text+='\nFrom BBB24 Require Import StateOnlyCloseout.\n'
    text+=f'''Lemma state_small_sound : StateBoardSound (N.to_nat {data['bound']}%N) board.
Proof. intros family Hin tm Hle. exact (proj1 (board_small_sound family Hin tm Hle)). Qed.
Lemma state_sound : StateBoardSound score board.
Proof. intros family Hin tm Hle. exact (proj1 (board_sound family Hin tm Hle)). Qed.
Print Assumptions board_small_sound.
'''
    ctx.emit(out,text,'check_affine_children source construction')


def _unpack_json(ctx, rel):
    data=ctx.read_json(rel)
    if data.get('encoding')=='zlib-base64':
        import base64,zlib
        raw=zlib.decompress(base64.b64decode(data['data'],validate=True))
        assert hashlib.sha256(raw).hexdigest()==data['uncompressed_sha256']
        return json.loads(raw)
    return data


def next_boards(ctx):
    """The supplementary boards, from their frozen compact certificates."""
    if _needed(ctx,'four/build/next-rw/'):
        m=_mod(ctx,'replay_next_rw')
        report=ctx.read_json('four/research/next-rw-batch32v1-report.json')
        # This existing prepare function returns text only. It checks tracked
        # pins, without reading generated source/objects or launching jobs.
        checked_pins=m.checked_pins
        def available_pins(root,pins):
            # The frozen helper tests is_file before its first read. Make its
            # explicitly named input files available to the isolated tree.
            for rel in pins:ctx.require_input('four/'+rel)
            return checked_pins(root,pins)
        with _attrs(m,checked_pins=available_pins):
            plan=m.prepare_document(report,ctx.repo/'four')
        for rel,text in plan['sources'].items():
            ctx.emit('four/'+rel,text,'replay_next_rw.prepare_document')
    for batch in ('nonrw-v1','burn2-rw128-v1','burn2-rw256-offset256-v1'):
        out='four/build/next-timeout/'+batch+'/'
        if not _needed(ctx,out):continue
        m=_mod(ctx,'check_closure_wave');pack=_mod(ctx,'check_campaign').packed
        report=ctx.read_json('four/research/next-timeout-'+batch+'-summary.json')
        desc=report['board_descriptor'];inv=desc['inventories'][0]
        data=_unpack_json(ctx,'four/'+inv['path'])
        assert data['columns']==m.FIELDS
        rows=[dict(zip(data['columns'],r))for r in data['rows']]
        assert len(rows)==desc['rows']==report['checked_families']
        names=['Row'+hashlib.sha256(r['machine'].encode()).hexdigest()[:16]for r in rows]
        for name,row in zip(names,rows):
            ctx.emit(out+name+'.v',m.shard_source([row]),'check_next_timeout closure.shard_source')
        inventory='['+';'.join(str(pack(r['machine']))+'%N'for r in rows)+']'
        text=m.aggregate_source(names,desc['module'].rsplit('.',1)[0],4096,len(rows))+f'''
From BBB24 Require Import BoardManifest.
Definition inventory : list N := {inventory}.
Lemma inventory_checked : manifest_check inventory board = true.
Proof. vm_compute. reflexivity. Qed.
Theorem inventory_exact : manifest_board inventory = board.
Proof. apply manifest_check_sound. exact inventory_checked. Qed.
Print Assumptions inventory_exact.
'''
        ctx.emit(out+'All.v',text,'check_next_timeout aggregate plus exact inventory')
    if _needed(ctx,'four/build/next-weighted-state/full/'):
        m=_mod(ctx,'check_weighted_state');agg=_mod(ctx,'check_state_pipeline_batch').aggregate
        report=ctx.read_json('four/research/next-weighted-state-checked.json');desc=report['descriptor']
        rows,inputs=m.load_input(ctx.path('four/research/next-weighted-state-input.json'))
        assert inputs==report['inputs']
        rows=rows[:report['selected_rows']];out='four/build/next-weighted-state/full/'
        names=[f'WeightedState{i:04}'for i in range((len(rows)+7)//8)]
        for i,name in enumerate(names):
            ctx.emit(out+name+'.v',m.render_shard(rows[i*8:(i+1)*8]),'check_weighted_state.render_shard')
        ctx.emit(out+'WeightedStateAll.v',agg(names,len(rows),4096,'BBB24NextWeightedState'),'check_state_pipeline_batch.aggregate')
        ctx.emit(out+'WeightedStateInventory.v',_mod(ctx,'check_campaign').inventory_source({**desc,'machines':[r['machine']for r in rows]}),'check_campaign.inventory_source')
    if _needed(ctx,'four/build/next-capacity/'):
        wrapper=_mod(ctx,'replay_next_capacity')
        frozen=ctx.read_json('four/research/next-capacity-inventory-check.json')
        for kind,name,namespace,count in wrapper.KINDS:
            weighted_portable(ctx,['python3','four/tools/replay_portable_weighted.py',
                '--report',f'four/research/next-capacity-{kind}-check.json',
                '--registry',f'four/research/next-capacity-{kind}-registry.json',
                '--output-dir',f'four/build/next-capacity/{kind}-proof'])
            report=ctx.read_json(f'four/research/next-capacity-{kind}-check.json')
            inventory=ctx.read_json(f'four/research/next-capacity-{kind}-checked-machines.json')
            desc=next(d for d in frozen['boards']if d['id']=='next_'+kind)
            text=wrapper.validate_contract(kind,report,inventory,desc)
            ctx.emit('four/build/next-capacity/inventory-proof/'+name+'.v',text,'replay_next_capacity.validate_contract pure inventory source')


def render(ctx):
    """Emit all requested campaign namespaces; returns dispatched recipe IDs."""
    affine_foundations(ctx)
    plan=ctx.read_json('four/research/campaign-build.json');done=[]
    for step in plan['steps']:
        command=step['command']
        if len(command)<2 or command[0]!='python3':continue
        tool=Path(command[1]).stem
        if tool in ('replay_affine_wave','prepare_affine_templates'):affine_wave(ctx,command)
        elif tool=='replay_portable_weighted':weighted_portable(ctx,command)
        elif tool=='replay_portable_weighted_closeout':weighted_closeout(ctx,command)
        elif tool in ('check_state_pipeline_batch','check_state_repwl_batch','check_state_pipeline_cached','check_state_repwl_recorded'):pipeline(ctx,command)
        elif tool=='check_affine_children':affine_children(ctx,command)
        elif tool in ('check_weighted_reuse','check_weighted_suffix')or tool.startswith('check_weighted_stream_reuse'):weighted_reuse(ctx,command)
        elif tool in ('check_ready_reuse','check_ready_reuse_v2'):ready_reuse(ctx,command)
        elif tool in ('check_conjugate_batch','compile_conjugate_extension'):conjugates(ctx,command)
        elif tool in ('check_one_state_reach','check_weighted_state','replay_recorded_closure','check_late_cycles','check_late_cycle_sources'):ordinary_boards(ctx,command)
        else:simple(ctx,command)
        done.append(step['id'])
    # These v4 weighted providers are used by the later whole-inventory union.
    for kind in ('ordinary','weighted'):
        weighted_portable(ctx,['python3','four/tools/replay_portable_weighted.py',
            '--report',f'four/research/burn2-capacity-{kind}-check.json',
            '--registry',f'four/research/burn2-capacity-{kind}-registry.json',
            '--output-dir',f'four/build/burn2-capacity/{kind}-proof'])
    next_boards(ctx)
    return done
