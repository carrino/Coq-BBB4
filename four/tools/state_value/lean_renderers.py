"""Pure Lean inventory, compact residual and original packed-unit adapters."""
import hashlib,json

def residual(ctx):
    prefix='four/build/state-global-residual485/proof'
    if not ctx.any_needed(prefix):return
    mod=ctx.module('render_state_residual485')
    base='four/research/state-residual485/'
    registry=ctx.read_json(base+'registry.json')
    metadata=ctx.read_json(base+'renderer-versions.json')
    rows=[]
    for bundle in registry['bundles']:
        path=ctx.path(base+bundle['path']);raw=path.read_bytes()
        if len(raw)!=bundle['bytes']or hashlib.sha256(raw).hexdigest()!=bundle['sha256']:raise ValueError('changed compact residual bundle')
        rows.extend(mod.bundle_decode(raw.decode('utf-8')))
    machine_hash=hashlib.sha256(('\n'.join(r['machine']for r in rows)+'\n').encode()).hexdigest()
    if len(rows)!=registry['rows']or len(rows)!=metadata['rows']or machine_hash!=metadata['machine_order_sha256']:raise ValueError('changed residual row order')
    versions=dict(zip((r['machine']for r in rows),metadata['renderers']))
    if len(versions)!=485 or len(metadata['renderers'])!=485:raise ValueError('wrong residual renderer count')
    for offset in range(0,len(rows),8):
        target=prefix+f'/Part{offset//8:03}.v'
        if ctx.need(target):ctx.emit(target,mod.shard(rows[offset:offset+8],versions),'untrusted public compact residual rows')
    if ctx.need(prefix+'/All.v'):ctx.emit(prefix+'/All.v',mod.aggregate(rows),'compact residual whole-board aggregate')

def inventory(ctx):
    target='four/build/state-lean-global-sources/LeanGlobalSources.v'
    if not ctx.need(target):return
    mod=ctx.module('render_state_lean_global')
    ctx.emit(target,mod.render(ctx.read_json('four/research/state-lean-providers.json')),'ordered189 provider inventory')

def units(ctx):
    prefix='four/build/state-global-units'
    if not(ctx.any_needed(prefix+'/data')or any(ctx.need(prefix+'/proof/'+n)for n in ['Families.v','Checks.v','ChecksPilot.v','Bounds.v','Exports.v'])):return
    mod=ctx.module('render_state_packed_units')
    metadata=[];words_hash=hashlib.sha256();node_count=0
    data=ctx.path('four/research/state-global-census-words.jsonl.gz')
    pin=ctx.read_json('four/research/state-global-census-words-manifest.json')
    if hashlib.sha256(data.read_bytes()).hexdigest()!=pin['gzip_sha256']:raise ValueError('changed packed census data')
    for row in mod.iter_units(data):
        uid=row['id'];node_count+=len(row['words'])
        for ordinal,word in enumerate(row['words']):words_hash.update(f'{uid}:{ordinal}:{word}\n'.encode())
        target=prefix+f'/data/Unit{uid:03}.v'
        if ctx.need(target):ctx.emit(target,mod.render_unit(row),'untrusted literal packed census word data')
        metadata.append({k:v for k,v in row.items()if k!='words'})
    if len(metadata)!=448 or node_count!=pin['node_count']or words_hash.hexdigest()!=pin['packed_words_sha256']:raise ValueError('changed packed census word stream')
    emitters={'Families.v':lambda:mod.render_families(metadata),
              'Checks.v':lambda:mod.render_checks(list(range(448))),
              'ChecksPilot.v':lambda:mod.render_checks([87,18,381,447]),
              'Bounds.v':lambda:mod.render_bounds(metadata),
              'Exports.v':lambda:mod.render_exports(metadata)}
    for name,emit in emitters.items():
        target=prefix+'/proof/'+name
        if ctx.need(target):ctx.emit(target,emit(),'pure packed census proof skeleton from parent metadata')

def render(ctx):
    residual(ctx)
    inventory(ctx)
    units(ctx)
