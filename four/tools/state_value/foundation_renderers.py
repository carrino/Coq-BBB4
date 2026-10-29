"""Pure foundation/campaign adapters; no native or Coq process is run."""
import gzip,hashlib,json


def templates(ctx):
    for target,source in ctx.spec.get('template_matches',{}).items():
        if ctx.need(target):
            ctx.emit(target,ctx.path(source).read_bytes(),'explicit source template '+source)


def campaigns(ctx):
    mod=ctx.module('check_campaign_v2')
    inventory=ctx.module('campaign_next_boards')
    # The original immutable manifest supplies exact descriptor and row order.
    candidates=[('four/research/campaign-final-input.json','four/build/campaign-final','BBB24CampaignFinal'),
                ('four/research/burn12-campaign-input.json','four/build/burn12-campaign','BBB24Burn12Campaign')]
    for source,prefix,namespace in candidates:
        if not ctx.any_needed(prefix):continue
        data=ctx.read_json(source);boards=data['boards']
        for board in boards:
            board=dict(board)
            board['machines']=[m for spec in board['inventories']for m in mod.read_inventory(spec)]
            ctx.emit(prefix+'/'+board['id']+'.v',inventory.inventory_source(board),'campaign exact inventory')
        ctx.emit(prefix+'/Campaign.v',mod.aggregate_source(namespace,boards),'campaign aggregate')


def blank_certificates(ctx):
    prefix='four/build/burn13-state-census'
    if not ctx.any_needed(prefix):return
    data=ctx.read_json('four/research/burn13-state-census-blank-input.json')
    meta=ctx.read_json('four/research/state-global-blank-certificates-manifest.json')
    packed=ctx.path('four/research/state-global-blank-certificates.json.gz').read_bytes()
    assert hashlib.sha256(packed).hexdigest()==meta['gzip_sha256']
    raw=gzip.decompress(packed);assert hashlib.sha256(raw).hexdigest()==meta['plain_sha256']
    cert=json.loads(raw);units=cert['units']
    assert len(units)==len(data['plan']['units'])==meta['unit_count']
    assert cert['recipe_sha256']==hashlib.sha256(ctx.path('four/research/burn13-state-census-blank-input.json').read_bytes()).hexdigest()
    for i,(unit,expected)in enumerate(zip(units,data['plan']['units'])):
        encoded=json.dumps(unit,separators=(',',':')).encode()
        assert len(encoded)==expected['compact_bytes']
        assert hashlib.sha256(encoded).hexdigest()==expected['compact_sha256']
        assert unit['dependencies']==expected['direct_dependencies']
    mod=ctx.module('check_burn13_state_census_blank');mapping=mod.unit_module(data)
    for index in range(len(data['plan']['modules'])):
        rel=prefix+f'/M{index:03}.v'
        if ctx.need(rel):
            source,_=mod.module_source(index,data,units,mapping)
            ctx.emit(rel,source,'untrusted frozen blank node certificates')


def blank_closeout(ctx):
    if not ctx.any_needed('four/build/burn15-blank-closeout'):return
    mod=ctx.module('check_burn15_blank_closeout')
    data=ctx.read_json('four/research/burn15-blank-closeout-input.json')
    routing=ctx.read_json('four/research/burn15-legacy-routing-input.json')
    data['_routed_origins']=routing['origins']
    # These functions only construct source strings and write source files.
    # The context read/write guard forbids old object/receipt dependencies.
    for function in(mod.source_files,mod.frontier_files,mod.census_files):
        function(data)


def render(ctx):
    templates(ctx)
    late_prefix='four/build/late-marker-branch/LatePrefix.v'
    if ctx.need(late_prefix):
        mod=ctx.module('check_late_marker_branch')
        ctx.emit(late_prefix,mod.prefix(ctx.read_json('four/research/late-marker-branch-input.json')),
                 'late marker undefined-cell prefix renderer')
    campaigns(ctx)
    blank_certificates(ctx)
    blank_closeout(ctx)
    if ctx.need('four/build/state-global-foundation/GlobalSources.v'):
        mod=ctx.module('render_state_global_sources')
        origins=ctx.read_json('four/research/state-global-origins-input.json')
        ctx.emit('four/build/state-global-foundation/GlobalSources.v',
                 mod.render_global_sources(origins),'67 whole proved inventory manifest')

    # Current Lean Final route; the original whole67 route stays independently frozen.
    import lean_renderers
    lean_renderers.render(ctx)

    import light_renderers
    light_renderers.render(ctx)
