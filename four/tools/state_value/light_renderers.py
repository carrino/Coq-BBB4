"""Pure current lightweight provider and opaque448 source generation."""
import hashlib

def index(ctx):
    prefix='four/build/state-light-index189'
    if not ctx.any_needed(prefix):return
    mod=ctx.module('render_state_light_index189')
    pin=ctx.read_json('four/research/state-light-index189-manifest.json')
    path=ctx.path('four/research/state-light-index189.json.gz')
    if hashlib.sha256(path.read_bytes()).hexdigest()!=pin['gzip_rows_sha256']:raise ValueError('changed lightweight routed rows')
    count=0
    for group in mod.read_groups(path):
        uid=group['provider_index'];count+=group['count']
        for name,text in [(f'Data{uid:03}.v',mod.data_source(group)),(f'Adapter{uid:03}.v',mod.adapter_source(group))]:
            if ctx.need(prefix+'/'+name):ctx.emit(prefix+'/'+name,text,'compact routed byte data and checked provider transfer')
    if count!=190809:raise ValueError('wrong lightweight row count')
    for name,make in [('IndexData.v',mod.index_source),('AggregateSound.v',mod.aggregate_source)]:
        if ctx.need(prefix+'/'+name):ctx.emit(prefix+'/'+name,make(),'light data/proof layer assembly')

def opaque(ctx):
    prefix='four/build/state-opaque-census448'
    if not ctx.any_needed(prefix):return
    import base64,gzip,json
    mod=ctx.module('render_state_opaque_byte448')
    archive=ctx.path('four/research/state-global-census-words.jsonl.gz')
    pin=ctx.read_json('four/research/state-global-census-words-manifest.json')
    if hashlib.sha256(archive.read_bytes()).hexdigest()!=pin['gzip_sha256']:raise ValueError('changed byte-witness archive')
    templates={name:ctx.path('four/proof-sources/state-opaque-byte448/'+name).read_text()for name in mod.TEMPLATES}
    for name,wanted in mod.TEMPLATES.items():
        if hashlib.sha256(templates[name].encode()).hexdigest()!=wanted:raise ValueError('changed byte-witness template '+name)
    metadata=[];batch=[];stream=hashlib.sha256();nodes=0
    with gzip.open(archive,'rt',encoding='utf-8')as source:
        header=json.loads(next(source))
        if header['format']!='BBB24 packed census word data v1'or header['units']!=448:raise ValueError('changed word format')
        for line in source:
            row=json.loads(line);uid=row['id']
            if uid!=len(metadata):raise ValueError('changed unit order')
            raw=base64.b64decode(row.pop('words_base64'),validate=True);words=mod.decode(raw)
            if len(words)!=row['nodes']or mod.encode(words)!=raw:raise ValueError('changed word encoding')
            for ordinal,word in enumerate(words):stream.update(f'{uid}:{ordinal}:{word}\n'.encode())
            metadata.append(row);batch.append((row,raw));nodes+=len(words)
            if len(batch)==16:
                name=f'CheckBatch{uid//16:03}.v'
                if ctx.need(prefix+'/'+name):ctx.emit(prefix+'/'+name,mod.batch_source(batch),'ordinary byte witnesses inside opaque checked-certificate proofs')
                batch=[]
    if batch or len(metadata)!=448 or nodes!=1495171 or stream.hexdigest()!=mod.STREAM:raise ValueError('changed word stream')
    if mod.metadata_source(metadata)!=templates['Metadata.v']:raise ValueError('archive metadata differs from reviewed template')


def render(ctx):
    index(ctx)
    opaque(ctx)
