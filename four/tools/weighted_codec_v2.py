"""Compact, lossless data encoding for weighted certificates (no trusted logic).

Context strings are state + left window + head + right window. Integer vectors
use [value, repeat-count] runs, and active-node sets use [start, length] ranges.
Decoding is bounded by the declared context count before Coq source generation.
"""
from itertools import groupby
import base64
import hashlib
import json
import zlib


def bundle_encode(rows):
    payload=''.join(json.dumps(row,separators=(',',':'))+'\n' for row in rows).encode()
    if len(payload)>4*1024*1024:raise ValueError('Decoded bundle exceeds 4MiB')
    return json.dumps({'encoding':'zlib+base64-jsonl-v1','rows':len(rows),
                       'decoded_bytes':len(payload),'decoded_sha256':hashlib.sha256(payload).hexdigest(),
                       'data':base64.b64encode(zlib.compress(payload,9)).decode()},indent=2)+'\n'


def bundle_decode(text):
    if not text.lstrip().startswith('{\n'):
        return [json.loads(line) for line in text.splitlines()]
    wrapped=json.loads(text)
    if wrapped.get('encoding')!='zlib+base64-jsonl-v1':raise ValueError('Unknown bundle encoding')
    size=wrapped['decoded_bytes']
    if type(size) is not int or not 0<size<=4*1024*1024:raise ValueError('Invalid decoded bundle size')
    decoder=zlib.decompressobj()
    payload=decoder.decompress(base64.b64decode(wrapped['data'],validate=True),size+1)
    if not decoder.eof or decoder.unused_data or len(payload)!=size:raise ValueError('Invalid compressed bundle length')
    if hashlib.sha256(payload).hexdigest()!=wrapped['decoded_sha256']:raise ValueError('Decoded bundle hash differs')
    rows=[json.loads(line) for line in payload.decode().splitlines()]
    if len(rows)!=wrapped['rows']:raise ValueError('Decoded bundle row count differs')
    return rows

def pack_vector(values):
    return [[value,len(list(group))] for value,group in groupby(values)]

def unpack_vector(runs,expected):
    if type(expected) is not int or not 0<=expected<=100000:
        raise ValueError('Invalid vector length')
    out=[]
    for pair in runs:
        if len(pair)!=2 or any(type(x) is not int for x in pair) or pair[1]<1 or len(out)+pair[1]>expected:
            raise ValueError('Invalid vector run')
        out += [pair[0]]*pair[1]
    if len(out)!=expected:raise ValueError('Vector length mismatch')
    return out

def pack_active(values):
    out=[]
    for value in values:
        if out and out[-1][0]+out[-1][1]==value:out[-1][1]+=1
        else:out.append([value,1])
    return out

def unpack_active(runs,size):
    values=[]
    for pair in runs:
        if len(pair)!=2 or any(type(x) is not int for x in pair):raise ValueError('Invalid active range')
        start,length=pair
        if start<0 or length<1 or start+length>size or (values and start<=values[-1]):raise ValueError('Invalid active range')
        values.extend(range(start,start+length))
    return values

def word(value):return ''.join(map(str,value))

def unword(value):
    if not isinstance(value,str) or any(c not in '0123' for c in value):raise ValueError('Invalid word')
    return [int(c) for c in value]

def pack(row):
    graph=row['graph'];width=graph['n']
    result={k:graph[k] for k in ['machine','mirror','n','t','fuel','rounds']}
    result['kind']='weighted'
    result['nodes']=[]
    for q,left,head,right in graph['nodes']:
        if len(left)!=width or len(right)!=width:raise ValueError('Nonuniform context width')
        result['nodes'].append(chr(65+q)+word(left)+str(head)+word(right))
    result['certs']={}
    result['components']=[]
    component_ids={}
    for target,cert in row['certs'].items():
        compact={'k':cert['k'],'guards':[word(g) for g in cert['guards']],
                 'inside':[[q,word(left),head,word(right)] for q,left,head,right in cert['inside']],
                 'components':[]}
        for comp in cert['components']:
            if comp['kind']=='rank':
                raw={'kind':'rank','rank':comp['rank']}
                compressed={'kind':'rank','rank_rle':pack_vector(comp['rank'])}
            else:
                raw={'kind':comp['kind'],'values':comp['values']}
                compressed={'kind':comp['kind'],'values_rle':pack_vector(comp['values'])}
            packed=compressed if len(json.dumps(compressed))<len(json.dumps(raw)) else raw
            if comp['kind']!='rank':
                active=pack_active(comp['active'])
                if len(json.dumps(active))<len(json.dumps(comp['active'])):packed['active_runs']=active
                else:packed['active']=comp['active']
            key=json.dumps(packed,sort_keys=True,separators=(',',':'))
            if key not in component_ids:
                component_ids[key]=len(result['components']);result['components'].append(packed)
            compact['components'].append(component_ids[key])
        result['certs'][str(target)]=compact
    return result

def unpack(row):
    if row['kind']!='weighted':raise ValueError('Expected weighted certificate')
    width=row['n']
    if type(width) is not int or not 1<=width<=8:raise ValueError('Invalid context width')
    graph={k:row[k] for k in ['machine','mirror','n','t','fuel','rounds']}
    graph.update(states=2,symbols=4,nodes=[])
    for text in row['nodes']:
        if not isinstance(text,str) or len(text)!=2*width+2 or text[0] not in 'AB':raise ValueError('Invalid context encoding')
        digits=unword(text[1:])
        graph['nodes'].append([ord(text[0])-65,digits[:width],digits[width],digits[width+1:]])
    size=len(graph['nodes'])
    if not 0<size<=100000:raise ValueError('Invalid context count')
    certs={}
    for target,cert in row['certs'].items():
        full={'k':cert['k'],'guards':[unword(g) for g in cert['guards']],
              'inside':[[q,unword(left),head,unword(right)] for q,left,head,right in cert['inside']],
              'components':[]}
        for index in cert['components']:
            if type(index) is not int or not 0<=index<len(row['components']):raise ValueError('Invalid component reference')
            comp=row['components'][index]
            if comp['kind']=='rank':
                if ('rank' in comp)==('rank_rle' in comp):raise ValueError('Ambiguous rank encoding')
                ranks=comp['rank'] if 'rank' in comp else unpack_vector(comp['rank_rle'],size)
                if len(ranks)!=size or any(type(x) is not int for x in ranks):raise ValueError('Invalid rank vector')
                full['components'].append({'kind':'rank','rank':ranks})
            elif comp['kind'] in ['linear','w']:
                if ('values' in comp)==('values_rle' in comp) or ('active' in comp)==('active_runs' in comp):raise ValueError('Ambiguous coefficient encoding')
                expected=size+(12 if comp['kind']=='linear' else 16)
                values=comp['values'] if 'values' in comp else unpack_vector(comp['values_rle'],expected)
                if len(values)!=expected or any(type(x) is not int for x in values):raise ValueError('Invalid coefficient vector')
                active=comp['active'] if 'active' in comp else unpack_active(comp['active_runs'],size)
                if any(type(x) is not int or not 0<=x<size for x in active):raise ValueError('Invalid active nodes')
                full['components'].append({'kind':comp['kind'],'values':values,'active':active})
            else:raise ValueError('Invalid component kind')
        certs[target]=full
    return {'graph':graph,'certs':certs}
