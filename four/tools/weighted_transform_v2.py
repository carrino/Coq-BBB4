"""Rename reusable certificates without mutating aliased coefficient vectors.

Compact-v2 decoding may share a plain values list across distinct certificate
components. Each renamed component therefore receives a fresh vector. All
results remain untrusted inputs to the unchanged Coq tail/suffix checker.
"""
import copy
from weighted_reuse_search import node


def transform(source,p,swap):
    row=copy.deepcopy(source);g=row['graph']
    g['nodes']=[node(c,p,swap)for c in g['nodes']]
    certs={}
    for target,cert in row['certs'].items():
        target=int(target);renamed=4*((target//4)^swap)+p[target%4]
        cert['guards']=[[p[x]for x in word]for word in cert['guards']]
        cert['inside']=[node(c,p,swap)for c in cert['inside']]
        for comp in cert['components']:
            if comp['kind']=='rank':continue
            old=comp['values'];values=old[:]
            count=12 if comp['kind']=='linear' else 16
            for block in range(0,count,4):
                for symbol in range(4):values[block+p[symbol]]=old[block+symbol]
            comp['values']=values
        certs[str(renamed)]=cert
    row['certs']=certs
    return row
