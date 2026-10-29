"""Serialize untrusted template data for the extracted tail selector.

Numbers used for Coq Z remain exact signed binary strings. Natural counts are
checked by the selector's host parser; any producer failure stops selection.
Every selected success is separately replayed by the Coq proof producer.
"""
import group_families as grouping
from generate_pipeline_examples import codes
from weighted_codec_v2 import unpack
from weighted_reuse_search import original_sets,transform


def serialize(pool,chunks):
    tokens=[]
    def put(value):tokens.append(str(value))
    def natural(value):
        if type(value)is not int or value<0:raise ValueError('Natural expected')
        put(value)
    def integer(value):
        if type(value)is not int:raise ValueError('Integer expected')
        put(('-'if value<0 else'')+bin(abs(value))[2:])
    def boolean(value):
        if type(value)is not bool:raise ValueError('Boolean expected')
        put(int(value))
    def sequence(values,emit):
        natural(len(values))
        for value in values:emit(value)
    def word(xs):sequence(xs,natural)
    def node(c):
        q,l,h,r=c;natural(q);word(l);natural(h);word(r)
    natural(len(chunks))
    for rows in chunks:
        raw=pool[rows[0][1]];source=raw if 'graph'in raw else unpack(raw)
        p=(0,)+tuple(map(int,rows[0][2]));swap=rows[0][3];g=source['graph']
        changed=transform(source,p,swap)
        loop=grouping.render(grouping.rename(grouping.parse(g['machine']),p,mirror=bool(g['mirror']),swap=swap))
        word(codes(loop));natural(g['n']);left,right=original_sets(source)
        for grams in [left,right]:sequence([[p[x]for x in w]for w in sorted(grams)],word)
        sequence(changed['graph']['nodes'],node)
        certs=sorted(changed['certs'].items(),key=lambda x:int(x[0]));natural(len(certs))
        for target,cert in certs:
            natural(int(target));natural(cert['k']);sequence(cert['guards'],word);sequence(cert['inside'],node)
            natural(len(cert['components']))
            for comp in cert['components']:
                if comp['kind']=='rank':natural(0);word(comp['rank']);continue
                values=comp['values'];active=set(comp['active'])
                if comp['kind']=='linear':
                    natural(1);counts=[]
                    for side in range(3):
                        for symbol in [1,2,3]:
                            value=values[4*side+symbol]
                            if value:counts.append((value,side,symbol))
                    natural(len(counts))
                    for count in counts:
                        for value in count:natural(value)
                    word(values[12:])
                elif comp['kind']=='w':
                    natural(2)
                    for value in values[:16]:integer(value)
                    sequence(values[16:],integer)
                else:raise ValueError('Unknown component')
                sequence([i in active for i in range(len(g['nodes']))],boolean)
        natural(len(rows))
        for machine,_,_,_,mirror,boot in rows:word(codes(machine));boolean(mirror);natural(boot)
    return ' '.join(tokens)+'\n'
