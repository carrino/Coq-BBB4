"""Render an untrusted OCaml selector for the extracted weighted-tail checks.

The output selects candidate rows only. The Coq producer must still prove every
success with the original Boolean checker and kernel-audit the resulting board.
"""
import group_families as grouping
from generate_pipeline_examples import codes
from weighted_codec_v2 import unpack
from weighted_reuse_search import original_sets,transform

HEADER='''open Weighted_tail
let pos bits =
 if String.length bits=0 || bits.[0]<>'1' then invalid_arg "positive";
 let p=ref XH in
 for i=1 to String.length bits-1 do
 p:=(match bits.[i]with '0'->XO !p|'1'->XI !p|_->invalid_arg "bit") done;!p
let z bits = if bits="0" then Z0 else if bits.[0]='-' then
 Zneg(pos(String.sub bits 1(String.length bits-1)))else Zpos(pos bits)
let bound=Npos(pos "1000000000000")
'''


def seq(xs):return '['+';'.join(map(str,xs))+']'
def syms(xs):return seq('S'+str(x) for x in xs)
def integer(v):
    if type(v)is not int:raise ValueError('Integer required')
    return '(z "'+('-'if v<0 else'')+bin(abs(v))[2:]+'")'
def node(c):
    q,l,h,r=c
    return '(St'+chr(65+q)+',(('+syms(l)+',S'+str(h)+'),'+syms(r)+'))'


def template(raw,rows,name):
    source=raw if 'graph' in raw else unpack(raw)
    p=(0,)+tuple(map(int,rows[0][2]));swap=rows[0][3]
    changed=transform(source,p,swap);g=source['graph']
    body=f'module {name} = struct\nlet nodes='+seq(node(c)for c in changed['graph']['nodes'])+'\n'
    branches=[]
    for target,cert in sorted(changed['certs'].items(),key=lambda x:int(x[0])):
        components=[]
        for comp in cert['components']:
            kind=comp['kind']
            if kind=='rank':
                components.append('WRank(wc_table 0 nodes '+seq(comp['rank'])+')');continue
            values=comp['values'];active=set(comp['active'])
            gate='wc_table false nodes '+seq('true'if i in active else'false'for i in range(len(g['nodes'])))
            if kind=='linear':
                counts=[]
                for part,ctor in enumerate(['MAll','MLeft','MRight']):
                    for symbol in [1,2,3]:
                        value=values[part*4+symbol]
                        if value<0:raise ValueError('Negative natural weight')
                        if value:counts.append(f'({value},{ctor} C{symbol})')
                components.append('WLinear('+seq(counts)+',wc_table 0 nodes '+seq(values[12:])+','+gate+')')
            elif kind=='w':
                scores=['wc_score '+' '.join(integer(v)for v in values[j:j+4])for j in [0,4,8,12]]
                components.append('WBinary('+','.join(scores)+',wc_table Z0 nodes '+seq(integer(v)for v in values[16:])+','+gate+')')
            else:raise ValueError('Unknown component')
        body+=f'let target_{target}={{wc_k={cert["k"]};wc_guards='+seq(syms(w)for w in cert['guards'])+';wc_inside='+seq(node(c)for c in cert['inside'])+';wc_components='+seq(components)+'}\n'
        i=int(target);branches.append(f'|(St{chr(65+i//4)},S{i%4})->Some target_{i}')
    body+='let certificate=function '+''.join(branches)+(''if len(branches)==8 else'|_->None')+'\n'
    loop=grouping.render(grouping.rename(grouping.parse(g['machine']),p,mirror=bool(g['mirror']),swap=swap))
    left,right=original_sets(source)
    def gram_set(grams):return 'gadds '+seq(syms([p[x]for x in word])for word in sorted(grams))+' gempty'
    body+='let tail={wt_source=machine_of_codes '+seq(codes(loop))+f';wt_width={g["n"]};wt_left='+gram_set(left)+';wt_right='+gram_set(right)+';wt_nodes=nodes;wt_cert=certificate}\n'
    body+='let rows='+seq('{reuse_codes='+seq(codes(m))+';reuse_mirrored='+str(mirror).lower()+f';reuse_boot={boot}'+'}'for m,_,_,_,mirror,boot in rows)+'\n'
    body+='let ()=List.iter(fun answer->print_endline(string_of_bool answer))(wt_hybrid_results bound bound tail rows)\nend\n'
    return body
