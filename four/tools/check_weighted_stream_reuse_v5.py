"""Share fixed weighted tail checks across targets in each template batch.

The V5 producer uses explicit gram sets from the supplied source certificate.
WeightedTail checks that closure and its rankings once, independently of target
boots. Each target still checks its boot, prefix, and every live instruction.
The original WeightedSuffix checker is retained as a sound fallback. No source
certificate is assumed correct; default replay checks the tracked target list.
"""
from pathlib import Path

import check_weighted_stream_reuse as pipeline
from generate_pipeline_examples import codes
from kernel_audit_cache import digest
from weighted_codec_v2 import unpack
from weighted_render import coqlist,symbols
from weighted_render_v4 import HEADER,render
from weighted_reuse_search import original_sets,transform

ROOT=Path(__file__).resolve().parents[1]
_sources=pipeline.sources
_generate=pipeline.generate
_pipeline_source=Path(pipeline.__file__).resolve()
COMMON=pipeline.COMMON+'From BBB24 Require Import WeightedTail.\n'


def sources(registry):
    rows,ids,inputs=_sources(registry)
    for path in (_pipeline_source,ROOT/'tools/weighted_render_v3.py',
                 ROOT/'tools/weighted_render_v4.py',ROOT/'theories/WeightedTail.v'):
        inputs[str(path.relative_to(ROOT))]=digest(path)
    return rows,ids,inputs


def template(raw,rows,name,proof):
    source=raw if 'graph' in raw else unpack(raw)
    _,_,permutation,swap,_,_=rows[0]
    p=(0,)+tuple(map(int,permutation));changed=transform(source,p,swap)
    prefix=render(changed)
    if not prefix.startswith(HEADER):raise ValueError('Certificate renderer header changed')
    body=prefix[len(HEADER):].split('Definition family:TM:=',1)[0]
    g=source['graph'];left,right=original_sets(source)
    def gram_set(grams):
        return 'gadds '+coqlist(symbols([p[x] for x in word]) for word in sorted(grams))+' gempty'
    loop=pipeline.grouping.render(pipeline.grouping.rename(
        pipeline.grouping.parse(g['machine']),p,mirror=bool(g['mirror']),swap=swap))
    body+='Definition source := machine_of_codes ['+';'.join(map(str,codes(loop)))+'].\n'
    body+=f'Definition tail := weighted_tail source {g["n"]} ({gram_set(left)}) ({gram_set(right)}) nodes certificate.\n'
    body+='Definition rows : list WeightedReuseRow := [\n'+';\n'.join(
        'weighted_reuse_row ['+';'.join(map(str,codes(m)))+f'] {str(mirror).lower()} {boot}'
        for m,_,_,_,mirror,boot in rows)+'].\n'
    if proof:
        body+='''Lemma checked : wt_hybrid_check 4096%N 4096%N tail rows=true.
Proof. vm_compute. reflexivity. Qed.
Definition board := map reuse_tm rows.
Lemma strong : StrongBoard 4096%N 4096%N board.
Proof. exact (wt_hybrid_batch_sound _ _ _ _ checked). Qed.
Lemma pending_checked : forallb (pending_check 9 empty bootstrap) board=true.
Proof. vm_compute. reflexivity. Qed.
'''
    return f'Module {name}.\n'+body+f'End {name}.\n',g['n']


def generate(sources,rows,build,namespace,proof):
    if proof:return _generate(sources,rows,build,namespace,proof)
    paths=[];chunks=pipeline.groups(rows);counts=[]
    for start in range(0,len(chunks),pipeline.TEMPLATES_PER_PART):
        body=COMMON;checks=[];count=0
        for i,chunk in enumerate(chunks[start:start+pipeline.TEMPLATES_PER_PART]):
            name=f'T{i:03}';text,_=template(sources[chunk[0][1]],chunk,name,False)
            body+=text;count+=len(chunk)
            checks.append(f'wt_hybrid_results 4096%N 4096%N {name}.tail {name}.rows')
        body+='Eval vm_compute in ('+' ++ '.join('('+c+')' for c in checks)+').\n'
        path=build/f'Part{start//pipeline.TEMPLATES_PER_PART:04}.v'
        path.write_text(body);paths.append(path);counts.append(count)
    return paths,counts


def main():
    if HEADER!=pipeline.CERT_HEADER:raise ValueError('Renderer header interface changed')
    pipeline.sources=sources
    pipeline.template=template
    pipeline.generate=generate
    pipeline.COMMON=COMMON
    pipeline.__file__=__file__
    pipeline.main()


if __name__=='__main__':main()
