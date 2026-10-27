"""Use the extracted tail checkers for untrusted selection, then Coq replay.

V6 changes only the exploratory probe. The V5 producer still proves each
selected target with wt_hybrid_check and audits the resulting board. Default
replay needs only the tracked compact input and certificate bundles; it does
not run extraction, OCaml compilation, or the target search.
"""
from pathlib import Path
import resource
import subprocess
import time

import check_weighted_stream_reuse as pipeline
import check_weighted_stream_reuse_v5 as coq
from kernel_audit_cache import digest
from weighted_tail_native import HEADER,template

ROOT=Path(__file__).resolve().parents[1]
_select=pipeline.select
_selection_stats=None


def sources(registry):
    rows,ids,inputs=coq.sources(registry)
    for path in (Path(coq.__file__),ROOT/'tools/weighted_tail_native.py',ROOT/'tools/ExtractWeightedTail.v'):
        inputs[str(path.resolve().relative_to(ROOT))]=digest(path)
    return rows,ids,inputs


def select(*args,**kwargs):
    global _selection_stats
    rows,_selection_stats=_select(*args,**kwargs)
    return rows,_selection_stats


def prepare():
    base=ROOT/'build/weighted-tail-native';base.mkdir(exist_ok=True)
    subprocess.run(['coqc','-native-compiler','no','-Q','theories','BBB24','tools/ExtractWeightedTail.v'],cwd=ROOT,check=True)
    for suffix in ['mli','ml']:
        subprocess.run(['ocamlopt','-w','-a','-I',str(base),'-c',str(base/('weighted_tail.'+suffix))],check=True)
    return base


def probe(sources,rows,build,namespace,timeout):
    started=time.monotonic();usage=resource.getrusage(resource.RUSAGE_CHILDREN)
    base=prepare();directory=build/'native-probe';directory.mkdir(exist_ok=True)
    selected=[];offset=0;chunks=pipeline.groups(rows);parts=0
    for start in range(0,len(chunks),pipeline.TEMPLATES_PER_PART):
        body=HEADER;count=0
        for i,chunk in enumerate(chunks[start:start+pipeline.TEMPLATES_PER_PART]):
            body+=template(sources[chunk[0][1]],chunk,f'T{i:03}');count+=len(chunk)
        path=directory/f'Part{start//pipeline.TEMPLATES_PER_PART:04}.ml';path.write_text(body)
        binary=path.with_suffix('')
        result=subprocess.run(['ocamlopt','-w','-a','-I',str(base),'-o',str(binary),str(base/'weighted_tail.cmx'),str(path)],capture_output=True,text=True,timeout=timeout)
        path.with_suffix('.compile.log').write_text(result.stdout+result.stderr)
        result.check_returncode()
        result=subprocess.run([str(binary)],capture_output=True,text=True,check=True,timeout=timeout)
        path.with_suffix('.log').write_text(result.stdout+result.stderr)
        values=result.stdout.splitlines()
        if len(values)!=count or any(v not in {'true','false'}for v in values):
            raise ValueError('Malformed native selection output')
        selected.extend(row for row,value in zip(rows[offset:offset+count],values)if value=='true')
        offset+=count;parts+=1;print('Native-probed '+path.name,flush=True)
    if offset!=len(rows):raise ValueError('Native probe omitted rows')
    after=resource.getrusage(resource.RUSAGE_CHILDREN)
    stats=dict(kind='untrusted extracted OCaml; all successes subsequently replayed in Coq',parts=parts,
               wall_seconds=time.monotonic()-started,
               child_cpu_seconds=after.ru_utime+after.ru_stime-usage.ru_utime-usage.ru_stime,
               extracted_sha256={suffix:digest(base/('weighted_tail.'+suffix))for suffix in ['ml','mli']})
    if _selection_stats is not None:_selection_stats['native_probe']=stats
    return selected


def main():
    pipeline.sources=sources;pipeline.select=select;pipeline.probe=probe
    pipeline.template=coq.template;pipeline.generate=coq.generate;pipeline.COMMON=coq.COMMON
    pipeline.__file__=__file__;pipeline.main()


if __name__=='__main__':main()
