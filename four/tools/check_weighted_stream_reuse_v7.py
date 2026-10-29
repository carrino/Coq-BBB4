"""Probe immutable template data with one extracted native checker executable.

Selection is untrusted. The unchanged V5 Coq producer independently proves
all retained rows and kernel-audits the full board. Default proof replay reads
only tracked compact target references and source certificate bundles; no
native executable, graph extraction, or large target survey is required.
"""
from pathlib import Path
import fcntl
import resource
import shutil
import subprocess
import time

import check_weighted_stream_reuse as pipeline
import check_weighted_stream_reuse_v5 as coq
import check_weighted_stream_reuse_v6 as static_native
from kernel_audit_cache import digest
from weighted_tail_data import serialize

ROOT=Path(__file__).resolve().parents[1]
_select=pipeline.select
_selection_stats=None


def sources(registry):
    rows,ids,inputs=static_native.sources(registry)
    for path in (Path(static_native.__file__),ROOT/'tools/weighted_tail_data.py',ROOT/'tools/weighted_tail_selector.ml'):
        inputs[str(path.resolve().relative_to(ROOT))]=digest(path)
    return rows,ids,inputs


def select(*args,**kwargs):
    global _selection_stats
    rows,_selection_stats=_select(*args,**kwargs)
    return rows,_selection_stats


def prepare(build,timeout):
    runtime=build/'selector-runtime';runtime.mkdir(exist_ok=True)
    shared=ROOT/'build/weighted-tail-native';shared.mkdir(exist_ok=True)
    # Each batch receives its own exact object copy. Concurrent V7 selections
    # serialize extraction/copy only; their checker runs are independent.
    with(shared/'selector.lock').open('a')as lock:
        fcntl.flock(lock,fcntl.LOCK_EX)
        static_native.prepare()
        for suffix in ['ml','mli','cmx','cmi','o']:
            shutil.copyfile(shared/('weighted_tail.'+suffix),runtime/('weighted_tail.'+suffix))
    obj=runtime/'weighted_tail_selector.cmx';binary=runtime/'selector'
    with(runtime/'compile.log').open('w')as log:
        subprocess.run(['ocamlopt','-w','-a','-I',str(runtime),'-c','-o',str(obj),str(ROOT/'tools/weighted_tail_selector.ml')],stdout=log,stderr=subprocess.STDOUT,check=True,timeout=timeout)
        subprocess.run(['ocamlopt','-w','-a','-I',str(runtime),'-o',str(binary),str(runtime/'weighted_tail.cmx'),str(obj)],stdout=log,stderr=subprocess.STDOUT,check=True,timeout=timeout)
    return runtime,binary


def probe(sources,rows,build,namespace,timeout):
    started=time.monotonic();usage=resource.getrusage(resource.RUSAGE_CHILDREN)
    runtime,binary=prepare(build,timeout)
    directory=build/'native-data-probe';directory.mkdir(exist_ok=True)
    selected=[];offset=0;chunks=pipeline.groups(rows);parts=0
    for start in range(0,len(chunks),pipeline.TEMPLATES_PER_PART):
        batch=chunks[start:start+pipeline.TEMPLATES_PER_PART]
        count=sum(map(len,batch));path=directory/f'Part{start//pipeline.TEMPLATES_PER_PART:04}.txt'
        path.write_text(serialize(sources,batch))
        result=subprocess.run([str(binary),str(path)],capture_output=True,text=True,check=True,timeout=timeout)
        path.with_suffix('.log').write_text(result.stdout+result.stderr)
        values=result.stdout.splitlines()
        if len(values)!=count or any(v not in {'true','false'}for v in values):
            raise ValueError('Malformed native data selection output')
        selected.extend(row for row,value in zip(rows[offset:offset+count],values)if value=='true')
        offset+=count;parts+=1;print('Native-data-probed '+path.name,flush=True)
    if offset!=len(rows):raise ValueError('Native data probe omitted rows')
    after=resource.getrusage(resource.RUSAGE_CHILDREN)
    stats=dict(kind='untrusted extracted OCaml with data reader; all successes subsequently replayed in Coq',parts=parts,
               wall_seconds=time.monotonic()-started,
               child_cpu_seconds=after.ru_utime+after.ru_stime-usage.ru_utime-usage.ru_stime,
               extracted_sha256={suffix:digest(runtime/('weighted_tail.'+suffix))for suffix in ['ml','mli']},
               selector_sha256=digest(binary))
    if _selection_stats is not None:_selection_stats['native_probe']=stats
    return selected


def main():
    pipeline.sources=sources;pipeline.select=select;pipeline.probe=probe
    pipeline.template=coq.template;pipeline.generate=coq.generate;pipeline.COMMON=coq.COMMON
    pipeline.__file__=__file__;pipeline.main()


if __name__=='__main__':main()
