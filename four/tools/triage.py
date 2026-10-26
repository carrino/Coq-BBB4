"""Reproduce an exploratory residual-family sample. No output is a Coq proof.

Run with --irules /path/to/BBB/bin/irules. The existing multisymbol survey is
compiled with a node budget and one fixed initial transition per run. Reflection
and blank-preserving symbol permutations give the two nontrivial root classes;
this quotient is used only for exploration, not the certified bootstrap.
"""
import argparse
import csv
import hashlib
import heapq
import json
import subprocess
from collections import Counter
from pathlib import Path


def replace_once(source, old, new):
    assert source.count(old) == 1, f'Survey source changed near {old!r}'
    return source.replace(old, new, 1)


def scoped_source(source):
    source = replace_once(source, 'int states = 2, symbols = 3, fuel = 256, window_size = 64;',
        'int states = 2, symbols = 3, fuel = 256, window_size = 64;\nuint64_t budget = 10000000; int fixed_root = 1;')
    source = replace_once(source, 'void census(int free_slots) {\n  ++nodes;',
        'void census(int free_slots) {\n  if (nodes >= budget) { ++leaves["unvisited"]; weighted["unvisited"] += power(free_slots); covered += power(free_slots); return; }\n  ++nodes;')
    source = replace_once(source, 'argc > 6', 'argc > 8')
    source = replace_once(source, 'if (argc > 5) states = stoi(argv[5]);',
        'if (argc > 5) states = stoi(argv[5]);\n  if (argc > 6) fixed_root = stoi(argv[6]);\n  if (argc > 7) budget = stoull(argv[7]);')
    source = replace_once(source, 'certificates.open(string(argv[1]) + ".certificates.tsv");',
        'certificates.open("/dev/null");\n  machine[0] = fixed_root;')
    source = replace_once(source, 'census(states * symbols);', 'census(states * symbols - 1);')
    source = source.replace('power(states * symbols)', 'power(states * symbols - 1)')
    return source


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def profile(path):
    with path.open() as f:
        rows = list(csv.DictReader(f))
    return {'rows':len(rows), 'statuses':dict(Counter(r['status'] for r in rows)),
            'quasihalting':dict(Counter(r['qh'] for r in rows if r['status']=='irules')),
            'unresolved_reasons':dict(Counter(r[None][0].split()[0] for r in rows if r['status']=='undecided' and None in r)),
            'successful_examples':[r['machine'] for r in rows if r['status']=='irules'][:12],
            'unresolved_examples':[r['machine'] for r in rows if r['status']=='undecided'][:12]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--irules',type=Path,required=True)
    parser.add_argument('--fuel',type=int,default=256)
    parser.add_argument('--window',type=int,default=64)
    parser.add_argument('--max-nodes',type=int,default=10000000)
    parser.add_argument('--sample-per-root',type=int,default=512)
    parser.add_argument('--rule-steps',type=int,default=4096)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    build = root/'build'/'triage'; build.mkdir(parents=True,exist_ok=True)
    original = root.parent/'tools'/'multisymbol'/'survey.cpp'
    source = build/'survey.cpp'; source.write_text(scoped_source(original.read_text()))
    exe = build/'survey'
    subprocess.run(['g++','-O3','-std=c++17',str(source),'-o',str(exe)],check=True)
    roots = {}; sample = []
    for label,code in [('blank',1),('nonblank',5)]:
        prefix=build/label
        result=subprocess.run([str(exe),str(prefix),'4',str(args.fuel),str(args.window),'2',str(code),str(args.max_nodes)],capture_output=True,text=True,check=True,timeout=300)
        roots[label]=json.loads(result.stdout)
        (build/f'{label}.json').write_text(result.stdout)
        if roots[label]['weighted'].get('unvisited',0):
            raise SystemExit(f'{label}: node budget reached; no complete-root profile claimed')
        with prefix.with_suffix('.unresolved.txt').open() as f:
            sample += heapq.nsmallest(args.sample_per_root,(s.strip() for s in f),key=lambda s:hashlib.sha256(s.encode()).digest())
    sample_path=build/'sample.txt'; sample_path.write_text('\n'.join(sample)+'\n')
    output=build/'irules.csv'
    with output.open('w') as f:
        subprocess.run([str(args.irules.resolve()),'--max-steps',str(args.rule_steps),'--tape-cells','65536','--why',str(sample_path)],stdout=f,check=True,timeout=300)
    report={'status':'Untrusted exploration; no additional machine bounds certified.',
            'parameters':{k:str(v) if isinstance(v,Path) else v for k,v in vars(args).items()},
            'survey_source_sha256':digest(original),'irules_binary_sha256':digest(args.irules),
            'sampling':'512 (by default) lowest SHA-256 machine hashes per fixed-root residual file; unweighted partial-table families, not a population-rate estimator.',
            'sample_sha256':digest(sample_path),'roots':roots,'profile':profile(output)}
    (build/'summary.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report['profile'],sort_keys=True))


if __name__=='__main__':
    main()
