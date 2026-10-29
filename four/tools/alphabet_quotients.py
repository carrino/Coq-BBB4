"""Measure exact alphabet quotients on a frozen state-only survivor queue.

A partition identifies symbols only when both states' transitions agree in
presence, direction, next state, and projected write. Blank is class0.
Search counts are not proof claims.67-step survival is required before a
literal partial machine can serve as a nonhalting completion-family source.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path

from generate_pipeline_examples import codes

ROOT=Path(__file__).resolve().parents[1]


def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()


def partitions():
    result=[]
    def visit(prefix):
        if len(prefix)==4:
            if max(prefix)<3:result.append(tuple(prefix))
            return
        for label in range(min(2,max(prefix)+1)+1):visit(prefix+[label])
    visit([0])
    return sorted(result,key=lambda p:(-max(p),p))


def compatible(table,partition):
    for state in range(2):
        signatures={}
        for symbol in range(4):
            value=table[4*state+symbol]
            signature=None if value==16 else (partition[value//4],value%4)
            block=partition[symbol]
            if block in signatures and signatures[block]!=signature:return False
            signatures[block]=signature
    return True


def survives(table,steps=67):
    tape={};state=position=0
    for _ in range(steps):
        value=table[4*state+tape.get(position,0)]
        if value==16:return False
        tape[position]=value//4
        position+=1 if value//2%2 else -1
        state=value%2
    return True


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input',type=Path,default=ROOT/'build/state-pipeline/deep-full/not-accepted.txt')
    parser.add_argument('--prior-report',type=Path,default=ROOT/'research/state-closure-deep-full.json')
    parser.add_argument('--output',type=Path,default=ROOT/'research/state-alphabet-quotient-search.json')
    parser.add_argument('--check',action='store_true')
    args=parser.parse_args()
    machines=args.input.read_text().splitlines();prior=json.loads(args.prior_report.read_text())
    if len(machines)!=len(set(machines)) or len(machines)!=prior['not_accepted_rows'] or sha(args.input)!=prior['not_accepted_sha256']:
        raise ValueError('Input does not match the frozen state residual')
    parts=partitions()
    assert len(parts)==14 and all(p[0]==0 for p in parts)
    rows=[];failed_survival=[];all_matches=0
    for machine in machines:
        table=codes(machine);matches=[p for p in parts if compatible(table,p)]
        if not matches:continue
        all_matches+=len(matches)
        record=dict(machine=machine,partition=list(matches[0]),compatible_partitions=len(matches),partial='---' in machine)
        if survives(table):rows.append(record)
        else:failed_survival.append(record)
    report=dict(status='untrusted_state_only_search',input_families=len(machines),
        input_sha256=sha(args.input),prior_report_sha256=sha(args.prior_report),
        symbol_partitions=len(parts),compatible_pairs=all_matches,
        coherent_families=len(rows)+len(failed_survival),surviving_candidate_families=len(rows),
        concrete=sum(not r['partial'] for r in rows),partial=sum(r['partial'] for r in rows),
        alphabet_size_histogram=dict(sorted(Counter(max(r['partition'])+1 for r in rows).items())),
        rows=rows,failed_survival=failed_survival,
        source_sha256={str(p.relative_to(ROOT)):sha(p) for p in [Path(__file__).resolve(),ROOT/'tools/generate_pipeline_examples.py']},
        semantics='Preserves the state trace only. Individual instruction identities can be merged, so no instruction-bound claim.',
        accounting='Original core families; no proof or census discharge claimed by this search report.')
    text=json.dumps(report,indent=2)+'\n'
    if args.check:
        if args.output.read_text()!=text:raise ValueError('Quotient search evidence changed')
    else:args.output.write_text(text)
    print(json.dumps({k:v for k,v in report.items() if k not in ('rows','failed_survival','source_sha256','semantics','accounting')}))


if __name__=='__main__':main()
