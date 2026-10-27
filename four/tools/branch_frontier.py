"""Record newly reached partial-family branches without promoting child hits.

Every root remains unresolved until all sixteen defined children and the
separate None/halt choice have a proved bound. This report is search evidence.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path

from generate_pipeline_examples import codes

ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def children(machine, fuel):
    table = codes(machine)
    tape = {}
    state = position = 0
    for anchor in range(fuel):
        cell = 4*state + tape.get(position, 0)
        transition = table[cell]
        if transition == 16:
            break
        tape[position] = transition//4
        position += 1 if transition//2 % 2 else -1
        state = transition % 2
    else:
        raise ValueError(f'No reached undefined cell within budget: {machine}')
    words = [machine[3*i+(i>=4):3*i+(i>=4)+3] for i in range(8)]
    result = []
    for value in range(16):
        child = words.copy()
        child[cell] = f'{value//4}{"LR"[value//2%2]}{"AB"[value%2]}'
        result.append(''.join(child[:4])+'_'+''.join(child[4:]))
    return dict(family=machine, anchor=anchor, cell=cell,
                halting_choice_step=anchor+1, defined_children=result)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--roots', type=Path,
        default=ROOT/'build/late-cycles/full-f65536-n256.jsonl')
    parser.add_argument('--cycles', type=Path,
        default=ROOT/'build/late-cycles/new-branch-children-cycles.jsonl')
    parser.add_argument('--affine', type=Path,
        default=ROOT/'build/affine-wave/branch-children/accepted-certificates.json')
    parser.add_argument('--fuel', type=int, default=65536)
    parser.add_argument('--output', type=Path, default=ROOT/'research/branch-frontier.json')
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    roots = [json.loads(line) for line in args.roots.read_text().splitlines()]
    selected = [r for r in roots if r['branch_nodes'] and r['status']=='pending']
    if len(selected) != len({r['machine'] for r in selected}):
        raise ValueError('Repeated original family')
    families = [children(r['machine'], args.fuel) for r in selected]
    all_children = [m for r in families for m in r['defined_children']]
    if len(all_children) != len(set(all_children)):
        raise ValueError('Child overlap requires explicit separate accounting')
    cycle_rows = [json.loads(line) for line in args.cycles.read_text().splitlines()]
    if {r['machine'] for r in cycle_rows} != set(all_children) or len(cycle_rows) != len(all_children):
        raise ValueError('Cycle results do not exactly cover the child frontier')
    cycles = {r['machine']:r['certificate'] for r in cycle_rows if r['status']=='candidate_closed'}
    affine = json.loads(args.affine.read_text())
    if not set(affine) <= set(all_children):
        raise ValueError('Outside child in affine candidate registry')
    for r in families:
        hits = []
        for value, machine in enumerate(r.pop('defined_children')):
            hits.append(dict(value=value, machine=machine,
                cycle_candidate=cycles.get(machine),
                affine_candidate_sha256=sha(REPO/affine[machine]) if machine in affine else None))
        r['children'] = hits
        r['candidate_children'] = sum(h['cycle_candidate'] is not None or h['affine_candidate_sha256'] is not None for h in hits)
    report = dict(
        status='untrusted_search_frontier', original_families=len(families),
        unique_defined_children=len(all_children), halting_choices=len(families),
        cycle_candidate_children=len(cycles), affine_candidate_children=len(affine),
        distinct_candidate_children=len(set(cycles)|set(affine)),
        completely_candidate_covered_families=sum(r['candidate_children']==16 for r in families),
        checked_new_families=0,
        child_success_histogram=dict(sorted(Counter(r['candidate_children'] for r in families).items())),
        sources_sha256={str(p.relative_to(REPO)):sha(p) for p in
            [args.roots,args.cycles,args.affine,Path(__file__).resolve(),ROOT/'tools/generate_pipeline_examples.py']},
        rows=families,
        accounting='Each row is one original family; child hits are not original-family discharges. Every completed branch also needs the explicit None/halt case.')
    text = json.dumps(report, indent=2)+'\n'
    if args.check:
        if args.output.read_text() != text:
            raise ValueError('Frontier evidence changed')
    else:
        args.output.write_text(text)
    print(json.dumps({k:v for k,v in report.items() if k not in ('rows','sources_sha256','accounting')}))


if __name__ == '__main__':
    main()
