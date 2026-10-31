"""Independent bounded controls for S020's proved cut rules; zero proof credit."""
import argparse
import hashlib
import itertools
import json
from pathlib import Path
from generate_pipeline_examples import codes

ROOT = Path(__file__).resolve().parents[1]
PREFIX = ROOT/'research/burn30-s020-counter'
MACHINE = '1LB0RB1LA3RA_1RB3LA2LB2RA'
P, Z, O, E = '1312', '1111', '3213', '1321'

def artifact(suffix):
    return PREFIX.with_name(PREFIX.name+'-'+suffix)

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def decode(machine):
    text = machine.replace('_', '')
    return [(int(text[i]), 1 if text[i+1] == 'R' else -1,
             0 if text[i+2] == 'A' else 1) for i in range(0, 24, 3)]

def step(table, conf):
    q, left, head, right = conf
    write, direction, q = table[4*q+head]
    if direction == 1:
        return q, [write]+left, right[0] if right else 0, right[1:]
    return q, left[1:], left[0] if left else 0, [write]+right

def conf(word):
    return 0, [], 0, list(map(int, word))

def cut(n, tail):
    return conf('322'+P*n+'111'+tail)

def tag(m):
    return '322'+P*m+'1311'

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    inp = artifact('native-input.json')
    data_in = json.loads(inp.read_text())
    assert data_in['machine'] == MACHINE
    frontier = ROOT/data_in['frontier_source']
    assert sha(frontier) == data_in['frontier_sha256']
    assert MACHINE in frontier.read_text().splitlines()
    table = decode(MACHINE)
    values = [4*w+(2 if d == 1 else 0)+q for w,d,q in table]
    assert values == codes(MACHINE)
    rows, seen = [], set()
    def control(kind, n, j, m, start, expected, cost):
        current = start
        for t in range(cost):
            q,l,h,r = current
            assert not (q == 1 and h == 0 and all(x == 0 for x in r)), (kind,n,j,m,t)
            current = step(table, current)
        assert current == expected, (kind,n,j,m,cost,current,expected)
        rows.append(dict(kind=kind,n=n,carry=j,tag=m,steps=cost))
        seen.add(kind)
    bound = data_in['maximum_parameter']
    suffixes = ['', '0', '1', '3', '0012', E, tag(0), tag(2)]
    for n,j,r in itertools.product(range(bound+1),range(bound+1),suffixes):
        control('increment',n,j,r,cut(n,O*j+Z+r),cut(n+1,Z*j+O+r),64*n+114+16*j)
    for n,j in itertools.product(range(bound+1), repeat=2):
        control('overflow_E',n,j,None,cut(n,O*j+E),cut(0,O+Z*n+tag(j)),54*n+26*j+147)
    for n,j,m in itertools.product(range(bound+1), repeat=3):
        control('overflow_G',n,j,m,cut(n,O*j+tag(m)),cut(n+1,Z*j+O+Z*m+E),64*n+16*j+22*m+152)
    assert seen == {'increment','overflow_E','overflow_G'}
    actual = (0,[],0,[])
    for _ in range(176):
        actual = step(table, actual)
    assert actual == cut(0,O+E)
    negatives = [((0,[],0,list(map(int,'31311'))),29),
                 ((0,[3],0,[]),3),((0,[3],2,[]),3)]
    negative_rows = []
    for start, cost in negatives:
        current = start
        for _ in range(cost):
            current = step(table,current)
        q,left,h,right = current
        assert (q,h,right) == (1,0,[])
        for count in range(65):
            assert current == (1,[1]*count+left,0,[])
            current = step(table,current)
        negative_rows.append(dict(start=start,escape_steps=cost,drift_checks=65))
    data = dict(scope='Independent finite cut-macro and negative-boundary controls only; zero proof credit.',
                rows=[dict(machine=MACHINE,code=sum(v*17**i for i,v in enumerate(values)))],
                actual_blank_entry_steps=176,macro_controls=rows,
                macro_control_count=len(rows),maximum_macro_steps=max(x['steps'] for x in rows),
                negative_boundary_controls=negative_rows,
                inputs_sha256={str(p.relative_to(ROOT)):sha(p) for p in (inp,frontier)},
                source_sha256={str(p.relative_to(ROOT)):sha(p) for p in (Path(__file__),ROOT/'tools/generate_pipeline_examples.py')},
                checked_state_families=0,checked_instruction_families=0)
    # Compare the serialized representation, so tuple/list normalization cannot
    # change replay semantics after JSON reload.
    data = json.loads(json.dumps(data))
    report = artifact('native.json')
    if args.check:
        assert json.loads(report.read_text()) == data
    else:
        if report.exists():
            raise ValueError('Frozen native report exists; use --check')
        report.write_text(json.dumps(data,indent=2,sort_keys=True)+'\n')
    print(json.dumps(dict(macro_controls=len(rows),negative_boundaries=len(negative_rows),maximum_macro_steps=data['maximum_macro_steps'])),flush=True)

if __name__ == '__main__':
    main()
