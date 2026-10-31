"""Independent bounded S059 increment and unsafe-boundary controls; zero proof credit."""
import argparse
import hashlib
import itertools
import json
from pathlib import Path
from generate_pipeline_examples import codes

ROOT = Path(__file__).resolve().parents[1]
PREFIX = ROOT/'research/burn36-s059-counter'
MACHINE = '1LB2LB3RA0RA_2RB3RA2LB3LA'
P, Z, O = '3330', '00', '03'

def artifact(suffix):
    return PREFIX.with_name(PREFIX.name+'-'+suffix)

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def decode(machine):
    text = machine.replace('_', '')
    return [(int(text[i]), 1 if text[i+1] == 'R' else -1,
             0 if text[i+2] == 'A' else 1) for i in range(0,24,3)]

def step(table, conf):
    q,left,head,right = conf
    write,direction,q = table[4*q+head]
    if direction == 1:
        return q,[write]+left,right[0] if right else 0,right[1:]
    return q,left[1:],left[0] if left else 0,[write]+right

def maincut(n, word):
    return 0,list(map(int,P*n+'32'+word)),0,[]

def guard(conf):
    q,left,head,right = conf
    return q == 1 and all(x in (0,2) for x in left) and (head == 2 or (head == 0 and bool(right) and right[0] == 2))

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check',action='store_true')
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
    rows = []
    def control(n,j,suffix,implicit):
        tail = '' if implicit else Z+suffix
        start = maincut(n,O*j+tail)
        expected = maincut(n+1,Z*j+O+suffix)
        cost = 64*n+72+12*j
        current = start
        for t in range(cost):
            assert not guard(current),(n,j,suffix,implicit,t)
            current = step(table,current)
        assert current == expected,(n,j,suffix,implicit,cost,current,expected)
        rows.append(dict(n=n,carry=j,suffix=suffix,implicit_end=implicit,steps=cost))
    bound = data_in['maximum_parameter']
    for n,j,suffix in itertools.product(range(bound+1),range(bound+1),['','0','1','2','3','0012',Z+O,O+Z]):
        control(n,j,suffix,False)
    for n,j in itertools.product(range(bound+1),repeat=2):
        control(n,j,'',True)
    actual = (0,[],0,[])
    for t in range(19):
        if t == 3:
            assert actual == maincut(0,'')
        if t == 18:
            assert actual == (0,[3,3,0,3,2],0,[])
        actual = step(table,actual)
    negatives = [((0,[3,3],0,[]),5),((0,[3,3,3,0,3,3],0,[]),17)]
    negative_rows = []
    for start,cost in negatives:
        current = start
        for _ in range(cost):
            current = step(table,current)
        assert guard(current)
        reached = current
        for _ in range(65):
            assert guard(current)
            current = step(table,current)
        negative_rows.append(dict(start=start,escape_steps=cost,reached=reached,guard_checks=65))
    data = dict(scope='Independent finite increment and unsafe-boundary controls only; zero proof credit.',
                rows=[dict(machine=MACHINE,code=sum(v*17**i for i,v in enumerate(values)))],
                actual_blank_main_steps=3,earlier_partial_entry_steps=18,
                macro_controls=rows,macro_control_count=len(rows),
                maximum_macro_steps=max(x['steps'] for x in rows),negative_boundary_controls=negative_rows,
                inputs_sha256={str(p.relative_to(ROOT)):sha(p) for p in (inp,frontier)},
                source_sha256={str(p.relative_to(ROOT)):sha(p) for p in (Path(__file__),ROOT/'tools/generate_pipeline_examples.py')},
                checked_state_families=0,checked_instruction_families=0)
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
