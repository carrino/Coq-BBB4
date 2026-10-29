"""Bounded residual screen for accepted handwritten suffix proofs.

All24 images use six blank-preserving symbol permutations, reflection, and
optional state exchange. A state-exchanged match still needs an actual prefix.
This is untrusted discovery: no census discharge is claimed by this program.
"""
import hashlib
import itertools
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
RESIDUAL = ROOT / 'build/burn3-burndown/both-remaining.txt'
OUTPUT = ROOT / 'research/burn5-handwritten-template-screen.json'
LIMIT = 4096
TEMPLATES = [
    {'name': 'paired_digit_tail', 'machine': '1LB2LA1RB3RB_3RA1RB3LA1RA',
     'support': [0, 1, 2, 3, 4, 6, 7], 'quiet': [5],
     'source': 'research/burn3-tail-invariant/TailInvariant.v',
     'report': 'research/burn3-tail-invariant-checked.json'},
    {'name': 'pair_capacity', 'machine': '1LB2RA3RA0RA_1RA2LA0LB3LA',
     'support': list(range(8)), 'quiet': [],
     'source': 'research/burn3-pair-capacity/PairCapacity.v',
     'report': 'research/burn3-pair-capacity-checked.json'},
]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def cells(machine):
    flat = machine.replace('_', '')
    if len(machine) != 25 or machine[12] != '_':
        raise ValueError('Invalid table')
    return [flat[3*i:3*i+3] for i in range(8)]


def word(xs):
    return len(xs) % 2 == 0 and all(xs[i] in (2, 3) and xs[i+1] == 2 for i in range(0, len(xs), 2))


def left_marker(xs):
    n = 0
    while n < len(xs) and xs[n] == 1:
        n += 1
    return (n, xs[n+1:]) if n < len(xs) and xs[n] == 3 else None


def phase(q, left, head, right):
    # The generalized form permits an inert suffix beyond the leftmost marker.
    if q == 0 and head == 3 and word(right):
        return {'constructor': 'marker', 'digits': right[::2], 'dormant_left_suffix': left}
    marker = left_marker(left)
    if marker:
        n, suffix = marker
        if q == 1 and n % 2 == 0:
            if head in (2, 3) and right and right[0] == 2 and word(right[1:]):
                return {'constructor': 'digit', 'k': n//2, 'digit': head,
                        'digits': right[1::2], 'dormant_left_suffix': suffix}
            if head == 0 and not right:
                return {'constructor': 'front_B', 'k': n//2, 'dormant_left_suffix': suffix}
            if head == 3 and right == [1]:
                return {'constructor': 'turn', 'k': n//2, 'dormant_left_suffix': suffix}
        if q == 0:
            if n % 2 == 1 and head == 2 and word(right):
                return {'constructor': 'separator', 'k': (n-1)//2,
                        'digits': right[::2], 'dormant_left_suffix': suffix}
            if head == 1:
                j = 0
                while True:
                    if (n+j+1) % 2 == 0 and word(right[j:]):
                        return {'constructor': 'reset', 'l': n, 'j': j, 'k': (n+j+1)//2,
                                'digits': right[j::2], 'dormant_left_suffix': suffix}
                    if j == len(right) or right[j] != 2:
                        break
                    j += 1
    if q == 0 and head == 0 and not right and left and left[0] == 3:
        marker = left_marker(left[1:])
        if marker and marker[0] % 2 == 0:
            return {'constructor': 'front_A', 'k': marker[0]//2, 'dormant_left_suffix': marker[1]}
    return None


def prefix(machine, sigma, mirror, swapped):
    table = [None if c == '---' else (int(c[0]), -1 if c[1]=='L' else 1, ord(c[2])-65)
             for c in cells(machine)]
    inverse = {s:i for i,s in enumerate(sigma)}
    orientation = -1 if mirror else 1
    tape, position, state = {}, 0, 0
    for step in range(LIMIT+1):
        transformed = {orientation*(p-position):inverse[h] for p,h in tape.items()}
        lo, hi = min([0, *transformed]), max([0, *transformed])
        left = [transformed.get(p,0) for p in range(-1,lo-1,-1)]
        right = [transformed.get(p,0) for p in range(1,hi+1)]
        found = phase(state ^ swapped, left, inverse[tape.get(position,0)], right)
        if found:
            return {'status':'invariant_entry', 'entry_step':step, 'simulated_steps':step,
                    'phase':found, 'normalized_configuration':[state ^ swapped,left,inverse[tape.get(position,0)],right]}
        if step == LIMIT:
            break
        tr = table[4*state+tape.get(position,0)]
        if tr is None:
            return {'status':'undefined_transition','simulated_steps':step}
        write, direction, state = tr
        if write:tape[position]=write
        else:tape.pop(position,None)
        position += direction
    return {'status':'prefix_limit','simulated_steps':LIMIT}


def main():
    pins = [Path(__file__), RESIDUAL, ROOT/'research/burn3-burndown-summary.json']
    exclusion_paths = [ROOT/('research/burn4-ternary-'+name+'-machines.json')
                       for name in ('counter','template','swapped')]
    pins.extend(exclusion_paths)
    exclusions = {row['machine'] for path in exclusion_paths for row in json.loads(path.read_text())['rows']}
    original = RESIDUAL.read_text().splitlines()
    summary = json.loads((ROOT/'research/burn3-burndown-summary.json').read_text())
    if (len(original) != 31495 or len(set(original)) != 31495
            or sha(RESIDUAL) != summary['outputs']['both-remaining.txt']['sha256']):
        raise ValueError('Unexpected exact instruction residual')
    residual = [m for m in original if m not in exclusions]
    reports = []
    for template in TEMPLATES:
        pins.extend([ROOT/template['source'], ROOT/template['report']])
        patterns=[]
        base=cells(template['machine'])
        for perm in itertools.permutations([1,2,3]):
            sigma=[0,*perm]
            for mirror,swapped in itertools.product((False,True),repeat=2):
                constraints=[]
                for target in template['support']:
                    q,h=divmod(target,4);c=base[target]
                    direction=({'L':'R','R':'L'}[c[1]])if mirror else c[1]
                    destination=chr(65+((ord(c[2])-65)^swapped))
                    constraints.append((4*(q^swapped)+sigma[h],str(sigma[int(c[0])])+direction+destination))
                patterns.append((sigma,mirror,swapped,constraints))
        matches=[]
        for machine in residual:
            table=cells(machine)
            for sigma,mirror,swapped,constraints in patterns:
                if all(table[i]==value for i,value in constraints):
                    extra=prefix(machine,sigma,mirror,swapped)if template['name']=='paired_digit_tail'else {'status':'exact_table_image','simulated_steps':0}
                    matches.append({'machine':machine,'symbol_map':sigma,'mirror':mirror,'state_exchange':swapped,**extra})
        reports.append({**template,'image_patterns':len(patterns),'matched_ids':len({r['machine']for r in matches}),
                        'matches':matches,'total_simulated_steps':sum(r['simulated_steps']for r in matches)})
    result={'scope':'Untrusted deterministic template screen; no proof or discharge claim.',
            'sources_sha256':{str(p.relative_to(ROOT)):sha(p)for p in pins},
            'original_residual_rows':len(original),'excluded_ternary_rows':len(set(original)&exclusions),
            'screened_rows':len(residual),'prefix_limit_per_match':LIMIT,'templates':reports}
    text=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if OUTPUT.exists() and OUTPUT.read_text()!=text:raise ValueError('Frozen screen differs')
    if not OUTPUT.exists():OUTPUT.write_text(text)
    print(json.dumps({'screened_rows':len(residual),'templates':[{k:r[k]for k in ['name','matched_ids','total_simulated_steps']}for r in reports]}))


if __name__=='__main__':main()
