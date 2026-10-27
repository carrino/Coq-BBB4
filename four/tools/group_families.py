"""Exploratory grouping of the fixed BBB(2,4) survey, not proof discharge.

Uses blank-preserving symbol permutations and the already-normalized first
direction. Also looks for the blank-prefix shadows used by BBB4's shadowlib,
and groups complete representatives by their state-avoiding submachines.
Large representative/mapping files stay under ignored build/.
"""
import argparse
import csv
import hashlib
import json
from collections import Counter
from functools import lru_cache
from itertools import permutations
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PERMS = [(0,) + p for p in permutations((1, 2, 3))]


def parse(machine):
    return tuple(machine.replace('_', '')[i:i+3] for i in range(0, 24, 3))


def render(table):
    return ''.join(table[:4]) + '_' + ''.join(table[4:])


def rename(table, perm, mirror=False, swap=False):
    out = ['---'] * 8
    for i, tr in enumerate(table):
        q, s = divmod(i, 4)
        dest = 4 * (q ^ swap) + perm[s]
        if tr != '---':
            direction = ('R' if tr[1] == 'L' else 'L') if mirror else tr[1]
            out[dest] = str(perm[int(tr[0])]) + direction + chr(65 + ((ord(tr[2])-65) ^ swap))
    return tuple(out)


def variants(table):
    """Root-normalized orbit with A fixed and blank symbol 0 fixed."""
    assert table[0] != '---' and table[0][2] == 'B'
    written = int(table[0][0])
    for perm in PERMS:
        if written == 0 or perm[written] == 1:
            yield rename(table, perm, mirror=table[0][1] == 'R')


def canonical(table):
    return min(render(t) for t in variants(table))


def defined_mask(table):
    return sum(1 << i for i, tr in enumerate(table) if tr != '---')


@lru_cache(maxsize=None)
def avoid_canonical(table):
    """One live state: 8=return to the removed state, 0..7=write/direction.

    Used only for fully defined input tables. These are shared proof templates,
    not equivalence classes of blank-start machine executions.
    """
    images = []
    for perm in PERMS:
        for flip in (0, 1):
            out = [8] * 4
            for s, tr in enumerate(table):
                out[perm[s]] = 8 if tr == 8 else 2*perm[tr//2] + ((tr % 2) ^ flip)
            images.append(tuple(out))
    return min(images)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    parser.add_argument('--survey-dir', type=Path, default=ROOT/'build/triage')
    args = parser.parse_args()
    baseline = json.loads((ROOT/'research/burndown-summary.json').read_text())
    groups, summary = {}, {}
    outdir = ROOT/'build/grouping'; outdir.mkdir(parents=True, exist_ok=True)
    for label in ('blank', 'nonblank'):
        path = args.survey_dir/f'{label}.unresolved.txt'
        assert hashlib.sha256(path.read_bytes()).hexdigest() == baseline['roots'][label]['inventory_sha256']
        machines = path.read_text().splitlines(); members = set(machines)
        grouped = Counter(canonical(parse(m)) for m in machines)
        assert len(members) == len(machines)
        # Check each reported orbit is complete in the input inventory.
        for rep, size in grouped.items():
            orbit = {render(t) for t in variants(parse(rep))}
            assert orbit <= members and len(orbit) == size
        groups[label] = grouped
        summary[label] = dict(input_families=len(machines), representatives=len(grouped),
                              orbit_size_histogram=dict(sorted(Counter(grouped.values()).items())),
                              input_sha256=baseline['roots'][label]['inventory_sha256'])
        (outdir/f'{label}.representatives.txt').write_text('\n'.join(sorted(grouped))+'\n')

    # A0=0LB leaves an entirely blank tape in state B after exactly one step.
    # Swap A/B, normalize symbols/direction, and look for a core subtable.
    pool = set(groups['nonblank'])
    masks = sorted({defined_mask(parse(m)) for m in pool}, key=lambda n: (-n.bit_count(), n))
    shadows = []
    for machine in sorted(groups['blank']):
        table = parse(machine)
        assert table[0] == '0LB' and table[4][0] in '123' and table[4][2] == 'A'
        reroot = rename(table, (0, 1, 2, 3), swap=True)
        hit = None
        for candidate in variants(reroot):
            available = defined_mask(candidate)
            for mask in masks:
                if mask & ~available:
                    continue
                partner = render(tuple(tr if mask & (1 << i) else '---' for i, tr in enumerate(candidate)))
                if partner in pool:
                    hit = dict(machine=machine, partner=partner, prefix_steps=1,
                               transformed=render(candidate), status='unchecked_transport')
                    break
            if hit:
                break
        if hit:
            shadows.append(hit)
    with (outdir/'shadow-candidates.tsv').open('w') as f:
        writer = csv.DictWriter(f, ['machine', 'partner', 'prefix_steps', 'transformed', 'status'],
                                delimiter='\t', lineterminator='\n')
        writer.writeheader(); writer.writerows(shadows)

    avoid, complete = Counter(), 0
    for label in groups:
        for machine in groups[label]:
            table = parse(machine)
            if '---' in table:
                continue
            complete += 1
            for removed in (0, 1):
                other = 1 - removed
                sub = tuple(8 if ord(tr[2])-65 == removed else
                            2*int(tr[0]) + (tr[1] == 'R') for tr in table[4*other:4*other+4])
                avoid[avoid_canonical(sub)] += 1
    result = dict(status='Exploratory grouping only; no new bounds or census discharges',
                  input_families=sum(r['input_families'] for r in summary.values()),
                  symmetry_representatives=sum(r['representatives'] for r in summary.values()),
                  roots=summary, candidate_blank_prefix_shadows=len(shadows),
                  unmatched_blank_representatives=len(groups['blank'])-len(shadows),
                  avoid_templates=dict(complete_representatives=complete,
                                       machine_target_pairs=2*complete, distinct_templates=len(avoid),
                                       largest_template_pair_count=max(avoid.values())),
                  proof_status='Symbol transport, shadow timing/prefix obligations, and avoid-template lemmas still need BBB24 coverage integration')
    text = json.dumps(result, indent=2)+'\n'
    target = ROOT/'research/grouping-256.json'
    if args.check:
        assert target.read_text() == text, 'Grouping report changed'
    else:
        target.write_text(text)
    print(text, end='')


if __name__ == '__main__':
    main()
