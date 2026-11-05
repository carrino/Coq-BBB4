#!/usr/bin/env python3
"""Untrusted, reproducible first-post-cutoff searches on explicit candidate lists.

These lists are not an exhaustive census. A null observation never proves silence.
Only reflection and state permutations fixing A are used for deduplication.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
import itertools
import json
from pathlib import Path
import re
import subprocess
import time

MACHINE = re.compile(r'(?:(?:[01][LR][A-D]|---){2}_){3}(?:[01][LR][A-D]|---){2}')


def canonical(machine):
    cells = [row[j:j+3] for row in machine.split('_') for j in (0, 3)]
    variants = []
    for rest in itertools.permutations(range(1, 4)):
        perm = (0,) + rest
        for mirror in (False, True):
            out = ['---'] * 8
            for q in range(4):
                for a in range(2):
                    tr = cells[2*q+a]
                    if tr != '---':
                        dr = {'L': 'R', 'R': 'L'}[tr[1]] if mirror else tr[1]
                        tr = tr[0] + dr + chr(65 + perm[ord(tr[2])-65])
                    out[2*perm[q]+a] = tr
            variants.append('_'.join(out[2*q]+out[2*q+1] for q in range(4)))
    return min(variants, key=lambda s: (s[1] == 'L', s))


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--source', action='append', required=True, type=Path)
    ap.add_argument('--binary', required=True, type=Path)
    ap.add_argument('--output', required=True, type=Path)
    ap.add_argument('--start', type=int, default=32779478)
    ap.add_argument('--cap', type=int, default=500000000)
    ap.add_argument('--jobs', type=int, default=2)
    ap.add_argument('--mode', choices=('state', 'instruction'), default='state')
    args = ap.parse_args()
    if args.jobs < 1 or args.start < 0 or args.cap < args.start:
        ap.error('require jobs >= 1 and 0 <= start <= cap')
    args.output.mkdir(parents=True, exist_ok=True)
    aliases = {}
    sources = []
    for src in args.source:
        found = set(MACHINE.findall(src.read_text()))
        sources.append({'path': str(src), 'sha256': digest(src), 'distinct_rows': len(found)})
        for machine in sorted(found):
            aliases.setdefault(canonical(machine), set()).add(machine)
    machines = sorted(aliases)
    manifest = {'schema': 1, 'proof_credit': 0, 'universe': 'explicit candidate lists only',
                'start': args.start, 'cap': args.cap, 'mode': args.mode,
                'sources': sources, 'binary_sha256': digest(args.binary),
                'scanner_source_sha256': digest(Path(__file__).with_name('scan.cpp')),
                'driver_sha256': digest(Path(__file__)),
                'symmetry': 'reflection and state permutations fixing A; no rerooting',
                'distinct_input_rows': len(set().union(*aliases.values())),
                'canonical_candidates': len(machines),
                'aliases': {m: sorted(aliases[m]) for m in machines}}
    (args.output/'manifest.json').write_text(json.dumps(manifest, indent=2)+'\n')
    chunks = [machines[i::args.jobs] for i in range(args.jobs)]
    started = time.monotonic()

    def run(i):
        with (args.output/f'worker-{i:02}.jsonl').open('w') as out:
            subprocess.run([str(args.binary.resolve()), str(args.start), str(args.cap), args.mode],
                           input='\n'.join(chunks[i])+'\n', text=True, stdout=out, check=True)

    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        list(pool.map(run, range(args.jobs)))
    rows = []
    for i in range(args.jobs):
        rows += [json.loads(x) for x in (args.output/f'worker-{i:02}.jsonl').read_text().splitlines()]
    rows.sort(key=lambda x: x['machine'])
    if [r['machine'] for r in rows] != machines:
        raise RuntimeError('missing or duplicate scanner results')
    (args.output/'results.jsonl').write_text(''.join(json.dumps(r, sort_keys=True)+'\n' for r in rows))
    summary = {'proof_credit': 0, 'canonical_candidates': len(rows),
               'seconds': round(time.monotonic()-started, 3),
               'outcomes': {status: sum(r['status'] == status for r in rows)
                            for status in sorted({r['status'] for r in rows})}}
    for kind in ('state', 'instruction'):
        observations = [(t, r['machine'], i) for r in rows for i,t in enumerate(r[kind+'_first']) if t is not None]
        latest = max(observations, default=None)
        summary[kind+'_record'] = None if latest is None else {
            'horizon': latest[0], 'extra_wait': latest[0]-args.start,
            'machine': latest[1], 'target_index': latest[2]}
        summary[kind+'_control_mask_candidates'] = sum(r[kind+'_control_closed_at'] is not None for r in rows)
    (args.output/'summary.json').write_text(json.dumps(summary, indent=2)+'\n')
    print(json.dumps(summary, indent=2))


if __name__ == '__main__':
    main()
