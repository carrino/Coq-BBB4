#!/usr/bin/env python3
"""UNTRUSTED regression: every COMMITTED board re-renders BYTE-IDENTICAL.

This is the non-negotiable check for any change to `emit_lapcert.derive`, to
`lapcert`'s chain search, or to the step language in `Checkers/LapDecider.v`.
A single changed byte means the candidate ordering shifted underneath the
boards that are already in the tree -- which is how an additive-looking change
silently re-routes 500 proofs.

It re-derives each board from its machine spec into a SCRATCH directory and
diffs against `theories/Machines/`.  `coqc` is stubbed out, because the point
is the rendered text and a real compile of ~900 boards is hours: the cost is
that a board which needed a `coqc` RETRY (the first anchor family rendered but
did not compile, so `process` moved on) re-renders as its first family and is
reported as a mismatch.  Re-run those few with `--compile` to tell a retry
artefact from a genuine re-route.

The spec -> file map comes from `tools/closeout/frozen_map.tsv`, so only boards
that are actually load-bearing for the closeout are checked.

Usage
  rerender_check.py [--prefix LAPC,NLAP,PEEL,LAPQ] [--limit N] [--compile]
                    [--out DIR] [--only SPEC]
"""
import argparse
import collections
import os
import shutil
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, '..', '..'))
sys.path.insert(0, HERE)

import emit_lapcert as EL                                          # noqa: E402

FROZEN = os.path.join(REPO, 'tools', 'closeout', 'frozen_map.tsv')
OWNED = ('LAPC', 'NLAP', 'PEEL', 'LAPQ')


def boards(prefixes):
    """(vfile -> spec) for every committed board emit_lapcert owns.  A vfile
    can serve several machines (the 0RB shadows); the FIRST spec listed is the
    one the file was rendered from."""
    out = {}
    with open(FROZEN) as f:
        next(f)
        for line in f:
            p = line.rstrip('\n').split('\t')
            if len(p) < 3:
                continue
            spec, vfile = p[0], p[2]
            base = os.path.basename(vfile)
            if not base.startswith(tuple(x + '_' for x in prefixes)):
                continue
            out.setdefault(vfile, spec)
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--prefix', default=','.join(OWNED))
    ap.add_argument('--limit', type=int, default=0)
    ap.add_argument('--compile', action='store_true')
    ap.add_argument('--out')
    ap.add_argument('--only')
    a = ap.parse_args()

    prefixes = [x.strip() for x in a.prefix.split(',') if x.strip()]
    todo = boards(prefixes)
    if a.only:
        todo = {v: s for v, s in todo.items() if s == a.only}
    items = sorted(todo.items())
    if a.limit:
        items = items[:a.limit]

    scratch = a.out or tempfile.mkdtemp(prefix='rerender_')
    os.makedirs(scratch, exist_ok=True)
    EL.OUTDIR = scratch
    if not a.compile:
        EL.coqc = lambda path: (True, '')

    cnt = collections.Counter()
    bad = []
    for i, (vfile, spec) in enumerate(items):
        committed = os.path.join(REPO, vfile)
        got = os.path.join(scratch, os.path.basename(vfile))
        if os.path.exists(got):
            os.remove(got)
        try:
            r = EL.process(spec, True, True)
        except Exception as e:                                 # noqa: BLE001
            cnt['ERROR'] += 1
            bad.append((vfile, spec, '%s: %s' % (type(e).__name__, e)))
            continue
        if not r.get('ok'):
            cnt['no longer derives'] += 1
            bad.append((vfile, spec, 'no longer derives: %s' % r.get('why')))
        elif not os.path.exists(got):
            cnt['rendered elsewhere'] += 1
            bad.append((vfile, spec,
                        'rendered %s' % os.path.basename(r.get('file') or '?')))
        elif open(got, 'rb').read() == open(committed, 'rb').read():
            cnt['IDENTICAL'] += 1
        else:
            cnt['DIFFERS'] += 1
            bad.append((vfile, spec, 'bytes differ'))
        if (i + 1) % 50 == 0:
            print('  %d/%d  %s' % (i + 1, len(items), dict(cnt)), flush=True)

    print()
    for k, v in cnt.most_common():
        print('%6d  %s' % (v, k))
    if bad:
        print('\n%d board(s) not byte-identical:' % len(bad))
        for vfile, spec, why in bad[:60]:
            print('  %-58s %-30s %s' % (os.path.basename(vfile), spec, why))
    print('\nscratch dir: %s' % scratch)
    return 1 if bad else 0


if __name__ == '__main__':
    sys.exit(main())
