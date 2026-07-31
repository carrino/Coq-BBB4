#!/usr/bin/env python3
"""UNTRUSTED hygiene check: every .v under theories/ is either IN _CoqProject
or explicitly exempt.

A board that is not in `_CoqProject` is not built by `make`, so nothing --
not the kernel, not CI -- ever checks it again.  That has bitten twice:
`Counters/RegGlue.v` (a board's dependency, missing, so a fresh `make` died)
and the Stage-B ladder's partial boards (emitted, never wired, silently
unbuilt).  The first is a build break, the second is proof-shaped code that
nobody verifies.

Exemptions live in `tools/coqproject_exempt.txt`, one glob per line with a
reason, so that every unbuilt file under `theories/` is a deliberate,
reviewed decision rather than drift.

Usage:  python3 tools/check_coqproject.py       (exit 1 on any surprise)
"""
import fnmatch
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, '..'))


def load_exempt():
    pats = []
    path = os.path.join(REPO, 'tools', 'coqproject_exempt.txt')
    for line in open(path):
        line = line.split('#', 1)[0].strip()
        if line:
            pats.append(line)
    return pats


def main():
    os.chdir(REPO)
    listed = set()
    for line in open('_CoqProject'):
        line = line.strip()
        if line.endswith('.v'):
            listed.add(line)

    exempt = load_exempt()
    on_disk = []
    for root, _dirs, files in os.walk('theories'):
        for f in files:
            if f.endswith('.v'):
                on_disk.append(os.path.join(root, f))

    unwired = []
    for p in sorted(on_disk):
        if p in listed:
            continue
        if any(fnmatch.fnmatch(p, pat) for pat in exempt):
            continue
        unwired.append(p)

    ghosts = sorted(p for p in listed if not os.path.exists(p))

    ok = True
    if unwired:
        ok = False
        print('UNWIRED: %d .v file(s) under theories/ are neither in '
              '_CoqProject nor exempt:' % len(unwired))
        for p in unwired:
            print('  ', p)
        print('Add them to _CoqProject, or add a pattern with a reason to '
              'tools/coqproject_exempt.txt.')
    if ghosts:
        ok = False
        print('GHOSTS: %d path(s) in _CoqProject do not exist:' % len(ghosts))
        for p in ghosts:
            print('  ', p)

    if ok:
        print('COQPROJECT CHECK: OK (%d listed, %d exempt-matched, 0 unwired, '
              '0 ghosts)' % (len(listed), len(on_disk) - len(listed)))
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
