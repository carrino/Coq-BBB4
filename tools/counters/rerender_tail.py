#!/usr/bin/env python3
"""UNTRUSTED regression: re-render every board `tailcert.py` owns into a
scratch directory, for the A/B diff.

`rerender_check.py` covers the prefixes `emit_lapcert` owns (LAPC/NLAP/PEEL/
LAPQ) and cannot see the REG_* boards this module writes.  Any change to
`tailcert`'s derive, to its templates, or to the alphabet list it searches has
to be shown NOT to move the boards already in the tree, and -- per the wave-31
lesson (`WAVE31_FINDINGS.md` section 11 and the wave-32 prompt's NON-NEGOTIABLE)
-- the check is an **A/B**: run this from a pristine worktree at the merge base
and again from the patched tree, then `diff -rq` the two output directories.
Comparing against the tree itself cannot work, because most committed boards
predate today's templates.

`coqc` is never called: the point is the rendered text.

Usage
  rerender_tail.py --out DIR [--list FILE]
"""
import argparse
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, '..', '..'))
sys.path.insert(0, HERE)

import tailcert as TC                                              # noqa: E402
from emit_interleave import mach_id                                # noqa: E402
from mirror_common import mirrorize                                # noqa: E402

DEFAULT = os.path.join(HERE, 'tailcert_derived12.txt')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--out', required=True)
    ap.add_argument('--list', default=DEFAULT)
    a = ap.parse_args()
    os.makedirs(a.out, exist_ok=True)
    specs = [x.split()[0] for x in open(a.list)
             if x.strip() and not x.startswith('#')]
    nok, nno = 0, 0
    for i, s in enumerate(specs):
        try:
            D = TC.derive(s)
            src = TC.render(D)
            if D['mirror']:
                src = mirrorize(src, s, D['spec'])
        except Exception as e:                                      # noqa: BLE001
            # a row that no longer derives is itself a diff: record the reason
            # in the output tree so the A/B shows it instead of hiding it.
            src = 'FAILED: %s\n' % e
            nno += 1
        else:
            nok += 1
        with open(os.path.join(a.out, '%s_%s.v' % (TC.PREFIX, mach_id(s)))
                  , 'w') as f:
            f.write(src)
        print('%4d/%d %-30s %s' % (i + 1, len(specs), s,
                                   'ok' if not src.startswith('FAILED')
                                   else src.strip()))
    print('\n%d rendered, %d failed -> %s' % (nok, nno, a.out))
    return 0


if __name__ == '__main__':
    sys.exit(main())
