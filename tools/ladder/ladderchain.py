#!/usr/bin/env python3
"""UNTRUSTED: derive, for each valfam ARM, a chain the Coq kernel accepts.

[Checkers/LadderKernel.v] validates a rule by replaying a list of steps with
[rrun] and comparing the result to the rule's right-hand side.  The steps are
the reused engine's ([LapDecider.sstep]) plus [RU i], "apply ladder rule i".
This module finds such a list, using tools/counters/lapcert.py -- which is
already a faithful Python mirror of [sstep]/[srun], written so that whatever
it accepts the Coq kernel accepts verbatim.

Nothing here is trusted.  A wrong chain makes [rrun] return [None] and the
board fails to compile.
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'counters'))
sys.path.insert(0, HERE)

import lapcert as LC                                              # noqa: E402
from ladderarm import normalize, parse_tm, ArmShape               # noqa: E402


def _side(s):
    pre, u, a, b, post = s
    return (tuple(pre), tuple(u), a, b, tuple(post))


def _conf(c):
    q, h, L, R = c
    return (q, _side(L), h, _side(R))


def derive_arm(tab, lhs_s, rhs_s, steps_s, maxdepth=32, nmax=120):
    """(chain, ca, cb, el, er, lhs, rhs) or raise ArmShape.

    The certificate's right-hand side is printed with trailing blanks
    stripped, so the search matches it up to [lift] and the rule the kernel
    is handed carries the EXACT configuration the chain reaches.  That is
    both stronger and what composition needs: a rule whose target is only
    correct up to blanks cannot be the source of the next one.

    The step count is still required to be exactly the certificate's: an arm
    whose count is off by one is a wrong arm, and the kernel says so rather
    than rounding it away."""
    L, R, ca, cb, el, er = normalize(lhs_s, rhs_s, steps_s)
    c0, c1 = _conf(L), _conf(R)
    chain = LC.derive_chain(tab, el, er, c0, c1, maxdepth=maxdepth,
                            nmax=nmax, lift=True)
    if chain is None:
        raise ArmShape('no chain found')
    got = LC.srun(tab, el, er, chain, c0)
    if got is None:
        raise ArmShape('chain does not replay')
    cf, gca, gcb = got
    if not LC._match(cf, c1, el, er, True):
        raise ArmShape('chain lands off the rhs: %r vs %r' % (cf, c1))
    if (gca, gcb) != (ca, cb):
        raise ArmShape('step count %d*j+%d, certificate claims %d*j+%d'
                       % (gca, gcb, ca, cb))
    return chain, ca, cb, el, er, c0, cf


def main():
    import argparse
    import json
    ap = argparse.ArgumentParser()
    ap.add_argument('cert')
    ap.add_argument('--maxdepth', type=int, default=32)
    ap.add_argument('--nmax', type=int, default=120)
    args = ap.parse_args()
    cert = json.load(open(args.cert))
    if isinstance(cert, list):
        cert = cert[0]
    tab = parse_tm(cert['spec'])
    ok, bad = 0, []
    for a in cert['arms']:
        try:
            chain, ca, cb, el, er, _, _ = derive_arm(
                tab, a['lhs'], a['rhs'], a['steps'],
                maxdepth=args.maxdepth, nmax=args.nmax)
            print('%-8s ok  %2d steps  %d*j+%-3d el=%-5s er=%-5s  %s'
                  % (a['name'], len(chain), ca, cb, el, er, chain))
            ok += 1
        except (ArmShape, ValueError) as e:
            print('%-8s FAIL %s' % (a['name'], e))
            bad.append((a['name'], str(e)))
    print('\n%d/%d arms have a kernel chain' % (ok, len(cert['arms'])))
    return 0 if not bad else 1


if __name__ == '__main__':
    sys.exit(main())
