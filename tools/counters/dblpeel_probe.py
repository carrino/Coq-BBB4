#!/usr/bin/env python3
"""UNTRUSTED measurement: does the DOUBLE PEEL open the `no interior j=0` gate?

`tailcert.py` splits the interior branch two ways -- `j = 0` concrete and
`j = S j'` with one unit copy peeled -- and 70 of the 113 two-form rows stop at
the FIRST of those (`no interior j=0 chain at octave parity b`).  Wave-29 read
the reason off the machine: at `j = 0` the frame is

    Z0 = (q, left = sS CONCRETE, head = S0, right = far)

and the lap leaves `sS` immediately and runs into the OPAQUE left tail
`XL = E q0 ++ tail`.  The frame is too SHORT -- the lap wants cells of `E q0`,
which no framing names.

So peel ONE MORE DIGIT.  `cview p = (j, Some q0)` leaves `E q0` untouched by
the increment (`E p = rep uS j ++ sS ++ E q0`,
`E (succ p) = rep uD j ++ sD ++ E q0` -- the same `E q0` on both sides), so
q0's LOW DIGIT can move into the concrete prefix on both sides at once:

    j = 0, q0's low digit d:   sS ++ dig(d)  ->  sD ++ dig(d)

with `dig(0) = sS` and `dig(1) = uS` (the alphabet's own digit words), plus the
base case `q0 = 1`, whose `E q0` is the terminator `E 1`.

This measures, per row and per octave parity, whether the peeled `j = 0` chains
derive -- exactly and up to `lift` -- BEFORE any template is written.

Usage
  dblpeel_probe.py --list FILE [--limit N] [--out JSON]
  dblpeel_probe.py --spec SPEC
"""
import argparse
import collections
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import lapcert as LC                                               # noqa: E402
import tailcert as TC                                              # noqa: E402
from emit_lapcert import ENCDATA, ENC                              # noqa: E402
from emit_interleave import parse, LAB                             # noqa: E402
from mirror_common import mirror_spec                              # noqa: E402
from regcert import RegError, F                                    # noqa: E402

SYM = {0: '0', 1: '1'}


def fs(t):
    return ''.join(SYM.get(x, '?') for x in t) or '.'


def digits(enc):
    """The alphabet's own digit words and terminator: dig(0), dig(1), E 1."""
    d = ENCDATA[enc]
    return dict(d0=tuple(d['sS']), d1=tuple(d['uS']),
                term=tuple(ENC[enc](1)))


def probe(spec):
    last = None
    for mir in (False, True):
        dspec = mirror_spec(spec) if mir else spec
        tab = parse(dspec)
        try:
            enc, frames, ks = TC.two_form(dspec)
        except RegError as e:
            last = str(e)
            continue
        d = ENCDATA[enc]
        uS, uD = tuple(d['uS']), tuple(d['uD'])
        sS, sD = tuple(d['sS']), tuple(d['sD'])
        dg = digits(enc)
        out = dict(spec=spec, mirror=mir, enc=enc, ks=ks,
                   dig0=fs(dg['d0']), dig1=fs(dg['d1']),
                   term=fs(dg['term']), parity={})
        for b in (0, 1):
            st = frames[b][0]
            far = tuple(frames[b][2])
            # the CURRENT (single-peel) j = 0 frame, for the control
            Z0 = (st, (sS, (), 0, 0, ()), 0, F(far))
            Z1 = (st, (sD, (), 0, 0, ()), 0, F(far))
            r = dict(tail=fs(tuple(frames[b][1])), far=fs(far), cases={})
            ch = LC.derive_chain(tab, False, True, Z0, Z1)
            chl = (None if ch is not None
                   else LC.derive_chain(tab, False, True, Z0, Z1, lift=True))
            r['cases']['j0'] = dict(exact=ch is not None, lift=chl is not None,
                                    cost=None if ch is None else
                                    LC.srun(tab, False, True, ch, Z0)[2])
            # the DOUBLE PEEL: q0's low digit in the concrete prefix
            for name, dig in (('j0+d0', dg['d0']), ('j0+d1', dg['d1']),
                              ('j0+term', dg['term'])):
                A = (st, (sS + dig, (), 0, 0, ()), 0, F(far))
                B = (st, (sD + dig, (), 0, 0, ()), 0, F(far))
                ch = LC.derive_chain(tab, False, True, A, B)
                chl = (None if ch is not None
                       else LC.derive_chain(tab, False, True, A, B, lift=True))
                cost = None
                if ch is not None:
                    cost = LC.srun(tab, False, True, ch, A)[2]
                r['cases'][name] = dict(exact=ch is not None,
                                        lift=chl is not None, cost=cost)
            # j = S j' is the branch that already derives; re-check it
            P0 = (st, (uS, uS, 1, 0, sS), 0, F(far))
            P1 = (st, (uD, uD, 1, 0, sD), 0, F(far))
            ch = LC.derive_chain(tab, False, True, P0, P1)
            r['cases']['jS'] = dict(exact=ch is not None, lift=False,
                                    cost=None if ch is None else
                                    LC.srun(tab, False, True, ch, P0)[2])
            out['parity'][b] = r
        return out
    return dict(spec=spec, verdict=last or 'no family')


def verdict(o):
    """Does the DOUBLE PEEL close the j = 0 gate at BOTH parities?"""
    if 'parity' not in o:
        return 'no family'
    need, got_x, got_l = False, True, True
    for b in (0, 1):
        c = o['parity'][b]['cases']
        if c['j0']['exact']:
            continue                              # this parity never blocked
        need = True
        ok_x = c['j0+d0']['exact'] and c['j0+d1']['exact']
        ok_l = ((c['j0+d0']['exact'] or c['j0+d0']['lift'])
                and (c['j0+d1']['exact'] or c['j0+d1']['lift']))
        got_x &= ok_x
        got_l &= ok_l
    if not need:
        return 'j=0 already derives at both parities'
    if got_x:
        return 'DOUBLE PEEL derives EXACTLY'
    if got_l:
        return 'double peel derives up to lift'
    return 'double peel does not derive'


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--list')
    ap.add_argument('--spec')
    ap.add_argument('--limit', type=int, default=0)
    ap.add_argument('--out')
    a = ap.parse_args()
    specs = ([a.spec] if a.spec else
             [x.strip() for x in open(a.list) if x.strip()])
    if a.limit:
        specs = specs[:a.limit]
    res, cnt = [], collections.Counter()
    for i, spec in enumerate(specs):
        try:
            o = probe(spec)
        except Exception as e:                                 # noqa: BLE001
            o = dict(spec=spec, verdict='ERR %s: %s' % (type(e).__name__, e))
        o['verdict'] = o.get('verdict') or verdict(o)
        if 'parity' in o:
            o['verdict'] = verdict(o)
        res.append(o)
        cnt[o['verdict']] += 1
        print('%3d/%d %-30s %-16s %s' % (i + 1, len(specs), spec,
                                         o.get('enc', '-'), o['verdict']),
              flush=True)
        for b in (0, 1):
            if b not in o.get('parity', {}):
                continue
            c = o['parity'][b]['cases']
            print('        parity %d tail=%-8s far=%-8s %s' % (
                b, o['parity'][b]['tail'], o['parity'][b]['far'],
                '  '.join('%s=%s' % (k, 'exact/%s' % v['cost'] if v['exact']
                                     else 'lift' if v['lift'] else '-')
                          for k, v in c.items())))
    print()
    for k, v in cnt.most_common():
        print('%5d  %s' % (v, k))
    if a.out:
        json.dump(res, open(a.out, 'w'), indent=1)


if __name__ == '__main__':
    main()
