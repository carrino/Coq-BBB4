#!/usr/bin/env python3
"""UNTRUSTED measurement: does a DEEPER PEEL open the `no interior j=S j` gate?

The standing do-not-retry (WAVE30 section 8, restated WAVE31 section 8) reads
*"a deeper peel on the two-form interior branch -- the peeled `j = 0` frames
return the same `lift` verdict as the unpeeled one"*.  That entry is about the
**`j = 0`** half, and `dblpeel_probe.py` is the probe that earned it.  The
**`j = S j'`** half is not covered by it and has never been tried, which is
what makes it item (2) of the wave-32 prompt.

`tailcert._derive` states that half with ONE unit copy in the prefix:

    P0 = (st[b], (uS, uS, 1, 0, sS), 0, F(fr[b]))
    P1 = (st[b], (uD, uD, 1, 0, sD), 0, F(fr[b]))

This probe measures three deepenings of it, per row and per octave parity:

* **more units in the prefix** (depth 2 and 3), each with the extra concrete
  case the reindex leaves behind (`j = 1`, and `j = 2` at depth 3);
* **q0's low digit peeled into the POST**, which is `dblpeel_probe`'s move --
  the opaque side is `E q0 ++ tail` and the increment leaves `E q0` alone, so
  its low digit is concrete on both sides at once -- applied to THIS half;
* **both at once.**

A chain's cost is affine in its symbolic index by construction (`srun` returns
`a * j + b`), so a row whose interior lap is measured NON-affine cannot be
expressed by any of these; `intfit.py` is the probe for that and this one
reports the peel verdict independently, so the two can be read against each
other.

Usage
  jspeel.py --list FILE [--json OUT]
  jspeel.py --spec SPEC
"""
import argparse
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import lapcert as LC                                               # noqa: E402
import tailcert as TC                                              # noqa: E402
from emit_lapcert import ENCDATA, ENC                              # noqa: E402
from emit_interleave import parse                                  # noqa: E402
from mirror_common import mirror_spec                              # noqa: E402
from regcert import RegError, F                                    # noqa: E402


def _try(tab, A, B):
    """(verdict, cost) for one framing: exact, up to lift, or blocked."""
    ch = LC.derive_chain(tab, False, True, A, B)
    if ch is not None:
        r = LC.srun(tab, False, True, ch, A)
        if r is not None and r[2] != 0:
            return 'exact', (r[1], r[2])
    ch = LC.derive_chain(tab, False, True, A, B, lift=True)
    if ch is not None:
        r = LC.srun(tab, False, True, ch, A)
        if r is not None and r[2] != 0:
            return 'lift', (r[1], r[2])
    return 'blocked', None


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
        # the alphabet's own digit words and terminator, as `dblpeel_probe`
        # reads them: dig(0) = sS, dig(1) = uS, E 1 = the terminator.
        digs = (('d0', sS), ('d1', uS), ('term', tuple(ENC[enc](1))))
        out = dict(spec=spec, mirror=mir, enc=enc, ks=ks, parity={})
        for b in (0, 1):
            st, far = frames[b][0], tuple(frames[b][2])
            cases = {}
            # depth 1 -- the control, exactly what `_derive` states today
            cases['depth1'] = _try(tab, (st, (uS, uS, 1, 0, sS), 0, F(far)),
                                        (st, (uD, uD, 1, 0, sD), 0, F(far)))
            # deeper prefixes, plus the concrete cases the reindex leaves
            for n in (2, 3):
                cases['depth%d' % n] = _try(
                    tab, (st, (uS * n, uS, 1, 0, sS), 0, F(far)),
                         (st, (uD * n, uD, 1, 0, sD), 0, F(far)))
                for m in range(1, n):
                    cases['depth%d.j%d' % (n, m)] = _try(
                        tab, (st, (uS * m + sS, (), 0, 0, ()), 0, F(far)),
                             (st, (uD * m + sD, (), 0, 0, ()), 0, F(far)))
            # q0's low digit in the POST -- `dblpeel_probe`'s move, on THIS half
            for nm, dg in digs:
                cases['post.' + nm] = _try(
                    tab, (st, (uS, uS, 1, 0, sS + dg), 0, F(far)),
                         (st, (uD, uD, 1, 0, sD + dg), 0, F(far)))
                cases['depth2.post.' + nm] = _try(
                    tab, (st, (uS * 2, uS, 1, 0, sS + dg), 0, F(far)),
                         (st, (uD * 2, uD, 1, 0, sD + dg), 0, F(far)))
            out['parity'][b] = dict(cases=cases)
        return out
    return dict(spec=spec, verdict=last or 'no family')


def verdict(o):
    """Does any deepening derive the `j = S j'` half at BOTH parities, where
    the depth-1 framing does not?"""
    if 'parity' not in o:
        return 'no family', None
    need = [b for b in (0, 1)
            if o['parity'][b]['cases']['depth1'][0] == 'blocked']
    if not need:
        return 'depth 1 already derives at both parities', None
    keys = [k for k in o['parity'][0]['cases'] if k != 'depth1'
            and '.j' not in k]
    for k in keys:
        vs = [o['parity'][b]['cases'][k][0] for b in need]
        if all(v == 'exact' for v in vs):
            return 'DERIVES EXACTLY', k
    for k in keys:
        vs = [o['parity'][b]['cases'][k][0] for b in need]
        if all(v in ('exact', 'lift') for v in vs):
            return 'derives up to lift', k
    return 'no deepening derives', None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--list')
    ap.add_argument('--spec')
    ap.add_argument('--json')
    a = ap.parse_args()
    specs = ([a.spec] if a.spec else
             [x.split()[0] for x in open(a.list) if x.strip()
              and not x.startswith('#')])
    out, tally = [], {}
    for i, s in enumerate(specs):
        try:
            o = probe(s)
        except Exception as e:                                      # noqa: BLE001
            o = dict(spec=s, verdict='probe failed: %s' % e)
        v, where = verdict(o)
        o['result'] = v
        o['opened_by'] = where
        out.append(o)
        tally[v] = tally.get(v, 0) + 1
        print('%4d/%d %-30s %-28s %s'
              % (i + 1, len(specs), s, v, where or ''))
    print('\n--- tally ---')
    for k in sorted(tally, key=lambda x: -tally[x]):
        print('%5d  %s' % (tally[k], k))
    if a.json:
        with open(a.json, 'w') as f:
            json.dump(out, f, indent=1, sort_keys=True)
    return 0


if __name__ == '__main__':
    sys.exit(main())
