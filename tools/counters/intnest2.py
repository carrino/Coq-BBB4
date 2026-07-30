#!/usr/bin/env python3
"""UNTRUSTED probe: is the interior lap's INNER lap affine, or is the interior
branch a DOUBLE nesting?

`intnest.py` measures that 38 of the 40 `no interior j=S j chain` rows carry a
FULL inner counter family -- values exactly `2^(j-1)..2^j-1` -- inside ONE
interior lap, at both octave parities.  That is the signature of the nested lap
`Counters/NestedLapLift.v` already carries, and it would make the interior
branch the same build the OVERFLOW arm already has.

But `intfit.py` measures the interior lap growing by a factor of 3 or 4 per
octave, not 2, and a single nesting predicts 2: summing an affine inner cost
`a*i + b` over `2^(j-1)` inner laps is `Theta(2^j)`.  A factor of 4 says the
INNER lap is itself exponential -- wave-30 section 6g's double nesting, whose
phase ratio it measured at ~4.

So measure the inner lap directly: step counts between consecutive inner
anchors, fitted against the inner carry index `i`.  Affine means ONE level of
nesting is enough for these rows and `nested_overflow_lift` transfers.  Not
affine means two, and the item to write is `NestedLap2`/the cascade, not a
straight transfer.

Usage
  intnest2.py --list FILE [--json OUT]
"""
import argparse
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import intfit as IF                                                # noqa: E402
import intnest as IN                                               # noqa: E402
import lapcert as LC                                               # noqa: E402
import tailcert as TC                                              # noqa: E402
from emit_lapcert import ENCDATA, ENC                              # noqa: E402
from emit_interleave import parse, carry                           # noqa: E402
from mirror_common import mirror_spec                              # noqa: E402
from regcert import RegError, octave                               # noqa: E402

MAXSTEP = 20000000


def inner_laps(spec, maxk=7):
    """For the deepest interior lap at each parity: the step count between
    consecutive anchors of the inner family `intnest` found, per inner carry
    index, and whether an affine law fits them."""
    o = IN.probe(spec, maxk)
    if 'parity' not in o:
        return o
    for mir in (False, True):
        if mir != o['mirror']:
            continue
        dspec = o['dspec']
        tab = parse(dspec)
        enc, frames, ks = TC.two_form(dspec)
        st = {b: frames[b][0] for b in (0, 1)}
        tl = {b: tuple(frames[b][1]) for b in (0, 1)}
        fr = {b: tuple(frames[b][2]) for b in (0, 1)}
        encf = ENC[enc]
        for b in (0, 1):
            P = o['parity'][b]
            if P['verdict'] != 'ok' or not P['full']:
                P['inner'] = dict(verdict='no full inner family')
                continue
            name_in, q_in, ti, fi, oct_ = P['full'][0]
            ti, fi = tuple(ti), tuple(fi)
            ienc = ENC[name_in]
            p = P['p']
            src = (st[b], tuple(encf(p)) + tl[b], 0, fr[b])
            nb = octave(p + 1) % 2
            want = (st[nb], LC.rstrip0(tuple(encf(p + 1)) + tl[nb]), 0,
                    LC.rstrip0(fr[nb]))
            # The run has to come from THE SAME key as the encoding: `full[0]`
            # is the first FULL-octave key and `hits[0]` is the longest-run one,
            # and they are routinely different keys -- reading `lo`/`hi` off the
            # latter while decoding with the former builds a match table that
            # nothing in the phase can hit, which is what "anchors 0/N" was.
            K = P['K']
            lo, hi = 2 ** (K - 1 + oct_), 2 ** (K + oct_) - 1
            for h in P['hits']:
                if (h['key'][0] == name_in and h['key'][1] == q_in
                        and tuple(h['key'][2]) == ti
                        and tuple(h['key'][3]) == fi):
                    lo, hi = h['lo'], h['hi']
                    break
            key = {}
            for v in range(lo, hi + 1):
                key[(q_in, LC.rstrip0(tuple(ienc(v)) + ti),
                     LC.rstrip0(fi))] = v
            seen, cfg, n = {}, src, 0
            while n < MAXSTEP:
                cfg = LC.wstep(tab, False, False, cfg)
                n += 1
                q, l, h, r = cfg
                if h == 0:
                    if (q == want[0] and LC.rstrip0(l) == want[1]
                            and LC.rstrip0(r) == want[3]):
                        break
                    v = key.get((q, LC.rstrip0(l), LC.rstrip0(r)))
                    if v is not None and v not in seen:
                        seen[v] = n
            vs = sorted(seen)
            costs = {}
            for v in vs:
                if v + 1 in seen:
                    costs.setdefault(carry(v)[0], set()).add(seen[v + 1]
                                                             - seen[v])
            pts = sorted((i, sorted(s)) for i, s in costs.items())
            rows = [dict(j=i, n=c[0]) for i, c in pts if len(c) == 1]
            multi = [[i, c] for i, c in pts if len(c) > 1]
            f = IF.fit(rows) if rows else None
            P['inner'] = dict(
                verdict=('affine' if f and not multi else
                         ('not a function of i' if multi else 'not affine')),
                law=f, nanchor=len(vs), want=hi - lo + 1,
                pts=[[i, c] for i, c in pts], clash=multi)
        return o
    return o


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
            o = inner_laps(s)
        except Exception as e:                                      # noqa: BLE001
            o = dict(spec=s, verdict='probe failed: %s' % e)
        out.append(o)
        if 'parity' not in o:
            print('%4d/%d %-30s %s' % (i + 1, len(specs), s, o['verdict']))
            continue
        for b in (0, 1):
            P = o['parity'][b] if b in o['parity'] else o['parity'][str(b)]
            I = P.get('inner', {})
            v = I.get('verdict', P['verdict'])
            tally['b%d %s' % (b, v)] = tally.get('b%d %s' % (b, v), 0) + 1
            print('%4d/%d %-30s b%d %-20s %s  %s'
                  % (i + 1, len(specs), s, b, v,
                     ('%d*i+%d' % I['law']) if I.get('law') else '',
                     ('anchors %d/%d' % (I['nanchor'], I['want']))
                     if 'nanchor' in I else ''))
    print('\n--- tally ---')
    for k in sorted(tally, key=lambda x: -tally[x]):
        print('%5d  %s' % (tally[k], k))
    if a.json:
        with open(a.json, 'w') as f:
            json.dump(out, f, indent=1, sort_keys=True)
    return 0


if __name__ == '__main__':
    sys.exit(main())
