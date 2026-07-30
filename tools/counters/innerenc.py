#!/usr/bin/env python3
"""UNTRUSTED probe: is `no inner family at pow2 j` a fact about the MACHINE or
about the ALPHABET LIST the inner search is given?

`tailcert.two_form` reads the OUTER counter over `tailcert.TRY` -- the obS = 0
rows of `ENCS` plus the three alphabets tailcert registers privately in
`ENCDATA` (`Alph_01_11_11`, the obS = 0 spelling of Mp's, and wave-30's two
INVERTED rows).  `tailcert._nested_ovf` reads the INNER counter over plain
`ENCS`, so those three are invisible to it.

This probe reports, per row and per overflow arm, the full-octave inner
families found over each list, so the difference is a measurement rather than
an inference.

Usage
  innerenc.py --list FILE [--json OUT]
"""
import argparse
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import lapcert as LC                                               # noqa: E402
import nestcert as NC                                              # noqa: E402
import tailcert as TC                                              # noqa: E402
from emit_lapcert import ENCDATA, ENC, ENCS                        # noqa: E402
from emit_interleave import parse                                  # noqa: E402
from mirror_common import mirror_spec                              # noqa: E402
from regcert import RegError, F, _chain, _phase                    # noqa: E402


def arms(spec):
    """Every overflow arm of [spec]'s two-form family that is NOT flat, with
    the `mid` phase `_nested_ovf` would search."""
    last = None
    for mir in (False, True):
        dspec = mirror_spec(spec) if mir else spec
        try:
            tab = parse(dspec)
            enc, frames, ks = TC.two_form(dspec, None)
        except RegError as e:
            last = str(e)
            continue
        d = ENCDATA[enc]
        uS, uD = tuple(d['uS']), tuple(d['uD'])
        soS, soD = tuple(d['soS']), tuple(d['soD'])
        st = {b: frames[b][0] for b in (0, 1)}
        tl = {b: tuple(frames[b][1]) for b in (0, 1)}
        fr = {b: tuple(frames[b][2]) for b in (0, 1)}
        out = []
        for b in (0, 1):
            nb = 1 - b
            B0 = (st[b], (uS, uS, 1, 0, soS + tl[b]), 0, F(fr[b]))
            B1 = (st[nb], ((), uD, 1, 2, soD + tl[nb]), 0, F(fr[nb]))
            ch, r = _chain(tab, True, True, B0, B1)
            if ch is not None and r[0] == B1 and r[2] > 0:
                continue
            ok = [k for k in ks[:-1] if k % 2 == b]
            if not ok:
                continue
            K = max(ok)
            p = (1 << (K + 1)) - 1
            src = (st[b], tuple(ENC[enc](p)) + tl[b], 0, fr[b])
            nxt = (st[nb], tuple(ENC[enc](p + 1)) + tl[nb], 0, fr[nb])
            try:
                mid = _phase(tab, src, (nxt[0], nxt[1], LC.rstrip0(nxt[3])))
            except Exception:                                      # noqa: BLE001
                continue
            out.append((b, K, mid))
        return dspec, mir, enc, out
    raise RegError(last or 'no family')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--list', required=True)
    ap.add_argument('--json')
    a = ap.parse_args()
    specs = [x.split()[0] for x in open(a.list)
             if x.strip() and not x.startswith('#')]
    out, gained = [], 0
    for i, s in enumerate(specs):
        try:
            dspec, mir, enc, ar = arms(s)
        except Exception as e:                                     # noqa: BLE001
            print('%4d/%d %-30s NO: %s' % (i + 1, len(specs), s, e))
            continue
        rec = dict(spec=s, enc=enc, arms=[])
        for (b, K, mid) in ar:
            old = NC.families(mid, ENCDATA, ENCS, K=K)
            new = NC.families(mid, ENCDATA, TC.TRY, K=K)
            extra = [k for k in new if k not in old]
            rec['arms'].append(dict(b=b, K=K, nold=len(old), nnew=len(new),
                                    extra=[[k[0], k[1], list(k[2]),
                                            list(k[3]), k[4]] for k in extra]))
            tag = ('SAME' if not extra else
                   ('OPENS' if not old else '+%d' % len(extra)))
            if extra and not old:
                gained += 1
            print('%4d/%d %-30s b%d K=%d  ENCS %2d  TRY %2d  %s%s'
                  % (i + 1, len(specs), s, b, K, len(old), len(new), tag,
                     '  ' + ', '.join('%s/q%s/t%s/f%s/o%d'
                                      % (k[0], k[1], _w(k[2]), _w(k[3]), k[4])
                                      for k in extra[:3]) if extra else ''))
        out.append(rec)
    print('\narms the three private alphabets OPEN from nothing: %d' % gained)
    if a.json:
        with open(a.json, 'w') as f:
            json.dump(out, f, indent=1, sort_keys=True)
    return 0


def _w(x):
    return ''.join(str(c) for c in x) or '-'


if __name__ == '__main__':
    sys.exit(main())
