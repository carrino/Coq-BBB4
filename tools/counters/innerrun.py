#!/usr/bin/env python3
"""UNTRUSTED probe: what run does the INNER counter of a two-form overflow arm
actually make?

`nestcert.families` accepts a key only when its decoded values are exactly
`2^(K-1+o) .. 2^(K+o)-1`.  Wave-29 section 5d measured that on the exponential
arm they are not: the inner counter runs a PARTIAL octave and stops short of
the all-ones fill.  33 rows are filed `no inner family at pow2 j` and 6 more
reach the fill assertion and miss it, and neither number says WHAT the run is.

This probe answers that.  It rebuilds `tailcert._derive`'s overflow `mid` phase
and reports, for every (alphabet, state, tail, far, oct) key that decodes at
all, the CONTIGUOUS ASCENDING run it makes: its first value, its last value,
and how both sit against the octave `2^(K-1+o) .. 2^(K+o)-1` that `families`
demands.

Nothing here is a certificate; it is a measurement whose output the bounded
carrier's endpoint gets stated from.

Usage
  innerrun.py --list FILE [--json OUT]
  innerrun.py --spec SPEC [-v]
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
from emit_lapcert import ENCDATA, ENC                              # noqa: E402
from emit_interleave import parse                                  # noqa: E402
from mirror_common import mirror_spec                              # noqa: E402
from regcert import RegError, F, _chain, _phase                    # noqa: E402


def runs(mid, maxtail=NC.MAXTAIL, maxoct=NC.MAXOCT):
    """Every key in [mid] that decodes, with the contiguous ascending run it
    makes.  Same gather as `nestcert.families` with the `== want_run` test
    taken out, so a key that runs 132..191 is reported instead of dropped."""
    hits = {}
    for (q, l, r) in mid:
        for name in TC.TRY:
            d = ENCDATA[name]
            if d['obS'] != 0:
                continue
            A, B, C = tuple(d['uD']), tuple(d['uS']), tuple(d['soD'])
            for k in range(maxtail + 1):
                if k > len(l) - 1:
                    break
                head, tl = (l[:len(l) - k], l[len(l) - k:]) if k else (l, ())
                v = NC.decode(head, A, B, C)
                if v is not None:
                    hits.setdefault((name, q, tl, r), []).append(v)
    out = []
    for key, vs in hits.items():
        # the LONGEST +1 run in the order the phase visits them; a family the
        # carrier can express has to be consecutive, and the reader must not
        # be allowed to stitch two frames into one apparent run.
        best, cur = [vs[0]], [vs[0]]
        for a, b in zip(vs, vs[1:]):
            cur = cur + [b] if b == a + 1 else [b]
            if len(cur) > len(best):
                best = cur
        out.append(dict(key=list(key[:1]) + [key[1], list(key[2]),
                                            list(key[3])],
                        n=len(vs), run=len(best), lo=best[0], hi=best[-1]))
    out.sort(key=lambda h: -h['run'])
    return out


def probe(spec):
    """[tailcert._derive]'s overflow arms, reported instead of derived."""
    last = None
    for mir in (False, True):
        dspec = mirror_spec(spec) if mir else spec
        try:
            return _probe(spec, dspec, mir)
        except RegError as e:
            last = str(e)
    raise RegError(last or 'no family')


def _probe(spec, dspec, mirrored):
    tab = parse(dspec)
    enc, frames, ks = TC.two_form(dspec, None)
    d = ENCDATA[enc]
    uS, uD = tuple(d['uS']), tuple(d['uD'])
    soS, soD = tuple(d['soS']), tuple(d['soD'])
    st = {b: frames[b][0] for b in (0, 1)}
    tl = {b: tuple(frames[b][1]) for b in (0, 1)}
    fr = {b: tuple(frames[b][2]) for b in (0, 1)}

    arms = {}
    for b in (0, 1):
        nb = 1 - b
        B0 = (st[b], (uS, uS, 1, 0, soS + tl[b]), 0, F(fr[b]))
        B1 = (st[nb], ((), uD, 1, 2, soD + tl[nb]), 0, F(fr[nb]))
        ch, r = _chain(tab, True, True, B0, B1)
        if ch is not None and r[0] == B1 and r[2] > 0:
            arms[b] = dict(kind='flat')
            continue
        ok = [k for k in ks[:-1] if k % 2 == b]
        if not ok:
            arms[b] = dict(kind='none')
            continue
        K = max(ok)
        p = (1 << (K + 1)) - 1
        src = (st[b], tuple(ENC[enc](p)) + tl[b], 0, fr[b])
        nxt = (st[nb], tuple(ENC[enc](p + 1)) + tl[nb], 0, fr[nb])
        try:
            mid = _phase(tab, src, (nxt[0], nxt[1], LC.rstrip0(nxt[3])))
        except Exception as e:                                     # noqa: BLE001
            arms[b] = dict(kind='nophase', why=str(e))
            continue
        hits = runs(mid)
        arms[b] = dict(kind='nested', K=K, nmid=len(mid), hits=hits,
                       want=[[2 ** (K - 1 + o), 2 ** (K + o) - 1]
                             for o in range(NC.MAXOCT + 1)])
    return dict(spec=spec, dspec=dspec, mirror=mirrored, enc=enc, ks=ks,
                arms=arms)


def _fmt(h, K):
    """One key's run, against the octave `families` would demand of it."""
    lo, hi = h['lo'], h['hi']
    o = max(0, lo.bit_length() - K)
    return ('%-14s q%s t%-9s f%-9s run %4d  %5d..%-5d  vs %5d..%-5d %s'
            % (h['key'][0], h['key'][1], _w(h['key'][2]), _w(h['key'][3]),
               h['run'], lo, hi, 2 ** (K - 1 + o), 2 ** (K + o) - 1,
               _why(lo, hi, K, o)))


def _w(x):
    return ''.join(str(c) for c in x) or '-'


def _why(lo, hi, K, o):
    a, b = 2 ** (K - 1 + o), 2 ** (K + o) - 1
    if lo == a and hi == b:
        return 'FULL'
    return '%s%s' % ('lo+%d ' % (lo - a) if lo != a else '',
                     'hi-%d' % (b - hi) if hi != b else '')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--list')
    ap.add_argument('--spec')
    ap.add_argument('--json')
    ap.add_argument('-v', action='store_true')
    ap.add_argument('--top', type=int, default=6)
    a = ap.parse_args()
    specs = ([a.spec] if a.spec else
             [x.split()[0] for x in open(a.list) if x.strip()
              and not x.startswith('#')])
    out = []
    for i, s in enumerate(specs):
        try:
            D = probe(s)
        except Exception as e:                                      # noqa: BLE001
            print('%4d/%d %-30s NO: %s' % (i + 1, len(specs), s, e))
            out.append(dict(spec=s, err=str(e)))
            continue
        out.append(D)
        for b in (0, 1):
            A = D['arms'][b]
            if A['kind'] != 'nested':
                print('%4d/%d %-30s b%d %s' % (i + 1, len(specs), s, b,
                                               A['kind']))
                continue
            print('%4d/%d %-30s b%d K=%d %s %d mid, %d keys'
                  % (i + 1, len(specs), s, b, A['K'], D['enc'], A['nmid'],
                     len(A['hits'])))
            for h in A['hits'][:a.top]:
                print('        ' + _fmt(h, A['K']))
    if a.json:
        with open(a.json, 'w') as f:
            json.dump(out, f, indent=1, sort_keys=True)
    return 0


if __name__ == '__main__':
    sys.exit(main())
