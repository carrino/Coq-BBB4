#!/usr/bin/env python3
"""UNTRUSTED measurement: does the alphabet's DIGIT WIDTH match the machine's
per-octave growth?

John's read of `1RB1RD_1LC1RA_0RB0LC_1LA0RD` -- "a counter with 0s to the left of
each bit with a wall on the right, msb on the right, when the msb overflows the
wall moves over 4" -- is a statement about CELLS.  The wall (the top of the word)
moves 4 cells per overflow.  `Alph_00_01_0` spells 2 cells per digit.  A counter
whose word grows 4 cells per octave under a 2-cell alphabet is not being read as
itself: the matched values are a SUBSEQUENCE, one reader-digit per two machine
digits, and the register step then tries to move the mark one digit where the
machine moves it two.  That is what `register step does not close` means.

Per row: the length of the matched word at the first pass through each octave,
its increment per octave, and the alphabet's digit width.  A row where
`growth != digit width` needs a WIDER alphabet, not a different carrier.

Usage
  digitwidth.py --list FILE [--out JSON]
  digitwidth.py --spec SPEC
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

SYM = {0: '0', 1: '1'}


def fs(t):
    return ''.join(SYM.get(x, '?') for x in t) or '.'


def octave(v):
    k = 0
    while (1 << (k + 1)) <= v:
        k += 1
    return k


def probe(spec, maxT=400000, vhi=4000):
    for mir in (False, True):
        ds = mirror_spec(spec) if mir else spec
        try:
            enc, frames, ks = TC.two_form(ds)
        except Exception:                                      # noqa: BLE001
            continue
        tab = parse(ds)
        d = ENCDATA[enc]
        dw = len(d['uS'])                     # the alphabet's digit width
        lut = {tuple(ENC[enc](v)): v for v in range(1, vhi)}
        keys = {(frames[b][0], tuple(frames[b][1]), tuple(frames[b][2])): b
                for b in frames}
        cfg, first = (0, (), 0, ()), {}
        for t in range(1, maxT):
            try:
                cfg = LC.wstep(tab, False, False, cfg)
            except LC.Halt:
                break
            q, l, h, r = cfg
            if h:
                continue
            rr = LC.rstrip0(r)
            for k in range(7):
                if k > len(l) - 1:
                    break
                w = tuple(l[:len(l) - k]) if k else tuple(l)
                tl = tuple(l[len(l) - k:]) if k else ()
                v = lut.get(w)
                if v is None or v < 4:
                    continue
                if (q, tl, rr) in keys and v not in first:
                    first[v] = (t, len(w))
        # word length at the LOWEST value of each octave the family covers
        per = {}
        for v, (t, n) in first.items():
            k = octave(v)
            if k not in per or v < per[k][0]:
                per[k] = (v, n)
        ok = sorted(per)
        grow = [per[ok[i + 1]][1] - per[ok[i]][1] for i in range(len(ok) - 1)]
        g = collections.Counter(grow).most_common(1)
        return dict(spec=spec, mirror=mir, enc=enc, digit_width=dw,
                    octaves=ok, lengths=[per[k][1] for k in ok],
                    growth=grow, mode=(g[0][0] if g else None),
                    verdict=('no octaves' if len(ok) < 3 else
                             'MATCHES digit width %d' % dw
                             if g and g[0][0] == dw else
                             'MISMATCH: grows %s cells/octave, digit is %d'
                             % (g[0][0], dw) if g else 'irregular'))
    return dict(spec=spec, verdict='no family')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--list')
    ap.add_argument('--spec')
    ap.add_argument('--out')
    a = ap.parse_args()
    specs = ([a.spec] if a.spec else
             [x.strip() for x in open(a.list) if x.strip()])
    res, cnt = [], collections.Counter()
    for i, spec in enumerate(specs):
        try:
            o = probe(spec)
        except Exception as e:                                 # noqa: BLE001
            o = dict(spec=spec, verdict='ERR %s: %s' % (type(e).__name__, e))
        res.append(o)
        cnt[o['verdict'].split(':')[0]] += 1
        print('%3d/%d %-30s %-16s dw=%-3s growth=%-12s %s' % (
            i + 1, len(specs), spec, o.get('enc', '-'),
            o.get('digit_width', '-'), o.get('growth', '-'),
            o['verdict']), flush=True)
    print()
    for k, v in cnt.most_common():
        print('%5d  %s' % (v, k))
    if a.out:
        json.dump(res, open(a.out, 'w'), indent=1)


if __name__ == '__main__':
    main()
