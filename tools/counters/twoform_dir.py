#!/usr/bin/env python3
"""UNTRUSTED measurement: which WAY does a two-form family count?

`tailcert.two_form` accepts a PAIR of anchor keys whose value sets union to a
gap-free range and which split by octave parity.  That is a condition on the
SET of values, and it says nothing about the ORDER the machine visits them in.
Every downstream derivation assumes ASCENDING (`emit_lapcert`'s whole model is
`E p -> E (Pos.succ p)`), so a family the machine walks DOWNWARD has no
interior lap at any framing -- and no peel, however deep, can produce one.

This walks the real machine, keeps every rest that matches either key, and
reports per frame:

  * `dir`  the sign of the median step from one anchor to the next in the SAME
           frame: +1 ascending, -1 descending, 0 neither;
  * `lap`  whether `E p -> E (p+1)` is actually realised between consecutive
           rests, which is what an interior chain would have to certify;
  * `dup`  whether the two keys are reading the SAME tape word at two
           different tail splits -- the reader pairing a value with its own
           half, which makes the "gap-free union" an artefact.

Usage
  twoform_dir.py --list FILE [--limit N] [--out JSON]
  twoform_dir.py --spec SPEC
"""
import argparse
import collections
import json
import os
import statistics
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import lapcert as LC                                               # noqa: E402
import tailcert as TC                                              # noqa: E402
from emit_lapcert import ENC                                       # noqa: E402
from emit_interleave import parse, LAB                             # noqa: E402
from mirror_common import mirror_spec                              # noqa: E402
from regcert import RegError                                       # noqa: E402

SYM = {0: '0', 1: '1'}
VHI = 256


def fs(t):
    return ''.join(SYM.get(x, '?') for x in t) or '.'


def walk(tab, enc, frames, maxtail=3, maxT=400000, vlo=8, vhi=VHI):
    """Every rest matching either key, in VISIT ORDER."""
    lut = {tuple(ENC[enc](v)): v for v in range(1, vhi + 1)}
    keys = {}
    for b in frames:
        keys[(frames[b][0], tuple(frames[b][1]), tuple(frames[b][2]))] = b
    cfg, out = (0, (), 0, ()), []
    for t in range(1, maxT):
        try:
            cfg = LC.wstep(tab, False, False, cfg)
        except LC.Halt:
            break
        q, l, h, r = cfg
        if h:
            continue
        rr = LC.rstrip0(r)
        for k in range(maxtail + 1):
            if k > len(l) - 1:
                break
            w = tuple(l[:len(l) - k]) if k else tuple(l)
            tl = tuple(l[len(l) - k:]) if k else ()
            v = lut.get(w)
            if v is None or not (vlo <= v < vhi):
                continue
            b = keys.get((q, tl, rr))
            if b is not None:
                out.append((t, b, v))
    return out


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
        seq = walk(tab, enc, frames)
        out = dict(spec=spec, mirror=mir, enc=enc, ks=ks, n=len(seq),
                   frames={b: '%s@tail=%s far=%s'
                              % (LAB[frames[b][0]], fs(frames[b][1]),
                                 fs(frames[b][2])) for b in frames},
                   per={})
        # the two keys reading ONE tape at two tail splits: same step index
        bysteps = collections.defaultdict(set)
        for (t, b, v) in seq:
            bysteps[t].add((b, v))
        dup = sum(1 for t in bysteps if len({b for b, _ in bysteps[t]}) > 1)
        out['dup'] = dup
        for b in frames:
            vs = [(t, v) for (t, bb, v) in seq if bb == b]
            d = [vs[i + 1][1] - vs[i][1] for i in range(len(vs) - 1)]
            lap = sum(1 for x in d if x == 1)
            out['per'][b] = dict(
                anchors=len(vs), steps_up=sum(1 for x in d if x > 0),
                steps_dn=sum(1 for x in d if x < 0), lap_p_to_p1=lap,
                median=(statistics.median(d) if d else None))
        ups = sum(out['per'][b]['steps_up'] for b in frames)
        dns = sum(out['per'][b]['steps_dn'] for b in frames)
        laps = sum(out['per'][b]['lap_p_to_p1'] for b in frames)
        out['verdict'] = (
            'no anchors' if not seq else
            'ASCENDING, p->p+1 realised %d times' % laps if laps else
            'DESCENDING (%d down / %d up), NO p->p+1 anywhere' % (dns, ups)
            if dns > ups else
            'neither (%d down / %d up), no p->p+1' % (dns, ups))
        return out
    return dict(spec=spec, verdict=last or 'no family')


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
        res.append(o)
        key = o['verdict'].split(',')[0].split(' (')[0]
        cnt[key] += 1
        print('%3d/%d %-30s %-16s dup=%-4s %s' % (
            i + 1, len(specs), spec, o.get('enc', '-'), o.get('dup', '-'),
            o['verdict']), flush=True)
    print()
    for k, v in cnt.most_common():
        print('%5d  %s' % (v, k))
    if a.out:
        json.dump(res, open(a.out, 'w'), indent=1)


if __name__ == '__main__':
    main()
