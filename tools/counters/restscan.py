#!/usr/bin/env python3
"""UNTRUSTED: the TOLERANT rest scan -- anchors() has two gaps, not one.

WAVE26 section 8c: `anchors()` misses machines for two reasons -- the
`phase_mid` closure (fixed by skipcert.py's virtual anchors) and the
TAIL/PREFIX enumeration.  John's read of 0RB0LC_1LC1RB_1RD1LA_1LD1LB ("a
normal counter ... and 2 extra ones on the right") is a machine with NO skip
at all whose anchor family simply carries a tail the enumeration never
offered.

This scan reads the family off the machine's own rests instead: every
blank-head configuration over a long run is decoded against EVERY alphabet
with EVERY tail split (up to TAILMAX cells), and the (alphabet, state, tail,
far) key with the largest consecutive-value coverage wins.  The key is then
classified:

    plain    no gaps            -> the FLAT route boards it as-is
                                   (emit_lapcert.derive with the found key)
    skip-s   {2^k..2^k+s-1}     -> skipcert.derive_skip with the found key
    other    anything else      -> reported (the register x counter shape
                                   of section 8b, or a deeper skip)

With --emit it boards the plain and skip rows through those routes.

Usage
  restscan.py --list FILE [--emit] [--json OUT]
"""
import argparse
import collections
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, '..', '..'))
sys.path.insert(0, HERE)

import emit_lapcert as EL                                          # noqa: E402
from emit_interleave import parse, LAB, mach_id, DeriveError       # noqa: E402
from mirror_common import mirror_spec, mirrorize                   # noqa: E402
import lapcert as LC                                               # noqa: E402
import nestcert as NC                                              # noqa: E402
import skipcert as SC                                              # noqa: E402

TAILMAX = 6
MAXT = 200000


def rests(spec, maxT=MAXT):
    """Every blank-head configuration of the run, with first-arrival time."""
    tab = parse(spec)
    cfg = (0, (), 0, ())
    out = {}
    for t in range(maxT):
        q, l, h, r = cfg
        if h == 0 and l and len(l) <= 240:
            key = (q, tuple(l), LC.rstrip0(r))
            if key not in out:
                out[key] = t
        try:
            cfg = LC.wstep(tab, False, False, cfg)
        except LC.Halt:
            break
    return out


def best_key(spec):
    """The (enc, state, tail, far) with the largest consecutive coverage."""
    R = rests(spec)
    hits = collections.defaultdict(dict)
    for (q, l, far), t in R.items():
        for enc in EL.ENCS:
            d = EL.ENCDATA[enc]
            A, B, C = tuple(d['uD']), tuple(d['uS']), tuple(d['soD'])
            for k in range(min(TAILMAX, len(l) - 1) + 1):
                head, tl = (l[:len(l) - k], l[len(l) - k:]) if k else (l, ())
                v = NC.decode(head, A, B, C)
                if (v is not None and v <= 400
                        and v not in hits[(enc, q, tl, far)]):
                    hits[(enc, q, tl, far)][v] = t
    best = None
    for key, vs in hits.items():
        hi = max(vs)
        cover = len([v for v in vs if v >= 8])
        if cover < 150:
            continue
        # the run's own transient hides small values; boarding does not
        # care (p0 fences everything below the boot anchor), so the skip
        # set is read above the first floor that makes it regular
        rank, kind, s, missing = 2, 'other', None, []
        for f in (8, 16, 24, 32, 48, 64):
            miss = [v for v in range(f, hi + 1) if v not in vs]
            if not miss:
                rank, kind, s, missing = 0, 'plain', 0, []
                break
            sf = None
            for st in (1, 2):
                want = set()
                for k in range(1, 20):
                    want.update(2 ** k + i for i in range(st))
                if set(miss) == {w for w in want if f <= w <= hi - 2}:
                    sf = st
                    break
            if sf is not None:
                rank, kind, s, missing = 1, 'skip-%d' % sf, sf, miss[:16]
                break
            missing = miss[:16]
        score = (rank, -cover)
        if best is None or score < best[0]:
            best = (score, key, vs, kind, s, missing)
    return best


def classify(spec):
    out = None
    for mirrored in (False, True):
        dspec = mirror_spec(spec) if mirrored else spec
        b = best_key(dspec)
        if b is None:
            continue
        (score, (enc, q, tl, far), vs, kind, s, missing) = b
        r = dict(spec=spec, ok=True, kind=kind, s=s, enc=enc,
                 edge=LAB[q], tail=list(tl), far=list(far),
                 mirror=mirrored, cover=-score[1], missing=missing)
        if out is None or score < out[0]:
            out = (score, r)
    if out is None:
        return dict(spec=spec, ok=False, kind='no-rest-family')
    return out[1]


def board(spec, r, force=False):
    """Board through the flat or the skip route with the discovered key."""
    dspec = mirror_spec(spec) if r['mirror'] else spec
    edge, tail, far, enc = r['edge'], tuple(r['tail']), tuple(r['far']), \
        r['enc']
    if r['kind'] == 'plain':
        # the flat route; p0 from the boot probe over the measured family
        tab = parse(dspec)
        st0 = LAB.index(edge)
        from ovfshape import anchor_times
        at = anchor_times(dspec, st0, EL.ENC[enc], tail, far, 300, 4000000)
        if not at:
            return dict(spec=spec, ok=False, why='no boot anchor')
        p0 = min(at, key=lambda p: at[p])
        try:
            D = EL.derive(dspec, edge, list(tail), p0, enc, far)
        except (DeriveError, LC.Halt) as e:
            return dict(spec=spec, ok=False, why='flat: %s' % e)
        pref = (EL.NEST_PREFIX if D.get('nest')
                else EL.AVOID_PREFIX if D.get('avoid') else EL.PREFIX)
        path = os.path.join(EL.OUTDIR, '%s_%s.v' % (pref, mach_id(spec)))
        if os.path.exists(path) and not force:
            return dict(spec=spec, ok=True, file=path, skipped=True)
        try:
            src = EL.render(D)
            if r['mirror']:
                src = mirrorize(src, spec, dspec)
        except (DeriveError, RuntimeError) as e:
            return dict(spec=spec, ok=False, why='render: %s' % e)
        open(path, 'w').write(src)
        ok, log = EL.coqc(os.path.relpath(path, REPO))
        if not ok:
            os.remove(path)
            lg = [x for x in log.strip().splitlines() if x.strip()]
            return dict(spec=spec, ok=False,
                        why='coqc: ' + (lg[-1] if lg else '?'))
        return dict(spec=spec, ok=True, file=path, route='flat')
    if r['kind'] in ('skip-1', 'skip-2'):
        try:
            D = SC.derive_skip(dspec, edge, tail, enc, far)
        except (SC.SkipError, DeriveError, LC.Halt) as e:
            return dict(spec=spec, ok=False, why='skip: %s' % e)
        path = os.path.join(SC.OUTDIR, 'SKIP_%s.v' % mach_id(spec))
        if os.path.exists(path) and not force:
            return dict(spec=spec, ok=True, file=path, skipped=True)
        try:
            src = SC.render_skip(D)
            if r['mirror']:
                src = mirrorize(src, spec, dspec)
        except (SC.SkipError, DeriveError, RuntimeError) as e:
            return dict(spec=spec, ok=False, why='render: %s' % e)
        open(path, 'w').write(src)
        ok, log = EL.coqc(os.path.relpath(path, REPO))
        if not ok:
            os.remove(path)
            lg = [x for x in log.strip().splitlines() if x.strip()]
            return dict(spec=spec, ok=False,
                        why='coqc: ' + (lg[-1] if lg else '?'))
        return dict(spec=spec, ok=True, file=path, route='skip')
    return dict(spec=spec, ok=False, why=r['kind'])


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--list')
    ap.add_argument('--spec')
    ap.add_argument('--emit', action='store_true')
    ap.add_argument('--json')
    ap.add_argument('--force', action='store_true')
    a = ap.parse_args()
    specs = ([a.spec] if a.spec else
             [x.strip() for x in open(a.list) if x.strip()])
    cnt = collections.Counter()
    res = []
    for i, spec in enumerate(specs):
        r = classify(spec)
        line = r['kind']
        if r['ok'] and a.emit and r['kind'] in ('plain', 'skip-1', 'skip-2'):
            br = board(spec, r, a.force)
            r['board'] = br
            line += ' -> ' + ('BOARDED %s' % os.path.basename(
                br.get('file', '')) if br['ok'] else 'no: %s'
                % br['why'][:70])
        cnt[r['kind']] += 1
        print('%4d/%d %-40s %s%s' % (
            i + 1, len(specs), spec, line,
            ('  [%s@%s tail=%s far=%s mir=%s cov=%d]'
             % (r.get('enc'), r.get('edge'), r.get('tail'), r.get('far'),
                r.get('mirror'), r.get('cover', 0))) if r['ok'] else ''),
            flush=True)
        res.append(r)
    print()
    for k, v in cnt.most_common():
        print('%5d  %s' % (v, k))
    if a.json:
        json.dump(res, open(a.json, 'w'), indent=1)


if __name__ == '__main__':
    main()
