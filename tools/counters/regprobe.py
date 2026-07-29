#!/usr/bin/env python3
"""UNTRUSTED probe: the register bucket's lap laws, fitted PER OCTAVE CLASS.

`regscan.lap_law` fits the two laps a virtual anchor carries (`vin`, the
ordinary overflow into it; `vout`, the register step out of it) with ONE
affine law over all `k`.  On a family whose FRAME has period P that is the
wrong fit: the frame at octave `k` is `forms[(k - k0) mod P]`, so the lap
into and out of the virtual anchor at `2^k` depends on `k mod P` too, and a
single fit over consecutive `k` mixes P different laws.  Measured on the
`period-2+virt` exemplar `0RB0LC_1LC1RB_1LD1LA_1RD0RC`:

    vin   k = 4,5,6,7 -> 19, 25, 27, 33     one fit: none
                        even k: 4k+3, odd k: 4k+5   per-parity: BOTH affine

so three of the four branches are ordinary chains and only ONE -- the
register step out of the virtual anchor on one parity -- is Theta(2^k).
This probe reports the per-class fit, which is what the board has to state.

Usage
  regprobe.py --spec SPEC [--kind KIND] [--pmax N]
  regprobe.py --json tools/counters/reg113.json [--kind KIND]
"""
import argparse
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, '..', '..'))
sys.path.insert(0, HERE)

import regscan as RS                                                # noqa: E402
import emit_lapcert as EL                                           # noqa: E402
from emit_interleave import carry, LAB                              # noqa: E402
from mirror_common import mirror_spec                               # noqa: E402


def affine(pts):
    """cost = a*j + b on every measured j (>= 2 of them), or None."""
    js = sorted(pts)
    if len(js) < 2:
        return None
    dj, num = js[1] - js[0], pts[js[1]] - pts[js[0]]
    if dj == 0 or num % dj:
        return None
    a = num // dj
    b = pts[js[0]] - a * js[0]
    return (a, b) if all(pts[j] == a * j + b for j in js) else None


def classify(walk, law, floor):
    """Bucket every chased lap by (branch, octave class) and fit each."""
    P, k0 = law.get('period', 1), law.get('k0', 0)
    virt = law.get('virt')
    cls = {}
    for p, _, _, cost in walk[1:]:
        src = p - 1
        if src < floor:
            continue
        k = RS.octave(src)
        r = (k - k0) % P
        if virt and src == (1 << k):
            key = ('vout', r)
            idx = k
        elif virt and p == (1 << RS.octave(p)):
            key = ('vin', (RS.octave(p) - 1 - k0) % P)
            idx = RS.octave(src)
        else:
            j, ov = carry(src)
            key = (('ovf' if ov else 'int'), r)
            idx = j
        cls.setdefault(key, {})[idx] = cost
    return {k: (affine(v), sorted(v.items())[:6]) for k, v in cls.items()}


def probe(spec, enc, tail, mirrored, pmax=140):
    dspec = mirror_spec(spec) if mirrored else spec
    sd = RS.seeds(dspec, enc, tail)
    if not sd:
        return None
    v0, cfg0 = sd[0]
    walk = RS.chase(dspec, enc, tail, v0, cfg0, pmax)
    law = RS.frame_law(walk)
    law.update(spec=spec, enc=enc, tail=list(tail), mirror=mirrored,
               n=len(walk), v0=v0)
    if 'forms' not in law:
        return law, walk, {}
    return law, walk, classify(walk, law, max(8, v0))


def fmt(law, cls):
    out = ['%-40s %-14s %s@tail=%s mir=%s n=%d' % (
        law['spec'], law['kind'], law['enc'], law['tail'], law['mirror'],
        law['n'])]
    if law.get('forms'):
        out.append('  frames: ' + ' | '.join(
            '%s@%s' % (LAB[q], ''.join(map(str, f)) or '-')
            for q, f in law['forms']) + '   k0=%d' % law.get('k0', 0))
    for key in sorted(cls):
        a, raw = cls[key]
        out.append('  %-10s r=%d  %-14s %s' % (
            key[0], key[1], ('%d*j+%d' % a) if a else 'NOT AFFINE', raw))
    return '\n'.join(out)


def walk_cfgs(spec, enc, tail, mirrored, pmax):
    """The chase, keeping the CONFIGURATION at every anchor."""
    dspec = mirror_spec(spec) if mirrored else spec
    sd = RS.seeds(dspec, enc, tuple(tail))
    if not sd:
        return None, None, None
    v0, cfg0 = sd[0]
    tab = RS.EL.parse(dspec) if hasattr(RS.EL, 'parse') else None
    from emit_interleave import parse
    tab = parse(dspec)
    encf, tl = EL.ENC[enc], tuple(tail)
    out = {v0: cfg0}
    cfg = cfg0
    for p in range(v0, pmax):
        want = tuple(encf(p + 1)) + tl
        for _ in range(RS.LAPCAP):
            cfg = RS.LC.wstep(tab, False, False, cfg)
            if (cfg[2] == 0 and tuple(cfg[1]) == want
                    and len(RS.LC.rstrip0(cfg[3])) <= RS.FARMAX):
                out[p + 1] = cfg
                break
        else:
            break
    return tab, out, dspec


def vout_phase(tab, cfg0, want):
    """Every blank-head configuration strictly between the virtual anchor and
    the next one -- the register step's own phase, in [nestcert.phase_mid]'s
    format (state, left stripped, far stripped)."""
    mid, cfg = [], cfg0
    for _ in range(4000000):
        cfg = RS.LC.wstep(tab, False, False, cfg)
        q, l, h, r = cfg
        if (h == 0 and tuple(l) == want[1] and q == want[0]
                and RS.LC.rstrip0(r) == want[2]):
            return mid
        if h == 0:
            mid.append((q, RS.LC.rstrip0(l), RS.LC.rstrip0(r)))
    raise RuntimeError('vout phase did not close')


def nested_probe(spec, enc, tail, mirrored, ks, pmax=140):
    """Is the register step an inner COUNT?  Run [nestcert.families] over the
    lap out of the virtual anchor at each requested octave."""
    import nestcert as NC
    tab, cfgs, _ = walk_cfgs(spec, enc, tail, mirrored, pmax)
    if not cfgs:
        return []
    encf, tl = EL.ENC[enc], tuple(tail)
    out = []
    for k in ks:
        p = 1 << k
        if p not in cfgs or (p + 1) not in cfgs:
            continue
        nxt = cfgs[p + 1]
        want = (nxt[0], tuple(encf(p + 1)) + tl, RS.LC.rstrip0(nxt[3]))
        mid = vout_phase(tab, cfgs[p], want)
        keys = NC.families(mid, EL.ENCDATA, EL.ENCS, K=k)
        out.append((k, len(mid), keys[:6], cfgs[p], nxt))
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--spec')
    ap.add_argument('--enc')
    ap.add_argument('--tail')
    ap.add_argument('--mirror', action='store_true')
    ap.add_argument('--json')
    ap.add_argument('--kind')
    ap.add_argument('--pmax', type=int, default=140)
    ap.add_argument('--nested', help='comma-separated octaves to probe')
    ap.add_argument('--grow', action='store_true',
                    help='fit the growing far, lowest octave held out')
    ap.add_argument('--wide', action='store_true',
                    help='re-chase with TAILMAX=4 and FARMAX=40')
    ap.add_argument('--tailmax', type=int, default=4)
    a = ap.parse_args()
    if a.wide:
        # The `short` bucket is the reader, not the machines: [_tails]
        # enumerates at most TAILMAX = 2 cells and the exemplar's tail is
        # THREE (John's "fixed 01 two cells right of the frame").  Widen it
        # and the chase walks 130+ anchors.  Left out of regscan.py's own
        # defaults so that reg113.json still reproduces.
        RS.TAILMAX, RS.FARMAX = a.tailmax, 40
        rows = [r for r in json.load(open(a.json))
                if not a.kind or r['kind'] == a.kind]
        import collections as _c
        cnt = _c.Counter()
        for i, r in enumerate(rows):
            try:
                g = RS.scan(r['spec'], False, a.pmax)
            except Exception as e:                             # noqa: BLE001
                g = dict(kind='ERR:%s' % e)
            cnt[g.get('kind', '?')] += 1
            print('%4d/%d %-40s %-12s %s tail=%s mir=%s n=%s' % (
                i + 1, len(rows), r['spec'], g.get('kind'), g.get('enc'),
                g.get('tail'), g.get('mirror'), g.get('n')), flush=True)
        print()
        for k, v in cnt.most_common():
            print('%5d  %s' % (v, k))
        return
    if a.grow:
        rows = [r for r in json.load(open(a.json))
                if not a.kind or r['kind'] == a.kind]
        import collections as _c
        cnt = _c.Counter()
        for spec, got, byoct in grow_scan(rows, a.pmax):
            if isinstance(got, dict):
                key = 'grow-%s/%s drop=%d' % (''.join(map(str, got['unit'])),
                                              got['mode'], got['drop'])
            else:
                key = str(got)
            cnt[key] += 1
            print('%-40s %s' % (spec, key))
        print()
        for k, v in cnt.most_common():
            print('%5d  %s' % (v, k))
        return
    if a.nested:
        ks = [int(x) for x in a.nested.split(',')]
        rows = ([r for r in json.load(open(a.json))
                 if not a.kind or r['kind'] == a.kind] if a.json else
                [dict(spec=a.spec, enc=a.enc or 'Alph_10_11_11',
                      tail=json.loads(a.tail) if a.tail else [],
                      mirror=a.mirror)])
        for r in rows:
            print(r['spec'], r['enc'], r['tail'], 'mir=%s' % r['mirror'])
            for (k, n, keys, c0, c1) in nested_probe(
                    r['spec'], r['enc'], tuple(r['tail']), r['mirror'], ks,
                    a.pmax):
                print('  k=%d  mid=%d  virt=%s' % (k, n, (LAB[c0[0]], c0[1],
                                                          c0[3])))
                for key in keys:
                    print('      key %s' % (key,))
            print()
        return
    rows = []
    if a.json:
        rows = [r for r in json.load(open(a.json))
                if not a.kind or r['kind'] == a.kind]
    else:
        rows = [dict(spec=a.spec, enc=a.enc or 'Alph_10_11_11',
                     tail=json.loads(a.tail) if a.tail else [],
                     mirror=a.mirror)]
    for r in rows:
        got = probe(r['spec'], r['enc'], tuple(r['tail']), r['mirror'],
                    a.pmax)
        if got is None:
            print('%-40s  no seed' % r['spec'])
            continue
        law, _, cls = got
        print(fmt(law, cls))
        print()




def grow_law(byoct, ks, drop=1):
    """Fit `far = pre ++ rep u m ++ post` over the octaves, holding out the
    lowest [drop] of them.

    `regscan.frame_law` fits the growth from ks[0] and requires the unit to
    be APPENDED, so a family whose lowest octave is exceptional (a different
    state, or a shorter far) or whose unit is PREPENDED falls through to
    `drift`.  Measured over the 113: that is the whole of the `drift`
    bucket."""
    ks = [k for k in ks if k >= ks[0] + drop]
    if len(ks) < 3:
        return None
    q0 = byoct[ks[0]][0]
    if any(byoct[k][0] != q0 for k in ks):
        return None
    f0, f1 = tuple(byoct[ks[0]][1]), tuple(byoct[ks[1]][1])
    d = len(f1) - len(f0)
    if d <= 0:
        return None
    for mode in ('append', 'prepend'):
        if mode == 'append':
            u = f1[len(f0):]
            ok = f1[:len(f0)] == f0
            fam = lambda i, u=u: f0 + u * i                     # noqa: E731
        else:
            u = f1[:d]
            ok = f1[d:] == f0
            fam = lambda i, u=u: u * i + f0                     # noqa: E731
        if not ok or not u:
            continue
        if all(tuple(byoct[k][1]) == fam(k - ks[0]) for k in ks):
            return dict(unit=list(u), mode=mode, base=list(f0), st=q0,
                        k0=ks[0], octs=len(ks))
    return None


def grow_scan(rows, pmax=140):
    """The `drift` question, answered: re-walk each row and fit [grow_law]
    with the lowest octave held out."""
    import regcert as RC
    out = []
    # the chase caps the far side at [regscan.FARMAX] = 8 cells, which a
    # GROWING far outruns after three octaves -- so the reader, not the
    # machine, is what stopped the walk.  Widen it for this fit.
    save, RS.FARMAX = RS.FARMAX, 40
    for r in rows:
        try:
            ds = (mirror_spec(r['spec']) if r['mirror'] else r['spec'])
            _, cfgs, v0 = RC.walk(ds, r['enc'], tuple(r['tail']), pmax)
            byoct, atpow, virt, ks = RC.read_frames(cfgs, max(8, v0))
        except Exception as e:                                 # noqa: BLE001
            out.append((r['spec'], 'walk: %s' % e, None))
            continue
        got = None
        for drop in (0, 1, 2):
            got = grow_law(byoct, ks, drop)
            if got:
                got['drop'] = drop
                break
        out.append((r['spec'], got, {k: (LAB[q], f)
                                     for k, (q, f) in byoct.items()}))
    RS.FARMAX = save
    return out

if __name__ == '__main__':
    main()
