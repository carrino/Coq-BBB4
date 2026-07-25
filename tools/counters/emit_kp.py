#!/usr/bin/env python3
"""UNTRUSTED emitter for PLAIN binary counters ([KpCounter.Kp]).

Clones theories/Machines/Counters/ILK_1RB0LD_0LC1LA_0RC1LA_1RC0LD.v.

Kp is the counter with NOTHING between the bits -- the tape word IS the base-2
expansion, LSB nearest the head.  It is the largest family in the residue
(`tools/counter_encodings.tsv` calls it KCOPY1, 389 machines) and it is by far
the richest seam measured so far: 34 of 60 sampled KCOPY1 machines are affine
on BOTH lap branches, against ~19% for the Ip family.

Lap shape (all one-cell units, and the arithmetic that pins the step counts):

    interior, j = 0        P1 . STP0                        = nP1 + nSTP0
    interior, j = S j'     P1 . RIP^j' . STP . RET^(S j')   = nP1+nRIP*j'+nSTP+nRET*(j'+1)
    overflow, j = S j'     P1 . RIP^j' . STPO . RET^(S j')

so with the measured interior fit n = a + b*j:

    nRIP + nRET = b                  (slope)
    nP1 + nSTP  + nRET = a + b       (intercept)
    nP1 + nSTP0        = a           (the j = 0 branch)

which leaves a tiny search.  The j = 0 / j >= 1 split is forced, not a choice:
the prologue consumes the cell nearest the head and that cell IS the low bit,
so with no carry run the prologue lands on S0 and the stop fires immediately.

Everything here is UNTRUSTED: a wrong constant cannot mis-prove anything, it
fails to typecheck.  The kernel re-checks every emitted board.

Usage
  emit_kp.py --list FILE [--emit] [--json OUT]
  emit_kp.py SPEC... [--emit]
"""
import argparse
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, '..', '..'))
sys.path.insert(0, HERE)

from executor import Exec, Wall                                    # noqa: E402
from emit_qh import Raw, strip0, LAB, ST, SYM, carry, mach_id, coq_table, DeriveError  # noqa: E402
from emit_ip import conc, cycl, cycr, mirror_spec, coqc            # noqa: E402

OUTDIR = os.path.join(REPO, 'theories', 'Machines', 'Counters')
MAXN = 12


# ------------------------------------------------------------ the encoding ---
def Kp(m):
    """Nearest-first: plain base-2, LSB first, MSB deepest."""
    out = []
    while m:
        out.append(m & 1)
        m >>= 1
    return out


def m_int(j):
    return (1 << (j + 1)) + (1 << j) - 1 if j else 2


# ------------------------------------------------------------ the anchor -----
def anchor_candidates(spec, T=120000, minrun=14):
    """Plain-counter anchors read off the real run, ranked by run length.

    Sweeps the orientation axes that the wave-8/9 recognizers had collapsed:
    which side the counter sits on, which end holds the MSB, and a short
    wall/suffix at either end.  (Inversion is NOT swept -- of 34 measured
    both-affine KCOPY1 machines, zero are inverted.)
    """
    tab = Raw(spec).tab
    raw = Raw(spec)
    cfg = (0, [], 0, [])
    first = {}
    for t in range(T):
        q, l, h, r = cfg
        for side in ('L', 'R'):
            near, far = (strip0(l), strip0(r)) if side == 'L' else (strip0(r), strip0(l))
            if len(far) > 3 or not near:
                continue
            word = list(reversed(near)) if side == 'L' else list(near)
            for nw in range(0, 3):
                for ns in range(0, 3):
                    for msbl in (True, False):
                        body = word[nw:len(word) - ns] if ns else word[nw:]
                        if not body:
                            continue
                        bits = list(body) if msbl else list(body)[::-1]
                        if bits[0] != 1:
                            continue
                        v = 0
                        for b in bits:
                            v = v * 2 + b
                        if v > 1:
                            first.setdefault(
                                (LAB[q], h, side, nw, ns, msbl, tuple(far)),
                                {}).setdefault(v, t)
        cfg = raw.step(cfg)
        if cfg is None:
            break
    out = []
    for key, fv in first.items():
        vs = sorted(fv)
        run, br, st = 1, 0, None
        for i in range(1, len(vs)):
            if vs[i] == vs[i - 1] + 1 and fv[vs[i]] > fv[vs[i - 1]]:
                run += 1
            else:
                if run > br:
                    br, st = run, vs[i - run]
                run = 1
        if run > br:
            br, st = run, vs[len(vs) - run]
        if br >= minrun:
            out.append((br, key, st))
    out.sort(key=lambda x: -x[0])
    if not out:
        raise DeriveError('no plain-counter anchor family in the run')
    return out


def anchor_cfg(E, head, side, nw, ns, msbl, far, p):
    """Rebuild the anchor configuration for value p."""
    bits = Kp(p)                       # LSB first
    body = bits[::-1] if msbl else bits    # tape order: MSB first if msbl
    # `word` is in TAPE order including wall/suffix; wall/suffix are read off
    # the run, so we require them empty here and carry the wall on the far side.
    if nw or ns:
        return None
    near = list(reversed(body)) if side == 'L' else list(body)
    return (E, near, head, list(far)) if side == 'L' else (E, list(far), head, near)


def lap_len(spec, E, head, side, far, msbl, p, maxsteps=200000):
    raw = Raw(spec)
    a = anchor_cfg(E, head, side, 0, 0, msbl, far, p)
    b = anchor_cfg(E, head, side, 0, 0, msbl, far, p + 1)
    if a is None or b is None:
        return None
    cfg = a
    for n in range(1, maxsteps):
        cfg = raw.step(cfg)
        if cfg is None:
            return None
        if cfg == b:
            return n
    return None


def affine(pts):
    js = sorted(pts)
    if len(js) < 2 or any(pts[j] is None for j in js):
        return None
    d = js[1] - js[0]
    if (pts[js[1]] - pts[js[0]]) % d:
        return None
    b = (pts[js[1]] - pts[js[0]]) // d
    a = pts[js[0]] - b * js[0]
    if b <= 0 or a <= 0:
        return None
    return (a, b) if all(pts[j] == a + b * j for j in js) else None


def profile(spec, E, head, side, far, msbl):
    inter = {j: lap_len(spec, E, head, side, far, msbl, m_int(j)) for j in range(4)}
    over = {j: lap_len(spec, E, head, side, far, msbl, (1 << j) - 1) for j in range(2, 5)}
    ai, ao = affine(inter), affine(over)
    return None if (ai is None or ao is None) else (ai, ao)


# ------------------------------------------------------------- the skeleton --
def replay_int0(ex, cfg0, s):
    """j = 0: P1 . STP0."""
    U = {}
    cfg, U['P1'] = conc(ex, cfg0, True, True, s['nP1'], 1, 1)
    cfg, U['STP0'] = conc(ex, cfg, True, True, s['nSTP0'], 0, None)
    return cfg, U


def replay_int(ex, cfg0, jp, s):
    """j = S jp: P1 . RIP^jp . STP . RET^(jp+1)."""
    U = {}
    cfg, U['P1'] = conc(ex, cfg0, True, True, s['nP1'], 1, 1)
    cfg, U['RIP'] = cycl(ex, cfg, 1, s['nRIP'], jp)
    cfg, U['STP'] = conc(ex, cfg, True, True, s['nSTP'], 1, 0)
    cfg, U['RET'] = cycr(ex, cfg, 1, s['nRET'], jp + 1)
    return cfg, U


def replay_ov(ex, cfg0, jp, s):
    """overflow: P1 . RIP^jp . STPO . RET^(jp+1), STPO left-open."""
    U = {}
    cfg, U['P1o'] = conc(ex, cfg0, True, True, s['nP1'], 1, 1)
    cfg, _ = cycl(ex, cfg, 1, s['nRIP'], jp)
    cfg, U['STPO'] = conc(ex, cfg, False, True, s['nSTPO'], None, 0)
    cfg, U['RET2'] = cycr(ex, cfg, 1, s['nRET'], jp + 1)
    return cfg, U


def derive(spec, E, head, side, far, msbl, ai, ao):
    a, b = ai
    ao0, _ = ao
    ex = Exec(spec)
    JI, KO = 3, 4
    c_i = anchor_cfg(E, head, side, 0, 0, msbl, far, m_int(JI))
    t_i = anchor_cfg(E, head, side, 0, 0, msbl, far, m_int(JI) + 1)
    c_0 = anchor_cfg(E, head, side, 0, 0, msbl, far, m_int(0))
    t_0 = anchor_cfg(E, head, side, 0, 0, msbl, far, m_int(0) + 1)
    c_o = anchor_cfg(E, head, side, 0, 0, msbl, far, (1 << KO) - 1)
    t_o = anchor_cfg(E, head, side, 0, 0, msbl, far, 1 << KO)
    for nP1 in range(1, MAXN):
        for nRIP in range(1, MAXN):
            nRET = b - nRIP
            if nRET < 1:
                continue
            nSTP = a + b - nP1 - nRET
            nSTP0 = a - nP1
            if nSTP < 1 or nSTP0 < 1:
                continue
            s = dict(nP1=nP1, nRIP=nRIP, nSTP=nSTP, nRET=nRET, nSTP0=nSTP0)
            try:
                if replay_int0(ex, c_0, s)[0] != t_0:
                    continue
                if replay_int(ex, c_i, JI - 1, s)[0] != t_i:
                    continue
            except (Wall, KeyError, IndexError):
                continue
            # ao(j) = nP1 + nRIP*(j-1) + nSTPO + nRET*j + 0
            for nSTPO in range(1, MAXN + 4):
                if nP1 - nRIP + nSTPO != ao0:
                    continue
                s2 = dict(s, nSTPO=nSTPO)
                try:
                    if replay_ov(ex, c_o, KO - 1, s2)[0] != t_o:
                        continue
                except (Wall, KeyError, IndexError):
                    continue
                _, U0 = replay_int0(ex, c_0, s2)
                _, U = replay_int(ex, c_i, JI - 1, s2)
                _, UO = replay_ov(ex, c_o, KO - 1, s2)
                U.update(U0)
                U.update(UO)
                return s2, U
    raise DeriveError('no plain skeleton fits both lap branches')


def validate(spec, E, head, side, far, msbl, s, hi=90):
    """Differential check of the symbolic lap against the raw lap, every p."""
    ex = Exec(spec)
    n = 0
    for m in range(2, hi):
        j, ov = carry(m)
        raw = lap_len(spec, E, head, side, far, msbl, m)
        if raw is None:
            raise DeriveError('raw lap does not close at m=%d' % m)
        c0 = anchor_cfg(E, head, side, 0, 0, msbl, far, m)
        tgt = anchor_cfg(E, head, side, 0, 0, msbl, far, m + 1)
        if ov:
            cfg, _ = replay_ov(ex, c0, j - 1, s)
            got = s['nP1'] + s['nRIP'] * (j - 1) + s['nSTPO'] + s['nRET'] * j
        elif j == 0:
            cfg, _ = replay_int0(ex, c0, s)
            got = s['nP1'] + s['nSTP0']
        else:
            cfg, _ = replay_int(ex, c0, j - 1, s)
            got = s['nP1'] + s['nRIP'] * (j - 1) + s['nSTP'] + s['nRET'] * j
        if cfg != tgt:
            raise DeriveError('m=%d: symbolic lap misses the next anchor' % m)
        if got != raw:
            raise DeriveError('m=%d: symbolic %d != raw %d' % (m, got, raw))
        n += 1
    return n


def boot_probe(spec, E, head, side, far, msbl, p0, maxT=40000):
    raw = Raw(spec)
    tgt = anchor_cfg(E, head, side, 0, 0, msbl, far, p0)
    tq, tl, th, tr = tgt
    key = (tq, strip0(tl), th, strip0(tr))
    cfg = (0, [], 0, [])
    for t in range(maxT):
        q, l, h, r = cfg
        if (q, strip0(l), h, strip0(r)) == key:
            return t
        cfg = raw.step(cfg)
        if cfg is None:
            raise DeriveError('halts during bootstrap at t=%d' % t)
    raise DeriveError('no bootstrap to Cc(%d)' % p0)


def process(spec, do_emit, scratch):
    """Try the machine directly, then as the mirror of a left-growth one."""
    res = {'spec': spec, 'ok': False}
    tried = []
    for mirror, sp in ((False, spec), (True, mirror_spec(spec))):
        try:
            cands = anchor_candidates(sp)
        except DeriveError as e:
            tried.append('%s: %s' % ('mirror' if mirror else 'direct', e))
            continue
        for (run, (edge, head, side, nw, ns, msbl, far), p0) in cands[:6]:
            if nw or ns:
                continue                     # wall must ride the far side
            if side != 'L':
                continue                     # right-growth goes through mirror
            E = LAB.index(edge)
            pr = profile(sp, E, head, side, list(far), msbl)
            if pr is None:
                tried.append('%s %s: laps not affine on both branches'
                             % ('mirror' if mirror else 'direct', edge))
                continue
            ai, ao = pr
            try:
                s, U = derive(sp, E, head, side, list(far), msbl, ai, ao)
                nchk = validate(sp, E, head, side, list(far), msbl, s)
                boot = boot_probe(sp, E, head, side, list(far), msbl, p0)
            except (DeriveError, Wall, KeyError, IndexError) as e:
                tried.append('%s %s: %s' % ('mirror' if mirror else 'direct', edge, e))
                continue
            res.update({'mirror': mirror, 'edge': edge, 'head': head,
                        'side': side, 'far': list(far), 'msb_left': msbl,
                        'p0': p0, 'boot': boot, 'skel': s, 'nchecked': nchk,
                        'int_affine': ai, 'ov_affine': ao})
            res['ok'] = True
            res['why'] = 'derived+validated (emission not yet wired)'
            return res
    res['why'] = tried[0] if tried else 'no candidate'
    res['tried'] = tried[:5]
    return res


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('specs', nargs='*')
    ap.add_argument('--list')
    ap.add_argument('--emit', action='store_true')
    ap.add_argument('--json')
    ap.add_argument('--scratch', default='/tmp')
    a = ap.parse_args()
    specs = list(a.specs)
    if a.list:
        specs += [x.strip() for x in open(a.list) if x.strip()]
    out = []
    for spec in specs:
        try:
            r = process(spec, a.emit, a.scratch)
        except Exception as e:
            r = {'spec': spec, 'ok': False, 'why': '%s: %s' % (type(e).__name__, e)}
        out.append(r)
        print('%s %s %s' % ('PASS' if r['ok'] else 'FAIL', spec, r.get('why', '')))
        sys.stdout.flush()
    if a.json:
        json.dump(out, open(a.json, 'w'), indent=1)
    print('== %d/%d derived' % (sum(1 for r in out if r['ok']), len(out)))


if __name__ == '__main__':
    main()
