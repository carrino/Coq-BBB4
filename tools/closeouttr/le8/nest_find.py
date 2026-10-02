#!/usr/bin/env python3
"""LE8 UNTRUSTED plan finder for `emit_nest.py` (SCOPING_INSTR 7.4.LE8).

Given a row's outer counter (an LE4 positional reading: anchor, side, far
cells, head prefix, digit words Z / O, terminator T), find a PLAN: the outer
carry and the overflow as chains of linear pieces and INNER COUNTS.

For the overflow `O^k W T -> Z^(k+d) W T` (and the carry `O^k Z X ->
Z^k O X`) at three widths k, the machine is run from the start to the end
configuration and every visit to the counter's anchor shape (its state and
head prefix) at ANY offset is decoded: far cells (nearest-first), the digit
string over Z / O, and the rest.  A maximal run of visits at one offset
and far context whose digit strings go 0, 1, 2, ..., 2^w - 1 (LSB at the
head) is an inner count of width w.  The runs must line up across the
widths with w = k + c and a rest that is one constant cell list (plus the
opaque tail X for the carry); the linear stretches between them become
arm pieces, which `emit_nest.py` derives and validates.

    python3 nest_find.py ROWS.txt OUT_DIR [--pos le4/pos.jsonl] [--min 3]
writes OUT_DIR/<spec>.json for every row it plans (and prints why not).
"""
import argparse
import json
import os
import random
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from csim import parse, step, norm  # noqa: E402

XMARK = (1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 1)   # the opaque tail in the carry runs


def conf(c, cells, fix=None):
    q = 'ABCD'.index(c['q'])
    fx = tuple(c['fix'] if fix is None else fix)
    if c['side'] == 'R':
        return (q, fx, cells[0], tuple(cells[1:]))
    return (q, tuple(cells[1:]), cells[0], fx)


def run_visits(tab, c, cells0, cells1, maxn=3 * 10 ** 6):
    """run from the counter configuration `cells0` until `cells1` (same far
    side, up to blanks); every anchor-shaped visit on the way as
    (time, offset, far, near cells)"""
    q0 = 'ABCD'.index(c['q'])
    sgn = 1 if c['side'] == 'R' else -1
    tape = {}
    for i, v in enumerate(c['fix']):
        tape[-sgn * (1 + i)] = v
    for i, v in enumerate(cells0):
        tape[sgn * i] = v
    tgt = {}
    for i, v in enumerate(c['fix']):
        tgt[-sgn * (1 + i)] = v
    for i, v in enumerate(cells1):
        tgt[sgn * i] = v
    want_near = strip0(cells1)
    want_far = strip0(c['fix'])
    pos, q = 0, q0
    pre = list(c['pre'])
    out = []
    lo, hi = min(tape) - 1, max(tape) + 1
    for t in range(maxn):
        if q == q0 and tape.get(pos, 0) == pre[0]:
            lo, hi = min(lo, pos), max(hi, pos)
            near = [tape.get(pos + sgn * i, 0) for i in range(0, (hi - lo) + 2)]
            far = [tape.get(pos - sgn * (1 + i), 0) for i in range(0, (hi - lo) + 2)]
            if near[:len(pre)] == pre:
                out.append((t, sgn * pos, tuple(strip0(far)), strip0(near[len(pre):])))
            if t > 0 and strip0(near) == want_near and strip0(far) == want_far:
                return out
        e = tab[(q, tape.get(pos, 0))]
        if e is None:
            return None
        w, d, nq = e
        tape[pos] = w
        pos += 1 if d == 'R' else -1
        lo, hi = min(lo, pos), max(hi, pos)
        q = nq
    return None


def decode(cells, Z, O):
    """the digit string (LSB first) read off `cells` and the rest"""
    x, i = [], 0
    while True:
        if cells[i:i + len(Z)] == Z:
            x.append(0); i += len(Z)
        elif cells[i:i + len(O)] == O:
            x.append(1); i += len(O)
        else:
            break
    return x, cells[i:]


def val(x):
    return sum(b << i for i, b in enumerate(x))


def strip0(rest):
    rest = list(rest)
    while rest and rest[-1] == 0:
        rest.pop()
    return rest


def counts(vs, Z, O):
    """maximal runs at one (offset, far): the low w digits go 0 .. 2^w - 1 by
    +1 with every cell beyond them unchanged; the outermost runs, in time order"""
    by = {}
    for v in vs:
        by.setdefault((v[1], v[2]), []).append(v)
    runs = []
    wz = len(Z)
    for key, lst in by.items():
        i = 0
        while i < len(lst):
            cells = lst[i][3] + [0] * (4 * wz)
            x, _ = decode(cells, Z, O)
            lead = 0
            while lead < len(x) and x[lead] == 0:
                lead += 1
            best = None
            for w in range(lead, 0, -1):
                upper = strip0(cells[w * wz:])
                cur, j, ok = 0, i, True
                while cur < 2 ** w - 1:
                    nxt = None
                    for j2 in range(j + 1, len(lst)):
                        c2 = lst[j2][3] + [0] * (4 * wz)
                        x2, _ = decode(c2[:w * wz], Z, O)
                        if len(x2) == w and strip0(c2[w * wz:]) == upper:
                            v2 = val(x2)
                            if v2 == cur + 1:
                                nxt = j2
                                break
                    if nxt is None:
                        ok = False
                        break
                    cur += 1
                    j = nxt
                if ok:
                    best = (w, j, upper)
                    break
            if best:
                w, j, upper = best
                runs.append(dict(key=key, w=w, t0=lst[i][0], t1=lst[j][0], rest=upper))
                i = j + 1
            else:
                i += 1
    runs.sort(key=lambda r: (r['t0'], -r['w']))
    out = []
    for r in runs:
        if out and r['t0'] <= out[-1]['t1']:
            continue
        out.append(r)
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('rows')
    ap.add_argument('outdir')
    ap.add_argument('--pos', default=os.path.join(HERE, '..', 'le4', 'pos.jsonl'))
    a = ap.parse_args()
    rows = open(a.rows).read().split()
    os.makedirs(a.outdir, exist_ok=True)
    pos = {}
    for l in open(a.pos):
        d = json.loads(l)
        if d.get('closed'):
            pos[d['spec']] = d
    for spec in rows:
        if spec not in pos:
            print(spec, 'no positional reading')
            continue
        d = pos[spec]
        f = d['family']
        c = dict(q=f['state'], side=f['side'], fix=f['other_side_cells'],
                 pre=[f['head']] + f['near_head_prefix'], Z=f['digits'][0], O=f['digits'][1],
                 T=f['terminators_by_phase'][0])
        fl = d['fill']
        try:
            plan = find_plan(spec, c, fl)
        except Exception as e:  # noqa: BLE001
            print(spec, 'error', repr(e)[:200])
            continue
        if isinstance(plan, str):
            print(spec, plan)
            continue
        json.dump(plan, open(os.path.join(a.outdir, spec + '.json'), 'w'), indent=1)
        print(spec, 'PLAN', plan['name'])


def ovf_cells(c, fl, k):
    """start and end cell lists of the overflow at width k, and (W, d)"""
    Z, O = list(c['Z']), list(c['O'])
    suf = fl['target_suffix']
    if fl['target_prefix'] or fl['target_fill_digit'] != 0 or suf not in ([], [1]):
        return None
    if suf == [1]:
        W, d = O, fl['widens_by']
        k = k - 1
    else:
        W, d = [], fl['widens_by']
    start = c['pre'] + O * k + W + c['T']
    end = c['pre'] + Z * (k + d) + W + c['T']
    return start, end, W, d


def zero_laps(spec, c, steps=2 * 10 ** 6, minL=3):
    """the anchor's ZERO configurations Z^L R along a run from blank: a rest
    R seen with L in arithmetic progression (>= 3 times); (R, d, [L...])"""
    tab = parse(spec)
    q0 = 'ABCD'.index(c['q'])
    sgn = 1 if c['side'] == 'R' else -1
    pre, Z = list(c['pre']), list(c['Z'])
    fix = list(c['fix'])
    tape, pos, q = {}, 0, 0
    seen = {}
    for t in range(steps):
        if q == q0 and tape.get(pos, 0) == pre[0]:
            far = [tape.get(pos - sgn * (1 + i), 0) for i in range(len(fix) + 6)]
            if strip0(far) == fix:
                near = [tape.get(pos + sgn * i, 0) for i in range(0, 400)]
                near = strip0(near)
                if near[:len(pre)] == pre:
                    cells = near[len(pre):]
                    L = 0
                    while cells[L * len(Z):(L + 1) * len(Z)] == Z:
                        L += 1
                    rest = tuple(cells[L * len(Z):])
                    if L >= minL and len(rest) <= 12:
                        seen.setdefault(rest, []).append(L)
        e = tab[(q, tape.get(pos, 0))]
        if e is None:
            return None
        w, d, nq = e
        tape[pos] = w
        pos += 1 if d == 'R' else -1
        q = nq
    best = None
    for rest, Ls in seen.items():
        Ls = sorted(set(Ls))
        if len(Ls) < 3:
            continue
        dd = Ls[1] - Ls[0]
        if dd > 0 and all(Ls[i + 1] - Ls[i] == dd for i in range(len(Ls) - 1)):
            if best is None or len(Ls) > len(best[2]):
                best = (list(rest), dd, Ls)
    return best


def find_plan(spec, c, fl):
    tab = parse(spec)
    Z, O = list(c['Z']), list(c['O'])
    zl = zero_laps(spec, c)
    if zl is None:
        return 'no zero laps at the anchor'
    R, d, Ls = zl
    ks = (Ls[1], Ls[2], Ls[3]) if len(Ls) > 3 else tuple(Ls[:3])
    chains = {}
    for k in ks:
        s = c['pre'] + O * k + R
        e = c['pre'] + Z * (k + d) + R
        vs = run_visits(tab, c, s, e)
        if vs is None:
            return 'overflow O^%d R -> Z^%d R not reached (R = %r)' % (k, k + d, R)
        chains[k] = (None, vs, counts(vs, Z, O))
    shapes = [[(r['key'][1], r['w'] - k, tuple(r['rest'])) for r in chains[k][2]] for k in ks]
    if not (shapes[0] == shapes[1] == shapes[2]):
        return 'overflow: the inner counts do not line up across widths: %r' % (
            [[(r['key'][0], r['w'] - k) for r in chains[k][2]] for k in ks],)
    pieces = []
    for (far, dw, rest) in shapes[0]:
        pieces.append(dict(far=list(far), dw=dw, rest=list(rest)))
    L0 = max([ks[0] - Ls[0] if False else 1] + [1 - p['dw'] for p in pieces])
    levels = {}
    carry_pieces = []
    for i, p in enumerate(pieces):
        nm = 'I%d' % i
        levels[nm] = dict(q=c['q'], side=c['side'], fix=p['far'], pre=c['pre'], Z=Z, O=O)
        b = L0 + p['dw']
        frm0 = dict(q=c['q'], side=c['side'], fix=p['far'],
                    items=[['c', c['pre']], ['r', Z, b], ['c', p['rest']]])
        frm1 = dict(q=c['q'], side=c['side'], fix=p['far'],
                    items=[['c', c['pre']], ['r', O, b], ['c', p['rest']]])
        carry_pieces.append(['arm', frm0])
        carry_pieces.append(['count', nm, frm1])
    plan = dict(spec=spec, name='auto (zero laps %s, rest %s, d %d, %d inner counts)'
                % (Ls[:4], R, d, len(pieces)),
                outer=dict(q=c['q'], side=c['side'], fix=c['fix'], pre=c['pre'], Z=Z, O=O,
                           T=[]),
                levels=levels,
                ovf=dict(W=R, d=d, L0=L0, pieces=carry_pieces))
    return plan


if __name__ == '__main__':
    main()
