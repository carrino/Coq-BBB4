#!/usr/bin/env python3
"""LE6 UNTRUSTED finder: Zeckendorf counters over arbitrary token WORDS.

LE4's zeck2 code, generalised: read from the head, a Zeckendorf string x
(LSB nearest the head) splits uniquely into the tokens 0 and 10; the tape
is that token string with 0 -> A and 10 -> B for cell words A, B:

    pre ++ zw(x ++ [0]) ++ T        zw: 0 -> A, 10 -> B

LE3's one-cell code is A = 0, B = 10 (with T), LE4's is A = 0, B = 11.
Tries every anchor visited >= NCHECK+10 times with a constant far side,
prefixes up to 3 cells, A and B of 1..4 cells, terminators up to 8.

    python3 zeckw_detect.py ROWS.txt OUT.jsonl [--steps 400000] [--jobs 4]
"""
import argparse, itertools, json, os, sys
from multiprocessing import Pool
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'le4'))
from zeck2_detect import parse, rstrip0, zinc, zok, visits

NCHECK = 150
MODES = [('inc', 0), ('dec', 0), ('dec', 1), ('dec', 'w2'), ('dec', 'w3')]
WORDS = [list(w) for n in range(1, 5) for w in itertools.product([0, 1], repeat=n)]


def zdec(x):
    """Zeckendorf x - 1 (LSB first), x nonzero: 0^i 1 r -> alt(i) 0 r"""
    i = x.index(1)
    alt = [1 if (i - j) % 2 == 1 else 0 for j in range(i)]
    return alt + [0] + x[i + 1:]


def ztop(L, off):
    """the largest Zeckendorf string of length L whose top `off` digits are 0"""
    return [1 if (L - 1 - off - j) % 2 == 0 and j <= L - 1 - off else 0 for j in range(L)]


def zstep(x, mode):
    if mode[0] == 'inc':
        return zinc(x)
    if any(x):
        return zdec(x)
    if isinstance(mode[1], str):          # ('dec', 'wN'): the bottom widens by N digits
        return ztop(len(x) + int(mode[1][1:]), 0)
    return ztop(len(x) + 1, mode[1])


def zw(x, A, B):
    out, i = [], 0
    while i < len(x):
        if x[i] == 0:
            out += A; i += 1
        else:
            out += B; i += 2
    return out


def unzw(cells, A, B):
    """greedy decode (A, B prefix-free is checked by the caller); returns y or None"""
    y, i = [], 0
    while i < len(cells):
        if cells[i:i + len(A)] == A:
            y.append(0); i += len(A)
        elif cells[i:i + len(B)] == B:
            y += [1, 0]; i += len(B)
        else:
            return None
    return y


def prefix_free(A, B):
    return A != B and A[:len(B)] != B and B[:len(A)] != A


SKIP = 8      # visits at the anchor key that are not anchor visits (mid-sweep)


def follow(vs, b, x, mode, pre, A, B, T, far0):
    """NCHECK successive values from visit b, skipping up to SKIP other visits
    between two (LE6: the key also catches the head passing the anchor cell)"""
    xx, j = x, b
    for _ in range(1, NCHECK):
        xx = zstep(xx, mode)
        want = rstrip0(pre + zw(xx + [0], A, B) + T)
        for j2 in range(j + 1, min(j + 2 + SKIP, len(vs))):
            if vs[j2][1] == want and vs[j2][2] == far0:
                j = j2
                break
        else:
            return False
    return True


def try_anchor(vs):
    for b in range(min(40, len(vs))):
        if len(vs) - b < NCHECK:
            return None
        t0, near0, far0 = vs[b]
        near1 = vs[b + 1][1]
        for np_ in range(0, 4):
            if len(near0) < np_:
                break
            pre = near0[:np_]
            body = near0[np_:]
            for A in WORDS:
                for B in WORDS:
                    if not prefix_free(A, B):
                        continue
                    for nt in range(0, min(8, len(body)) + 1):
                        T = body[len(body) - nt:] if nt else []
                        mid = body[:len(body) - nt]
                        for pad in range(0, 5):
                            y = unzw(mid + [0] * pad, A, B)
                            if y is None or not y or y[-1] != 0:
                                continue
                            x = y[:-1]
                            if not x or not zok(x):
                                continue
                            for mode in MODES:
                                if follow(vs, b, x, mode, pre, A, B, T, far0):
                                    return b, pre, A, B, T, x, mode
    return None


def find(spec, steps):
    vis = visits(spec, steps)
    for key, vs in sorted(vis.items(), key=lambda kv: -len(kv[1])):
        if len(vs) < NCHECK + 10:
            continue
        got = try_anchor(vs)
        if got is None:
            continue
        b, pre, A, B, T, x, mode = got
        q, hs, side = key
        t0, near, far = vs[b]
        return dict(spec=spec, closed=True, kind='zeckw', state='ABCD'[q], head=hs, side=side,
                    far=far, pre=pre, A=A, B=B, T=T, x0=x, t0=t0, cells=near, mode=list(mode))
    return dict(spec=spec, closed=False)


def work(a):
    try:
        return find(*a)
    except Exception as e:  # noqa: BLE001
        return dict(spec=a[0], closed=False, error=repr(e))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('rows'); ap.add_argument('out')
    ap.add_argument('--steps', type=int, default=400000)
    ap.add_argument('--jobs', type=int, default=4)
    a = ap.parse_args()
    rows = open(a.rows).read().split()
    done = set()
    if os.path.exists(a.out):
        done = {json.loads(l)['spec'] for l in open(a.out)}
    todo = [(r, a.steps) for r in rows if r not in done]
    with open(a.out, 'a') as fo, Pool(a.jobs) as P:
        for d in P.imap_unordered(work, todo):
            fo.write(json.dumps(d) + '\n'); fo.flush()
            if d.get('closed'):
                print(d['spec'], d['state'], d['head'], d['side'], 'pre', d['pre'], 'A', d['A'], 'B', d['B'], 'T', d['T'], d['mode'])


if __name__ == '__main__':
    main()


def to_cert(d):
    """a zeckw_detect record -> the zeck2-shaped certificate emit_zeckd.py reads"""
    num = {'inc': 'zeckw', 'dec': 'zeckd'}[d['mode'][0]]
    return dict(spec=d['spec'], closed=True, kind=num, mode=d['mode'],
                family=dict(state=d['state'], head=d['head'], side=d['side'],
                            other_side_cells=d['far'], digits=[d['A'], d['B']],
                            near_head_prefix=d['pre'], terminator=d['T'],
                            terminators_by_phase=[d['T']], n_phases=1, base=2, digit_len=1,
                            code='binary', value_step_per_anchor_visit=1,
                            numeration=num, zA=d['A'], zB=d['B'], order='LSB nearest head'),
                fill=dict(widens_by=1, target_prefix=[], target_fill_digit=0,
                          target_suffix=[], lands_in_phase=0),
                arms=[], ladder=[],
                boot=dict(steps_from_blank=d['t0'], digits_lsb_first=d['x0'], phase=0,
                          cells=d['cells']))


def find_after(cert, steps, after):
    """the first anchor visit past index `after` that decodes, checked over
    the next 40 visits; a boot dict or None"""
    fam = cert['family']
    q = ord(fam['state']) - 65
    key = (q, fam['head'], fam['side'])
    vs = visits(cert['spec'], steps).get(key, [])
    pre, T, A, B = fam['near_head_prefix'], fam['terminator'], fam['zA'], fam['zB']
    mode = cert.get('mode', ['dec', 0])
    for b, (t0, near, far) in enumerate(vs):
        if t0 <= after or far != fam['other_side_cells'] or near[:len(pre)] != pre:
            continue
        body = near[len(pre):]
        if T and body[len(body) - len(T):] != T:
            continue
        mid = body[:len(body) - len(T)] if T else body
        for pad in range(0, 5):
            y = unzw(mid + [0] * pad, A, B)
            if y is None or not y or y[-1] != 0:
                continue
            x = y[:-1]
            if not x or not zok(x):
                continue
            xx, ok = x, True
            for k in range(1, min(40, len(vs) - b)):
                xx = zstep(xx, mode)
                if rstrip0(pre + zw(xx + [0], A, B) + T) != vs[b + k][1]:
                    ok = False
                    break
            if ok:
                return dict(steps_from_blank=t0, digits_lsb_first=x, phase=0, cells=near)
    return None
