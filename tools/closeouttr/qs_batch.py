#!/usr/bin/env python3
"""Sweep counters -> closeout batches (UNTRUSTED emitter + batch writer).

    python3 tools/closeouttr/qs_batch.py find ROWS.txt OUT.jsonl [--jobs 4]
    python3 tools/closeouttr/qs_batch.py batch OUT.jsonl [...] --tag QS [--chunk 40]

A sweep counter (SCOPING_INSTR.md 7.4.QC/7.4.QS) keeps a block of units
with one travelling hole; its anchor is two-index,

    swC i k = (q, (Lpre ++ uL^i ++ Lpost, h, Rpre ++ uR^k ++ Rpost))

and theories/Counters/SweepGlueTr.v decides a certificate [swcert] for it
with one boolean check, [sweep_check].  `find` searches the certificate:

  1. run the machine (and its mirror) for N steps, pin the instructions
     silent over the last two thirds (plus the undefined ones);
  2. for every (state, head) and small prefix/unit lengths, split the
     late configurations at that instruction as Lpre uL^i Lpost | h |
     Rpre uR^k Rpost and keep a split whose (i, k) sequence steps as
     (i, k+1) -> (i+1, k) and (i, 0) -> (e, i + d) with constant e, d;
  3. derive the inner chain (from [swA0]) and the outer chain (from
     [swB0]) with tools/counters/lapcert.derive_chain on the WRAPPED
     table, the boot (the first fitting anchor after the last quiet
     fire) and a chain prefix firing each unpinned instruction.

Everything is re-checked by the kernel ([sweep_check] under
[vm_compute]); a wrong certificate fails to compile, it cannot mis-prove.
The row lemma is [coversTr_qh3] of [sweep_sound] ([sweep_sound_mirror]
when the hole moves left), at the row's own [row_to_tm], so a batch
needs no per-machine definitions.

Only rows still in closeouttr_remaining.txt are written.  Compile each
batch before committing; drop a row Coq rejects with --skip SPEC.  Then
run tools/closeouttr/gen_closeout_tr.py.
"""
import argparse
import collections
import json
import os
import sys
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, '..', 'counters'))
from cbt import REPO, next_free, write_batch  # noqa: E402
import lapcert as LC                           # noqa: E402

N_STEPS = 60000
BOOT_CAP = 4096          # SweepGlueTr.sw_boot_cap
ST = ['StA', 'StB', 'StC', 'StD']
SYM = ['S0', 'S1']


def parse(spec):
    tab = {}
    for si, part in enumerate(spec.split('_')):
        for yi in range(2):
            e = part[3 * yi:3 * yi + 3]
            tab[(si, yi)] = None if e == '---' else (
                int(e[0]), +1 if e[1] == 'R' else -1, ord(e[2]) - ord('A'))
    return tab


def mirror(tab):
    return {k: (None if v is None else (v[0], -v[1], v[2])) for k, v in tab.items()}


def rstrip0(t):
    i = len(t)
    while i and t[i - 1] == 0:
        i -= 1
    return tuple(t[:i])


def lpad_eq(a, b):
    return rstrip0(a) == rstrip0(b)


def sflat(w):
    return (tuple(w), (), 0, 0, ())


def split_side(s, p, u):
    """s = pre ++ u^i ++ post with |pre| = p and i maximal"""
    if len(s) < p:
        return None
    a, i, x = len(u), 0, p
    while s[x:x + a] == u:
        i += 1
        x += a
    return s[:p], u, i, s[x:]


def run_occ(tab, n):
    """the configuration at every step, grouped by instruction: (t, L, R)
    with both half-tapes nearest-first and trailing blanks stripped"""
    tape, pos, q, lo, hi = {}, 0, 0, 0, 0
    occ, fires = collections.defaultdict(list), collections.defaultdict(list)
    for t in range(n):
        h = tape.get(pos, 0)
        fires[(q, h)].append(t)
        L = rstrip0([tape.get(pos - 1 - j, 0) for j in range(pos - lo)])
        R = rstrip0([tape.get(pos + 1 + j, 0) for j in range(hi - pos)])
        occ[(q, h)].append((t, L, R))
        tr = tab[(q, h)]
        if tr is None:
            return None, None
        w, d, nq = tr
        tape[pos] = w
        pos += d
        q = nq
        lo, hi = min(lo, pos), max(hi, pos)
    return occ, fires


def candidates(occ, n):
    """anchor splits of one instruction's late configurations whose (i, k)
    sequence is a sweep: yields (key, e, d)"""
    late = [o for o in occ if o[0] > n // 3]
    if len(late) < 20:
        return
    Lm = max((o[1] for o in late), key=len)
    Rm = max((o[2] for o in late), key=len)
    for p in range(4):
        for a in (1, 2, 3):
            uL = Lm[p:p + a]
            if len(uL) < a:
                continue
            for s in range(4):
                for b in (1, 2, 3):
                    uR = Rm[s:s + b]
                    if len(uR) < b:
                        continue
                    res = []
                    for t, L, R in late:
                        x, y = split_side(L, p, uL), split_side(R, s, uR)
                        if x is None or y is None:
                            break
                        res.append((t, x, y))
                    else:
                        keys = collections.Counter((x[0], x[1], x[3], y[0], y[1], y[3])
                                                   for _, x, y in res)
                        key, cnt = keys.most_common(1)[0]
                        if cnt < 0.9 * len(res):
                            continue
                        seq = [(x[2], y[2]) for _, x, y in res
                               if (x[0], x[1], x[3], y[0], y[1], y[3]) == key]
                        inner, outer, eds = 0, 0, collections.Counter()
                        for (i1, k1), (i2, k2) in zip(seq, seq[1:]):
                            if k1 > 0 and (i2, k2) == (i1 + 1, k1 - 1):
                                inner += 1
                            elif k1 == 0:
                                outer += 1
                                eds[(i2, k2 - i1)] += 1
                        if inner >= len(seq) // 2 and outer >= 2 and len(eds) == 1:
                            (e, d), = eds.keys()
                            if e + d >= 1 and d >= 0:
                                yield key, e, d


def end_inner_ok(c1, q, h, Lpre, uL, Rpre, uR, Rpost, c):
    """SweepGlueTr.sw_inner_ok's test on the chain's end ([sside_end_is])"""
    cq, cl, ch, cr = c1
    if not (cq == q and ch == h and cl == (tuple(Lpre + uL), (), cl[2], cl[3], ())
            and cr[1] == uR and cr[2] == 1 and cr[3] <= c):
        return False
    return any(cr[0] == Rpre + uR * x and lpad_eq(cr[4], uR * (c - cr[3] - x) + Rpost)
               for x in range(c - cr[3] + 1))


def end_base_ok(c1, q, h, Lpre, uL, R):
    """SweepGlueTr.sw_base1_ok's test on the chain's end"""
    cq, cl, ch, cr = c1
    return (cq == q and ch == h and cl == (tuple(Lpre + uL), (), cl[2], cl[3], ())
            and cr[1] == () and cr[4] == () and lpad_eq(cr[0], R))


NANB = ((1, 0), (0, 1), (1, 1), (2, 0), (0, 2), (2, 1), (1, 2), (2, 2))


def end_outer_ok(c1, q, h, Lpre, uL, Lpost, Rpre, uR, Rpost, e, c):
    """SweepGlueTr.sw_outer_ok's test on the chain's end ([c = ma + mb + d])"""
    cq, cl, ch, cr = c1
    if not (cq == q and ch == h and cl[1] == () and cl[4] == ()
            and lpad_eq(cl[0], Lpre + uL * e + Lpost)
            and cr[1] == uR and cr[2] == 1 and cr[3] <= c):
        return False
    return any(cr[0] == Rpre + uR * x and lpad_eq(cr[4], uR * (c - cr[3] - x) + Rpost)
               for x in range(c - cr[3] + 1))


MAMB = ((0, 0), (1, 0), (0, 1), (1, 1), (2, 0), (0, 2))


def try_anchor(tab, tabw, pins, lastq, q, h, occ, key, e, d):
    Lpre, uL, Lpost, Rpre, uR, Rpost = key
    # the units unrolled ahead of the inner lap: [na] at the near end (to
    # step onto the block), [nb] at the far end (to turn on it); the last
    # na + nb - 1 inner laps are concrete [base] chains
    chi = None
    for na, nb in NANB:
        c = na + nb - 1
        A0 = (q, sflat(Lpre), h, (Rpre + uR * na, uR, 1, 0, uR * nb + Rpost))
        for x in range(c + 1):
            A1 = (q, sflat(Lpre + uL), h, (Rpre + uR * x, uR, 1, 0, uR * (c - x) + Rpost))
            chi = LC.derive_chain(tabw, False, True, A0, A1, lift=True)
            if chi is not None:
                r = LC.srun(tabw, False, True, chi, A0)
                if (r is not None and r[2] > 0
                        and end_inner_ok(r[0], q, h, Lpre, uL, Rpre, uR, Rpost, c)):
                    break
                chi = None
        if chi is None:
            continue
        base = []
        for k in range(c):
            S0 = (q, sflat(Lpre), h, sflat(Rpre + uR * (k + 1) + Rpost))
            T0 = (q, sflat(Lpre + uL), h, sflat(Rpre + uR * k + Rpost))
            ch = LC.derive_chain(tabw, False, True, S0, T0, lift=True)
            r = ch is not None and LC.srun(tabw, False, True, ch, S0)
            if not r or r[2] <= 0 or not end_base_ok(r[0], q, h, Lpre, uL, Rpre + uR * k + Rpost):
                break
            base.append(ch)
        else:
            break
        chi = None
    if chi is None:
        return None, 'no inner chain'
    # the outer lap: [ma] / [mb] units behind unrolled at the two ends
    cho = None
    for ma, mb in MAMB:
        c = ma + mb + d
        B0 = (q, (Lpre + uL * ma, uL, 1, 0, uL * mb + Lpost), h, sflat(Rpre + Rpost))
        for x, b in [(0, c)] + [(x, 0) for x in range(c + 1)]:
            B1 = (q, sflat(Lpre + uL * e + Lpost), h,
                  (Rpre + uR * x, uR, 1, b, uR * (c - b - x) + Rpost))
            cho = LC.derive_chain(tabw, True, True, B0, B1, lift=True)
            if cho is not None:
                r = LC.srun(tabw, True, True, cho, B0)
                if (r is not None and r[2] > 0 and
                        end_outer_ok(r[0], q, h, Lpre, uL, Lpost, Rpre, uR, Rpost, e, c)):
                    break
                cho = None
        if cho is not None:
            break
    if cho is None:
        return None, 'no outer chain'
    boot = None
    for t, L, R in occ:
        if t <= lastq:
            continue
        x, y = split_side(L, len(Lpre), uL), split_side(R, len(Rpre), uR)
        if (x and y and x[0] == Lpre and lpad_eq(x[3], Lpost)
                and y[0] == Rpre and lpad_eq(y[3], Rpost) and x[2] + y[2] >= ma + mb):
            boot = (t, x[2], y[2])
            break
    if boot is None or boot[0] > BOOT_CAP:
        return None, 'no boot'
    fires = []
    for ins in sorted(tab):
        if ins in pins:
            continue
        wit = None
        for outer, c0, ch, el in ((False, A0, chi, False), (True, B0, cho, True)):
            f = LC.reach_instr(tabw, el, True, c0, ch, ins)
            if f is None:
                continue
            rr = LC.srun(tabw, el, True, f, c0)
            if rr and (rr[0][0], rr[0][2]) == ins:
                wit = (outer, f)
                break
        if wit is None:
            return None, 'no fire witness for %s%d' % ('ABCD'[ins[0]], ins[1])
        fires.append(wit)
    return dict(q=q, h=h, key=[list(x) for x in key], e=e, d=d, na=na, nb=nb, base=base, ma=ma, mb=mb, chi=chi, cho=cho,
                boot=boot, fires=fires), None


def find(spec):
    base = parse(spec)
    why = collections.Counter()
    for mir in (False, True):
        tab = mirror(base) if mir else base
        occ, fires = run_occ(tab, N_STEPS)
        if occ is None:
            return dict(spec=spec, err='halts')
        pins = sorted(k for k in tab if tab[k] is None or not fires.get(k)
                      or fires[k][-1] < N_STEPS // 3)
        quiet = [k for k in pins if tab[k] is not None and fires.get(k)]
        if not quiet:
            return dict(spec=spec, err='no quiet instruction')
        lastq = max(fires[k][-1] for k in quiet)
        tabw = {k: (None if k in pins else v) for k, v in tab.items()}
        for (q, h), o in sorted(occ.items()):
            for key, e, d in candidates(o, N_STEPS):
                try:
                    c, err = try_anchor(tab, tabw, pins, lastq, q, h, o, key, e, d)
                except LC.Halt:
                    c, err = None, 'halt in chain search'
                if c:
                    c.update(spec=spec, mir=mir, pins=[list(p) for p in pins])
                    return c
                why[err] += 1
    return dict(spec=spec, err=why.most_common(1)[0][0] if why else 'no sweep anchor')


# ------------------------------------------------------------------ render ---

def clist(xs):
    return '[' + ';'.join(SYM[x] for x in xs) + ']'


def cstep(st):
    return '(%s)' % ' '.join([st[0]] + [str(x) for x in st[1:]])


def cchain(ch):
    return '[' + '; '.join(cstep(tuple(s)) for s in ch) + ']'


def render(c):
    Lpre, uL, Lpost, Rpre, uR, Rpost = c['key']
    pins = '[' + '; '.join('(%s, %s)' % (ST[q], SYM[s]) for q, s in c['pins']) + ']'
    fires = '[' + '; '.join('(%s, %s)' % ('true' if o else 'false', cchain(ch))
                            for o, ch in c['fires']) + ']'
    t0, i0, k0 = c['boot']
    base = '[' + '; '.join(cchain(ch) for ch in c['base']) + ']'
    cert = ('(mkSW %s %s %s %s %s %s %s %s %s %d %d %d %d\n      %s\n      %s\n      %d %d %s\n      %s\n      %d %d %d)'
            % (pins, ST[c['q']], SYM[c['h']], clist(Lpre), clist(uL), clist(Lpost),
               clist(Rpre), clist(uR), clist(Rpost), c['e'], c['d'], c['na'], c['nb'],
               cchain(c['chi']), base, c.get('ma', 0), c.get('mb', 0), cchain(c['cho']),
               fires, t0, i0, k0))
    lemma = 'sweep_sound_mirror' if c['mir'] else 'sweep_sound'
    return 'apply coversTr_qh3, (%s _\n      %s).\n  vm_cast_no_check (eq_refl true).' % (lemma, cert)


def remaining():
    return set(l.strip() for l in open(os.path.join(REPO, 'closeouttr_remaining.txt')))


def cmd_find(a):
    specs = [l.split()[0] for l in open(a.rows) if l.strip() and not l.startswith('#')]
    done = set()
    if os.path.exists(a.out):
        done = set(json.loads(l)['spec'] for l in open(a.out))
    todo = [s for s in specs if s not in done]
    stats = collections.Counter()
    with open(a.out, 'a') as f, Pool(a.jobs) as pool:
        for r in pool.imap_unordered(find, todo):
            f.write(json.dumps(r) + '\n')
            f.flush()
            stats[r.get('err', 'ok')] += 1
    print(dict(stats))


def cmd_batch(a):
    rem = remaining()
    certs, seen = [], set()
    for p in a.found:
        for line in open(p):
            c = json.loads(line)
            s = c['spec']
            if 'err' in c or s not in rem or s in seen or s in a.skip:
                continue
            seen.add(s)
            certs.append(c)
    if a.limit:
        certs = certs[:a.limit]
    nn = next_free(a.tag)
    made = []
    for i in range(0, len(certs), a.chunk):
        chunk = certs[i:i + a.chunk]
        entries = [(c['spec'], render(c)) for c in chunk]
        made.append(write_batch(a.tag, nn, ['From BBB4.Checkers Require Import LapDecider.',
                                            'From BBB4.Counters Require Import SweepGlueTr.'],
                                entries, 'sweep counters by the two-index lap glue '
                                         '(SweepGlueTr, sweep_check)'))
        nn += 1
    print('%d rows -> %d batch file(s): %s' % (len(certs), len(made),
          ' '.join(os.path.relpath(p, REPO) for p in made)))


def main():
    ap = argparse.ArgumentParser()
    sp = ap.add_subparsers(dest='cmd', required=True)
    p = sp.add_parser('find')
    p.add_argument('rows')
    p.add_argument('out')
    p.add_argument('--jobs', type=int, default=4)
    p = sp.add_parser('batch')
    p.add_argument('found', nargs='+')
    p.add_argument('--tag', default='QS')
    p.add_argument('--chunk', type=int, default=40)
    p.add_argument('--limit', type=int, default=0)
    p.add_argument('--skip', action='append', default=[])
    a = ap.parse_args()
    {'find': cmd_find, 'batch': cmd_batch}[a.cmd](a)


if __name__ == '__main__':
    main()
