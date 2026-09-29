#!/usr/bin/env python3
"""Never-quasihalting sweep counters -> closeout batches (UNTRUSTED emitter
+ batch writer).

    python3 tools/closeouttr/sw_batch.py find ROWS.txt OUT.jsonl [--jobs 4] [--timeout 300]
    python3 tools/closeouttr/sw_batch.py batch OUT.jsonl [...] --tag SW [--chunk 40]

The dense (class DN) sweep counters of SCOPING_INSTR.md 7.4.DX / 7.4.SW
keep a block of units with one travelling hole, like the quiet ones of
7.4.QS, but every defined instruction keeps firing.  The certificate is
theories/Counters/SweepGlueNeverTr.v's [swncert], a CYCLE of anchor
families

    fC f i k = (q, (Lpre ++ uL^i ++ Lpost, h, Rpre ++ uR^k ++ Rpost))

each with an inner lap (i, k+1) -> (i+1, k) that sweeps the units AHEAD
(SweepGlueTr's lap, from [swAa]) or BEHIND (from [swAb]), and an outer lap
(i, 0) -> (e, i + d) landing on the NEXT family.  Two families alternate
when the block grows by one cell a round but the units are two cells.
[sweep_nqh_check] decides it; the conclusion is [NeverQuasiHaltsTr]
through LapGlueTr.glue_neverqhtr.  `find` searches the certificate:

  1. run the machine (and its mirror) for N steps; the pins are the
     instructions that never fire (the undefined ones, in practice);
  2. for every (state, head) and small prefix/unit lengths, split the
     late configurations at that instruction as Lpre uL^i Lpost | h |
     Rpre uR^k Rpost, group them by split key (a family), and follow the
     outer transitions (k = 0 -> the next key at (e, i + d)) to a cycle of
     keys whose block grows;
  3. derive each family's inner chain (ahead first, then behind), its
     short concrete inner laps, and its outer chain onto the next family
     with tools/counters/lapcert.derive_chain on the wrapped table; the
     boot (the first fitting anchor of the run) and a chain prefix firing
     each unpinned instruction.

Everything is re-checked by the kernel ([sweep_nqh_check] under
[vm_compute]); a wrong certificate fails to compile, it cannot mis-prove.
The row lemma is [coversTr_nqh] of [sweep_nqh_sound]
([sweep_nqh_sound_mirror] when the hole moves left), at the row's own
[row_to_tm], so a batch needs no per-machine definitions.

Only rows still in closeouttr_remaining.txt are written.  Compile each
batch before committing; drop a row Coq rejects with --skip SPEC.  Then
run tools/closeouttr/gen_closeout_tr.py.
"""
import argparse
import collections
import json
import os
import signal
import sys
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import qs_batch as QS                          # noqa: E402
from cbt import REPO, next_free, write_batch   # noqa: E402

LC = QS.LC
sflat = QS.sflat
lpad_eq = QS.lpad_eq

N = 60000
NANB_A = ((1, 0), (0, 1), (1, 1), (2, 0), (0, 2), (2, 1), (1, 2), (2, 2))
NANB_B = ((0, 0), (1, 0), (0, 1), (1, 1), (2, 0), (0, 2), (2, 1), (1, 2), (2, 2))
MAMB = ((0, 0), (1, 0), (0, 1), (1, 1), (2, 0), (0, 2), (2, 1), (1, 2), (2, 2))


def side_end_is(s, pre, u, c, post, exact_post):
    """[sside_end_is]: s denotes pre ++ u^(n + c) ++ post (b <= c)"""
    if not (s[1] == u and s[2] == 1 and s[3] <= c):
        return False
    for x in range(c - s[3] + 1):
        if s[0] == pre + u * x:
            want = u * (c - s[3] - x) + post
            if (s[4] == want) if exact_post else lpad_eq(s[4], want):
                return True
    return False


def is_flat(s, w, exact):
    return s[1] == () and s[4] == () and (s[0] == w if exact else lpad_eq(s[0], w))


def ends(c, x_max):
    return [(0, c)] + [(x, 0) for x in range(c + 1)]


def inner_ahead(tabw, F):
    q, h = F['q'], F['h']
    Lpre, uL, Lpost, Rpre, uR, Rpost = F['key']
    for na, nb in NANB_A:
        c = na + nb - 1
        A0 = (q, sflat(Lpre), h, (Rpre + uR * na, uR, 1, 0, uR * nb + Rpost))
        chi = None
        for x, b in ends(c, c):
            A1 = (q, sflat(Lpre + uL), h, (Rpre + uR * x, uR, 1, b, uR * (c - b - x) + Rpost))
            ch = LC.derive_chain(tabw, False, True, A0, A1, lift=True)
            if ch is None:
                continue
            r = LC.srun(tabw, False, True, ch, A0)
            if (r and r[2] > 0 and r[0][0] == q and r[0][2] == h
                    and is_flat(r[0][1], Lpre + uL, True)
                    and side_end_is(r[0][3], Rpre, uR, c, Rpost, False)):
                chi = ch
                break
        if chi is None:
            continue
        base = []
        for k in range(c):
            S0 = (q, sflat(Lpre), h, sflat(Rpre + uR * (k + 1) + Rpost))
            T0 = (q, sflat(Lpre + uL), h, sflat(Rpre + uR * k + Rpost))
            ch = LC.derive_chain(tabw, False, True, S0, T0, lift=True)
            r = ch is not None and LC.srun(tabw, False, True, ch, S0)
            if not (r and r[2] > 0 and r[0][0] == q and r[0][2] == h
                    and is_flat(r[0][1], Lpre + uL, True)
                    and is_flat(r[0][3], Rpre + uR * k + Rpost, False)):
                break
            base.append(ch)
        else:
            return dict(behind=False, na=na, nb=nb, chi=chi, base=base, A0=A0)
    return None


def inner_behind(tabw, F):
    q, h = F['q'], F['h']
    Lpre, uL, Lpost, Rpre, uR, Rpost = F['key']
    for na, nb in NANB_B:
        c = na + nb + 1
        A0 = (q, (Lpre + uL * na, uL, 1, 0, uL * nb + Lpost), h, sflat(Rpre + uR))
        chi = None
        for x, b in ends(c, c):
            A1 = (q, (Lpre + uL * x, uL, 1, b, uL * (c - b - x) + Lpost), h, sflat(Rpre))
            ch = LC.derive_chain(tabw, True, False, A0, A1, lift=True)
            if ch is None:
                continue
            r = LC.srun(tabw, True, False, ch, A0)
            if (r and r[2] > 0 and r[0][0] == q and r[0][2] == h
                    and is_flat(r[0][3], Rpre, True)
                    and side_end_is(r[0][1], Lpre, uL, c, Lpost, False)):
                chi = ch
                break
        if chi is None:
            continue
        base = []
        for i in range(na + nb):
            S0 = (q, sflat(Lpre + uL * i + Lpost), h, sflat(Rpre + uR))
            T0 = (q, sflat(Lpre + uL * (i + 1) + Lpost), h, sflat(Rpre))
            ch = LC.derive_chain(tabw, True, False, S0, T0, lift=True)
            r = ch is not None and LC.srun(tabw, True, False, ch, S0)
            if not (r and r[2] > 0 and r[0][0] == q and r[0][2] == h
                    and is_flat(r[0][3], Rpre, True)
                    and is_flat(r[0][1], Lpre + uL * (i + 1) + Lpost, False)):
                break
            base.append(ch)
        else:
            return dict(behind=True, na=na, nb=nb, chi=chi, base=base, A0=A0)
    return None


def outer(tabw, F, G, e, d):
    q, h = F['q'], F['h']
    Lpre, uL, Lpost, Rpre, uR, Rpost = F['key']
    q2, h2 = G['q'], G['h']
    Lpre2, uL2, Lpost2, Rpre2, uR2, Rpost2 = G['key']
    for ma, mb in MAMB:
        c = ma + mb + d
        B0 = (q, (Lpre + uL * ma, uL, 1, 0, uL * mb + Lpost), h, sflat(Rpre + Rpost))
        for x, b in ends(c, c):
            B1 = (q2, sflat(Lpre2 + uL2 * e + Lpost2), h2,
                  (Rpre2 + uR2 * x, uR2, 1, b, uR2 * (c - b - x) + Rpost2))
            ch = LC.derive_chain(tabw, True, True, B0, B1, lift=True)
            if ch is None:
                continue
            r = LC.srun(tabw, True, True, ch, B0)
            if (r and r[2] > 0 and r[0][0] == q2 and r[0][2] == h2
                    and is_flat(r[0][1], Lpre2 + uL2 * e + Lpost2, False)
                    and side_end_is(r[0][3], Rpre2, uR2, c, Rpost2, False)):
                return dict(ma=ma, mb=mb, cho=ch, B0=B0)
    return None


def fam_candidates(occ, n, minhits=12, maxfam=4):
    """yield family cycles [(key, e, d)] for one instruction"""
    late = [o for o in occ if o[0] > n // 3]
    if len(late) < minhits:
        return
    Lm = max((o[1] for o in late), key=len)
    Rm = max((o[2] for o in late), key=len)
    seen = set()
    for p in range(4):
        for a in (1, 2, 3, 4):
            uL = Lm[p:p + a]
            if len(uL) < a:
                continue
            for s in range(4):
                for b in (1, 2, 3, 4):
                    uR = Rm[s:s + b]
                    if len(uR) < b:
                        continue
                    seq = []
                    cnt = collections.Counter()
                    for t, L, R in late:
                        x, y = QS.split_side(L, p, uL), QS.split_side(R, s, uR)
                        if x is None or y is None:
                            continue
                        key = (x[0], x[1], x[3], y[0], y[1], y[3])
                        seq.append((key, x[2], y[2]))
                        cnt[key] += 1
                    good = {k for k, v in cnt.items() if v >= minhits}
                    seq = [z for z in seq if z[0] in good]
                    inner = collections.Counter()
                    outs = collections.defaultdict(collections.Counter)
                    for (k1, i1, j1), (k2, i2, j2) in zip(seq, seq[1:]):
                        if k1 == k2 and j1 > 0 and (i2, j2) == (i1 + 1, j1 - 1):
                            inner[k1] += 1
                        elif j1 == 0 and j2 >= i1:
                            outs[k1][(k2, i2, j2 - i1)] += 1
                    # cycles: start at each key with inner laps
                    for k0 in sorted(good, key=lambda k: -inner[k]):
                        if inner[k0] < 3:
                            continue
                        cyc, k = [], k0
                        ok = False
                        for _ in range(maxfam):
                            if not outs[k]:
                                break
                            (k2, e, d), m = outs[k].most_common(1)[0]
                            if m < 2:
                                break
                            cyc.append((k, e, d))
                            k = k2
                            if k == k0:
                                ok = True
                                break
                        if ok and sum(e + d for _, e, d in cyc) >= 1:
                            sig = tuple(cyc)
                            if sig not in seen:
                                seen.add(sig)
                                yield cyc


def fam_candidates_skip(occ, n, minhits=12, maxfam=4, emax=3):
    """[fam_candidates] for anchors whose split key ALTERNATES inside a
    round: the hole moves one cell a sweep but the units are two cells, so
    a family's anchors are every other sweep and its inner lap is two
    sweeps.  Inner laps are read off each key's own subsequence; an outer
    transition goes from a key's [k = 0] anchor to the next anchor (of any
    key) that starts a round ([i <= emax])."""
    late = [o for o in occ if o[0] > n // 3]
    if len(late) < minhits:
        return
    Lm = max((o[1] for o in late), key=len)
    Rm = max((o[2] for o in late), key=len)
    seen = set()
    for p in range(4):
        for a in (1, 2, 3, 4):
            uL = Lm[p:p + a]
            if len(uL) < a:
                continue
            for s in range(4):
                for b in (1, 2, 3, 4):
                    uR = Rm[s:s + b]
                    if len(uR) < b:
                        continue
                    seq = []
                    cnt = collections.Counter()
                    for t, L, R in late:
                        x, y = QS.split_side(L, p, uL), QS.split_side(R, s, uR)
                        if x is None or y is None:
                            continue
                        key = (x[0], x[1], x[3], y[0], y[1], y[3])
                        seq.append((key, x[2], y[2]))
                        cnt[key] += 1
                    good = {k for k, v in cnt.items() if v >= minhits}
                    seq = [z for z in seq if z[0] in good]
                    inner = collections.Counter()
                    last = {}
                    for key, i2, j2 in seq:
                        if key in last:
                            i1, j1 = last[key]
                            if j1 > 0 and (i2, j2) == (i1 + 1, j1 - 1):
                                inner[key] += 1
                        last[key] = (i2, j2)
                    outs = collections.defaultdict(collections.Counter)
                    for x, (k1, i1, j1) in enumerate(seq):
                        if j1 != 0:
                            continue
                        for k2, i2, j2 in seq[x + 1:]:
                            if i2 <= emax and j2 >= i1:
                                outs[k1][(k2, i2, j2 - i1)] += 1
                                break
                    for k0 in sorted(good, key=lambda k: -inner[k]):
                        if inner[k0] < 3:
                            continue
                        cyc, k, ok = [], k0, False
                        for _ in range(maxfam):
                            if not outs[k]:
                                break
                            (k2, e, d), m = outs[k].most_common(1)[0]
                            if m < 2:
                                break
                            cyc.append((k, e, d))
                            k = k2
                            if k == k0:
                                ok = True
                                break
                        if ok and sum(e + d for _, e, d in cyc) >= 1:
                            sig = tuple(cyc)
                            if sig not in seen:
                                seen.add(sig)
                                yield cyc


def try_cycle(tab, tabw, pins, q, h, occ, cyc):
    """the whole certificate for one cycle of families, or (None, why)"""
    # [sweep_nqh_check] wants family 0 to grow the block ([1 <= e_0 + d_0])
    r = next(j for j, (_, e, d) in enumerate(cyc) if e + d >= 1)
    cyc = cyc[r:] + cyc[:r]
    fams = []
    for key, e, d in cyc:
        F = dict(q=q, h=h, key=key, e=e, d=d)
        inn = inner_ahead(tabw, F) or inner_behind(tabw, F)
        if inn is None:
            return None, 'no inner chain'
        F.update(inn)
        fams.append(F)
    for j, F in enumerate(fams):
        G = fams[(j + 1) % len(fams)]
        o = outer(tabw, F, G, F['e'], F['d'])
        if o is None:
            return None, 'no outer chain'
        F.update(o)
    M = max(F['ma'] + F['mb'] for F in fams)
    boot = None
    for t, L, R in occ:
        for j, F in enumerate(fams):
            Lpre, uL, Lpost, Rpre, uR, Rpost = F['key']
            x, y = QS.split_side(L, len(Lpre), uL), QS.split_side(R, len(Rpre), uR)
            if (x and y and x[0] == Lpre and lpad_eq(x[3], Lpost)
                    and y[0] == Rpre and lpad_eq(y[3], Rpost) and x[2] + y[2] >= M):
                boot = (t, j, x[2], y[2])
                break
        if boot:
            break
    if boot is None:
        return None, 'no boot'
    fires = []
    for ins in sorted(tab):
        if ins in pins:
            continue
        wit = None
        for j, F in enumerate(fams):
            for outer_, c0, ch, el, er in ((False, F['A0'], F['chi'], F['behind'], not F['behind']),
                                           (True, F['B0'], F['cho'], True, True)):
                f = LC.reach_instr(tabw, el, er, c0, ch, ins)
                if f is None:
                    continue
                rr = LC.srun(tabw, el, er, f, c0)
                if rr and (rr[0][0], rr[0][2]) == ins:
                    wit = (j, outer_, f)
                    break
            if wit:
                break
        if wit is None:
            return None, 'no fire witness'
        fires.append(wit)
    return dict(fams=fams, M=M, boot=boot, fires=fires), None



def run_occ_rev(tab, n):
    """qs_batch.run_occ restricted to the steps where the head REVERSES
    (it arrived moving one way and leaves the other).  The hole of a sweep
    counter is where its sweeps turn, so this drops the anchor
    instruction's fires inside a sweep, which otherwise hide the anchor's
    units from [fam_candidates] (they are cut from the longest late
    configuration)."""
    tape, pos, q, lo, hi, dprev = {}, 0, 0, 0, 0, 0
    occ, fires = collections.defaultdict(list), collections.defaultdict(list)
    for t in range(n):
        h = tape.get(pos, 0)
        fires[(q, h)].append(t)
        tr = tab[(q, h)]
        if tr is None:
            return None, None
        w, d, nq = tr
        if dprev and d != dprev:
            L = QS.rstrip0([tape.get(pos - 1 - j, 0) for j in range(pos - lo)])
            R = QS.rstrip0([tape.get(pos + 1 + j, 0) for j in range(hi - pos)])
            occ[(q, h)].append((t, L, R))
        tape[pos] = w
        pos += d
        q = nq
        dprev = d
        lo, hi = min(lo, pos), max(hi, pos)
    return occ, fires


class Timeout(Exception):
    pass


def _alarm(signum, frame):
    raise Timeout()


def find(spec, timeout=0):
    base = QS.parse(spec)
    why = collections.Counter()
    if timeout:
        signal.signal(signal.SIGALRM, _alarm)
        signal.alarm(timeout)
    try:
        for skip, rev, mir in ((False, False, False), (False, False, True),
                               (False, True, False), (False, True, True),
                               (True, True, False), (True, True, True)):
            tab = QS.mirror(base) if mir else base
            occ, fires = (run_occ_rev if rev else QS.run_occ)(tab, N)
            if occ is None:
                return dict(spec=spec, err='halts')
            pins = sorted(k for k in tab if tab[k] is None or not fires.get(k))
            tabw = {k: (None if k in pins else v) for k, v in tab.items()}
            for (q, h), o in sorted(occ.items()):
                for cyc in (fam_candidates_skip if skip else fam_candidates)(o, N):
                    try:
                        c, err = try_cycle(tab, tabw, pins, q, h, o, cyc)
                    except LC.Halt:
                        c, err = None, 'halt in chain search'
                    if c:
                        c.update(spec=spec, mir=mir, pins=[list(p) for p in pins])
                        return c
                    why[err] += 1
    except Timeout:
        return dict(spec=spec, err='timeout')
    finally:
        if timeout:
            signal.alarm(0)
    return dict(spec=spec, err=why.most_common(1)[0][0] if why else 'no sweep anchor')


# ------------------------------------------------------------------ render ---

ST = QS.ST
SYM = QS.SYM
clist = QS.clist
cchain = QS.cchain


def render_fam(F):
    Lpre, uL, Lpost, Rpre, uR, Rpost = F['key']
    base = '[' + '; '.join(cchain(ch) for ch in F['base']) + ']'
    return ('(mkF %s %s %s %s %s %s %s %s %s %d %d\n        %s\n        %s\n'
            '        %d %d %s %d %d)'
            % (ST[F['q']], SYM[F['h']], clist(Lpre), clist(uL), clist(Lpost),
               clist(Rpre), clist(uR), clist(Rpost),
               'true' if F['behind'] else 'false', F['na'], F['nb'],
               cchain(F['chi']), base, F['ma'], F['mb'], cchain(F['cho']),
               F['e'], F['d']))


def render(c):
    pins = '[' + '; '.join('(%s, %s)' % (ST[q], SYM[s]) for q, s in c['pins']) + ']'
    fams = '[' + ';\n      '.join(render_fam(F) for F in c['fams']) + ']'
    fires = '[' + '; '.join('(%d, %s, %s)' % (j, 'true' if o else 'false', cchain(ch))
                            for j, o, ch in c['fires']) + ']'
    t0, j0, i0, k0 = c['boot']
    cert = '(mkSWN %s\n      %s\n      %d\n      %s\n      %d %d %d %d)' % (
        pins, fams, c['M'], fires, t0, j0, i0, k0)
    lemma = 'sweep_nqh_sound_mirror' if c['mir'] else 'sweep_nqh_sound'
    return 'apply coversTr_nqh, (%s _\n      %s).\n  vm_cast_no_check (eq_refl true).' % (lemma, cert)


def _find1(args):
    return find(*args)


def cmd_find(a):
    specs = [l.split()[0] for l in open(a.rows) if l.strip() and not l.startswith('#')]
    done = set()
    if os.path.exists(a.out):
        done = set(json.loads(l)['spec'] for l in open(a.out))
    todo = [(s, a.timeout) for s in specs if s not in done]
    stats = collections.Counter()
    with open(a.out, 'a') as f, Pool(a.jobs) as pool:
        for r in pool.imap_unordered(_find1, todo):
            f.write(json.dumps(r) + '\n')
            f.flush()
            stats[r.get('err', 'ok')] += 1
    print(dict(stats))


def cmd_batch(a):
    rem = QS.remaining()
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
                                            'From BBB4.Counters Require Import SweepGlueNeverTr.'],
                                entries, 'never-QH sweep counters by the multi-family '
                                         'two-index lap glue (SweepGlueNeverTr, sweep_nqh_check)'))
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
    p.add_argument('--timeout', type=int, default=300)
    p = sp.add_parser('batch')
    p.add_argument('found', nargs='+')
    p.add_argument('--tag', default='SW')
    p.add_argument('--chunk', type=int, default=40)
    p.add_argument('--limit', type=int, default=0)
    p.add_argument('--skip', action='append', default=[])
    a = ap.parse_args()
    {'find': cmd_find, 'batch': cmd_batch}[a.cmd](a)


if __name__ == '__main__':
    main()
