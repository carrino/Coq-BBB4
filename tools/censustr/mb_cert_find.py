#!/usr/bin/env python3
"""Multi-block RepWL finder (UNTRUSTED), SCOPING_INSTR.md 7.4.MB.

The Python mirror of CensusTr/RepWLMBTr.v.  A node is RepWL's [rconf]
(q, li, lb, h, rb, ri), but the item words have DIFFERENT lengths: each
side has a word list (DL, DR, nearest-first orientation) and the fold
that turns departed buffer cells into items ([mb_fold]) cuts the far end
of the buffer at whichever listed word it matches, as long as K cells
stay in the buffer; past X buffered cells it folds single cells.  A
popped blank is B cells.  So a tape (001)^a (0110)^b [head] (01)^c is
three items of three lengths, where single-block RepWL needs L = 12 and
up to 36 verbatim cells.

Coq re-runs everything at the found parameters ([mb_tier_tr spec DL DR
K X B T t fuel M]); nothing found here is trusted.

  find OUT.json --list ROWS [--jobs N] [--timeout S] [--qh [--scan SCAN]]
  probe OUT.json PROBE.v            `Time Eval vm_compute in mb_tier_tr ...`
                                    per certified row
"""
import argparse
import json
import multiprocessing as mp
import os
import signal
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, '..', '..'))
sys.path.insert(0, os.path.join(REPO, 'tools'))
sys.path.insert(0, HERE)
import repwl_prover as rp  # noqa: E402
from rw_cert_find import (procedure_tr, lex_check_tr, instr, fired_prefix,  # noqa: E402
                          _limit_memory, Timeout, _alarm, read_scan)

MAX_NODES = 30000
PMAX = 16  # longest block period looked for (--pmax; the long-period junk rows need 64)
T_CANDS = (0, 1024, 4096)


# ---- the abstraction (mirror of RepWLMBTr.v) ----

def asz(a):
    return len(a[1]) + len(a[5]) + len(a[2]) + len(a[4])


def push_raw(w, items):
    """mirror of [push_raw]: an exact one-copy item, never merged (a
    blank block against an empty list is absorbed)"""
    if not items and rp.word_blank(w):
        return ()
    return ((w, 1, False),) + items


def mb_fold(D, K, Y, X, T, buf, items):
    """mirror of [mb_fold]: while the buffer (nearest-first) holds at
    least Y cells, fold its far end into [items] at the first word that
    leaves >= K cells: the nearest item's word when it is listed (so a
    run keeps its phase), else a listed word the far end holds TWICE (so
    a rotation of a long word does not cut into a short-period run),
    else any listed word; with no word matching, past X cells fold the
    farthest single cell as an unmerged item."""
    for _ in range(len(buf)):
        n = len(buf)
        c = None
        if Y <= n:
            pref = [items[0][0]] if items and items[0][0] in D else []
            for w in pref:
                m = len(w)
                if m and K + m <= n and buf[n - m:] == w:
                    c = n - m
                    break
            if c is None:
                for w in D:
                    m = len(w)
                    if m and K + 2 * m <= n and buf[n - 2 * m:] == w + w:
                        c = n - m
                        break
            if c is None:
                for w in D:
                    m = len(w)
                    if m and K + m <= n and buf[n - m:] == w:
                        c = n - m
                        break
        if c is not None:
            items = rp.push_item(T, buf[c:], items)
            buf = buf[:c]
        elif X < n:
            items = push_raw(buf[n - 1:], items)
            buf = buf[:n - 1]
        else:
            return buf, items
    return buf, items


def mb_seed(tbl, DL, DR, K, Y, X, T, t):
    cs = rp.csteps(tbl, t)
    if cs is None:
        return None
    q, l, h, r = cs
    lb, li = mb_fold(DL, K, Y, X, T, tuple(l), ())
    rb, ri = mb_fold(DR, K, Y, X, T, tuple(r), ())
    return (q, li, lb, h, rb, ri)


def mb_succs(tbl, DL, DR, K, Y, X, B, T, a):
    q, li, lb, h, rb, ri = a
    tr = tbl[(q, h)]
    if tr is None:
        return None
    w, d, q2 = tr
    if d == 'R':
        if rb:
            return [(q2, li, (w,) + lb, rb[0], rb[1:], ri)]
        lb2, li2 = mb_fold(DL, K, Y, X, T, (w,) + lb, li)
        ps = rp.pop_item(B, ri)
        if ps is None:
            return None
        return [(q2, li2, lb2, wd[0], wd[1:], ri2) for wd, ri2 in ps]
    if lb:
        return [(q2, li, lb[1:], lb[0], (w,) + rb, ri)]
    rb2, ri2 = mb_fold(DR, K, Y, X, T, (w,) + rb, ri)
    ps = rp.pop_item(B, li)
    if ps is None:
        return None
    return [(q2, li2, wd[1:], wd[0], rb2, ri2) for wd, li2 in ps]


def closure(tbl, P, a0, cap=MAX_NODES):
    DL, DR, K, Y, X, B, T = P
    seen = set()
    adj = {}
    todo = [a0]
    while todo:
        a = todo.pop()
        if a in seen:
            continue
        seen.add(a)
        if len(seen) > cap:
            return None
        sl = mb_succs(tbl, DL, DR, K, Y, X, B, T, a)
        if sl is None:
            return None
        adj[a] = sl
        todo.extend(sl)
    return seen, adj


# ---- dictionaries from the tape ----

def tape_at(tbl, t):
    cs = rp.csteps(tbl, t)
    if cs is None:
        return None
    q, l, h, r = cs
    return list(reversed(l)) + [h] + list(r), len(l)


def runs(s, pmax=16, minlen=12):
    """maximal periodic runs (greedy, left to right): (i, j, p)"""
    out, i, n = [], 0, len(s)
    while i < n:
        best = (0, 1)
        for p in range(1, pmax + 1):
            j = i + p
            while j < n and s[j] == s[j - p]:
                j += 1
            if j - i > best[0] and j - i >= 2 * p:
                best = (j - i, p)
        ln, p = best
        if ln >= minlen:
            out.append((i, i + ln, p))
            i += ln
        else:
            i += 1
    return out


def snapshots(tbl, times):
    """the tape (tape order) at each of [times], from one run"""
    times = sorted(set(times))
    out = []
    tape = {}
    pos = q = 0
    k = 0
    for t in range(times[-1] + 1):
        while k < len(times) and times[k] == t:
            lo, hi = min(tape, default=0), max(tape, default=0)
            out.append([tape.get(i, 0) for i in range(lo, hi + 1)])
            k += 1
        tr = tbl[(q, tape.get(pos, 0))]
        if tr is None:
            break
        w, d, q = tr
        tape[pos] = w
        pos += 1 if d == 'R' else -1
    return out


SNAP_TIMES = tuple(sorted({int(2 ** (12 + k / 4.0)) for k in range(41)} |
                          {int(2 ** (12 + k / 4.0)) + 1000 for k in range(41)}))


def periods(tbl, times=SNAP_TIMES, pmax=None, minlen=10):
    """the canonical words of the periodic runs of the tape at [times],
    heaviest (most cells) first"""
    wt = {}
    for s in snapshots(tbl, times):
        for (i, j, p) in runs(s, pmax or PMAX, minlen):
            w = tuple(s[i:i + p])
            c = min(w[k:] + w[:k] for k in range(p))
            wt[c] = wt.get(c, 0) + (j - i)
    return [w for w, _ in sorted(wt.items(), key=lambda kv: (-kv[1], len(kv[0]), kv[0]))]


def rotations(ws):
    out = []
    for w in ws:
        for k in range(len(w)):
            r = w[k:] + w[:k]
            if r not in out:
                out.append(r)
    return out


def dicts(words):
    """(DL, DR): every rotation, longest first; DL mirrored (a left
    word is stored nearest-first)"""
    dr = sorted(rotations(words), key=lambda w: -len(w))
    dl = sorted(rotations([tuple(reversed(w)) for w in words]), key=lambda w: -len(w))
    return tuple(dl), tuple(dr)


def candidates(tbl, spec):
    """parameter candidates (DL, DR, K, Y, X, B, T), cheapest first"""
    out = []
    ws = periods(tbl)
    for nw in (2, 3, 4, 5, 6, 8):
        if nw > len(ws) and nw > 2:
            break
        dl, dr = dicts(ws[:nw])
        if not dr:
            continue
        mx = max(len(w) for w in dr)
        for K in (1, 2, mx):
            for Y in (K + mx, K + mx + 2):
                for T in (2, 3):
                    c = (dl, dr, K, Y, Y + max(4, mx), 1, T)
                    if c not in out:
                        out.append(c)
    return out


def try_params(tbl, P, t, tblw=None, cap=MAX_NODES):
    """never-QH: closure and search on [tbl], targets = the closure's and
    the prefix's instructions (mirror of [mb_tier_tr]); QH ([tblw] the
    wrapped machine): seed on [tbl], closure and search on [tblw],
    targets = the closure's instructions (mirror of [mb_tier_qhbtr])"""
    DL, DR, K, Y, X, B, T = P
    a0 = mb_seed(tbl, DL, DR, K, Y, X, T, t)
    if a0 is None:
        return None, 'halts'
    tc = tblw or tbl
    r = closure(tc, P, a0, cap)
    if r is None:
        return None, 'no closure'
    seen, adj = r
    targets = sorted({instr(a) for a in seen} | (set() if tblw else fired_prefix(tbl, t)))
    for tg in targets:
        comps = procedure_tr(tc, seen, adj, tg, rp.MEAS)
        if comps is None or not lex_check_tr(tc, adj, seen, tg, comps):
            return None, 'no cert for %s%d (%d nodes)' % (chr(65 + tg[0]), tg[1], len(seen))
    return (len(seen), max(asz(a) for a in seen)), 'ok'


def find_one(job):
    spec, timeout, scan, polish = job
    tbl = rp.parse(spec)
    tblw, pins, tcands = None, None, T_CANDS
    if scan is not None:
        # the QH side, as rw_cert_find.find_one_qh: pin every instruction
        # quiet for the last 90% of the scan, wrap, seed past the pins
        lasts = [l for c, l in scan.values() if c > 0]
        horizon = max(lasts) + 1 if lasts else 0
        pins = {tg: l for tg, (c, l) in scan.items() if c > 0 and l < horizon // 10}
        if not pins:
            return dict(spec=spec, ok=False, why={'no quiet instruction': 1}, tried=0, secs=0.0)
        tblw = dict(tbl)
        for tg in pins:
            tblw[tg] = None
        tmin = max(pins.values()) + 1
        tcands = [x for x in (0, 1024, 4096, 16384, 65536) if x >= tmin] or [tmin]
    signal.signal(signal.SIGALRM, _alarm)
    signal.alarm(timeout)
    t0 = time.time()
    why = {}
    tried = 0
    best = None
    try:
        for P in candidates(tbl, spec):
            for t in tcands:
                tried += 1
                # polishing: a closure no smaller than the best is useless
                cap = best['nodes'] - 1 if best else MAX_NODES
                res, w = try_params(tbl, P, t, tblw, cap)
                why[w.split(' (')[0]] = why.get(w.split(' (')[0], 0) + 1
                if res is None:
                    continue
                nodes, M = res
                DL, DR, K, Y, X, B, T = P
                if best is None:
                    # the kernel re-runs the search: its cost grows
                    # steeply with the closure (7.4.MB), so spend up to
                    # [polish] more seconds looking for a smaller one
                    signal.alarm(0)
                    signal.alarm(max(1, min(polish, int(timeout - (time.time() - t0)))))
                best = dict(spec=spec, ok=True, DL=[''.join(map(str, w)) for w in DL],
                            DR=[''.join(map(str, w)) for w in DR], K=K, Y=Y, X=X, B=B, T=T, t=t,
                            fuel=8 * nodes + 64, M=M + 8, nodes=nodes, tried=tried,
                            secs=round(time.time() - t0, 1), qh=pins is not None,
                            pins=sorted((q, sy, l) for (q, sy), l in pins.items()) if pins else None)
    except Timeout:
        why['timeout'] = 1
    except (RecursionError, MemoryError):
        why['memory'] = 1
    signal.alarm(0)
    if best:
        return best
    return dict(spec=spec, ok=False, why=why, tried=tried, secs=round(time.time() - t0, 1))


def do_find(a):
    global PMAX
    PMAX = a.pmax
    specs = [l.split()[0] for l in open(a.list) if l.strip() and not l.startswith('#')]
    out = []
    if os.path.exists(a.out):
        out = json.load(open(a.out))
        done = {r['spec'] for r in out}
        specs = [s for s in specs if s not in done]

    def save():
        with open(a.out + '.tmp', 'w') as f:
            json.dump(out, f, indent=0)
        os.replace(a.out + '.tmp', a.out)
    with mp.Pool(a.jobs, initializer=_limit_memory, initargs=(a.mem_gb,), maxtasksperchild=10) as pool:
        scan = read_scan(a.scan) if a.qh else None
        jobs = [(s, a.timeout, scan.get(s, {}) if scan is not None else None, a.polish) for s in specs]
        for i, r in enumerate(pool.imap_unordered(find_one, jobs)):
            out.append(r)
            print('%4d/%d %s %s' % (i + 1, len(specs), r['spec'],
                                    ('OK K=%d Y=%d X=%d T=%d t=%d nodes=%d DR=%s %.0fs' %
                                     (r['K'], r['Y'], r['X'], r['T'], r['t'], r['nodes'], r['DR'], r['secs']))
                                    if r['ok'] else 'no %s (%.0fs)' % (r['why'], r['secs'])), flush=True)
            save()
    save()
    print('%d / %d certified -> %s' % (sum(r['ok'] for r in out), len(out), a.out))


# ---- Coq rendering ----

def coq_word(w):
    return '[' + '; '.join('S' + c for c in w) + ']'


def coq_words(ws):
    return '[' + '; '.join(coq_word(w) for w in ws) + ']'


def coq_par(r):
    """the [mbpar] literal of a find row"""
    return '(MbPar %s %s %d %d %d %d %d)' % (coq_words(r['DL']), coq_words(r['DR']),
                                          r['K'], r['Y'], r['X'], r['B'], r['T'])


def fmt_nat(v):
    if v <= 5000:
        return str(v)
    return '(%s * 1000 + %d)' % (fmt_nat(v // 1000), v % 1000)


def call_args(r):
    """[mb_tier_tr tm] arguments: P t fuel M"""
    return '%s %s %s %d' % (coq_par(r), fmt_nat(r['t']), fmt_nat(r['fuel']), r['M'])


def coq_lf(pins):
    return '[' + '; '.join('((St%s, S%d), %s)' % (chr(65 + q), sy, fmt_nat(l)) for q, sy, l in pins) + ']'


def call_args_qh(r):
    """[mb_tier_qhbtr tm] arguments: lf P t fuel M"""
    return '%s %s' % (coq_lf(r['pins']), call_args(r))


PROBE_HEADER = '''From Coq Require Import Arith List.
From BBB4 Require Import BBB4_Statement BBBT4_Statement.
From BBB4.CensusTr Require Import RepWLMBTr.
Import ListNotations.
'''


def do_probe(a):
    from gen_walk_shards import tm_lambda
    rs = [r for r in json.load(open(a.src)) if r['ok']]
    with open(a.out, 'w') as f:
        f.write(PROBE_HEADER)
        for i, r in enumerate(rs):
            f.write('\n(* %s  nodes=%d *)\n' % (r['spec'], r['nodes']))
            f.write(tm_lambda('tm_%03d' % i, r['spec']) + '\n')
            if r.get('qh'):
                f.write('Time Eval vm_compute in mb_tier_qhbtr tm_%03d %s.\n' % (i, call_args_qh(r)))
            else:
                f.write('Time Eval vm_compute in mb_tier_tr tm_%03d %s.\n' % (i, call_args(r)))
    print('%d rows -> %s' % (len(rs), a.out))


def main():
    ap = argparse.ArgumentParser()
    sp = ap.add_subparsers(dest='cmd', required=True)
    p = sp.add_parser('find'); p.add_argument('out'); p.add_argument('--list', required=True)
    p.add_argument('--jobs', type=int, default=4); p.add_argument('--timeout', type=int, default=300)
    p.add_argument('--mem-gb', type=float, default=2)
    p.add_argument('--polish', type=int, default=60, help='seconds spent after a hit looking for a smaller closure')
    p.add_argument('--pmax', type=int, default=16, help='longest block period in the word lists')
    p.add_argument('--qh', action='store_true', help='the wrapped (quasihalting) tier; needs --scan')
    p.add_argument('--scan', default=os.path.join(REPO, 'censustr_v9_scan_1e8.txt'))
    p = sp.add_parser('probe'); p.add_argument('src'); p.add_argument('out')
    a = ap.parse_args()
    {'find': do_find, 'probe': do_probe}[a.cmd](a)


if __name__ == '__main__':
    main()
