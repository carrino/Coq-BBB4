#!/usr/bin/env python3
"""MP: blc4/learn4.py's language with the far end learned from a LONG run
(UNTRUSTED; SCOPING_INSTR.md §7.4.MP).

learn4 reads F and the END table from the anchors of the first 4M steps.  On
the ratio-4 multi-cell lists the far end (b_k and the end word after it)
keeps taking new forms until ~30-80M steps: every carry that reaches it
leaves a new one.  An exploration whose END table misses a form the machine
builds cannot fold its right window back into a tail at all, and the window
then holds the whole list (BLC4/BLC5's "too many families").  Here the END
table is completed from `asnap` (one anchor per far-end change, to T_LONG
steps), and F gains the core transitions those lists take.
"""
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, '..'))
sys.path.insert(0, os.path.join(HERE, '..', 'blc3'))
sys.path.insert(0, os.path.join(HERE, '..', 'blc4'))
import learn3 as L3                                 # noqa: E402
import learn4 as L4                                 # noqa: E402
import lg4                                          # noqa: E402
import ti_batch as T                                # noqa: E402

T_LONG = int(os.environ.get('MP_TLONG', '300000000'))
FARW = int(os.environ.get('MP_FARW', '60'))
ASNAP = os.path.join(os.environ.get('MP_BIN', '/tmp'), 'mp_asnap')


def asnap_bin():
    if not os.path.exists(ASNAP):
        subprocess.check_call(['cc', '-O2', '-o', ASNAP, os.path.join(HERE, 'asnap.c')])
    return ASNAP


def far_anchors(spec, mir, t0=50000, t1=None):
    side = 'R' if mir else 'L'
    out = subprocess.run([asnap_bin(), spec, side, str(t0), str(t1 or T_LONG), str(FARW)],
                         capture_output=True, text=True, timeout=3600).stdout
    rows = [L4.Row(line) for line in out.splitlines()]
    if mir:
        rows = [L4.mirror_row(r) for r in rows]
    return rows


def fit_local(data, M):
    """learn4.fit_F's replacement: the LOCAL language of the anchor lists.  A
    state is the symbol read last (b_0's start state ('b0', 0) before the
    first); a transition is a pair of consecutive symbols some anchor list
    has.  On the multi-cell ratio-4 lists every element cycles through a
    few phases (separator word and spelling), and the digit is a function
    of the phases: the pairs saturate early (128 by 1M steps on
    0RB0LD_1RC1LB_1LA1RA_1LA0LD, none new to 16M), while the bounded
    partial sum over-approximates them by far."""
    q0 = ('b0', 0)
    fwd = {}
    end = {}
    for syms, bk, endw in data:
        q = q0
        for x in syms[:len(syms) - M]:
            q2 = ('g', x)
            fwd[(q, x)] = q2
            q = q2
        end.setdefault(q, set()).add((tuple(syms[len(syms) - M:]), bk, endw))
    return dict(m=0, cen={}, lo=0, hi=0, fwd=fwd, end=end, q0=q0, M=M)


def fit_free(data, M):
    """learn4.fit_F's replacement: the FREE language over the anchor lists'
    symbols (b_0's symbols first, then any interior symbol, any end after
    any symbol): one state, no ordering constraint at all"""
    q0, S = ('b0', 0), ('g', 0)
    fwd, end = {}, {}
    for syms, bk, endw in data:
        core = syms[:len(syms) - M]
        for i, x in enumerate(core):
            fwd[(q0 if i == 0 else S, x)] = S
    ends = set((tuple(syms[len(syms) - M:]), bk, endw) for syms, bk, endw in data)
    for q in (q0, S):
        end[q] = set(ends)
    return dict(m=0, cen={}, lo=0, hi=0, fwd=fwd, end=end, q0=q0, M=M)


def learn_free(spec):
    old = L4.fit_F
    L4.fit_F = fit_free
    try:
        return L4.learn(spec)
    finally:
        L4.fit_F = old


def learn_local(spec):
    """learn4.learn with F the local language (fit_local)"""
    old = L4.fit_F
    L4.fit_F = fit_local
    try:
        return L4.learn(spec)
    finally:
        L4.fit_F = old


def extend(spec, lang, mir, info, t1=None):
    """lang with the END entries (and F transitions) of the long run's
    far-end forms added; returns (lang, stats)"""
    W, a = lang.unit, lang.a
    pseps = list(lang.psepsR) if len(W) == 1 else []
    seps = set(lang.seps)
    fwd = dict(lang.fwd)
    end = {q: list(l) for q, l in lang.end4.items()}
    M = info.get('M', 1)
    nnew_e = nnew_f = nbad = 0
    nnew_t = [0]
    LOCAL_ADD = info.get('F') == 'local'
    for r in far_anchors(spec, mir, t1=t1):
        cells = L3.strip_cells(r[6])
        rl = L4.read_list(cells, W, pseps, a, seps)
        if rl is None:
            nbad += 1
            continue
        syms, bk, endw = rl[:3]
        if len(syms) < M:
            nbad += 1
            continue
        q = lang.q0
        ok = True
        for x in syms[:len(syms) - M]:
            q2 = fwd.get((q, x))
            if q2 is None and LOCAL_ADD and (q == lang.q0 or q[0] == 'g'):
                # a local F: the long run's new pairs are new transitions
                q2 = fwd[(q, x)] = ('g', x)
                nnew_t[0] += 1
            if q2 is None:
                ok = False
                break
            q = q2
        if not ok:
            nnew_f += 1
            continue
        tail = syms[len(syms) - M:]
        # M = 1 only (expand_end makes longer tails single-symbol ends)
        if M != 1:
            nbad += 1
            continue
        ent = (tail[-1], bk, endw)
        if ent not in end.setdefault(q, []):
            end[q].append(ent)
            nnew_e += 1
    lang2 = lg4.Lang4(a, W, fwd, end, lang.q0, lang.lfwd, lang.lstart, sorted(seps, key=str),
                      lends=lang.lends, unitL=lang.unitL, sepsL=lang.sepsL,
                      psepsR=lang.psepsR, psepsL=lang.psepsL, lend_blank=lang.lend_blank)
    return lang2, dict(new_end=nnew_e, f_miss=nnew_f, unparsed=nbad, new_trans=nnew_t[0],
                       nendw=len(lang2.endws))
