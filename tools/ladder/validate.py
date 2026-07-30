#!/usr/bin/env python3
"""UNTRUSTED differential validation: every proven rule is re-checked against
the RAW simulator on concrete instances, sharing no replay code with the
engine.  A rule that fails here is a bug in the engine, full stop.

For a local rule (MARKER-bounded), the instance is embedded in a random
concrete context; the raw run must reach the rule's predicted rhs within a
step budget, and must not have consumed cells beyond the window (checked by
context-invariance: two different contexts produce the same local result)."""

import random

from engine import Expr, MARKER, cfg_counts, cfg_with_counts


def cells_of_side(runs, env, ctx):
    """Concrete cell list (nearest-first) for one side; MARKER expands to
    the context cells ctx."""
    out = []
    for w, e in runs:
        if w == MARKER:
            out.extend(ctx)
            continue
        n = e.subst(env)
        assert n.is_const()
        out.extend(list(w) * n.c)
    return out


def raw_run(tm, q, h, Lc, Rc, max_steps=200000):
    """Raw simulator; the region extends into implicit blanks as the head
    roams.  Tape dict; head at 0; L cells at -1.. ; R cells at +1.."""
    tape = {}
    for i, s in enumerate(Lc):
        tape[-1 - i] = s
    for i, s in enumerate(Rc):
        tape[1 + i] = s
    tape[0] = h
    pos = 0
    lo, hi = min(-len(Lc), 0), max(len(Rc), 0)
    for t in range(max_steps):
        yield t, q, pos, tape, lo, hi
        tr = tm.get((q, tape.get(pos, 0)))
        if tr is None:
            return
        w, d, q2 = tr
        tape[pos] = w
        pos += d
        q = q2
        lo = min(lo, pos)
        hi = max(hi, pos)


def check_rule(tm, rule, tries=3, ctx_len=6, max_steps=5000):
    """Instantiate rule vars concretely (lb, lb+1, lb+3), embed in random
    contexts, and require the raw run to reach the predicted rhs."""
    rng = random.Random(1234)
    varset = set()
    for e in cfg_counts(rule.lhs):
        varset |= set(e.v)
    for trial in range(tries):
        env = {v: Expr(rule.lbs.get(v, 1) + [0, 1, 3][trial % 3])
               for v in varset}
        ctxL = [rng.randint(0, 1) for _ in range(ctx_len)]
        ctxR = [rng.randint(0, 1) for _ in range(ctx_len)]
        q, h, L, R = rule.lhs
        Lc = cells_of_side(L, env, ctxL)
        Rc = cells_of_side(R, env, ctxR)
        # bulk-application semantics: dec drains to lb-1; a single
        # application is rhs as written.  Validate ONE application.
        rq, rh, RL, RR = rule.rhs
        wantL = cells_of_side(RL, env, ctxL)
        wantR = cells_of_side(RR, env, ctxR)
        ok = False
        for t, cq, pos, tape, lo, hi in raw_run(tm, q, h, Lc, Rc, max_steps):
            if t == 0:
                continue
            if cq != rq or tape.get(pos, 0) != rh:
                continue
            gotL = [tape.get(pos - 1 - i, 0) for i in range(pos - lo)]
            gotR = [tape.get(pos + 1 + i, 0) for i in range(hi - pos)]
            # compare up to trailing blanks
            def trim(x):
                x = list(x)
                while x and x[-1] == 0:
                    x.pop()
                return x
            if trim(gotL) == trim(wantL) and trim(gotR) == trim(wantR):
                ok = True
                break
        if not ok:
            return False
    return True


def check_ladder(tm, rules):
    bad = []
    for ru in rules:
        if not check_rule(tm, ru):
            bad.append(ru.name)
    return bad
