#!/usr/bin/env python3
"""UNTRUSTED reader for the `no anchor` bucket: the WALL-INDEXED bouncer.

Every other reader in this directory asks the same question -- "does the
machine REST in a decodable digit word, and is there an anchor family
`Cc p = (q, E p ++ tail, S0, far)`?"  Eight waves of anchor enumeration
(`emit_lapcert.anchors`, `restscan`'s tolerant reader over every alphabet x
tail split x far, `regscan`'s chase) answer NO on all 19 rows of this bucket,
which is why it is called `no anchor`.

John's read of `0RB0LD_1LA1LC_0LD0LC_1RD1RB` says why:

    "keeps bouncing back and forth with c and d states.  then when it passes
     the wall on the right it moves the wall over one and heads back left and
     then goes back to bouncing"

THE COUNTER IS NOT A WORD, IT IS THE WALL POSITION.  So this file measures
the only things that are actually there:

  * TURNAROUNDS -- every step at which the head reverses direction, with its
    column and state.  A bouncer is a turnaround sequence, nothing else.
  * FRONTIERS -- the leftmost/rightmost column ever visited, and the times at
    which each advances.  The frontier that advances RARELY is the macro
    index; the one that advances every bounce is the micro one.
  * The WALL -- the turnaround column that moves monotonically by a fixed
    step.  John's read predicts exactly one cell per cycle; that is measured
    here, not assumed.
  * CYCLE LENGTHS -- fitted affine and quadratic in the wall index.  A plain
    bouncer is affine (`MeasureGlue` not needed, `WrapBouncer`'s explicit
    induction suffices); a bouncer COUNTER is not, and the region between the
    walls carries its own count.
  * The two turnaround CONFIGURATIONS as an sside family in the WALL INDEX
    k -- `pre ++ rep u k ++ post` -- fitted by exact insertion-point search
    over consecutive members, never guessed from an alphabet table.

Nothing here decides anything.  The measurement half emits no Coq; the
`--emit` half renders `BNC_*` boards against `theories/Counters/BounceGlue.v`
and the Coq kernel re-runs every lap, so a wrong reading fails to compile
rather than proving a wrong theorem.

  bouncecert.py --all                 the bucket table (the deliverable)
  bouncecert.py --spec S --turns      turnaround table
  bouncecert.py --spec S --cycles     bounce cycles, wall column, costs
  bouncecert.py --spec S --macro      macro phases and their laws
  bouncecert.py --spec S --family     the sside family in the wall index
  bouncecert.py --spec S --anchors    the macro anchor (solid block) per phase
  bouncecert.py --spec S --all-views  all four, in order
  bouncecert.py --emit [--spec S]     render + compile the BNC_* boards
"""
import argparse
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, '..', '..'))
sys.path.insert(0, HERE)

# IMPORTED, never edited (see the wave prompt): the machine id and the coqc
# driver come from the lapcert emitter so a board named here is named the same
# way every other wave names it.
from emit_lapcert import mach_id, coqc                              # noqa: E402,F401
from mirror_common import mirror_spec                               # noqa: E402,F401

LAB = 'ABCD'

# The whole `no anchor` bucket, 19 rows.
BUCKET = """
0RB0LD_1LA1LC_0LD0LC_1RD1RB   0RB0RB_1LA1LC_0LD0LC_1RD1RB
0RB0RD_1LC1RB_1RA0LC_1LB0LC   0RB0RD_1LC1RB_1RA0LC_1LD0LC
0RB1LA_1LA1LC_0LD0LC_1RD1RB   0RB1LB_1LC1RC_1RD0LA_0RC1RB
0RB1LC_1LC0RD_1RD0LC_1LA1RB   0RB1LC_1LC1RD_1LA0LC_0RD1RB
0RB1RC_1RC0LB_0RD0RC_1LD1LA   1RB---_1LC0RB_1LD1RB_1LC1RB
1RB---_1LC1RD_1LB1RD_1LB0RD   1RB---_1LC1RD_1LB1RD_1LC0RD
1RB0RB_1LC0RC_1RA0LD_0LB0LC   1RB0RB_1LC1LD_0LC1RA_0LD0RA
1RB0RD_1LC0LB_1LD0LB_1RD0RA   1RB0RD_1LC0LC_1LD0LB_1RD0RA
1RB1LB_1LC0RD_0LB1LA_0LA1RA   1RB1LD_1RC1RB_1LC1LA_0RC0RD
1RB1RD_1RC0LD_1LB0RA_1LC0LC
""".split()


# ------------------------------------------------------------------ replay ---

def parse(spec):
    """(state, symbol) -> (write, dir, next) with dir in {+1,-1}; None = halt."""
    tab = {}
    for si, part in enumerate(spec.split('_')):
        for yi in range(2):
            e = part[3 * yi:3 * yi + 3]
            tab[(si, yi)] = None if e == '---' else (
                int(e[0]), +1 if e[1] == 'R' else -1, ord(e[2]) - ord('A'))
    return tab


class Replay:
    """A blank-tape replay that keeps the whole trajectory.

    [pos], [st] and the frontier pair are recorded per step; the tape is kept
    live so a configuration can be cut at any recorded time by re-running --
    which is cheap at the step budgets here and keeps the memory flat."""

    def __init__(self, spec, steps):
        self.spec, self.tab, self.steps = spec, parse(spec), steps
        self.pos = [0]
        self.st = [0]
        self.lo = [0]
        self.hi = [0]
        self.wr = []                  # (t, col) of every WRITE
        tape, p, q, lo, hi = {}, 0, 0, 0, 0
        self.halted = False
        for _ in range(steps):
            tr = self.tab.get((q, tape.get(p, 0)))
            if tr is None:
                self.halted = True
                break
            w, d, nq = tr
            tape[p] = w
            self.wr.append((len(self.pos) - 1, p))
            p += d
            q = nq
            lo, hi = min(lo, p), max(hi, p)
            self.pos.append(p)
            self.st.append(q)
            self.lo.append(lo)
            self.hi.append(hi)
        self.n = len(self.pos) - 1

    def conf_at(self, t, lo=None, hi=None):
        """(state, left-nearest-first, head, right) at time [t], blank-trimmed."""
        tape, p, q = {}, 0, 0
        for _ in range(t):
            tr = self.tab[(q, tape.get(p, 0))]
            w, d, nq = tr
            tape[p] = w
            p += d
            q = nq
        lo = self.lo[t] if lo is None else lo
        hi = self.hi[t] if hi is None else hi
        L = [tape.get(i, 0) for i in range(p - 1, lo - 1, -1)]
        R = [tape.get(i, 0) for i in range(p + 1, hi + 1)]
        while L and L[-1] == 0:
            L.pop()
        while R and R[-1] == 0:
            R.pop()
        return (q, tuple(L), tape.get(p, 0), tuple(R))


# ------------------------------------------------------------- turnarounds ---

def turnarounds(R):
    """Every direction reversal: (t, col, state, 'R'|'L').

    'R' = the head was moving right and now moves left (a RIGHT turnaround)."""
    out = []
    for i in range(1, R.n):
        d0 = R.pos[i] - R.pos[i - 1]
        d1 = R.pos[i + 1] - R.pos[i]
        if d0 * d1 < 0:
            out.append((i, R.pos[i], LAB[R.st[i]], 'R' if d0 > 0 else 'L'))
    return out


def frontier_events(R):
    """(t, side, col) each time a frontier advances; side in {'L','R'}."""
    out = []
    for t in range(1, R.n + 1):
        if R.hi[t] > R.hi[t - 1]:
            out.append((t, 'R', R.hi[t]))
        if R.lo[t] < R.lo[t - 1]:
            out.append((t, 'L', R.lo[t]))
    return out


def frontier_runs(R):
    """Frontier events grouped into SWEEPS: (t_start, t_end, side, from, to)."""
    ev = frontier_events(R)
    runs = []
    for t, side, col in ev:
        if runs and runs[-1][2] == side and runs[-1][1] == t - 1:
            runs[-1] = (runs[-1][0], t, side, runs[-1][3], col)
        else:
            runs.append((t, t, side, col, col))
    return runs


# -------------------------------------------------------------------- fits ---

def fit_affine(ks, ys):
    """(a, b) with y = a*k + b exactly, or None.  [ks] need not be contiguous."""
    if len(ks) < 3:
        return None
    d = ks[1] - ks[0]
    if d == 0:
        return None
    num = ys[1] - ys[0]
    if num % d:
        return None
    a = num // d
    b = ys[0] - a * ks[0]
    return (a, b) if all(y == a * k + b for k, y in zip(ks, ys)) else None


def fit_quad(ks, ys):
    """(a, b, c) with 2*y = a*k^2 + b*k + c exactly, or None (halved so a
    half-integer leading coefficient -- the triangular cost of a bouncer --
    is still an EXACT fit and not a rounding)."""
    if len(ks) < 4:
        return None
    import itertools
    (k0, k1, k2), (y0, y1, y2) = ks[:3], ys[:3]
    # solve exactly over the rationals with integer arithmetic
    A = [[k0 * k0, k0, 1], [k1 * k1, k1, 1], [k2 * k2, k2, 1]]
    det = (A[0][0] * (A[1][1] * A[2][2] - A[1][2] * A[2][1])
           - A[0][1] * (A[1][0] * A[2][2] - A[1][2] * A[2][0])
           + A[0][2] * (A[1][0] * A[2][1] - A[1][1] * A[2][0]))
    if det == 0:
        return None
    Y = [2 * y0, 2 * y1, 2 * y2]
    sol = []
    for j in range(3):
        M = [row[:] for row in A]
        for i in range(3):
            M[i][j] = Y[i]
        d = (M[0][0] * (M[1][1] * M[2][2] - M[1][2] * M[2][1])
             - M[0][1] * (M[1][0] * M[2][2] - M[1][2] * M[2][0])
             + M[0][2] * (M[1][0] * M[2][1] - M[1][1] * M[2][0]))
        if d % det:
            return None
        sol.append(d // det)
    a, b, c = sol
    del itertools
    return (a, b, c) if all(2 * y == a * k * k + b * k + c
                            for k, y in zip(ks, ys)) else None


def law(ks, ys):
    """A one-line description of the best exact law, or 'none'."""
    if len(set(ys)) == 1:
        return 'const %d' % ys[0]
    f = fit_affine(ks, ys)
    if f:
        return '%dk%+d' % f
    q = fit_quad(ks, ys)
    if q:
        a, b, c = q
        h = lambda n: ('%d' % (n // 2)) if n % 2 == 0 else ('%d/2' % n)
        return '(%s)k^2%+dk/2%+dk^0/2' % (h(a), b, c) if (b % 2 or c % 2) \
            else '%sk^2%+dk%+d' % (h(a), b // 2, c // 2)
    return 'none'


def _grow_fit(seq):
    """`s_k = pre ++ rep u k ++ post` for a GROWING family, or None."""
    d = len(seq[1]) - len(seq[0])
    if d <= 0 or any(len(seq[i + 1]) - len(seq[i]) != d
                     for i in range(len(seq) - 1)):
        return None
    base = seq[0]
    for i in range(len(base) + 1):
        u = seq[1][i:i + d]
        if all(seq[j + 1] == seq[j][:i] + u + seq[j][i:]
               for j in range(len(seq) - 1)):
            return (base[:i], u, base[i:])
    return None


def sside_fit(seq):
    """Fit a family of tuples as `pre ++ rep u k ++ post` in the WALL index.

    Exact insertion-point search: [u] must be a block whose repeated insertion
    at ONE position turns every member into the next.  No alphabet is assumed
    and no rotation is preferred -- the FIRST insertion point that works for
    the whole family is returned, and every one of them denotes the same set
    of tapes.

    A SHRINKING side is the same fact read from the other end (`rep u (m-k)`),
    which is what the far side of a bouncer does while the near side grows, so
    it is fitted too and reported with its own index.  Returns
    (pre, u, post, sense) with sense in {'k', 'm-k'}, or None."""
    if len(seq) < 3:
        return None
    f = _grow_fit(seq)
    if f:
        return f + ('k',)
    f = _grow_fit(seq[::-1])
    if f:
        return f + ('m-k',)
    return None


def cell(s):
    return ''.join(str(c) for c in s) if s else '()'


# ------------------------------------------------------------ bounce cycles ---

def cycles(R, T=None):
    """One BOUNCE CYCLE per consecutive turnaround pair.

    Returns (i, tL, colL, stL, tR, colR, stR, length) with the LEFT turnaround
    first; [length] is the step count from this left turnaround to the next."""
    T = turnarounds(R) if T is None else T
    out = []
    for i in range(len(T) - 1):
        if T[i][3] == 'L' and T[i + 1][3] == 'R':
            nxt = T[i + 2][0] if i + 2 < len(T) else None
            out.append((T[i][0], T[i][1], T[i][2],
                        T[i + 1][0], T[i + 1][1], T[i + 1][2],
                        (nxt - T[i][0]) if nxt is not None else None))
    return out


def regimes(cyc):
    """Segment a phase's bounce cycles by their per-cycle COLUMN STEP.

    Consecutive cycles with the same `(colL step, colR step)` are one regime.
    This is a measured segmentation with no threshold in it, and on John's
    exemplar it separates the two things that are visibly different on the
    tape -- the 3-step drift ripple `(-1,-1)` and the bounce proper
    `(-2,+1)` -- without either being named in advance.

    Returns [(i0, n, dL, dR, [lengths])]."""
    if len(cyc) < 2:
        return []
    out = []
    for i in range(len(cyc) - 1):
        dL = cyc[i + 1][1] - cyc[i][1]
        dR = cyc[i + 1][4] - cyc[i][4]
        if out and out[-1][2] == dL and out[-1][3] == dR:
            out[-1][1] += 1
            out[-1][4].append(cyc[i][6])
        else:
            out.append([i, 1, dL, dR, [cyc[i][6]]])
    return [tuple(r) for r in out]


def classify(costs):
    """Read the shape of ONE phase's cycle-cost sequence.

    Returns (kind, ndrift, law, tail_costs).  The split point is measured, not
    chosen: a bouncer's phase opens with a constant-cost DRIFT (the head
    walking the block at a fixed steps-per-cell) and then bounces with a cost
    that grows by a fixed amount per cell of wall travel.

      'affine'       the whole phase is one affine cost law
      'drift+affine' a constant prefix, then one affine law -- still a PLAIN
                     bouncer: the wall index alone determines the cost
      'const'        every cycle costs the same
      'irregular'    no such split -- the region between the walls carries its
                     own count, i.e. a bouncer COUNTER"""
    cs = [c for c in costs if c is not None]
    if len(cs) < 4:
        return ('short', 0, '-', cs)
    if len(set(cs)) == 1:
        return ('const', 0, 'const %d' % cs[0], cs)
    ks = list(range(len(cs)))
    if fit_affine(ks, cs):
        return ('affine', 0, law(ks, cs), cs)
    # The LONGEST affine SUFFIX, found by search rather than by assuming the
    # prologue's shape.  The last cycle of a phase straddles the frontier
    # advance, so it may be dropped -- that one only.
    for d in range(1, max(1, len(cs) - 3)):
        for tail, drop in ((cs[d:], 0), (cs[d:-1], 1)):
            if len(tail) >= 4 and fit_affine(list(range(len(tail))), tail):
                kind = 'drift+affine' if len(set(cs[:d])) == 1 else 'pro+affine'
                return (kind, d, law(list(range(len(tail))), tail), tail)
    if len(cs) >= 5 and fit_affine(list(range(len(cs) - 1)), cs[:-1]):
        return ('affine', 0, law(list(range(len(cs) - 1)), cs[:-1]), cs[:-1])
    return ('irregular', 0, 'none', cs)


def main_regime(rgs):
    """The regime the phase's TIME is spent in -- not merely the longest run.

    Ranking by run length picks the drift ripple on machines whose bounce is a
    single long sweep per visit; ranking by total cost picks the bounce.  Ties
    (a genuine uniform bounce) fall to the longer run."""
    cand = [r for r in rgs if len(set(r[4])) > 1]
    if not cand:
        cand = list(rgs)
    if not cand:
        return None
    return max(cand, key=lambda r: (sum(x for x in r[4] if x), r[1]))


def wall_of(rg):
    """The WALL side of a regime: the turnaround column that moves by exactly
    one cell per cycle (John's read), reported with its measured step."""
    if rg is None:
        return (None, None)
    dL, dR = rg[2], rg[3]
    if abs(dR) == 1 and abs(dL) != 1:
        return ('R', dR)
    if abs(dL) == 1 and abs(dR) != 1:
        return ('L', dL)
    if abs(dR) == 1:
        return ('R', dR)
    if abs(dL) == 1:
        return ('L', dL)
    return ('R' if abs(dR) <= abs(dL) else 'L', dR if abs(dR) <= abs(dL) else dL)


def macro_phases(R):
    """Segment the run by advances of the SLOW frontier.

    Returns (side, [(t_start, t_end, frontier_col, nturn, nsteps)]).  The slow
    frontier is the macro index: John's "moves the wall over one" happens once
    per phase, the bounces happen many times inside it.

    A side that never advances (a FIXED wall -- several rows here bounce off a
    permanent wall rather than a moving one) is not a candidate; when only one
    frontier advances at all, that one is the index and the machine is
    single-level, which [levels] reports."""
    runs = frontier_runs(R)
    cand = [s for s in ('R', 'L') if sum(1 for r in runs if r[2] == s) >= 3]
    if not cand:
        return (None, [])
    side = min(cand, key=lambda s: sum(1 for r in runs if r[2] == s))
    marks = [r for r in runs if r[2] == side]
    T = turnarounds(R)
    out = []
    for a, b in zip(marks, marks[1:]):
        t0, t1 = a[0], b[0]
        nt = sum(1 for t in T if t0 <= t[0] < t1)
        out.append((t0, t1, a[4], nt, t1 - t0))
    return (side, out)


def levels(R, C=None, ph=None):
    """1 if the slow frontier advances once per bounce (the wall IS the
    frontier -- a single-level bouncer), 2 if a phase holds many bounces."""
    C = cycles(R) if C is None else C
    ph = macro_phases(R)[1] if ph is None else ph
    if not ph or not C:
        return 1
    per = sum(len(phase_cycles(R, i, C, ph)) for i in range(len(ph))) / len(ph)
    return 1 if per <= 1.5 else 2


# ------------------------------------------------------------------- views ---

def view_turns(spec, R, n):
    T = turnarounds(R)
    print('== turnarounds (first %d of %d) ==' % (min(n, len(T)), len(T)))
    print('   i      t   col  st  dir   dcol   dt')
    prev = None
    for i, (t, c, q, d) in enumerate(T[:n]):
        print('%4d %6d %5d   %s   %s %6s %5s'
              % (i, t, c, q, d,
                 '' if prev is None else c - prev[1],
                 '' if prev is None else t - prev[0]))
        prev = (t, c)


def view_cycles(spec, R, n):
    C = cycles(R)
    print('== bounce cycles (first %d of %d) ==' % (min(n, len(C)), len(C)))
    print('   i    tL   colL st    tR   colR st   len')
    for i, c in enumerate(C[:n]):
        print('%4d %6d %5d  %s %6d %5d  %s %5s'
              % (i, c[0], c[1], c[2], c[3], c[4], c[5],
                 '' if c[6] is None else c[6]))


def phase_cycles(R, pi, C=None, ph=None):
    C = cycles(R) if C is None else C
    ph = macro_phases(R)[1] if ph is None else ph
    t0, t1 = ph[pi][0], ph[pi][1]
    return [c for c in C if t0 <= c[0] < t1]


def view_macro(spec, R, n):
    side, ph = macro_phases(R)
    C = cycles(R)
    print('== macro phases (slow frontier = %s; %d complete) ==' % (side, len(ph)))
    print('   i      t0     t1  frontier  nturn  nsteps   regimes'
          '  (n x dcolL/dcolR : cost law)')
    for i, p in enumerate(ph[:n]):
        rgs = regimes(phase_cycles(R, i, C, ph))
        desc = '  '.join(
            '%dx(%+d,%+d):%s' % (r[1], r[2], r[3],
                                 law(list(range(len(r[4]))), r[4])
                                 if all(x is not None for x in r[4]) else '?')
            for r in rgs[:4])
        print('%4d %7d %6d %9d %6d %7d   %s'
              % (i, p[0], p[1], p[2], p[3], p[4], desc))
    if len(ph) < 3:
        return
    ks = list(range(len(ph)))
    print('   frontier law: %s' % law(ks, [p[2] for p in ph]))
    print('   nturn    law: %s' % law(ks, [p[3] for p in ph]))
    print('   nsteps   law: %s' % law(ks, [p[4] for p in ph]))
    rg = main_regime(regimes(phase_cycles(R, len(ph) - 2, C, ph)))
    ws, wd = wall_of(rg)
    if rg is None:
        print('   VERDICT: no non-constant regime inside a macro phase')
        return
    lens = [x for x in rg[4] if x is not None]
    cl = law(list(range(len(lens))), lens)
    print('   main regime: %d cycles, colL %+d/cycle, colR %+d/cycle'
          % (rg[1], rg[2], rg[3]))
    print('   wall = %s turnaround, %+d cell(s) per cycle%s'
          % (ws, wd, '  (John\'s read)' if abs(wd) == 1 else ''))
    print('   cycle cost in the wall index: %s' % cl)
    print('   VERDICT: %s' % (
        'PLAIN BOUNCER -- cost affine in the wall index'
        if fit_affine(list(range(len(lens))), lens) else
        'BOUNCER COUNTER -- the region between the walls carries its own count'))


def view_family(spec, R, n, maxk=9):
    """The two turnaround configurations as an sside family in the WALL index.

    Fitted inside ONE macro phase and inside its MAIN regime, because that is
    where a wall index exists: the wall runs from its phase-start value up to
    the frontier, one cell per cycle."""
    side, ph = macro_phases(R)
    C = cycles(R)
    print('== turnaround families, indexed by the WALL, inside one macro phase ==')
    if len(ph) < 3:
        print('   (fewer than 3 macro phases in the budget -- nothing to index)')
        return
    for pi in (len(ph) - 3, len(ph) - 2):
        pc = phase_cycles(R, pi, C, ph)
        rg = main_regime(regimes(pc))
        if rg is None or rg[1] < 3:
            print('   phase %d: main regime too short to fit' % pi)
            continue
        ins = pc[rg[0]:rg[0] + rg[1] + 1]
        print('   -- phase %d, main regime: %d cycles from t=%d, (%+d,%+d) --'
              % (pi, rg[1], ins[0][0], rg[2], rg[3]))
        for nm, tix in (('L', 0), ('R', 3)):
            cf = [R.conf_at(c[tix]) for c in ins[:maxk]]
            qs = {c[0] for c in cf}
            print('      %s-turn state(s): %s' % (
                nm, ''.join(sorted(LAB[q] for q in qs))))
            for j, c in enumerate(cf[:5]):
                print('        k=%d  %s  %s [%s] %s' % (
                    j, LAB[c[0]], cell(c[1][::-1]), c[2], cell(c[3])))
            for lab, seq in (('left ', [c[1] for c in cf]),
                             ('right', [c[3] for c in cf])):
                f = sside_fit(seq)
                if f:
                    print('        %s = %s ++ rep %s (%s) ++ %s'
                          % (lab, cell(f[0]), cell(f[1]), f[3], cell(f[2])))
                else:
                    print('        %s : no single-insertion sside family' % lab)


# ------------------------------------------------------------------ summary ---

def window(R, C=None, ph=None):
    """The stretch of bounce cycles the wall index is read off.

    Two-level machines: the bounces inside one late macro phase.  Single-level
    machines: the whole run past its boot (the last two thirds), because there
    the wall IS the frontier and there is no inner phase to sit in."""
    C = cycles(R) if C is None else C
    ph = macro_phases(R)[1] if ph is None else ph
    if levels(R, C, ph) == 2 and len(ph) >= 3:
        return ('phase %d' % (len(ph) - 2), phase_cycles(R, len(ph) - 2, C, ph))
    return ('global', C[len(C) // 3:]) if C else ('global', [])


def analyse(spec, steps, R=None):
    R = Replay(spec, steps) if R is None else R
    T = turnarounds(R)
    mside, ph = macro_phases(R)
    C = cycles(R)
    row = dict(spec=spec, R=R, nturn=len(T), halted=R.halted, macro=mside,
               nphase=len(ph), lev=levels(R, C, ph), wall=None, wstep=None,
               kind='?', frontier_law='-', nturn_law='-', nstep_law='-',
               cost_law='-', nmain=0, famL='-', famR='-', states='',
               win='-', rgs=[], main=None, ins=[], shape='-', ndrift=0,
               cover=0)
    if len(ph) >= 3:
        ks = list(range(len(ph)))
        row['frontier_law'] = law(ks, [p[2] for p in ph])
        row['nturn_law'] = law(ks, [p[3] for p in ph])
        row['nstep_law'] = law(ks, [p[4] for p in ph])
    row['win'], pc = window(R, C, ph)
    row['rgs'] = regimes(pc)
    # THE verdict: the phase's own cycle-cost sequence, split at its measured
    # drift/bounce boundary.  A regime is a column-step fact; this is the cost
    # fact the task asks for, and the two are read independently.
    shape, ndrift, clw, tail = classify([c[6] for c in pc])
    row['shape'], row['ndrift'], row['cost_law'] = shape, ndrift, clw
    # COVERAGE, not merely existence: an affine suffix that accounts for a few
    # per cent of the phase's steps is a tail wagging a dog.  A plain bouncer
    # spends its phase in the bounce.
    tot = sum(c[6] for c in pc if c[6]) or 1
    row['cover'] = sum(tail) * 100 // tot if tail else 0
    row['kind'] = ('plain'
                   if shape in ('affine', 'drift+affine', 'pro+affine', 'const')
                   and row['cover'] >= 60 else 'counter')
    bounce = pc[ndrift:]
    rg = main_regime(regimes(bounce)) or main_regime(row['rgs'])
    row['main'] = rg
    if rg is None:
        return row
    row['wall'], row['wstep'] = wall_of(rg)
    row['nmain'] = len(bounce) if shape != 'irregular' else rg[1]
    if shape in ('affine', 'drift+affine'):
        ins = bounce[:9]
    else:
        ins = pc[rg[0]:rg[0] + rg[1] + 1][:9]
    row['ins'] = ins
    if len(ins) >= 3:
        cfL = [R.conf_at(c[0]) for c in ins]
        cfR = [R.conf_at(c[3]) for c in ins]
        row['cfL'], row['cfR'] = cfL, cfR
        row['states'] = '%s/%s' % (
            ''.join(sorted({LAB[c[0]] for c in cfL})),
            ''.join(sorted({LAB[c[0]] for c in cfR})))
        for tag, cf in (('L', cfL), ('R', cfR)):
            fl = sside_fit([c[1] for c in cf])
            fr = sside_fit([c[3] for c in cf])
            row['fam' + tag] = '%s / %s' % (
                ('%s|%s(%s)|%s' % (cell(fl[0]), cell(fl[1]), fl[3],
                                   cell(fl[2]))) if fl else 'no',
                ('%s|%s(%s)|%s' % (cell(fr[0]), cell(fr[1]), fr[3],
                                   cell(fr[2]))) if fr else 'no')
    return row


def summarise(spec, steps):
    return analyse(spec, steps)


def anchors_of(R, ph=None, n=9):
    """The configuration at each macro-phase boundary.

    THE bucket-wide fact, and the one every anchor enumeration missed: every
    one of the 19 DOES rest, once per macro phase, at a configuration with
    the head just off one end of the written region and NOTHING on the other
    side.  On eight of them the region is a solid block of ones; on the rest
    it carries structure.  Either way it is a legitimate anchor family -- it
    is simply not a digit WORD, so `anchors()`, `restscan` and `regscan`
    (which all decode the rest against an alphabet) cannot express it."""
    ph = macro_phases(R)[1] if ph is None else ph
    out = []
    for p in ph[:n]:
        q, l, h, r = R.conf_at(p[0])
        solid = (set(l) <= {1} and set(r) <= {1} and (not l or not r))
        out.append((p[0], LAB[q], len(l), h, len(r), solid))
    return out


def view_anchors(spec, R, n):
    side, ph = macro_phases(R)
    A = anchors_of(R, ph, n)
    print('== the macro anchor: one rest per phase (slow frontier = %s) =='
          % side)
    print('   i       t  st  |left|  head  |right|  solid block?')
    for i, a in enumerate(A):
        print('%4d %7d   %s %7d %5d %8d  %s'
              % (i, a[0], a[1], a[2], a[3], a[4], 'yes' if a[5] else 'NO'))
    ns = [max(a[2], a[4]) for a in A]
    if len(ns) >= 3:
        print('   block law: %s' % law(list(range(len(ns))), ns))
        print('   blocks: %s' % ', '.join(str(x) for x in ns))
        print('   states: %s' % ''.join(a[1] for a in A))


def view_all(steps):
    hdr = ('%-29s %3s %5s %5s %-9s %4s %5s %5s %6s %-13s %-12s %4s %-8s %-6s'
           % ('spec', 'lv', 'turns', 'phase', 'frontier', 'wall', 'step',
              'pro', 'cycles', 'cost law', 'shape', 'cov%', 'kind', 'states'))
    print(hdr)
    print('-' * len(hdr))
    rows = []
    for spec in BUCKET:
        r = summarise(spec, steps)
        rows.append(r)
        print('%-29s %3d %5d %5d %-9s %4s %5s %5d %6d %-13s %-12s %4d %-8s %-6s'
              % (r['spec'], r['lev'], r['nturn'], r['nphase'],
                 r['frontier_law'], r['wall'], r['wstep'], r['ndrift'],
                 r['nmain'], r['cost_law'], r['shape'], r['cover'], r['kind'],
                 r['states']))
    print()
    print('wall moves by exactly one cell per cycle: %d / %d'
          % (sum(1 for r in rows if r['wstep'] in (1, -1)), len(rows)))
    print('plain bouncers   (cycle cost AFFINE in the wall index): %d'
          % sum(1 for r in rows if r['kind'] == 'plain'))
    print('bouncer counters (cycle cost fits no affine law):       %d'
          % sum(1 for r in rows if r['kind'] == 'counter'))
    print()
    print('== the MACRO ANCHOR: the solid block at each phase boundary ==')
    print('  spec                           st  block law %-24s %s'
          % ('blocks', 'kind + the last one, written out'))
    for r in rows:
        A = anchors_of(r['R'])
        if len(A) < 3:
            print('  %-29s  (fewer than 3 phases)' % r['spec'])
            continue
        ns = [max(a[2], a[4]) for a in A]
        R2 = r['R']
        t = A[-1][0]
        q, l, h, rr = R2.conf_at(t)
        side = cell(l[::-1]) if l else cell(rr)
        print('  %-29s  %-4s %-9s %-24s %s%s'
              % (r['spec'], ''.join(sorted(set(a[1] for a in A))),
                 law(list(range(len(ns))), ns),
                 ', '.join(str(x) for x in ns[:6]),
                 'solid  ' if all(a[5] for a in A) else 'shaped ',
                 side[:34] + ('...' if len(side) > 34 else '')))
    print()
    print('== the wall-indexed turnaround families ==')
    for r in rows:
        print('  %-29s  L: %s' % (r['spec'], r['famL']))
        print('  %-29s  R: %s' % ('', r['famR']))
    return rows


# ------------------------------------------------------------------- emit ---
#
# The ERASE/FILL boards.  A machine is a customer of
# [theories/Counters/BounceGlue.v] when three of its states play the roles
# the reader measured:
#
#   E (eraser)  E1 -> 0 R E      E0 -> 1 L X
#   X, Y        X0 -> 1 L Y      X1 -> 1 R E
#               Y0 -> 1 L X      Y1 -> 1 R E
#
# The ROLES ARE READ OFF THE TABLE, never assigned: [E] is the unique state
# that writes a zero and moves right into itself, and X, Y follow.  Every
# hypothesis is then an [eq_refl] in the board, and the kernel re-checks the
# whole lap.

OUTDIR = os.path.join(REPO, 'theories', 'Machines', 'Counters')
BOARD_PREFIX = 'BNC'

BOARD = r'''(** * @PREF@_@ID@: machine @SPEC@ quasihalts, with bound 1.

    One of the three [1RB---] rows of the residue's `no anchor` bucket.
    [StA]'s [S1] transition is undefined, so [StA] fires once -- at
    configuration index 0 -- and [St@E@], [St@X@], [St@Y@] are CLOSED
    under the table: the machine genuinely QUASIHALTS and never halts, so
    the never-quasihalting tier can only reject it.  The tier it needs is
    [QHBound], via [LapGlueAbs.glue_qh_abs].

    The 3-state core is the ERASE/FILL bouncer of [BounceGlue], and the
    counter is THE WALL POSITION, not a word:

      mkB j = (St@E@, (repeat S0 j ++ [S1], S0, []))

    -- the head on the blank frontier, [j] erased cells behind it, and the
    surviving wall cell at the far end.  [St@E@] sweeps right over ones
    writing zeros; [St@X@] and [St@Y@] sweep back left over the zeros
    writing ones, alternating; the wall turns them around.  One bounce is

      mkB (S i)  -->  mkB (S (S i))   in exactly  2*i+5  steps,

    so the wall moves by exactly one cell per cycle and the cost is affine
    in the wall index -- a PLAIN bouncer, no measure and no well-founded
    recursion.  This is why eight waves of digit-alphabet anchor search
    returned nothing on this row: there is no digit word to find.

    The whole design was measured off the raw simulator by
    [tools/counters/bouncecert.py] (turnaround columns, wall step, cycle
    cost law, and the wall-indexed turnaround families) and the lap
    differentially validated at [j = 1..59] before any Coq was written.

    [Print Assumptions] = [functional_extensionality_dep] only. *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Census Require Import TNF_QH.
From BBB4.Counters Require Import LapGlueAbs BounceGlue.
Import ListNotations.

Definition mk (w : Sym) (d : Dir) (n : St) : option Trans :=
  Some (mkTrans w d n).

(** @SPEC@ *)
Definition tm_@ID@ : TM := fun q s => match q, s with
@TABLE@ end.

(** The wall-indexed anchor: [Cb St@E@ p = mkB St@E@ (Pos.to_nat p)]. *)
Lemma boot_@ID@ : exists t0,
  stepn tm_@ID@ t0 InitES = Some (lift (Cb St@E@ 1)).
Proof.
  exists @T0@.
  assert (H : match csteps tm_@ID@ @T0@ c0 with
              | Some c => ceqb c (Cb St@E@ 1)
              | None => false
              end = true) by (vm_compute; reflexivity).
  destruct (csteps tm_@ID@ @T0@ c0) as [c|] eqn:Eq; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ Eq).
  f_equal. apply ceqb_lift. exact H.
Qed.

Definition iqh (tm : TM) : Prop :=
  NonHalt tm /\ QHBound 2000 tm /\ QuasiHaltsSt tm.

(** @SPEC@: never halts, quasihalts, and every quiet state made its last
    visit by index 1. *)
Theorem iqh_@ID@ : iqh tm_@ID@.
Proof.
  apply (bounce_qh tm_@ID@ St@E@ St@X@ St@Y@
           eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
           boot_@ID@
           ltac:(vm_compute; reflexivity)
           ltac:(eexists; split; [vm_compute; reflexivity | cbn; tauto])
           ltac:(cbn; intuition discriminate)).
Qed.
'''


# ---------------------------------------------------------------- wall board ---
#
# The WALL BOUNCE class.  A machine is a customer of BounceGlue's
# [WallBounce] section when three of its states play the roles the reader
# measured -- Bq turns at the wall, Cq erases the run leftward with a
# self-loop, Dq fills it back rightward -- and the fourth, StA, is the drift.
# The roles are READ OFF THE TABLE, never assigned.  The emitter only takes
# machines whose roles land on (StB, StC, StD) in that order, because the
# board's visit case-split is written in state order; a permuted assignment
# is a template variant, not new theory.

WBOARD = r'''(** * @PREF@_@ID@: machine @SPEC@ never quasihalts.

    One of the residue's `no anchor` rows, and the class John read off the
    tape (WAVE29_FINDINGS.md section 6, on this row's sibling
    0RB0LD_1LA1LC_0LD0LC_1RD1RB -- the three differ only in row A):

      "keeps bouncing back and forth with c and d states.  then when it
       passes the wall on the right it moves the wall over one and heads
       back left and then goes back to bouncing"

    THE COUNTER IS NOT A WORD, IT IS THE WALL POSITION.  That is why eight
    waves of digit-alphabet anchor enumeration returned nothing here: the
    machine never rests in a decodable digit configuration, and the thing
    that grows monotonically is a COLUMN.  The family is [BounceGlue]'s
    wall-indexed pair

      wA St@B@ n   = (St@B@, (repeat S1 n, S0, []))
      wM St@B@ a r = (St@B@, (repeat S1 r, S1, repeat S1 a))

    and [BounceGlue.WallBounce] supplies everything not involving [StA]:
    one bounce is [wM (S a) r --> wM a (r+3)] in exactly [2*r+5] steps,
    the terminal [wM 0 r --> wA (r+3)] is the SAME derivation read at
    [a = 0] (which is why they cost the same), and [wmchain] composes [a]
    of them.  The wall moves by exactly ONE cell per bounce and the cost
    is affine in it, so the bounce count is explicit in the anchor and
    plain induction suffices -- no [MeasureGlue], no measure, no
    well-founded recursion.

    What is left, and all this file adds, is the COLLAPSE, the only place
    [StA] appears: it walks the solid block from its near end to its far
    end at @RP@ steps per cell LEAVING THE TAPE UNCHANGED, and @TL@ more
    steps turn the walk around into the first bounce:

      wA n  -->  wM (n-@CC1@) 3   in  @RP@*(n-1) + @TLP1@  steps.

    The macro lap is therefore [wA n --> wA (@NEXTN@)] and the block sizes
    are @B0@, @B1@, @B2@, @B3@, ...  Every state recurs inside one lap
    ([St@B@] at index 0, [StA] at 1, [St@C@] and [St@D@] inside the first
    bounce), so the closer is [LapGlue.glue_neverqh] directly -- Bounce_8's
    pattern, on a family indexed by the wall rather than by a counter.

    Measured off the raw simulator by [tools/counters/bouncecert.py]
    (turnaround columns, wall step +1 per cycle, the affine cost law, and
    the wall-indexed turnaround families) and differentially validated --
    the bounce and terminal over an (a, r) grid, the collapse at every
    n = 3..40, and the anchor sequence against the blank-tape replay --
    before any Coq was written.

    [Print Assumptions] = [functional_extensionality_dep] only. *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Census Require Import TNF_QH.
From BBB4.Counters Require Import LapGlue BounceGlue.
Import ListNotations.

Definition mk (w : Sym) (d : Dir) (n : St) : option Trans :=
  Some (mkTrans w d n).

(** @SPEC@ *)
Definition tm_@ID@ : TM := fun q s => match q, s with
@TABLE@ end.
Local Notation tm := tm_@ID@.

Local Notation aA := (wA St@B@).
Local Notation aM := (wM St@B@).

Lemma chain_@ID@ : forall n1 n2 c c1 c2,
  csteps tm n1 c = Some c1 -> csteps tm n2 c1 = Some c2 ->
  csteps tm (n1 + n2) c = Some c2.
Proof. intros. rewrite csteps_add, H. assumption. Qed.

(** ** The bounce, straight from [BounceGlue.WallBounce] *)

Definition mchain_@ID@ := wmchain tm St@B@ St@C@ St@D@
  eq_refl eq_refl eq_refl eq_refl eq_refl.
Definition visC_@ID@ := wvisC tm St@B@ St@C@ eq_refl.
Definition visD_@ID@ := wvisD tm St@B@ St@C@ St@D@ eq_refl eq_refl eq_refl.

(** ** The collapse: [StA] walks the block at @RP@ steps per cell *)

(** One cell of the walk.  The tape is UNCHANGED -- the cell is cleared
    and rewritten -- which is what makes the walk a pure translation. *)
Lemma rip1_@ID@ : forall L R,
  csteps tm @RP@ (StA, (S1 :: L, S1, S1 :: R))
    = Some (StA, (L, S1, S1 :: S1 :: R)).
Proof. intros L R. reflexivity. Qed.

Lemma ripn_@ID@ : forall k L R,
  csteps tm (@RP@ * k) (StA, (repeat S1 k ++ L, S1, S1 :: R))
    = Some (StA, (L, S1, repeat S1 k ++ S1 :: R)).
Proof.
  induction k as [|k IH]; intros L R; [reflexivity|].
  cbn [repeat app].
  replace (@RP@ * S k) with (@RP@ + @RP@ * k) by lia.
  apply (chain_@ID@ @RP@ (@RP@ * k) _
           (StA, (repeat S1 k ++ L, S1, S1 :: S1 :: R))).
  - apply rip1_@ID@.
  - rewrite IH, rep_snoc. reflexivity.
Qed.

(** The turn at the far end: the walk becomes the first bounce. *)
Lemma tail_@ID@ : forall X,
  csteps tm @TL@ (StA, ([], S1, @TAILPRE@X))
    = Some (St@B@, ([S1; S1; S1], chd X, ctl X)).
Proof. intro X. reflexivity. Qed.

Lemma wcol_@ID@ : forall m,
  csteps tm (@RP@ * @MPLUS@ + @TLP1@) (aA @NCOL@) = Some (aM m 3).
Proof.
  intro m. unfold wA.
  replace (@RP@ * @MPLUS@ + @TLP1@) with (1 + (@RP@ * @MPLUS@ + @TL@)) by lia.
  cbn [repeat].
  apply (chain_@ID@ 1 _ _ (StA, (repeat S1 @MPLUS@, S1, [S1]))).
  { reflexivity. }
  apply (chain_@ID@ (@RP@ * @MPLUS@) @TL@ _
           (StA, ([], S1, repeat S1 @MPLUS@ ++ [S1]))).
  { pose proof (ripn_@ID@ @MPLUS@ [] []) as Hr.
    rewrite app_nil_r in Hr. exact Hr. }
  rewrite rep_app1.
  exact (tail_@ID@ (repeat S1 (S m))).
Qed.

(** ** The macro lap *)

Lemma wlap_@ID@ : forall m, exists k, 0 < k /\
  csteps tm k (aA @NCOL@) = Some (aA (3 + 3 * m + 3)).
Proof.
  intro m. destruct (mchain_@ID@ m 3) as (k & Hk & Hrun).
  exists (@RP@ * @MPLUS@ + @TLP1@ + k). split; [lia|].
  apply (chain_@ID@ (@RP@ * @MPLUS@ + @TLP1@) k _ (aM m 3)).
  - apply wcol_@ID@.
  - exact Hrun.
Qed.

(** ** The anchor family: block sizes @B0@, @B1@, @B2@, ... *)

Fixpoint blk_@ID@ (t : nat) : nat :=
  match t with 0 => @B0@ | S t' => @BLKREC@ end.

Lemma blk_ge_@ID@ : forall t, @CC1@ <= blk_@ID@ t.
Proof. induction t; cbn; lia. Qed.

(** Every block the family visits is big enough to collapse. *)
Lemma anchor_@ID@ : forall t, exists m, blk_@ID@ t = @NCOL@.
Proof.
  intro t. pose proof (blk_ge_@ID@ t).
  exists (blk_@ID@ t - @CC1@). lia.
Qed.

Definition Cc (p : positive) : cconf := aA (blk_@ID@ (Pos.to_nat p)).

Lemma lap_@ID@ : forall p, exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. unfold Cc. rewrite Pos2Nat.inj_succ. cbn [blk_@ID@].
  destruct (anchor_@ID@ (Pos.to_nat p)) as (m & Hm). rewrite Hm.
  destruct (wlap_@ID@ m) as (k & Hk & Hrun).
  exists k, (aA (3 + 3 * m + 3)).
  split; [exact Hrun | split; [| exact Hk]].
  replace (3 + 3 * m + 3) with (3 * @NCOL@@GADDS@) by lia.
  reflexivity.
Qed.

(** ** Visits: every state recurs inside one lap *)

Lemma visA_@ID@ : forall m,
  exists c, csteps tm 1 (aA @NCOL@) = Some c /\ fst c = StA.
Proof.
  intro m. unfold wA. cbn [repeat]. eexists. split; reflexivity.
Qed.

Lemma vis_@ID@ : forall p q, exists k c,
  csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros p q. unfold Cc.
  destruct (anchor_@ID@ (Pos.to_nat p)) as (m & Hm). rewrite Hm.
  destruct q.
  - destruct (visA_@ID@ m) as (c & Hc & Hq).
    exists 1, c. split; [exact Hc | exact Hq].
  - exists 0. eexists. split; reflexivity.
  - destruct (visC_@ID@ m 3) as (c & Hc & Hq).
    exists (@RP@ * @MPLUS@ + @TLP1@ + 1), c. split; [| exact Hq].
    apply (chain_@ID@ (@RP@ * @MPLUS@ + @TLP1@) 1 _ (aM m 3)).
    + apply wcol_@ID@.
    + exact Hc.
  - destruct (visD_@ID@ m 3) as (c & Hc & Hq).
    exists (@RP@ * @MPLUS@ + @TLP1@ + (3 + 2)), c. split; [| exact Hq].
    apply (chain_@ID@ (@RP@ * @MPLUS@ + @TLP1@) (3 + 2) _ (aM m 3)).
    + apply wcol_@ID@.
    + exact Hc.
Qed.

(** ** Boot and the theorem *)

Lemma boot_@ID@ : exists t0, stepn tm t0 InitES = Some (lift (Cc 1)).
Proof.
  exists @T0@.
  assert (H : match csteps tm @T0@ c0 with
              | Some c => ceqb c (Cc 1)
              | None => false
              end = true) by (vm_compute; reflexivity).
  destruct (csteps tm @T0@ c0) as [c|] eqn:Eq; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ Eq).
  f_equal. apply ceqb_lift. exact H.
Qed.

Theorem nqh_@ID@ : NeverQuasiHaltsSt tm.
Proof.
  apply (glue_neverqh tm Cc 1).
  - exact boot_@ID@.
  - intros p _. apply lap_@ID@.
  - intros p q _. apply vis_@ID@.
Qed.

Theorem nonhalt_@ID@ : NonHalt tm.
Proof. apply never_qh_nonhalt, nqh_@ID@. Qed.
'''


def wroles(spec):
    """(Bq, Cq, Dq) for the WALL-BOUNCE shape, read off the table."""
    tab = parse(spec)
    for B in range(4):
        t = tab.get((B, 1))
        if t is None or t[:2] != (1, -1) or t[2] == B:
            continue
        C = t[2]
        if tab.get((C, 1)) != (0, -1, C):
            continue
        tc = tab.get((C, 0))
        if tc is None or tc[:2] != (0, -1):
            continue
        D = tc[2]
        if tab.get((D, 0)) != (1, 1, D) or tab.get((D, 1)) != (1, 1, B):
            continue
        if tab.get((B, 0)) != (1, -1, 0):        # the drift is entered here
            continue
        if (B, C, D) != (1, 2, 3):
            continue
        return (B, C, D)
    return None


def _run(tab, cfg, n):
    import lapcert as LC
    for _ in range(n):
        cfg = LC.wstep(tab, False, False, cfg)
    return cfg


def wmeasure(spec, B):
    """(rp, tl, cc1), measured -- plus a DIFFERENTIAL VALIDATION of every
    gadget the board is about to claim, against the raw simulator."""
    import lapcert as LC
    tab = parse(spec)

    def aA(n):
        return (B, (1,) * n, 0, ())

    def aM(a, r):
        return (B, (1,) * r, 1, (1,) * a)

    rp, c = None, (0, (1,) * 5, 1, (1,) * 3)
    for t in range(1, 40):
        c = LC.wstep(tab, False, False, c)
        if c == (0, (1,) * 4, 1, (1,) * 4):
            rp = t
            break
    if rp is None:
        return None
    tl, cc1, c = None, None, (0, (), 1, (1,) * 8)
    for t in range(0, 40):
        if c[0] == B and c[1] == (1, 1, 1) and c[2] == 1:
            tl, cc1 = t, 8 - len(c[3])
            break
        c = LC.wstep(tab, False, False, c)
    if tl is None or cc1 not in (1, 2):
        return None
    for r in range(0, 12):
        for a in range(0, 6):
            want = aA(r + 3) if a == 0 else aM(a - 1, r + 3)
            if _run(tab, aM(a, r), 2 * r + 5) != want:
                return None
    for n in range(cc1, 41):
        if _run(tab, aA(n), rp * (n - 1) + tl + 1) != aM(n - cc1, 3):
            return None
    return (rp, tl, cc1)


def wemit(spec, write=True, check=True):
    from emit_interleave import coq_table
    import lapcert as LC
    r = wroles(spec)
    if r is None:
        return (spec, 'not a wall bouncer', None)
    B, C, D = r
    m = wmeasure(spec, B)
    if m is None:
        return (spec, 'wall-bounce gadgets do not validate', None)
    rp, tl, cc1 = m
    gadd = 6 - 3 * cc1
    tab = parse(spec)
    blk = [3]
    for _ in range(4):
        blk.append(3 * blk[-1] + gadd)
    want, cfg, t0 = (B, (1,) * blk[1], 0, ()), (0, (), 0, ()), None
    for t in range(20000):
        if cfg == want:
            t0 = t
            break
        cfg = LC.wstep(tab, False, False, cfg)
    if t0 is None:
        return (spec, 'no boot to the p = 1 anchor', None)
    mid = mach_id(spec)
    tail = '' if gadd == 0 else ' + ' + str(gadd)
    nx = '3 * n' + tail
    br = '3 * blk_' + mid + " t'" + tail
    ncol = 'm'
    for _ in range(cc1):
        ncol = '(S ' + ncol + ')'
    mplus = 'm' if cc1 == 1 else '(S m)'
    nd = ''
    src = (WBOARD.replace('@PREF@', BOARD_PREFIX).replace('@ID@', mid)
           .replace('@SPEC@', spec).replace('@TABLE@', coq_table(spec))
           .replace('@B@', LAB[B]).replace('@C@', LAB[C]).replace('@D@', LAB[D])
           .replace('@RP@', str(rp)).replace('@TLP1@', str(tl + 1))
           .replace('@TL@', str(tl)).replace('@CC1@', str(cc1))
           .replace('@TAILPRE@', 'S1 :: ' * (cc1 - 1))
           .replace('@NCOL@', ncol).replace('@MPLUS@', mplus)
           .replace('@GADDS@', tail).replace('@NEXTN@', nx)
           .replace('@BLKREC@', br).replace('@T0@', str(t0))
           .replace('@B0@', str(blk[0])).replace('@B1@', str(blk[1]))
           .replace('@B2@', str(blk[2])).replace('@B3@', str(blk[3])))
    path = os.path.join(OUTDIR, BOARD_PREFIX + '_' + mid + '.v')
    if not write:
        return (spec, 'dry run', src)
    with open(path, 'w') as f:
        f.write(src)
    if not check:
        return (spec, 'written', path)
    ok, log = coqc(path)
    return (spec, 'BOARDED' if ok else 'coqc FAILED\n' + log, path)


def roles(spec):
    """(E, X, Y) as state indices, or None if the machine is not an
    erase/fill bouncer.  Read off the table; nothing is assigned."""
    tab = parse(spec)
    cand = [q for q in range(4) if tab.get((q, 1)) == (0, +1, q)]
    if len(cand) != 1:
        return None
    E = cand[0]
    if tab.get((E, 0)) is None or tab[(E, 0)][:2] != (1, -1):
        return None
    X = tab[(E, 0)][2]
    if tab.get((X, 0)) is None or tab[(X, 0)][:2] != (1, -1):
        return None
    Y = tab[(X, 0)][2]
    want = {(X, 1): (1, +1, E), (Y, 1): (1, +1, E), (Y, 0): (1, -1, X)}
    if any(tab.get(k) != v for k, v in want.items()):
        return None
    if len({E, X, Y}) != 3:
        return None
    return (E, X, Y)


def boot_time(spec, E, maxt=400):
    """The first index at which the machine is AT the p = 1 anchor."""
    import lapcert as LC
    tab = parse(spec)
    want = (E, (0, 1), 0, ())
    cfg = (0, (), 0, ())
    for t in range(maxt):
        if cfg == want:
            return t
        cfg = LC.wstep(tab, False, False, cfg)
    return None


def validate_lap(spec, E, hi=60):
    """Differential validation against the raw simulator: the lap holds
    EXACTLY, at every wall index, before a line of Coq is written."""
    import lapcert as LC
    tab = parse(spec)

    def mk(j):
        return (E, (0,) * j + (1,), 0, ())

    for j in range(1, hi):
        c = mk(j)
        for _ in range(2 * j + 3):
            c = LC.wstep(tab, False, False, c)
        if c != mk(j + 1):
            return 'lap fails at j=%d: %s' % (j, c)
    return None


def emit(spec, write=True, check=True):
    from emit_interleave import coq_table
    r = roles(spec)
    if r is None:
        return (spec, 'not an erase/fill bouncer', None)
    E, X, Y = r
    bad = validate_lap(spec, E)
    if bad:
        return (spec, bad, None)
    t0 = boot_time(spec, E)
    if t0 is None:
        return (spec, 'no boot to the p = 1 anchor', None)
    mid = mach_id(spec)
    src = (BOARD.replace('@PREF@', BOARD_PREFIX).replace('@ID@', mid)
           .replace('@SPEC@', spec).replace('@TABLE@', coq_table(spec))
           .replace('@T0@', str(t0))
           .replace('@E@', LAB[E]).replace('@X@', LAB[X])
           .replace('@Y@', LAB[Y]))
    path = os.path.join(OUTDIR, '%s_%s.v' % (BOARD_PREFIX, mid))
    if not write:
        return (spec, 'dry run', src)
    with open(path, 'w') as f:
        f.write(src)
    if not check:
        return (spec, 'written', path)
    ok, log = coqc(path)
    return (spec, 'BOARDED' if ok else 'coqc FAILED\n' + log, path)


def view_emit(specs, write, check):
    for spec in specs or BUCKET:
        s, msg, path = emit(spec, write=write, check=check)
        if path is None:
            _s2, msg2, path2 = wemit(spec, write=write, check=check)
            if path2 is not None or msg2 != 'not a wall bouncer':
                msg, path = msg2, path2
        print('%-29s %s%s' % (s, msg, ('  -> ' + path) if path and write else ''))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--spec')
    ap.add_argument('--steps', type=int, default=200000)
    ap.add_argument('--n', type=int, default=24)
    ap.add_argument('--turns', action='store_true')
    ap.add_argument('--cycles', action='store_true')
    ap.add_argument('--macro', action='store_true')
    ap.add_argument('--family', action='store_true')
    ap.add_argument('--anchors', action='store_true')
    ap.add_argument('--all-views', action='store_true')
    ap.add_argument('--all', action='store_true')
    ap.add_argument('--emit', action='store_true')
    ap.add_argument('--dry', action='store_true')
    a = ap.parse_args()
    if a.emit:
        view_emit([a.spec] if a.spec else None, write=not a.dry, check=True)
        return
    if a.all:
        view_all(a.steps)
        return
    if not a.spec:
        ap.error('--spec or --all')
    R = Replay(a.spec, a.steps)
    print('%s : %d steps replayed%s, frontier [%d, %d]'
          % (a.spec, R.n, ' (HALTED)' if R.halted else '', R.lo[-1], R.hi[-1]))
    if a.turns or a.all_views:
        view_turns(a.spec, R, a.n)
    if a.cycles or a.all_views:
        view_cycles(a.spec, R, a.n)
    if a.macro or a.all_views:
        view_macro(a.spec, R, a.n)
    if a.family or a.all_views:
        view_family(a.spec, R, a.n)
    if a.anchors or a.all_views:
        view_anchors(a.spec, R, a.n)


if __name__ == '__main__':
    main()
