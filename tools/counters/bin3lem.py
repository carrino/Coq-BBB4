#!/usr/bin/env python3
"""UNTRUSTED (tools/): state `theories/Counters/Bin3Lap.v`'s rules against
the probe BEFORE proving them, in SINGLE CELLS, over ALL instantiations of
the unknown context.

Every check here runs the row on a tape whose cells outside the lemma's own
statement are UNKNOWN, and aborts the moment the head reads one.  So a PASS
is a statement about every instantiation of the context, not about the one
the top-level run happens to supply -- which is the difference between a
lemma and a coincidence, and is what `fiblazy.py`, `gray2check.py` and §4y's
`6c+4 / 6c+6 / 6c+4` were each written for.

Checked, on BOTH rows:

  Hbc     the composite that absorbs the ONE transition they differ in
  core    the lap, over an unknown tail, in BOTH cview cases at once
  Hloop   the inner run -- and its DECOMPOSITION, which is the finding:
          k >= 1 is not a second carry induction, it is a descending
          cascade, so §4y's "an inner induction over the carry run" prices
          only half the board

    python3 tools/counters/bin3lem.py
"""
ROWS = [("row 1  B0 -> qB", "1RB1LC_1LB1RA_0LC0LD_0RA0RD"),
        ("row 2  B0 -> qC", "1RB1LC_1LC1RA_0LC0LD_0RA0RD")]


def parse(spec):
    tab = {}
    for si, part in enumerate(spec.split('_')):
        for yi in range(2):
            e = part[3 * yi:3 * yi + 3]
            tab[(si, yi)] = None if e == '---' else (
                int(e[0]), +1 if e[1] == 'R' else -1, ord(e[2]) - ord('A'))
    return tab


def run(spec, tape, pos, st, stop, limit=4000000):
    """Run until `stop(st, pos)`.  Reading a cell outside `tape` aborts.

    `tape` is a dict cell -> 0/1; anything else is UNKNOWN.  Returns
    (verdict, steps, tape).
    """
    tab = parse(spec)
    tape = dict(tape)
    n = 0
    while n < limit:
        if pos not in tape:
            return ("READ_UNKNOWN@%+d" % pos, n, tape)
        e = tab[(st, tape[pos])]
        if e is None:
            return ("HALT", n, tape)
        w, d, ns = e
        tape[pos] = w
        pos += d
        st = ns
        n += 1
        if stop(st, pos, tape):
            return ("STOP", n, tape)
    return ("LIMIT", n, tape)


def verdict(got, want, n, extra=""):
    """`want` is a dict cell -> 0/1 over the cells the lemma fixes; every
    other touched cell must be 0 (blank) or untouched."""
    bad = [(c, got[c]) for c in sorted(got) if got[c] != want.get(c, 0)]
    return ("OK(%d)%s" % (n, extra)) if not bad else "TAPE%s" % bad[:3]


# ---------------------------------------------------------------- Hbc

def check_bc(spec, chdL, R1):
    """(qB, (S1::L, S0, R)) --> (qD, (ctl L, chd L, S0::S1::R))

    head at 0; cell -1 = S1 (the `S1::` of the left word); cell -2 = chd L,
    the cell the run must LAND on without reading; cell +1 = R's head.
    Everything else is unknown."""
    t = {0: 0, -1: 1, -2: chdL, 1: R1}
    v, n, got = run(spec, t, 0, 1, lambda st, p, t: st == 3 and p == -2)
    if v != "STOP":
        return "%s(%d)" % (v, n)
    return verdict(got, {-2: chdL, -1: 0, 0: 1, 1: R1}, n)


# ---------------------------------------------------------------- core

def check_core(spec, j, ovf, chdL):
    """(qD, (L, S0, rep [S0;S1] j ++ w)) --> (qD, (L, S0, rep [S0] (2j+1) ++
    S1 :: ctl (ctl w)))

    `ovf` picks the cview case: interior takes w = S0::S0::UNKNOWN (so cells
    2j+3 on are unknown), overflow takes w = [] (so cells 2j+1, 2j+2 are the
    blanks the cconf does not carry, and cells 2j+3 on are unknown all the
    same).  Both must run, and both must land on the SAME target."""
    t = {0: 0, -1: chdL}
    for i in range(j):
        t[1 + 2 * i] = 0
        t[2 + 2 * i] = 1
    t[2 * j + 1] = 0
    t[2 * j + 2] = 0
    if not ovf:
        t[2 * j + 3] = 0          # chd of the tail Wp q, which starts S0
    v, n, got = run(spec, t, 0, 3, lambda st, p, t: st == 3 and p == 0)
    if v != "STOP":
        return "%s(%d)" % (v, n)
    want = {c: 0 for c in range(-1, 2 * j + 2)}
    want[-1] = chdL
    want[2 * j + 2] = 1
    if not ovf:
        want[2 * j + 3] = 0
    return verdict(got, want, n)


# ---------------------------------------------------------------- Hloop

def loop_tape(k, d, chdM):
    t = {0: 1}
    for i in range(1, d + 1):
        t[-i] = 0
    t[-(d + 1)] = 1
    t[-(d + 2)] = chdM
    for i in range(1, 2 * k + 2):
        t[i] = 0
    t[2 * k + 2] = 1
    return t, -(d + 2), 2 * k + 2


def check_loop(spec, k, d, chdM):
    """(qD, (rep [S0] d ++ S1::M, S1, rep [S0] (2k+1) ++ S1::R))
   --> (qD, (ctl M, chd M, rep [S0] (2k+3+d) ++ S1::R))"""
    t, end, hi = loop_tape(k, d, chdM)
    v, n, got = run(spec, t, 0, 3, lambda st, p, t: st == 3 and p == end)
    if v != "STOP":
        return "%s(%d)" % (v, n), n
    want = {c: 0 for c in range(end, hi)}
    want[end] = chdM
    want[hi] = 1
    return verdict(got, want, n), n


def fr(spec, k):
    """step count of the field run at width k"""
    t = {0: 0, -1: 0}
    for i in range(2 * k):
        t[1 + i] = 0
    t[1 + 2 * k] = 1
    goal = Fld(2 ** (k + 1) - 1)
    return run(spec, t, 0, 3,
               lambda st, q, tp: (st == 3 and q == 0 and all(
                   tp.get(1 + i, 0) == c for i, c in enumerate(goal))))[1]


def cc(spec, t_, m, d):
    """step count of CASC(t, m, d)"""
    tp = {0: 1}
    for c in range(1, 2 * t_ + 1):
        tp[-c] = 1
    for c in range(1, d + 1):
        tp[-(2 * t_ + c)] = 0
    tp[-(2 * t_ + d + 1)] = 1
    tp[-(2 * t_ + d + 2)] = 0
    for c in range(1, 2 * m + 2):
        tp[c] = 0
    tp[2 * m + 2] = 1
    end = -(2 * t_ + d + 2)
    return run(spec, tp, 0, 3, lambda st, q, x: st == 3 and q == end)[1]


def loop_cost(spec, k, d=0):
    return check_loop(spec, k, d, 0)[1]


def lap_cost(spec, j):
    """One anchor lap at carry length j, from `core`'s own shape."""
    t = {0: 0, -1: 0}
    for i in range(j):
        t[1 + 2 * i] = 0
        t[2 + 2 * i] = 1
    t[2 * j + 1] = 0
    t[2 * j + 2] = 0
    t[2 * j + 3] = 0
    return run(spec, t, 0, 3, lambda st, p, t: st == 3 and p == 0)[1]


# ------------------------------------------------------- Fld, MARK, CASC
#
# The three shapes `Hloop` at k >= 1 decomposes into.  None of them was
# checked when §4z was written -- only the aggregate step count was -- so
# these are the ones a proof would otherwise be written blind against.

def Fld(p):
    """`Bin3Lap.Fld`: the field word, 2 cells a digit, LSB first, with the
    TOP bit dropped -- the marker `S1` above the field plays its part.

    `Wp p = Fld p ++ [S0;S1]`, so `cview` transfers verbatim."""
    out = []
    while p > 1:
        out += [0, p & 1]
        p >>= 1
    return out


def cview(p):
    j = 0
    while p > 1 and p & 1:
        j += 1
        p >>= 1
    return (j + 1, None) if p == 1 else (j, p >> 1)


def check_fld_inc(spec, p):
    """One field increment at a GENERAL value, not just at a power of two:

    (qD, (L, S0, Fld p ++ S1::R)) --> (qD, (L, S0, Fld (succ p) ++ S1::R))

    for every interior `p`.  This is `core` at `j = fst (cview p)` read in
    `Fld` terms, and it is what the field run iterates."""
    f = Fld(p)
    t = {0: 0, -1: 0}
    for i, c in enumerate(f):
        t[1 + i] = c
    t[1 + len(f)] = 1                      # the marker
    v, n, got = run(spec, t, 0, 3, lambda st, q, tp: st == 3 and q == 0)
    if v != "STOP":
        return "%s(%d)" % (v, n)
    g = Fld(p + 1)
    want = {0: 0, -1: 0, 1 + len(g): 1}
    for i, c in enumerate(g):
        want[1 + i] = c
    return verdict(got, want, n)


def check_field_run(spec, k):
    """The whole field run: Fld (2^k) (all clear) up to Fld (2^(k+1) - 1)
    (= rep [S0;S1] k, all set), by repeated increments at ONE anchor."""
    t = {0: 0, -1: 0}
    for i in range(2 * k):
        t[1 + i] = 0
    t[1 + 2 * k] = 1
    goal = Fld(2 ** (k + 1) - 1)

    def stop(st, q, tp):
        return (st == 3 and q == 0
                and all(tp.get(1 + i, 0) == c for i, c in enumerate(goal)))
    v, n, got = run(spec, t, 0, 3, stop)
    if v != "STOP":
        return "%s(%d)" % (v, n)
    want = {0: 0, -1: 0, 1 + 2 * k: 1}
    for i, c in enumerate(goal):
        want[1 + i] = c
    return verdict(got, want, n)


def check_mark(spec, i):
    """The step the field run CANNOT take: the all-set field meets the
    marker where a pad should be.

    (qD, (L, S0, rep [S0;S1] i ++ S1::R))
      --2i+3-->  (qD, (rep [S1] (2i-2) ++ S0::L, S1, S0::S1::R))

    The outward scan crosses i set digits, `A1` fires on the MARKER, and
    `C1` clears the digit below it -- so the head comes to rest ON a set
    cell, which is what the cascade then eats two at a time."""
    t = {0: 0, -1: 0}
    for c in range(i):
        t[1 + 2 * c] = 0
        t[2 + 2 * c] = 1
    t[2 * i + 1] = 1                       # the marker
    end = 2 * i - 1
    v, n, got = run(spec, t, 0, 3, lambda st, q, tp: st == 3 and q == end)
    if v != "STOP":
        return "%s(%d)" % (v, n)
    want = {-1: 0, 0: 0, 2 * i: 0, 2 * i + 1: 1}
    for c in range(1, 2 * i):
        want[c] = 1
    return verdict(got, want, n, "" if n == 2 * i + 3 else " [!=2i+3]")


def check_casc(spec, t_, m, d):
    """The descending cascade, as ONE lemma with ONE induction:

    (qD, (rep [S1] (2t) ++ rep [S0] d ++ S1::M, S1, rep [S0] (2m+1) ++ S1::R))
 -> (qD, (ctl M, chd M, rep [S0] (2(m+t)+3+d) ++ S1::R))

    Each turn is `Hloop` one level up, eating two set cells and laying down
    two clear ones -- which is why the LAST turn carries `d+2` and every
    other carries 0.  `t` counts the turns; the level `m` climbs."""
    tp = {0: 1}
    for c in range(1, 2 * t_ + 1):
        tp[-c] = 1
    for c in range(1, d + 1):
        tp[-(2 * t_ + c)] = 0
    tp[-(2 * t_ + d + 1)] = 1              # the S1 of S1::M
    tp[-(2 * t_ + d + 2)] = 0              # chd M, landed on but never read
    for c in range(1, 2 * m + 2):
        tp[c] = 0
    tp[2 * m + 2] = 1                      # the marker
    end = -(2 * t_ + d + 2)
    v, n, got = run(spec, tp, 0, 3, lambda st, q, x: st == 3 and q == end)
    if v != "STOP":
        return "%s(%d)" % (v, n)
    want = {c: 0 for c in range(end, 2 * m + 2)}
    want[2 * m + 2] = 1
    # the run must lay rep [S0] (2(m+t)+3+d) between the head and the marker
    return verdict(got, want, n)


def main():
    for name, spec in ROWS:
        print("=" * 72)
        print("%s   %s" % (name, spec))

        print("  Hbc    (qB,(S1::L,S0,R)) -> (qD,(ctl L,chd L,S0::S1::R))")
        print("         " + "  ".join(
            "chd L=S%d R1=S%d %s" % (a, b, check_bc(spec, a, b))
            for a in (0, 1) for b in (0, 1)))

        print("  core   (qD,(L,S0,rep[S0;S1] j ++ w))"
              " -> (qD,(L,S0,rep[S0](2j+1) ++ S1::ctl(ctl w)))")
        for ovf, tag in ((False, "interior w=S0::S0::_"), (True, "overflow w=[]")):
            print("         %-22s %s" % (tag, "  ".join(
                "j=%d %s" % (j, check_core(spec, j, ovf, 0)) for j in range(7))))
        print("         %-22s %s" % ("interior, chd L = S1", "  ".join(
            "j=%d %s" % (j, check_core(spec, j, False, 1)) for j in range(5))))

        print("  Hloop  (qD,(rep[S0] d ++ S1::M,S1,rep[S0](2k+1) ++ S1::R))")
        print("      -> (qD,(ctl M,chd M,rep[S0](2k+3+d) ++ S1::R))")
        for d in range(4):
            print("         d=%d  %s" % (d, "  ".join(
                "k=%d %s" % (k, check_loop(spec, k, d, 0)[0]) for k in range(6))))
        print("         chd M = S1 costs identical: %s" % (
            [loop_cost(spec, k) for k in range(5)]
            == [check_loop(spec, k, 0, 1)[1] for k in range(5)]))


        print("  Fld    Wp p = Fld p ++ [S0;S1], so cview transfers verbatim")
        print("  fld+1  (qD,(L,S0,Fld p ++ S1::R)) ->"
              " (qD,(L,S0,Fld (succ p) ++ S1::R))")
        print("         " + "  ".join(
            "p=%d %s" % (p, check_fld_inc(spec, p))
            for p in range(2, 24) if cview(p)[1] is not None))
        print("  field  Fld (2^k) ... Fld (2^(k+1)-1), one anchor, k = 1..5")
        print("         " + "  ".join(
            "k=%d %s" % (k, check_field_run(spec, k)) for k in range(1, 6)))
        print("  MARK   (qD,(L,S0,rep[S0;S1] i ++ S1::R)) -2i+3->"
              " (qD,(rep[S1](2i-2) ++ S0::L,S1,S0::S1::R))")
        print("         " + "  ".join(
            "i=%d %s" % (i, check_mark(spec, i)) for i in range(1, 7)))
        print("  CASC   (qD,(rep[S1](2t) ++ rep[S0] d ++ S1::M,S1,"
              "rep[S0](2m+1) ++ S1::R))")
        print("      -> (qD,(ctl M,chd M,rep[S0](2(m+t)+3+d) ++ S1::R))")
        for d in (0, 1, 2):
            print("         d=%d  %s" % (d, "  ".join(
                "t=%d,m=%d %s" % (t_, m, check_casc(spec, t_, m, d))
                for t_ in range(4) for m in (0, 1))))

        # --- the identity the proof follows, in one line ------------------
        print("  Hloop = D1 ; field run ; MARK ; CASC -- and that is the whole"
              " proof skeleton:")
        for k in range(1, 6):
            for d in (0, 1):
                lhs = 1 + fr(spec, k) + (2 * k + 3) + cc(spec, k - 1, 0, d + 2)
                rhs = loop_cost(spec, k, d)
                print("         k=%d d=%d : 1 + %d + %d + %d = %-5d "
                      "(LOOP=%d)  %s"
                      % (k, d, fr(spec, k), 2 * k + 3,
                         cc(spec, k - 1, 0, d + 2), lhs, rhs,
                         "MATCH" if lhs == rhs else "NO"))

        # --- the decomposition, which is what §4y did not price -----------
        print("  Hloop's SHAPE.  If k >= 1 were one more carry induction the"
              " cost would be")
        print("  affine in LOOP(k-1); it is a DESCENDING CASCADE, and the"
              " step counts say so:")
        lap = [lap_cost(spec, j) for j in range(8)]
        loop = [loop_cost(spec, k) for k in range(6)]
        print("         lap  per carry j : %s" % lap[:7])
        print("         LOOP(k,0)        : %s" % loop)
        for k in range(1, 5):
            # 1 (the D1 that opens it) + the k-digit field counted out
            # + the mark + the descending cascade LOOP(0,0)..LOOP(k-1,2)
            field = sum(lap[carry(v)] for v in range(2 ** k - 1))
            mark = 2 * k + 3
            casc = [loop_cost(spec, i) for i in range(k - 1)] \
                + [check_loop(spec, k - 1, 2, 0)[1]]
            tot = 1 + field + mark + sum(casc)
            print("         k=%d : 1 + %d + %d + %s = %d   (LOOP=%d)  %s"
                  % (k, field, mark, "+".join(map(str, casc)), tot,
                     loop[k], "MATCH" if tot == loop[k] else "NO"))


def carry(v):
    c = 0
    while v % 2 == 1:
        c += 1
        v //= 2
    return c


if __name__ == '__main__':
    main()
