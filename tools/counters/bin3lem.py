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
        if stop(st, pos):
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
    v, n, got = run(spec, t, 0, 1, lambda st, p: st == 3 and p == -2)
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
    v, n, got = run(spec, t, 0, 3, lambda st, p: st == 3 and p == 0)
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
    v, n, got = run(spec, t, 0, 3, lambda st, p: st == 3 and p == end)
    if v != "STOP":
        return "%s(%d)" % (v, n), n
    want = {c: 0 for c in range(end, hi)}
    want[end] = chdM
    want[hi] = 1
    return verdict(got, want, n), n


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
    return run(spec, t, 0, 3, lambda st, p: st == 3 and p == 0)[1]


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
