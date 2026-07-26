#!/usr/bin/env python3
"""Differential lap decomposer for wave machine #6 (1RB0LB_0LB0RC_1LD1RC_1LA1RB).

Same contract as lap9.py/lap8.py: build the lap out of the SAME combinators
the Coq file will use, and check the composite against the raw stepper for
many fronts.  If `lap6.py 400` prints ALL OK, the decomposition below is the
one to transcribe.

Gadget table read off tools/counters/probe6.py (edge C, side R, poff 1):

  FT     5  (StC,(S1::L,S0,[]))          -> (StA,(L,S1,[S1;S1]))
  XC     4  (StA,(S1::c::L,S1,R))        -> (StA,(L,c,S1::S1::R))       cross, 2 cells
  BT     5  (StA,(S0::S1::c::L,S1,R))    -> (StA,(L,c,S1::S1::S0::R))   block transition
  DEP    1  (StA,(L,S0,R))               -> (StB,(S1::L,chd R,ctl R))   deposit / turn
  RS     1  (StB,(L,S1,R))               -> (StC,(S0::L,chd R,ctl R))   return start
  RSW    1  (StC,(L,S1,R))               -> (StC,(S1::L,chd R,ctl R))   return sweep
  RSEP   3  (StC,(S1::L,S0,R))           -> (StC,(S0::S1::L,chd R,ctl R))  sep skip
                                          [C0/1LD, D1/1RB, B1/0RC]

THE KEY SIMPLIFICATION vs #27: the rightward return leaves the tape
BYTE-FOR-BYTE unchanged (C1 rewrites a one as a one; the 3-step separator
gadget writes 1 at x, 1 at x-1, then 0 back at x).  So there is no
relaid/bridge algebra at all -- the leftward wave alone lands the tape on
[wbody (nextf 1 front)] and the return is a pure traversal back to the
frontier blank.

The leftward wave in state A is a UNIFORM walk: XC when the cell below the
head is a one, BT when it is a separator, stopping the moment the head itself
lands on a separator (DEP).  That is the concrete reading of WaveCounter's
[carry]: entering a run at offset 0 deposits iff the run is even; entering at
offset 1 deposits iff it is odd; a non-depositing run always hands the next
run over at offset 1.
"""
import sys

TM = {
    (0, 0): (1, +1, 1), (0, 1): (0, -1, 1),   # A0=1RB A1=0LB
    (1, 0): (0, -1, 1), (1, 1): (0, +1, 2),   # B0=0LB B1=0RC
    (2, 0): (1, -1, 3), (2, 1): (1, +1, 2),   # C0=1LD C1=1RC
    (3, 0): (1, -1, 0), (3, 1): (1, +1, 1),   # D0=1LA D1=1RB
}
A, B, C, D = 0, 1, 2, 3
POFF = 1


def chd(l):
    return l[0] if l else 0


def ctl(l):
    return l[1:] if l else []


def cstep(c):
    st, (l, h, r) = c
    w, d, ns = TM[(st, h)]
    if d == +1:
        return (ns, ([w] + l, chd(r), ctl(r)))
    return (ns, (ctl(l), chd(l), [w] + r))


def csteps(c, n):
    for _ in range(n):
        c = cstep(c)
    return c


def norm(c):
    """Strip trailing blanks on both sides (CTape.lift equality)."""
    st, (l, h, r) = c
    l = list(l); r = list(r)
    while l and l[-1] == 0:
        l.pop()
    while r and r[-1] == 0:
        r.pop()
    return (st, (l, h, r))


# ---------------------------------------------------------------- abstract
def carry(po, blocks):
    if not blocks:
        return [] if po else [1]
    b, r = blocks[0], blocks[1:]
    if po:
        return [b + 1] + r
    return [b] + carry(b % 2 == 1, r)


def nextf(front):
    b0, r = front[0], front[1:]
    return [b0 + 1] + carry((b0 + POFF) % 2 == 1, r)


def wbody(front):
    if not front:
        return [1]
    b, r = front[0], front[1:]
    return [1] * b + [0] + wbody(r)


def Cf(front):
    return (C, (wbody(front), 0, []))


# ---------------------------------------------------------------- units
def unit(name, c, n, want):
    got = csteps(c, n)
    if got != want:
        raise AssertionError("%s: got %s want %s" % (name, got, want))
    return got


def check_units():
    """Every unit as a standalone Compute-checkable fact."""
    L = [1, 0, 1, 1, 0, 1]
    R = [0, 1, 1]
    unit("FT", (C, ([1] + L, 0, [])), 5, (A, (L, 1, [1, 1])))
    for c in (0, 1):
        unit("XC(c=%d)" % c, (A, ([1, c] + L, 1, R)), 4, (A, (L, c, [1, 1] + R)))
        unit("BT(c=%d)" % c, (A, ([0, 1, c] + L, 1, R)), 5,
             (A, (L, c, [1, 1, 0] + R)))
    unit("DEP", (A, (L, 0, R)), 1, (B, ([1] + L, R[0], R[1:])))
    unit("RS", (B, (L, 1, R)), 1, (C, ([0] + L, R[0], R[1:])))
    unit("RSW", (C, (L, 1, R)), 1, (C, ([1] + L, R[0], R[1:])))
    unit("RSEP", (C, ([1] + L, 0, R)), 3, (C, ([0, 1] + L, R[0], R[1:])))
    # the two edge forms the lap actually meets
    unit("FT-empty-L", (C, ([1], 0, [])), 5, (A, ([], 1, [1, 1])))
    unit("RSW-blank", (C, ([], 1, [])), 1, (C, ([1], 0, [])))
    return True


# ---------------------------------------------------------------- the lap
def lap_decomposed(front, dbg=False):
    """Run the lap using ONLY the units above; return (config, steps)."""
    c = Cf(front)
    n = 0

    def step(k):
        nonlocal c, n
        c = csteps(c, k)
        n += k
        if dbg:
            st, (l, h, r) = c
            print("   %4d %s l=%s h=%d r=%s" % (n, "ABCD"[st],
                  ''.join(map(str, reversed(l))), h, ''.join(map(str, r))))

    # 1. frontier turnaround
    assert c[1][0][0] == 1, "frontier run must be non-empty"
    step(5)                                     # FT
    # 2. the leftward wave: XC / BT until the head lands on a separator
    guard = 0
    while True:
        st, (l, h, r) = c
        assert st == A, ("wave must stay in A", c)
        if h == 0:
            break                               # deposit position reached
        if l[0] == 1:
            step(4)                             # XC
        else:
            assert l[1] == 1, ("BT needs a one below the separator", c)
            step(5)                             # BT
        guard += 1
        assert guard < 100000, "wave did not terminate"
    # 3. deposit + return start
    step(1)                                     # DEP  (A0/1RB)
    step(1)                                     # RS   (B1/0RC)
    # 4. the rightward return: sweep ones, re-lay separators, stop on blank
    guard = 0
    while True:
        st, (l, h, r) = c
        assert st == C, ("return must stay in C", c)
        if h == 0 and not r:
            break                               # landed on the new event
        if h == 1:
            step(1)                             # RSW
        else:
            assert r and r[0] == 1, ("RSEP needs a one", c)
            step(3)                             # RSEP
        guard += 1
        assert guard < 1000000, "return did not terminate"
    return c, n


def lap_raw(front):
    """Raw stepper to the next event config."""
    c = Cf(front)
    tgt = Cf(nextf(front))
    for n in range(1, 2000000):
        c = cstep(c)
        st, (l, h, r) = c
        if st == C and h == 0 and r == [] and l and l[0] == 1:
            if l == tgt[1][0]:
                return c, n
    return None, None


def fronts(limit):
    """The real orbit from the boot vector, then assorted hand-made fronts."""
    out = []
    f = [4, 2, 1]                # boot [1;1;2;4] frontier-first
    for _ in range(limit):
        out.append(list(f))
        f = nextf(f)
    return out


def main():
    limit = int(sys.argv[1]) if len(sys.argv) > 1 else 60
    dbg = '--dbg' in sys.argv
    check_units()
    print("units: ALL OK")
    bad = 0
    for f in fronts(limit):
        if sum(f) > 4000:
            break
        cd, nd = lap_decomposed(f, dbg=dbg and f == [4, 2, 1])
        cr, nr = lap_raw(f)
        want = Cf(nextf(f))
        ok = (norm(cd) == norm(want)) and (cd == cr) and (nd == nr)
        if not ok:
            bad += 1
            print("MISMATCH front=%s dec=%s/%s raw=%s/%s want=%s" %
                  (f, nd, norm(cd), nr, norm(cr), norm(want)))
            if bad > 4:
                break
    print("laps: %s (%d fronts, largest sum=%d)" %
          ("ALL OK" if not bad else "%d BAD" % bad,
           len(fronts(limit)), max(sum(f) for f in fronts(limit))))


if __name__ == '__main__':
    main()
