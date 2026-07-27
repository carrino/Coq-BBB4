#!/usr/bin/env python3
"""UNTRUSTED: find every machine the [Counters.BlankTail] closer boards.

BlankTail closes a machine that reaches a configuration where

  * the head reads a blank,
  * the whole half-tape AHEAD (direction of travel) is blank, and
  * [tm q S0 = Some (mkTrans w d q)] -- a SELF-LOOP on blank.

From there it marches across virgin tape forever in one state, so every
other state is quiet from that step on and [QHBound N0] holds.

That condition is cheap to detect exactly: simulate, and at each step ask
whether the current state self-loops on blank and the head sits at or beyond
the written frontier in the direction it would travel.  No windows, no
statistics, no two-window confirmation -- when this fires the machine IS
boardable, because the Coq closer proves it from the same facts.

Also reports the strictly larger CYCLIC class: the tail need not be a single
state.  If the machine escapes the written region and thereafter reads only
blanks, its state sequence there is eventually periodic, and every state off
that cycle is quiet.  That wants a period-k generalisation of the same lemma;
this tool measures how much it would buy before anyone writes it.
"""
import argparse
import collections
import sys
from concurrent.futures import ProcessPoolExecutor

LAB = "ABCD"


def parse(spec):
    tab = {}
    for si, part in enumerate(spec.split('_')):
        for yi in range(2):
            e = part[3 * yi:3 * yi + 3]
            tab[(si, yi)] = None if e == '---' else (
                int(e[0]), +1 if e[1] == 'R' else -1, ord(e[2]) - ord('A'))
    return tab


def scan(spec, T=3_000_000):
    """Return (kind, N0, state, dir, period)."""
    tab = parse(spec)
    tape = {}
    pos = q = 0
    lo = hi = 0                     # written frontier (cells ever written)
    for t in range(T):
        e = tab[(q, tape.get(pos, 0))]
        if e is None:
            return spec, "HALT", t, None, None, None
        # --- the BlankTail test, checked BEFORE stepping ---
        if tape.get(pos, 0) == 0:
            w, d, ns = e
            if ns == q:                       # self-loop on blank
                # is everything ahead blank?  the head must be at or beyond
                # the written frontier in the direction of travel
                if (d > 0 and pos >= hi) or (d < 0 and pos <= lo):
                    return spec, "SELFLOOP", t, LAB[q], ("R" if d > 0 else "L"), 1
        w, d, ns = e
        if tape.get(pos, 0) != 0 or w != 0:
            lo, hi = min(lo, pos), max(hi, pos)
        tape[pos] = w
        pos += d
        q = ns
    return spec, "NONE", None, None, None, None


def scan_cyclic(spec, T=3_000_000, margin=4):
    """The larger class: after some N0 the machine reads ONLY BLANKS forever.

    That is the right condition, and it is simply "the last step at which a
    non-blank cell is read".  If the machine reads only blanks from N0 on, its
    behaviour there is driven by [tm q S0] alone -- a pure blank walk, whose
    state sequence is eventually periodic.  The states on that cycle recur;
    every other state is quiet from N0, giving QHBound N0.

    (Period 1 is exactly the SELFLOOP case the Coq closer already proves.)
    """
    tab = parse(spec)
    tape = {}
    pos = q = 0
    last_nonblank_read = -1
    for t in range(T):
        sym = tape.get(pos, 0)
        if sym != 0:
            last_nonblank_read = t
        e = tab[(q, sym)]
        if e is None:
            return spec, "HALT", t, None, None
        w, d, ns = e
        tape[pos] = w
        pos += d
        q = ns
    N0 = last_nonblank_read + 1
    if N0 >= T // margin:
        return spec, "NONE", None, None, None
    # states on the blank-walk cycle, and its period
    tab2 = tab
    seen = {}
    sq = None
    # replay to N0 to get the state there
    tape2 = {}
    p2 = 0
    q2 = 0
    for t in range(N0):
        e = tab2[(q2, tape2.get(p2, 0))]
        w, d, ns = e
        tape2[p2] = w
        p2 += d
        q2 = ns
    cyc = []
    cur = q2
    for k in range(64):
        if cur in seen:
            per = k - seen[cur]
            return spec, "CYCLIC", N0, LAB[q2], per
        seen[cur] = k
        cyc.append(cur)
        e = tab2[(cur, 0)]
        if e is None:
            return spec, "NONE", None, None, None
        cur = e[2]
    return spec, "CYCLIC", N0, LAB[q2], 0


_T = 3_000_000
_CYC = False


def _work(spec):
    return scan_cyclic(spec, _T) if _CYC else scan(spec, _T)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--list', required=True)
    ap.add_argument('-T', type=int, default=3_000_000)
    ap.add_argument('--cyclic', action='store_true')
    a = ap.parse_args()
    specs = [l.strip() for l in open(a.list) if l.strip()]
    global _T, _CYC
    _T, _CYC = a.T, a.cyclic
    fn = _work
    c = collections.Counter()
    hits = []
    with ProcessPoolExecutor(max_workers=4) as ex:
        for i, res in enumerate(ex.map(fn, specs, chunksize=4)):
            kind = res[1]
            c[kind] += 1
            if kind in ("SELFLOOP", "CYCLIC"):
                hits.append(res)
                print("\t".join(str(x) for x in res), flush=True)
            if (i + 1) % 100 == 0:
                print("... %d/%d %s" % (i + 1, len(specs), dict(c)),
                      file=sys.stderr, flush=True)
    print("\n=== %s ===" % ("cyclic blank tail" if a.cyclic else "BlankTail (self-loop)"),
          file=sys.stderr)
    for k, v in c.most_common():
        print("  %-9s %d" % (k, v), file=sys.stderr)
    if hits:
        ns = sorted(h[2] for h in hits)
        print("  prefix length N0: min=%d median=%d max=%d"
              % (ns[0], ns[len(ns) // 2], ns[-1]), file=sys.stderr)
        print("  N0 > 2000 (blocked by the census constant): %d"
              % sum(1 for n in ns if n > 2000), file=sys.stderr)


main()
