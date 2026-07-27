#!/usr/bin/env python3
"""UNTRUSTED: does the machine's TAIL become a TRANSLATED cycler?

If, after a prefix of length N0, the configuration repeats up to TRANSLATION
with period P, then

  * every state occurring in the cycle recurs INFINITELY OFTEN -- liveness,
    free, with no measure and no acyclicity argument;
  * every state NOT in the cycle is quiet, last visit inside the prefix;

so QHBound N0 holds.  `theories/Checkers/TCycler.v` / `TCyclerN.v` carry the
Coq side.

METHOD (and a warning about the obvious wrong version).

The naive test -- "does (state, whole non-blank extent, head offset) repeat"
-- CANNOT WORK for a translated cycler: a cycler drifts, so it leaves written
tape behind it forever and the non-blank extent grows without bound.  Any
width cap then rejects every genuine cycler, and the scan silently reports
zero.  That is exactly what a first version of this file did.

mxdys' TC.v (busycoq BB6, verify/TC.v) does it right: it compares only the
region the head has actually TRAVELLED since the checkpoint (`firstn ld1 l`,
`firstn rd1 r`) and pads the rest with blanks.  This file follows that.

So: snapshot at RECORD positions (the head reaching a new rightmost/leftmost
cell, where everything beyond is blank by construction), key on
(state, the W cells behind the head), and confirm a candidate by checking the
machine never travelled further back than W during the interval.  Then the
configurations are genuinely equal up to translation and the cycle repeats
forever.

KNOWN LIMITATION -- READ BEFORE QUOTING ANY NUMBER FROM THIS FILE.
The "did it travel past the window" guard uses the GLOBAL max/min position,
which is monotone and therefore includes the PREFIX, not just the interval
since the snapshot.  So it under-reports: a machine with a long prefix
excursion is rejected even when its tail is a clean translated cycle (the
BlankTail machines are exactly this case -- a one-state blank march IS a
degenerate translated cycler, and this file misses all of them).  Fixing it
needs a per-snapshot max-since, not a global one.

In practice this matters little for the (4,2) residue, because the project
ALREADY sweeps translated cyclers (theories/Checkers/TCycler.v plus
tools/gen_tcycler_certs.py, 40 machines boarded upstream), so the residue is
by construction what survived that sweep.  Kept for the method note and for
reuse on other populations.
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


def scan(spec, T=200_000, W=160):
    """Look for a translated cycle anchored at record positions."""
    tab = parse(spec)
    tape = {}
    pos = q = 0
    maxp = minp = 0
    # key -> (t, pos, min position visited so far at the time of the snapshot)
    seenR, seenL = {}, {}
    seenX = {}                  # exact repeats, for NON-translated cyclers
    states_at = []
    # running minimum/maximum position since each snapshot is expensive to
    # keep exactly; track the global excursion instead and validate after.
    excursion_min = [0]     # min pos seen since index i (rebuilt lazily)
    for t in range(T):
        sym = tape.get(pos, 0)
        e = tab[(q, sym)]
        if e is None:
            return spec, "HALT", t, None, None, None
        # --- plain (non-translated) cycle: exact configuration repeat.
        # Only meaningful while the written region stays small; a translated
        # cycler drifts and is caught by the record snapshots below. ---
        nzc = [k for k, v in tape.items() if v != 0]
        if len(nzc) <= W:
            lo0 = min(nzc + [pos])
            hi0 = max(nzc + [pos])
            kx = (q, pos - lo0, tuple(tape.get(i, 0) for i in range(lo0, hi0 + 1)),
                  hi0 - lo0)
            if kx in seenX:
                t1 = seenX[kx]
                cyc = set(states_at[t1:t])
                return (spec, "TCYC", t1, t - t1,
                        "".join(LAB[x] for x in sorted(cyc)), len(cyc))
            seenX[kx] = t

        # --- right record: everything strictly right of pos is blank ---
        if pos > maxp or t == 0:
            key = (q, tuple(tape.get(pos - i, 0) for i in range(0, W)))
            if key in seenR:
                t1, p1, lo1 = seenR[key]
                if minp >= p1 - W + 1:      # never travelled past the window
                    cyc = set(states_at[t1:t])
                    return (spec, "TCYC", t1, t - t1,
                            "".join(LAB[x] for x in sorted(cyc)), len(cyc))
            else:
                seenR[key] = (t, pos, minp)
            maxp = max(maxp, pos)
        # --- left record ---
        if pos < minp:
            key = (q, tuple(tape.get(pos + i, 0) for i in range(0, W)))
            if key in seenL:
                t1, p1, hi1 = seenL[key]
                if maxp <= p1 + W - 1:
                    cyc = set(states_at[t1:t])
                    return (spec, "TCYC", t1, t - t1,
                            "".join(LAB[x] for x in sorted(cyc)), len(cyc))
            else:
                seenL[key] = (t, pos, maxp)
            minp = min(minp, pos)
        states_at.append(q)
        w, d, ns = e
        tape[pos] = w
        pos += d
        q = ns
        maxp = max(maxp, pos)
        minp = min(minp, pos)
    return spec, "NONE", None, None, None, None


_T = 200_000
_W = 160


def _work(spec):
    return scan(spec, _T, _W)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--list', required=True)
    ap.add_argument('-T', type=int, default=200_000)
    ap.add_argument('-W', type=int, default=160)
    a = ap.parse_args()
    global _T, _W
    _T, _W = a.T, a.W
    specs = [l.strip() for l in open(a.list) if l.strip()]
    c = collections.Counter()
    cov = collections.Counter()
    hits = []
    with ProcessPoolExecutor(max_workers=4) as ex:
        for i, res in enumerate(ex.map(_work, specs, chunksize=4)):
            c[res[1]] += 1
            if res[1] == "TCYC":
                hits.append(res)
                cov[res[5]] += 1
                print("\t".join(str(x) for x in res), flush=True)
            if (i + 1) % 100 == 0:
                print("... %d/%d %s" % (i + 1, len(specs), dict(c)),
                      file=sys.stderr, flush=True)
    print("\n=== translated-cycler tail, T=%d W=%d ===" % (a.T, a.W), file=sys.stderr)
    for k, v in c.most_common():
        print("  %-7s %d" % (k, v), file=sys.stderr)
    if hits:
        print("\n  states covered by the cycle:", file=sys.stderr)
        for n, v in sorted(cov.items()):
            route = ("never-QH (glue_neverqh)" if n == 4
                     else "QHBound, %d state(s) quiet" % (4 - n))
            print("    %d states : %4d machines  -> %s" % (n, v, route),
                  file=sys.stderr)
        ns = sorted(h[2] for h in hits)
        ps = sorted(h[3] for h in hits)
        print("\n  prefix N0: min=%d median=%d max=%d"
              % (ns[0], ns[len(ns) // 2], ns[-1]), file=sys.stderr)
        print("  period P : min=%d median=%d max=%d"
              % (ps[0], ps[len(ps) // 2], ps[-1]), file=sys.stderr)


main()
