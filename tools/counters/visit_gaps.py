#!/usr/bin/env python3
"""UNTRUSTED diagnosis: is each state's INTER-VISIT GAP bounded?

This measures whether the `Hvis` premise of [LapGlue.glue_neverqh] is
dischargeable by a FIXED-SIZE walled window.

    Hvis : forall p q, p0 <= p ->
             exists k c, csteps tm k (Cf p) = Some c /\ fst c = q

`Hvis` asks only for SOME k, so it is enough to exhibit a short prefix of the
lap in which every state appears -- and that prefix is p-independent exactly
as long as it stays inside the anchor's fixed window (which is what the walls
enforce).  Note this is insensitive to the lap's COST: a lap costing
Theta(2^j) still discharges Hvis from its first few dozen steps.  So the
exponential wall and the visit-witness problem are orthogonal.

The existing emitter derives its witness with lapcert.reach_state, which
searches SYMBOLIC chain steps (SWin/cyc/rot) and gives up when the machine
does something the chain vocabulary cannot express.  A concrete walled scan
has no vocabulary to run out of.  This tool measures what that would buy.

Classification, per machine, measured over the TAIL of a long run so that
start-up transients do not count:

  BOUNDED  every state recurs and its maximum gap does not grow between the
           third and fourth quarter of the run  => a fixed window discharges
           Hvis, and the machine is a NeverQuasiHalts candidate
  GROWING  every state recurs but some gap grows  => never-QH is still likely
           true, but a FIXED window will not see it; needs a lap-relative
           witness
  QUIET    some state stops occurring entirely    => quasi-halting CANDIDATE
           ONLY -- see the warning below; confirm with --confirm
  HALT     the machine halted

!! A SINGLE-WINDOW `QUIET` VERDICT IS UNSOUND. !!

A state visited at exponentially spaced times looks quiet at EVERY finite
window: its gap eventually exceeds T/4, so its last visit falls before the
3T/4 cutoff no matter how large T is.  Measured on this residue, the
single-window verdict was wrong for the large majority of the machines it
flagged -- the tell was a bimodal last-visit distribution with one cluster
at t <= 64 and another sitting at ~0.55*T, i.e. scaling with the window.

`confirm_quiet` runs TWO window sizes and keeps only states whose last
visit is the SAME ABSOLUTE STEP in both.  A genuinely quiet state's last
visit does not move; an exponential-gap state's scales with the window.
Always use --confirm before believing a QUIET verdict or reporting a count.
"""
import argparse
import sys

LAB = "ABCD"


def parse(spec):
    tab = {}
    for si, part in enumerate(spec.split('_')):
        for yi in range(2):
            e = part[3 * yi:3 * yi + 3]
            tab[(si, yi)] = None if e == '---' else (
                int(e[0]), +1 if e[1] == 'R' else -1, ord(e[2]) - ord('A'))
    return tab


def gaps(spec, T, nstates=4):
    """Run T steps from blank; return (halted, last[q], maxgap_q3[q], maxgap_q4[q], count[q])."""
    tab = parse(spec)
    tape = {}
    pos, q = 0, 0
    last = [None] * nstates
    mg3 = [0] * nstates
    mg4 = [0] * nstates
    cnt = [0] * nstates
    q3lo, q3hi = T // 2, 3 * T // 4
    for t in range(T):
        cnt[q] += 1
        if last[q] is not None:
            g = t - last[q]
            if q3lo <= t < q3hi:
                if g > mg3[q]:
                    mg3[q] = g
            elif t >= q3hi:
                if g > mg4[q]:
                    mg4[q] = g
        last[q] = t
        e = tab[(q, tape.get(pos, 0))]
        if e is None:
            return True, last, mg3, mg4, cnt
        w, d, ns = e
        tape[pos] = w
        pos += d
        q = ns
    return False, last, mg3, mg4, cnt


def classify(spec, T, nstates=4):
    halted, last, mg3, mg4, cnt = gaps(spec, T, nstates)
    if halted:
        return "HALT", {}
    tail = 3 * T // 4
    quiet = [q for q in range(nstates) if last[q] is None or last[q] < tail]
    if quiet:
        return "QUIET", dict(quiet=[LAB[q] for q in quiet],
                             last={LAB[q]: last[q] for q in range(nstates)})
    grow = [q for q in range(nstates) if mg4[q] > max(2 * mg3[q], mg3[q] + 8)]
    info = dict(maxgap={LAB[q]: mg4[q] for q in range(nstates)},
                prev={LAB[q]: mg3[q] for q in range(nstates)})
    if grow:
        info['growing'] = [LAB[q] for q in grow]
        return "GROWING", info
    return "BOUNDED", info


def last_visits(spec, T, nstates=4):
    """Last step at which each state occurs within T steps; None if halted."""
    tab = parse(spec)
    tape = {}
    pos, q = 0, 0
    last = [None] * nstates
    for _ in range(T):
        last[q] = _
        e = tab[(q, tape.get(pos, 0))]
        if e is None:
            return None
        w, d, ns = e
        tape[pos] = w
        pos += d
        q = ns
    return last


def confirm_quiet(spec, T1=400000, T2=4000000, nstates=4):
    """Two-window test -- the only sound way to call a state quiet here.

    Genuinely quiet: last visit is the SAME ABSOLUTE STEP at T1 and T2.
    Exponential gap:  last visit SCALES with the window.
    """
    a = last_visits(spec, T1, nstates)
    if a is None:
        return "HALT", {}
    b = last_visits(spec, T2, nstates)
    if b is None:
        return "HALT", {}
    quiet = [q for q in range(nstates) if a[q] is not None and b[q] == a[q]]
    if quiet:
        return "QUIET", dict(states=[LAB[q] for q in quiet],
                             B=max(a[q] for q in quiet))
    moved = [q for q in range(nstates)
             if a[q] is not None and b[q] != a[q] and a[q] < 3 * T1 // 4]
    if moved:
        return "EXPGAP", dict(states=[LAB[q] for q in moved])
    return "RECUR", {}


def anchor_offsets(spec, T, nstates=4):
    """ANCHOR-RELATIVE offsets -- the statistic `Hvis` actually needs.

    gaps() measures visit-to-visit distance, which is only an UPPER BOUND
    proxy: if a state fires once per lap right after the lap opens, its
    self-gap grows with the lap while its offset FROM THE ANCHOR stays small
    and constant.  So a growing gap says nothing, but a bounded offset is
    exactly `exists k` with k uniform in p.

    We need anchor times without knowing the anchor family.  Record-breaking
    head positions are a machine-independent proxy: a counter lap ends by
    pushing its frontier one cell further, so new records land about one per
    lap.  For each record time we measure how long until each state next
    occurs, and ask whether that offset stops growing.
    """
    tab = parse(spec)
    tape = {}
    pos, q = 0, 0
    lo = hi = 0
    rec = []                       # times at which a new record was set
    occ = [[] for _ in range(nstates)]
    for t in range(T):
        occ[q].append(t)
        e = tab[(q, tape.get(pos, 0))]
        if e is None:
            return None
        w, d, ns = e
        tape[pos] = w
        pos += d
        q = ns
        if pos < lo or pos > hi:
            lo, hi = min(lo, pos), max(hi, pos)
            rec.append(t)
    if len(rec) < 8:
        return None
    import bisect
    out = {}
    for s in range(nstates):
        if not occ[s]:
            return None
        offs = []
        for t in rec:
            i = bisect.bisect_left(occ[s], t)
            if i < len(occ[s]):
                offs.append(occ[s][i] - t)
        if len(offs) < 8:
            return None
        half = len(offs) // 2
        out[LAB[s]] = (max(offs[:half]), max(offs[half:]))
    return out


def classify_anchor(spec, T, nstates=4):
    """BOUNDED-ANCHOR iff no state's anchor-relative offset grows."""
    o = anchor_offsets(spec, T, nstates)
    if o is None:
        return "N/A", {}
    grow = [s for s, (a, b) in o.items() if b > max(2 * a, a + 8)]
    if grow:
        return "ANCHOR-GROWING", dict(offsets=o, growing=grow)
    return "ANCHOR-BOUNDED", dict(offsets=o,
                                  worst=max(b for _, b in o.values()))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--confirm', action='store_true',
                    help='two-window test: the only sound way to call a state '
                         'quiet (a single window cannot tell "stopped" from '
                         '"recurs at exponentially spaced times")')
    ap.add_argument('--anchor', action='store_true',
                    help='measure anchor-relative offsets (the Hvis statistic) '
                         'instead of visit-to-visit gaps')
    ap.add_argument('--list')
    ap.add_argument('--spec')
    ap.add_argument('-T', type=int, default=400000)
    ap.add_argument('--verbose', action='store_true')
    a = ap.parse_args()
    specs = [a.spec] if a.spec else [l.strip() for l in open(a.list) if l.strip()]
    import collections
    c = collections.Counter()
    worst = collections.Counter()
    for i, s in enumerate(specs):
        try:
            k, info = (confirm_quiet(s, a.T, 10 * a.T) if a.confirm
                       else classify_anchor(s, a.T) if a.anchor
                       else classify(s, a.T))
        except Exception as e:                                   # noqa: BLE001
            k, info = "ERROR", {'e': str(e)}
        c[k] += 1
        if k in ("BOUNDED", "ANCHOR-BOUNDED"):
            worst[info["worst"] if "worst" in info else max(info["maxgap"].values())] += 1
        if a.verbose or a.spec:
            print("%5d/%d %-40s %-8s %s" % (i + 1, len(specs), s, k, info), flush=True)
        elif (i + 1) % 100 == 0:
            print("... %d/%d %s" % (i + 1, len(specs), dict(c)), file=sys.stderr, flush=True)
    print("\n=== classification ===")
    for k, v in c.most_common():
        print("  %-8s %d" % (k, v))
    if worst:
        ws = sorted(worst)
        print("\nBOUNDED: largest inter-visit gap seen (a fixed window must exceed this)")
        print("  min=%d  median=%d  max=%d" % (ws[0], ws[len(ws) // 2], ws[-1]))


if __name__ == '__main__':
    main()
