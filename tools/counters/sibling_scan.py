#!/usr/bin/env python3
"""Is this machine an already-boarded machine in disguise?  (UNTRUSTED)

Two different questions, and the difference matters:

 1. **Relabelling that FIXES StA** (a permutation of {B,C,D}), optionally
    composed with the mirror.  This IS a proof transport: CloseoutKit's
    [boarded_unswap] (any transposition of non-start states) and
    [boarded_unmirror] chain to give the theorem for free.  The census's
    [Deferred] relation is already closed under exactly this orbit, so a hit
    here on a frozen row would be a bookkeeping bug, not a new proof --
    expect none.

 2. **Relabelling that MOVES StA.**  NOT a proof transport: the boarded
    theorem is about the same transition table started in a *different*
    state, and NeverQuasiHaltsSt is a statement about the blank-tape run
    from StA.  But it is worth a lot anyway:

      - the per-machine Coq file transcribes under the substitution (this is
        how Wave_24.v was produced from Wave_6.v -- see
        docs/HOLDOUTS_WAVE14.md S2 -- and it compiled on the first try; only
        the machine table, the boot count and the vis offsets are new);
      - if the sibling was boarded by a CHECKER (NGramHist, RepWL, irules),
        the hit says this machine's dynamics are inside that checker's reach,
        so running the checker on the machine itself is worth a try.

Usage:  sibling_scan.py [MACHINE_LIST]
        (default: the unproven holdouts, i.e. census_holdouts_kept.txt
         intersected with tools/closeout/frozen_unproven.txt)
"""
import csv
import itertools
import os
import sys

ROOT = os.path.dirname(os.path.dirname(
    os.path.dirname(os.path.abspath(__file__))))


def parse(spec):
    t = {}
    for si, part in enumerate(spec.split('_')):
        for yi in range(2):
            e = part[3 * yi:3 * yi + 3]
            t[(si, yi)] = None if e == '---' else (
                int(e[0]), e[1], ord(e[2]) - 65)
    return t


def fmt(t):
    return '_'.join(
        ''.join('---' if t[(s, y)] is None
                else '%d%s%s' % (t[(s, y)][0], t[(s, y)][1],
                                 chr(65 + t[(s, y)][2]))
                for y in range(2))
        for s in range(4))


def mirror(t):
    return {k: (None if v is None else (v[0], 'L' if v[1] == 'R' else 'R', v[2]))
            for k, v in t.items()}


def relabel(t, perm):
    """perm[old_state_index] = new_state_index."""
    out = {}
    for (s, y), v in t.items():
        out[(perm[s], y)] = None if v is None else (v[0], v[1], perm[v[2]])
    return out


def boarded_index():
    """spec -> board file.  The closeout inventory is authoritative for the
    frozen rows; the counters manifest adds the hand-written boards whose
    machines are NOT in D_census (decided by the census tier, but still a
    proven theorem we can transcribe from)."""
    idx = {}
    for rel, col in [('tools/closeout/frozen_map.tsv', 2),
                     ('tools/counters_manifest.tsv', 2)]:
        path = os.path.join(ROOT, rel)
        if not os.path.exists(path):
            continue
        for row in csv.reader(open(path), delimiter='\t'):
            if row and row[0] != 'machine':
                idx.setdefault(row[0], row[col].split('/')[-1])
    return idx


def targets():
    if len(sys.argv) > 1:
        return [l.strip() for l in open(sys.argv[1]) if l.strip()]
    rem = set(open(os.path.join(ROOT, 'tools/closeout/frozen_unproven.txt'))
              .read().split())
    hold = [l.strip() for l in
            open(os.path.join(ROOT, 'tools/census_holdouts_kept.txt'))
            if l.strip()]
    return [h for h in hold if h in rem]


def main():
    idx = boarded_index()
    tgts = targets()
    print("scanning %d machines against %d boarded" % (len(tgts), len(idx)))
    nfix = nmove = 0
    for h in tgts:
        th = parse(h)
        fixed, moved = [], []
        for mir in (False, True):
            base = mirror(th) if mir else th
            for p in itertools.permutations(range(4)):
                cand = fmt(relabel(base, list(p)))
                if cand in idx:
                    (fixed if p[0] == 0 else moved).append(
                        (mir, p, cand, idx[cand]))
        if fixed:
            nfix += 1
            print("  %s" % h)
            for mir, p, c, f in fixed:
                print("      TRANSPORT (StA fixed) mirror=%d perm=%s <- %s (%s)"
                      % (mir, p, c, f))
        if moved:
            nmove += 1
            if not fixed:
                print("  %s" % h)
            for mir, p, c, f in moved[:3]:
                print("      transcribe (StA moved) mirror=%d perm=%s <- %s (%s)"
                      % (mir, p, c, f))
    print("hits: %d transportable, %d transcribable, %d targets"
          % (nfix, nmove, len(tgts)))


if __name__ == '__main__':
    main()
