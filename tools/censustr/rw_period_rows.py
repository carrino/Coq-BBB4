#!/usr/bin/env python3
"""Tape-period detector for bouncers -> RepWL probe rows (UNTRUSTED).

Simulate each machine, snapshot the tape at T/4, T/2, T, and report the
smallest block period p (1..maxp) on which each side's non-blank content
is p-periodic on >= 90% of positions.  A bouncer's repeated-word
abstraction finitizes exactly when the RepWL block length is (a multiple
of) that period (state census: REPWL_BIGBLOCK_WAVE8; instruction level:
SCOPING_INSTR §7.1w), so the rows emitted are

    spec  L  T  t  fuel  M        (gen_provtr_rw.py's input)

with L in {p, 2p} (--mults) for each detected p (clipped to [2, maxL]),
T=2, t=0, fuel 30000, node cut 32.  The cut is what makes a wrong L cheap:
a misaligned block never compresses, its nodes grow past 32 items within
a few sweeps and the closure is abandoned in seconds; a matched L keeps
nodes small (measured: certifying closures of 263..19K nodes at cut 32).
With cut 128 / fuel 100K / L up to 4p the box needed hours per machine
(the certificate search on a 100K-node closure).  Measured on 13 sampled bouncers: 8 certify, and for 3 of
them only the doubled block does (the block must also align with the
sweep's write pattern, which can have period 2p).
Every row is re-checked by the kernel ([RepWLTr.rw_tier_tr_sound]); a
wrong period merely fails.

Usage: rw_period_rows.py LIST [--steps 20000] [--maxp 40] [--maxl 24]
                              [--fuel 30000] [--cut 32] [--mults 1,2] > rows.tsv
"""
import argparse
import sys


def parse(spec):
    tab = {}
    for si, part in enumerate(spec.split('_')):
        for yi in range(2):
            e = part[3 * yi:3 * yi + 3]
            tab[(si, yi)] = None if e == '---' else (
                int(e[0]), +1 if e[1] == 'R' else -1, ord(e[2]) - ord('A'))
    return tab


def best_period(s, maxp):
    n = len(s)
    if n < 12:
        return None
    for p in range(1, maxp + 1):
        if 3 * p > n:
            break
        agree = sum(1 for i in range(n - p) if s[i] == s[i + p])
        if agree >= 0.9 * (n - p):
            return p
    return None


def periods(spec, T, maxp):
    tab = parse(spec)
    tape = {}
    q = pos = 0
    out = set()
    for t in range(1, T + 1):
        r = tape.get(pos, 0)
        tr = tab[(q, r)]
        if tr is None:
            return set()
        w, d, nq = tr
        tape[pos] = w
        pos += d
        q = nq
        if t in (T // 4, T // 2, T):
            lo, hi = min(tape), max(tape)
            left = [tape.get(i, 0) for i in range(pos - 1, lo - 1, -1)]
            right = [tape.get(i, 0) for i in range(pos + 1, hi + 1)]
            for side in (left, right):
                p = best_period(side, maxp)
                if p:
                    out.add(p)
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('list')
    ap.add_argument('--steps', type=int, default=20000)
    ap.add_argument('--maxp', type=int, default=40)
    ap.add_argument('--maxl', type=int, default=24)
    ap.add_argument('--fuel', type=int, default=30000)
    ap.add_argument('--cut', type=int, default=32)
    ap.add_argument('--mults', default='1,2',
                    help='block multiples of the period to emit (default 1,2)')
    a = ap.parse_args()
    nrows = nm = 0
    for line in open(a.list):
        m = line.strip()
        if not m:
            continue
        nm += 1
        Ls = set()
        for p in periods(m, a.steps, a.maxp):
            for L in (p * int(k) for k in a.mults.split(',')):
                if 2 <= L <= a.maxl:
                    Ls.add(L)
        for L in sorted(Ls):
            print('%s\t%d\t2\t0\t%d\t%d' % (m, L, a.fuel, a.cut))
            nrows += 1
    sys.stderr.write('rw_period_rows: %d machines -> %d rows\n' % (nm, nrows))


if __name__ == '__main__':
    main()
