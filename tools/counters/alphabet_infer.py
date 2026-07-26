#!/usr/bin/env python3
"""UNTRUSTED: INFER the counter word family instead of guessing it.

Six alphabets have now been added to this project one at a time, five of them
because a human read a tape: [Ip]/[Jp] (marker before each bit), [Mp] (marker
after), [Kp] (no separator), [Dp] (doubled bits) and, this wave, [Bp] (bits
separated by a BLANK).  Each cost a reading and a build, and
WAVE13_FINDINGS.md put "widening the ENCODING table" on do-not-retry because
widening it ON SPEC bought almost nothing.

But every one of those six has the SAME SHAPE -- a positive-recursion with
three fixed words:

    E xH     = C
    E (xO q) = A ++ E q
    E (xI q) = B ++ E q

and that shape determines an ENCDATA row completely.  With p having j trailing
ones over a clear bit and a high part q0,

    interior   E p        = rep B j ++ A ++ E q0     ->  uS = B, sS = A
               E (succ p) = rep A j ++ B ++ E q0     ->  uD = A, sD = B
    overflow   E p        = rep B j ++ C             ->  obS = 0, soS = C
               E (succ p) = rep A (S j) ++ C         ->  soD = C

(Check: A=[S1;S0], B=[S1;S1], C=[S1] reproduces the [Ip] row verbatim, and
A=[S0;S0], B=[S0;S1], C=[S0;S1] reproduces [Bp].)

So the alphabet does not have to be guessed at all.  Take the anchor snapshots
at one (state, side, tail, far), assume they are E(1), E(2), E(3), ... in time
order, and READ A, B and C off the first three:

    C = E(1)                     A = E(2) with E(1) stripped from its right
                                 B = E(3) with E(1) stripped from its right

then VERIFY the recursion against every remaining snapshot.  A family that
survives 30+ words is not a coincidence, and it hands you the ENCDATA row and
the Coq fixpoint mechanically.

[Gp] (Gray) is deliberately NOT of this shape -- its lap flips a cell of the
high part -- which is why it needed its own file and is not inferable here.

Nothing here is trusted: it emits a candidate row, and the Coq kernel
re-checks every board built from it.
"""
import argparse
import collections
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

from emit_interleave import parse                                  # noqa: E402
import lapcert as LC                                               # noqa: E402

LAB = 'ABCD'


def snapshots(spec, T, maxtail, cap=160):
    """(state, side, tail, far) -> [near word] in TIME order, at blank-head
    configurations.  The near word keeps its tail so the caller can split.

    [cap] bounds the words kept per key: verifying the recursion on 160 words
    is already conclusive, and without the bound a 120k-step scan over four
    tail splits and two sides exhausts memory on the longer runs."""
    tab = parse(spec)
    cfg = (0, (), 0, ())
    out = collections.defaultdict(list)
    for t in range(T):
        q, l, h, r = cfg
        if h == 0:
            ls, rs = LC.rstrip0(l), LC.rstrip0(r)
            for side, near, far in (('L', ls, rs), ('R', rs, ls)):
                if not near:
                    continue
                for k in range(maxtail + 1):
                    if k > len(near) - 1:
                        break
                    head = near[:len(near) - k] if k else near
                    tail = near[len(near) - k:] if k else ()
                    k2 = (q, side, tail, far)
                    if len(out[k2]) < cap:
                        out[k2].append(head)
        try:
            cfg = LC.wstep(tab, False, False, cfg)
        except LC.Halt:
            break
    return out


def strip_suffix(word, suf):
    """word = pre ++ suf  ->  pre, else None."""
    if len(word) <= len(suf):
        return None
    if suf and tuple(word[len(word) - len(suf):]) != tuple(suf):
        return None
    return tuple(word[:len(word) - len(suf)])


def infer(words, minlen=24):
    """Read (A, B, C) off the first three words and verify the recursion on
    every word available.  [words] must be E(1), E(2), E(3), ... in order."""
    if len(words) < minlen:
        return None
    C = tuple(words[0])
    A = strip_suffix(words[1], C)
    B = strip_suffix(words[2], C)
    if not A or not B or A == B:
        return None

    def E(m):
        if m == 1:
            return C
        return (A if m % 2 == 0 else B) + E(m // 2)

    n = 0
    for i, w in enumerate(words):
        if i >= 160:
            break
        if tuple(w) != E(i + 1):
            return None
        n += 1
    return dict(A=list(A), B=list(B), C=list(C), verified=n)


def encdata_row(A, B, C):
    """The ENCDATA row this alphabet induces (see the module docstring)."""
    return dict(uS=tuple(B), sS=tuple(A), uD=tuple(A), sD=tuple(B),
                obS=0, soS=tuple(C), soD=tuple(C))


def best_family(spec, T=120000, maxtail=3, minlen=24):
    out = []
    for key, words in snapshots(spec, T, maxtail).items():
        # keep the longest run of words whose lengths are non-decreasing and
        # which start at the shortest -- E(1), E(2), ... is such a run
        if len(words) < minlen:
            continue
        r = infer(words, minlen)
        if r:
            r['key'] = (LAB[key[0]], key[1], list(key[2]), list(key[3]))
            out.append(r)
    out.sort(key=lambda r: -r['verified'])
    return out[0] if out else None


KNOWN = {
    (((1, 0)), ((1, 1)), ((1,))): 'Ip',
    (((1, 1)), ((1, 0)), ((1,))): 'Jp',
    (((0,)), ((1,)), ((1,))): 'Kp',
    (((0, 0)), ((1, 1)), ((1, 1))): 'Dp',
    (((0, 1)), ((1, 1)), ((1, 1))): 'Mp',
    (((0, 0)), ((0, 1)), ((0, 1))): 'Bp',
}


def name_of(r):
    return KNOWN.get((tuple(r['A']), tuple(r['B']), tuple(r['C'])), 'NEW')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--list')
    ap.add_argument('--spec')
    ap.add_argument('-T', type=int, default=120000)
    ap.add_argument('--minlen', type=int, default=24)
    a = ap.parse_args()
    specs = ([a.spec] if a.spec else
             [l.strip() for l in open(a.list) if l.strip()])
    c = collections.Counter()
    fams = collections.defaultdict(list)
    for i, s in enumerate(specs):
        try:
            r = best_family(s, a.T, 3, a.minlen)
        except Exception:                                          # noqa: BLE001
            r = None
        if r is None:
            c['none'] += 1
            print('%5d/%d %-40s -' % (i + 1, len(specs), s), flush=True)
            continue
        nm = name_of(r)
        c[nm] += 1
        fams[(tuple(r['A']), tuple(r['B']), tuple(r['C']))].append(s)
        print('%5d/%d %-40s %-4s A=%s B=%s C=%s  (%d words, state %s %s)'
              % (i + 1, len(specs), s, nm, r['A'], r['B'], r['C'],
                 r['verified'], r['key'][0], r['key'][1]), flush=True)
    print('\n=== families ===')
    for k, v in sorted(fams.items(), key=lambda kv: -len(kv[1])):
        print('%5d  A=%-8s B=%-8s C=%-8s  %-4s  e.g. %s'
              % (len(v), list(k[0]), list(k[1]), list(k[2]),
                 KNOWN.get(k, 'NEW'), v[0]))
    print('  none: %d' % c['none'])


if __name__ == '__main__':
    main()
