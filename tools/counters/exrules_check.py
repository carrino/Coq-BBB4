#!/usr/bin/env python3
"""UNTRUSTED: a sound REJECTION filter for mxdys' ExtraRules obligations.

Stage 0 (docs/MXDYS_INDUCTIVE_STAGE0.md) established that his Inductive
decider eats the counter families only when handed a hint -- an `ExtraRules`,
which is a counter increment/decrement rule stated as a bare `-[tm]->+`
progress fact over (d0, d1, d1a, qL, qR, QL, QR).  That is our anchor family
plus lap certificate in his notation, and `alphabet_infer.py`'s (A,B,C) is his
(d0,d1,d1a) exactly.

The hint space is not searchable -- three unbounded symbol WORDS plus two
states -- so hints must be derived from the run, not gridded.  But derivation
still produces candidates, and running his engine on a candidate costs
seconds.  This filter costs microseconds and REJECTS candidates that cannot
possibly hold.

Soundness of the filter (the only property that matters):
  the obligation is `forall l r n, <src> -[tm]->+ <dst>`, so ANY concrete
  (l, r, n) that fails is a definite counterexample.  We instantiate several
  and reject on the first failure.  Surviving a finite check is NOT a proof --
  the kernel (or his engine) still has to discharge the real obligation.  This
  only ever says NO with authority.

Tape conventions, checked against busycoq/verify/{TM,Helper}.v:
  * both half-tapes are ordered HEAD-OUTWARD (`hd l` is the cell adjacent to
    the head -- see `move_left`), which is also how tools/counters/executor.py
    represents them, so the translation is direct;
  * `l <* xs` = `Str_app xs l` puts xs[0] NEAREST the head, and `<*` is
    left-associative, so `l <* d0 <* d1^^n` = d1^^n ++ d0 ++ l;
  * `A <{{q}} B` = head sits ON A[0], left = A[1:], right = B;
  * `A {{q}}> B` = head sits ON B[0], left = A, right = B[1:];
  * `l ^^ n` = lpow = the word repeated n times.
"""
import argparse
import itertools
import sys

LAB = "ABCD"


def parse(spec):
    """bbchallenge machine text -> {(state, sym): (write, dir, next) | None}."""
    tab = {}
    for si, part in enumerate(spec.split('_')):
        for yi in range(2):
            e = part[3 * yi:3 * yi + 3]
            tab[(si, yi)] = None if e == '---' else (
                int(e[0]), +1 if e[1] == 'R' else -1, ord(e[2]) - ord('A'))
    return tab


def word(s):
    """"010" -> [0,1,0]; "." or "" -> []."""
    if s in ('.', ''):
        return []
    return [int(c) for c in s]


def state(s):
    return ord(s[0]) - ord('A')


class Sim:
    def __init__(self, spec):
        self.tab = parse(spec)

    def step(self, cfg):
        """One TM step on (q, l, h, r); None if the machine halts here."""
        q, l, h, r = cfg
        e = self.tab.get((q, h))
        if e is None:
            return None
        w, d, ns = e
        if d > 0:
            return (ns, [w] + l, (r[0] if r else 0), r[1:])
        return (ns, l[1:], (l[0] if l else 0), [w] + r)


def cfg_from_left_right(left, right, q, came_from):
    """Build (q, l, h, r) from busycoq's directed-head notation.

    came_from == 'L'  ->  `left <{{q}} right`  : head is ON left[0]
    came_from == 'R'  ->  `left {{q}}> right`  : head is ON right[0]
    """
    if came_from == 'L':
        return (q, left[1:], left[0], right)
    return (q, left, right[0], right[1:])


def matches(cfg, left, right, q, came_from, depth):
    """Does cfg equal the target, comparing only `depth` cells per side?

    The unspecified tails (the universally quantified l and r) are padded
    with blanks by the caller, so a prefix comparison of that depth is the
    honest test -- anything deeper is comparing padding to padding.
    """
    want = cfg_from_left_right(left, right, q, came_from)
    wq, wl, wh, wr = want
    gq, gl, gh, gr = cfg
    if gq != wq or gh != wh:
        return False

    def pad(x):
        return (list(x) + [0] * depth)[:depth]

    return pad(gl) == pad(wl) and pad(gr) == pad(wr)


def check_instance(sim, src, dst, budget):
    """Is dst reachable from src in >= 1 steps (progress) within budget?"""
    left, right, q, cf = src
    cfg = cfg_from_left_right(left, right, q, cf)
    dleft, dright, dq, dcf = dst
    depth = max(len(dleft), len(dright)) + 4
    for _ in range(budget):
        cfg = sim.step(cfg)
        if cfg is None:
            return False, "halted"
        if matches(cfg, dleft, dright, dq, dcf, depth):
            return True, "ok"
    return False, "budget"


# --- the rule shapes, transcribed from Inductive.v's ExtraRules_WF ----------

def clauses(kind, p, n, L, R):
    """Return [(src, dst), ...] for one instantiation.

    src/dst are (left, right, q, came_from) with left/right head-outward.
    L, R are the concrete stand-ins for the universally quantified sides.
    """
    d0, d1, d1a, d1b = p['d0'], p['d1'], p['d1a'], p['d1b']
    qL, qR, QL, QR = p['qL'], p['qR'], p['QL'], p['QR']
    out = []

    if kind in ('becpos', 'dec'):
        # forall l r n,
        #   l <* d0 <* d1^^n <{{QL}} qL *> r -->+ l <* d1 <* d0^^n <* qR {{QR}}> r
        out.append(((d1 * n + d0 + L, qL + R, QL, 'L'),
                    (qR + d0 * n + d1 + L, R, QR, 'R')))
    if kind == 'becpos':
        # forall r n, const s0 <* d1a <* d1^^n <{{QL}} qL *> r -->+
        #             const s0 <* d1a <* d0 <* d0^^n <* qR {{QR}}> r
        blank = [0] * 24
        out.append(((d1 * n + d1a + blank, qL + R, QL, 'L'),
                    (qR + d0 * n + d0 + d1a + blank, R, QR, 'R')))
    if kind == 'ov1':
        # forall r n, const s0 <* d1a <* d1^^n <{{QL}} qL *> r -->+
        #             const s0 <* d1b <* d0^^(1+n) <* qR {{QR}}> r
        blank = [0] * 24
        out.append(((d1 * n + d1a + blank, qL + R, QL, 'L'),
                    (qR + d0 * (1 + n) + d1b + blank, R, QR, 'R')))
    if kind == 'ov0':
        blank = [0] * 24
        out.append(((d1 * n + d1a + blank, qL + R, QL, 'L'),
                    (qR + d0 * n + d1b + blank, R, QR, 'R')))
    return out


PADS = [
    ([0] * 24, [0] * 24),                     # both sides blank
    ([1, 0] * 12, [0] * 24),                  # non-blank left
    ([0] * 24, [1, 0] * 12),                  # non-blank right
    ([1, 1, 0] * 8, [0, 1] * 12),             # both non-blank
]


def check(spec, kind, p, nmax=6, budget=20000, pads=PADS):
    """Sound rejection: returns (ok, reason).  ok=False is authoritative."""
    sim = Sim(spec)
    for n in range(nmax + 1):
        for (L, R) in pads:
            for src, dst in clauses(kind, p, n, L, R):
                good, why = check_instance(sim, src, dst, budget)
                if not good:
                    return False, "n=%d %s" % (n, why)
    return True, "survives n<=%d over %d paddings" % (nmax, len(pads))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('spec')
    ap.add_argument('--kind', default='becpos',
                    choices=['becpos', 'dec', 'ov0', 'ov1'])
    ap.add_argument('--d0', default='.')
    ap.add_argument('--d1', default='.')
    ap.add_argument('--d1a', default='.')
    ap.add_argument('--d1b', default='.')
    ap.add_argument('--qL', default='.')
    ap.add_argument('--qR', default='.')
    ap.add_argument('--QL', default='A')
    ap.add_argument('--QR', default='A')
    ap.add_argument('--nmax', type=int, default=6)
    ap.add_argument('--budget', type=int, default=20000)
    a = ap.parse_args()
    p = dict(d0=word(a.d0), d1=word(a.d1), d1a=word(a.d1a), d1b=word(a.d1b),
             qL=word(a.qL), qR=word(a.qR), QL=state(a.QL), QR=state(a.QR))
    ok, why = check(a.spec, a.kind, p, a.nmax, a.budget)
    print("%s  %s  %s" % ("PASS" if ok else "REJECT", a.spec, why))
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
