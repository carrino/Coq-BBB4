#!/usr/bin/env python3
"""UNTRUSTED: anchor AT THE CARRY -- the counter straddles the head.

Every scan in the tree (and every scan I ran earlier this session) pins the
anchor's head to a fixed offset from a tape end.  John's reading of
1RB---_1RC1LB_0LB1RD_0RA0RC is a plain binary counter, MSB to the LEFT, one
marker cell to the left of every bit, read at the moment the head sits on the
carry's stop bit -- so the head is INSIDE the word at a value-dependent
position and no such scan can see it.

Signature searched here, at each (state, head symbol):

    L (nearest-first) = pre ++ digits(low first) ++ term
    R (nearest-first) = rep u j                       (the carry run)
    value             = q0 * 2^(j+1) + (2^j - 1)

with q0 read from the digits.  That is [MonoCounter.cview] read backwards:
p's binary is q0, then the stop 0, then j ones.
"""
import itertools
import sys
from collections import defaultdict

LAB = "ABCD"


def parse(code):
    tm = {}
    for i, blk in enumerate(code.split("_")):
        q = LAB[i]
        for s in (0, 1):
            t = blk[3 * s:3 * s + 3]
            tm[(q, s)] = None if t == "---" else (int(t[0]), t[1], t[2])
    return tm


class Sim:
    """The raw machine, with conf() returning (state, left, head, right) --
    both sides nearest-first and stripped of trailing blanks."""

    def __init__(self, tm):
        from collections import defaultdict
        self.tm = tm
        self.tape = defaultdict(int)
        self.pos = 0
        self.q = 'A'
        self.lo = self.hi = 0

    def step(self):
        tr = self.tm[(self.q, self.tape[self.pos])]
        if tr is None:
            return False
        w, d, n = tr
        self.tape[self.pos] = w
        self.pos += 1 if d == 'R' else -1
        self.q = n
        self.lo = min(self.lo, self.pos)
        self.hi = max(self.hi, self.pos)
        return True

    def conf(self):
        left = [self.tape[i] for i in range(self.pos - 1, self.lo - 1, -1)]
        right = [self.tape[i] for i in range(self.pos + 1, self.hi + 1)]
        while left and left[-1] == 0:
            left.pop()
        while right and right[-1] == 0:
            right.pop()
        return (self.q, left, self.tape[self.pos], right)


def snaps(code, T=400000, cap=200):
    tm = parse(code)
    sm = Sim(tm)
    G = defaultdict(list)
    for t in range(T):
        q, l, h, r = sm.conf()
        g = G[(q, h)]
        if len(g) < cap:
            g.append((t, tuple(l), tuple(r)))
        if not sm.step():
            break
    return G


def runlen(r, u):
    """j with r = u^j (exactly), else None."""
    if len(r) % len(u):
        return None
    j = len(r) // len(u)
    return j if all(r[i * len(u):(i + 1) * len(u)] == u for i in range(j)) else None


def one(l, r, pre, term, w, u, d0, d1, pad):
    """The value of a single snapshot, or None if it does not parse.
    [pad] blank cells are restored past the far end of L (conf() strips
    them, and the counter's terminator may be one of them)."""
    l = l + (0,) * pad
    j = runlen(r, u)
    if j is None or len(l) < pre + term:
        return None
    body = l[pre:len(l) - term] if term else l[pre:]
    if not body or len(body) % w:
        return None
    q0 = 0
    for k in range(len(body) // w - 1, -1, -1):
        d = body[k * w:(k + 1) * w]
        if d == d0:
            b = 0
        elif d == d1:
            b = 1
        else:
            return None
        q0 = q0 * 2 + b
    return q0 * 2 ** (j + 1) + 2 ** j - 1


def decode(sel, pre, term, w, u, d0, d1, pad):
    """Longest run of CONSECUTIVE values among snapshots that parse.  A
    snapshot that does not parse breaks the run rather than the search:
    the reset phase of an epoch passes through the same (state, head) pair
    without being an anchor."""
    vals = [one(l, r, pre, term, w, u, d0, d1, pad) for _, l, r in sel]
    run = brun = 0
    bstart = 0
    for i, v in enumerate(vals):
        if v is None:
            run = 0
            continue
        if run and vals[i - 1] is not None and v == vals[i - 1] + 1:
            run += 1
        else:
            run, start = 1, i
        if run > brun:
            brun, bstart = run, (start if run == 1 else start)
    if brun < 10:
        return None
    return brun, [v for v in vals[bstart:bstart + 8]]


UNITS = [(1,), (1, 1), (0, 1), (1, 0), (1, 1, 1)]
DIGS = [((0, 1), (1, 1)), ((1, 0), (1, 1)), ((0, 0), (1, 0)), ((0, 0), (0, 1)),
        ((0,), (1,)), ((0, 0), (1, 1)), ((1, 1), (0, 1)), ((1, 1), (1, 0))]


def analyse(code):
    best = None
    for (q, h), sel in snaps(code).items():
        if len(sel) < 14:
            continue
        for pre in (0, 1, 2):
            for term in (0, 1, 2):
                for u in UNITS:
                    for d0, d1 in DIGS:
                        if len(d0) != len(d1):
                            continue
                        for pad in (0, 1, 2):
                            got = decode(sel, pre, term, len(d0), u, d0, d1, pad)
                            if got and (best is None or got[0] > best[0]):
                                best = (got[0], q, h, pre, term, u, d0, d1,
                                        got[1])
    return best


for code in [l.strip() for l in open(sys.argv[1]) if l.strip()]:
    b = analyse(code)
    if b is None:
        print('%-32s -- no carry-anchored decode' % code)
    else:
        s = lambda t: ''.join(map(str, t))
        print('%-32s run=%-4d state=%s head=%d pre=%d term=%d run-unit=%s '
              'digits %s/%s\n%34svalues=%s'
              % (code, b[0], b[1], b[2], b[3], b[4], s(b[5]), s(b[6]), s(b[7]),
                 '', b[8]))
