#!/usr/bin/env python3
"""UNTRUSTED: the MSB-FIRST marker encoding.

Human read of 0RB0RC_1LC1RB_0LD1RA_1RC1LD: "a 1 to the left of each bit, MSB is
on the left."

Every decoder in this project reads the near side NEAREST-FIRST, i.e. LSB
nearest the head, marker BEFORE each bit in that order.  This one is the other
orientation: in true tape order (left to right) the word is

    WALL ++ (1 b_{k-1}) (1 b_{k-2}) ... (1 b_0) ++ SUFFIX

with the MOST significant bit leftmost -- so read nearest-first it is
data-first with the markers on the far side of each bit, which the marker-first
tables can never match.

Searches wall/suffix lengths, anchor state, head symbol and side, and requires
the decoded values to be consecutive and ASCENDING IN TIME.
"""
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


def step(tab, cfg):
    q, l, h, r = cfg
    e = tab[(q, h)]
    if e is None:
        return None
    w, d, ns = e
    if d > 0:
        return (ns, [w] + l, r[0] if r else 0, r[1:])
    return (ns, l[1:], l[0] if l else 0, [w] + r)


def strip0(l):
    i = len(l)
    while i > 0 and l[i - 1] == 0:
        i -= 1
    return list(l[:i])


def decode(word, nw, ns, marker=1, mfirst=True, msb_left=True):
    """word is in TAPE order.  Drop nw wall cells and ns suffix cells, then
    read 2-cell groups.

    Two INDEPENDENT orientation axes, and the repo had only ever formalized one
    corner of the square:
      mfirst   the marker sits BEFORE the bit in tape order (True) or AFTER it
               (False) -- "1 to the left of each bit" vs "1 to the right".
      msb_left the most significant bit is leftmost (True) or rightmost.
    Ip/Jp are mfirst=True, msb_left=False read nearest-first from the head.
    """
    body = word[nw:len(word) - ns] if ns else word[nw:]
    if not body or len(body) % 2:
        return None
    bits = []
    for i in range(0, len(body), 2):
        m, b = (body[i], body[i + 1]) if mfirst else (body[i + 1], body[i])
        if m != marker:
            return None
        bits.append(b)
    if not bits:
        return None
    if not msb_left:
        bits = bits[::-1]
    v = 0
    for b in bits:
        v = v * 2 + b
    return v


def scan(spec, T=120000, minrun=10):
    tab = parse(spec)
    cfg = (0, [], 0, [])
    hits = {}
    for t in range(T):
        q, l, h, r = cfg
        for side in ('L', 'R'):
            near, far = (strip0(l), strip0(r)) if side == 'L' else (strip0(r), strip0(l))
            if len(far) > 4 or not near:
                continue
            word = list(reversed(near)) if side == 'L' else list(near)
            for nw in range(0, 4):
                for ns in range(0, 4):
                    for marker in (0, 1):
                        for mfirst in (True, False):
                            for msbl in (True, False):
                                v = decode(word, nw, ns, marker, mfirst, msbl)
                                if v is not None and v > 1:
                                    hits.setdefault(
                                        (LAB[q], h, side, nw, ns, marker,
                                         mfirst, msbl, tuple(far)),
                                        []).append((t, v))
        cfg = step(tab, cfg)
        if cfg is None:
            return None
    best = None
    for key, evs in hits.items():
        first = {}
        for t, v in evs:
            if v not in first:
                first[v] = t
        vs = sorted(first)
        run, bestrun, start = 1, 0, None
        for i in range(1, len(vs)):
            if vs[i] == vs[i - 1] + 1 and first[vs[i]] > first[vs[i - 1]]:
                run += 1
            else:
                if run > bestrun:
                    bestrun, start = run, vs[i - run]
                run = 1
        if run > bestrun:
            bestrun, start = run, vs[len(vs) - run]
        if bestrun < minrun:
            continue
        if best is None or bestrun > best[0]:
            best = (bestrun, key, start)
    return best


if __name__ == '__main__':
    for spec in sys.argv[1:]:
        b = scan(spec)
        if b is None:
            print("%-30s no MSB-first fit" % spec)
        else:
            run, (st, h, side, nw, ns, mk, mf, ml, far), p0 = b
            print("%-30s state=%s head=S%d side=%s wall=%d suf=%d marker=S%d "
                  "marker-%s msb-%s far=%s  run=%d from p=%d"
                  % (spec, st, h, side, nw, ns, mk,
                     'left' if mf else 'right', 'left' if ml else 'right',
                     list(far), run, p0))
