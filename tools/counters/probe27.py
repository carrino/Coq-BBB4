#!/usr/bin/env python3
"""Step-level probe for wave machine #27 (1RB1LC_1LC0RD_0LC1LA_1RB1RD).

Mirrors CTape.cstep EXACTLY (cconf = (state,(left,head,right)), left nearest-
first, blanks materialised as S0 at the edges).  Used to extract the exact
gadget windows (FT, cross-pair, sep-continue, deposit, return units) for the
Coq transcription of Wave_27.v, and to confirm the full cls1/cls2 pass lands
exactly on Cf27(nextf 1 front).

Usage: probe27.py [front...]   e.g. probe27.py 4 2 1
"""
import sys

# tm_27: state x sym -> (write, dir, next).  dir: +1=R, -1=L.  states A,B,C,D=0..3
# 1RB1LC_1LC0RD_0LC1LA_1RB1RD
TM = {
    (0, 0): (1, +1, 1), (0, 1): (1, -1, 2),   # A0=1RB A1=1LC
    (1, 0): (1, -1, 2), (1, 1): (0, +1, 3),   # B0=1LC B1=0RD
    (2, 0): (0, -1, 2), (2, 1): (1, -1, 0),   # C0=0LC C1=1LA
    (3, 0): (1, +1, 1), (3, 1): (1, +1, 3),   # D0=1RB D1=1RD
}
LAB = "ABCD"
POFF = 1


def chd(l): return l[0] if l else 0
def ctl(l): return l[1:] if l else []


def cstep(c):
    st, (l, h, r) = c
    w, d, ns = TM[(st, h)]
    if d == +1:   # DR: (w::l, chd r, ctl r)
        return (ns, ([w] + l, chd(r), ctl(r)))
    else:         # DL: (ctl l, chd l, w::r)
        return (ns, (ctl(l), chd(l), [w] + r))


def show(c):
    st, (l, h, r) = c
    ls = ''.join(str(x) for x in reversed(l))
    rs = ''.join(str(x) for x in r)
    return f"{LAB[st]} [{ls}]({h})[{rs}]"


def wbody(front):
    if not front:
        return [1]
    b, r = front[0], front[1:]
    return [1] * b + [0] + wbody(r)


def carry(po, blocks):
    if not blocks:
        return [] if po else [1]
    b, r = blocks[0], blocks[1:]
    if po:
        return [b + 1] + r
    return [b] + carry(b % 2 == 1, r)


def nextf(poff, front):
    if not front:
        return []
    b0, r = front[0], front[1:]
    return [b0 + 1] + carry((b0 + poff) % 2 == 1, r)


def Cf(front):
    return (3, (list(reversed(wbody(front)))[::-1], 0, []))


def Cf27(front):
    # (StD, (wbody front, S0, []))  -- left list is wbody (nearest-first == as written)
    return (3, (wbody(front), 0, []))


def run_to_event(front, verbose=True):
    c = Cf27(front)
    target = Cf27(nextf(POFF, front))
    steps = 0
    if verbose:
        print(f"  start Cf27{front} = {show(c)}")
    hist = [c]
    for _ in range(200000):
        c = cstep(c)
        steps += 1
        hist.append(c)
        # detect arrival at next event: state D, head S0, right empty, back at edge
        st, (l, h, r) = c
        if st == 3 and h == 0 and r == [] and l and l[0] == 1 and steps > 1:
            # candidate event; check equals target modulo trailing blanks
            if l == target[1][0]:
                if verbose:
                    print(f"  END   Cf27{nextf(POFF,front)} = {show(c)}  ({steps} steps)")
                return steps, hist, c == target or l == target[1][0]
    print("  NO EVENT")
    return steps, hist, False


def trace(front):
    print(f"=== front={front}  nextf={nextf(POFF,front)} ===")
    steps, hist, ok = run_to_event(front)
    print(f"  match={ok}")
    for i, c in enumerate(hist):
        st, (l, h, r) = c
        marker = ""
        print(f"   {i:3d}: {show(c)}{marker}")
    return steps


if __name__ == "__main__":
    front = [int(x) for x in sys.argv[1:]] or [4, 2, 1]
    trace(front)
