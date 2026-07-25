#!/usr/bin/env python3
"""Counter-encoding classifier for the (4,2) residue -- UNTRUSTED diagnosis.

Decides, per machine, whether the tape holds a plain binary counter and in WHICH
encoding, by decoding wall-anchored tape snapshots and requiring the decoded
integers to be CONSECUTIVE -- both early and again in a LATE window at large
counter values (a decode that works at value 6 but breaks at 10^3 is not a
decode).

Two encoding families, both = "interleaved counter with stride k" (the emitter's
stride parameter, COUNTER_EMITTER_WAVE8.md WAVE-2):
  KCOPY<k>  each bit stored in k IDENTICAL copies  (k=3 => "3x wider counter")
  SEP<k>    one data cell per k-cell block, other cells a constant separator
            (k=2 => "a counter with 0 between bits")

Design notes, each earned by a wrong answer this tool used to give:
  * the anchor cell is NOT the tape extreme -- the extreme is often visited once
    while the real per-lap turnaround sits 1-2 cells inward (the wall "gets some
    activity" when the low bit is incremented), so candidate refs are searched;
  * every state seen at the anchor is tried, not just the most frequent one;
  * the frontier (highest) digit group is allowed to be ragged -- it is
    mid-construction on a growing counter;
  * popcount OSCILLATES on a counter (7=111 -> 3 ones, 8=1000 -> 1), so a flat
    ones-count is NOT evidence that the value lives in gap lengths.

Nothing here carries proof weight; it only routes machines to a Coq route.

Usage: python3 tools/kcopy_classify.py <machine> [<machine> ...]
       python3 tools/kcopy_classify.py < machines.txt
"""
import sys
from collections import Counter, defaultdict

def parse(m):
    tbl = {}
    for qi, part in enumerate(m.split('_')):
        for si in range(2):
            e = part[3*si:3*si+3]
            tbl[(qi, si)] = None if e == '---' else (
                int(e[0]), 1 if e[1] == 'R' else -1, ord(e[2]) - 65)
    return tbl

def wall_side(m, base=20_000, steps=2_000_000):
    tbl = parse(m); N = 4_200_000
    tape = bytearray(N); pos = N//2; mn = mx = pos; q = 0
    for step in range(1, steps+1):
        s = tape[pos]; tr = tbl[(q, s)]
        if tr is None: return None, None, None
        w, d, q2 = tr
        tape[pos] = w; pos += d; q = q2
        if pos < mn: mn = pos
        elif pos > mx: mx = pos
        if step == base: mn1, mx1 = mn, mx
    dl, dr = mn1 - mn, mx - mx1
    if dl > 3 and dl > 3*dr: return 'R', mx1, N//2
    if dr > 3 and dr > 3*dl: return 'L', mn1, N//2
    return '?', None, None

def collect(m, wall, ref, steps=6_000_000, per_state=40, skip=0):
    """Snapshots grouped by anchor state: state -> [tape strings], taking
    anchors AFTER `skip` wall-visits (to reach large counter values)."""
    tbl = parse(m); N = 4_200_000
    tape = bytearray(N); pos = N//2; q = 0; lo = hi = N//2
    out = defaultdict(list); nvis = 0
    for step in range(1, steps+1):
        if pos == ref:
            nvis += 1
            if nvis > skip:
                seg = tape[lo:ref+1] if wall == 'R' else tape[ref:hi+1]
                if len(out[q]) < per_state:
                    out[q].append(''.join(str(b) for b in seg))
                if all(len(v) >= per_state for v in out.values()) and len(out) >= 2:
                    if sum(len(v) for v in out.values()) >= per_state*len(out):
                        break
        s = tape[pos]; tr = tbl[(q, s)]
        if tr is None: break
        w, d, q2 = tr
        tape[pos] = w; pos += d; q = q2
        if pos < lo: lo = pos
        elif pos > hi: hi = pos
    return out

def dec_kcopy(s, k, off, msb, minb=3):
    s = s[off:]; bits = []
    for i in range(0, len(s)-k+1, k):
        b = s[i:i+k]
        if b.count(b[0]) != k: break
        bits.append(1 if b[0] == '1' else 0)
    if len(bits) < minb: return None
    if msb: bits = bits[::-1]
    v = 0
    for i, b in enumerate(bits): v |= b << i
    return v

def dec_sep(s, k, off, dpos, msb, minb=3):
    s = s[off:]; bits = []; sv = None
    for i in range(0, len(s)-k+1, k):
        b = s[i:i+k]
        seps = [b[j] for j in range(k) if j != dpos]
        if sv is None and seps: sv = seps[0]
        if seps and any(c != sv for c in seps): break
        bits.append(1 if b[dpos] == '1' else 0)
    if len(bits) < minb: return None
    if msb: bits = bits[::-1]
    v = 0
    for i, b in enumerate(bits): v |= b << i
    return v

def candidates():
    c = []
    for k in (1, 2, 3, 4):
        for off in range(0, k+3):
            for msb in (False, True):
                c.append(('KCOPY%d' % k, k, off, None, msb))
    for k in (2, 3, 4):
        for off in range(0, k+3):
            for dpos in range(k):
                for msb in (False, True):
                    c.append(('SEP%d' % k, k, off, dpos, msb))
    return c

def score(segs, wall, kind, k, off, dpos, msb):
    vals = []
    for seg in segs:
        s = seg[::-1] if wall == 'R' else seg
        v = (dec_kcopy(s, k, off, msb) if dpos is None
             else dec_sep(s, k, off, dpos, msb))
        if v is not None: vals.append(v)
    if len(vals) < 6: return None
    d = [vals[i+1]-vals[i] for i in range(len(vals)-1)]
    unit = sum(1 for x in d if x == 1)
    return unit, sum(1 for x in d if x > 0), vals

def classify(m, late_skip=3000):
    """The anchor cell is NOT the tape extreme: the extreme is often visited
    once while the real per-lap turnaround sits a cell or two inward (the wall
    "gets some activity" on low-bit increments).  So search a few candidate
    reference cells inward from the fixed side."""
    wall, ext, _ = wall_side(m)
    if wall in (None, '?'): return dict(m=m, verdict='NO_WALL', wall=wall)
    res = dict(m=m, wall=wall)
    best = None
    step_in = 1 if wall == 'L' else -1
    for j in range(0, 5):
        ref = ext + j*step_in
        early = collect(m, wall, ref, per_state=24, skip=0)
        for q, segs in early.items():
            if len(segs) < 8: continue
            for kind, k, off, dpos, msb in candidates():
                sc = score(segs[-16:], wall, kind, k, off, dpos, msb)
                if sc is None: continue
                unit, inc, vals = sc
                if best is None or (unit, inc) > best[0]:
                    best = ((unit, inc), kind, k, off, dpos, msb, q, vals[:8], ref, j)
        if best is not None and best[0][0] >= 12:
            break                              # a clean read; stop searching
    if best is None:
        return dict(res, verdict='MIXED')
    (unit, inc), kind, k, off, dpos, msb, q, vals, ref, j = best
    if unit < 4:
        return dict(res, verdict='MIXED', best_unit=unit)
    # LATE-WINDOW confirmation at large counter values
    late = collect(m, wall, ref, per_state=24, skip=late_skip)
    lsc = score(late.get(q, [])[-16:], wall, kind, k, off, dpos, msb)
    late_ok = lsc is not None and lsc[0] >= 4
    return dict(res, verdict=kind if late_ok else kind + '_EARLY_ONLY',
                k=k, off=off, dpos=dpos, msb=msb, anchor_state=chr(65+q),
                anchor_inward=j, unit=unit, vals=vals,
                late_unit=(lsc[0] if lsc else None),
                late_vals=(lsc[2][:6] if lsc else None))

if __name__ == '__main__':
    ms = sys.argv[1:] or [l.strip() for l in sys.stdin if l.strip()]
    t = Counter()
    for m in ms:
        r = classify(m); t[r['verdict']] += 1
        x = ''
        if r.get('k'):
            x = (f" k={r['k']} off={r['off']} dpos={r['dpos']} msb={r['msb']}"
                 f" anchor={r['anchor_state']} early={r['vals']}"
                 f" late_unit={r.get('late_unit')} late={r.get('late_vals')}")
        print(f"{m}\t{r['verdict']}\twall={r.get('wall')}{x}", flush=True)
    print("TALLY:", dict(t), file=sys.stderr)
