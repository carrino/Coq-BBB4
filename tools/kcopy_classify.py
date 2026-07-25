#!/usr/bin/env python3
"""Counter-encoding classifier for the (4,2) residue -- UNTRUSTED diagnosis.

Decides, per machine, whether the tape holds a plain binary counter and in WHICH
encoding, by decoding anchored tape snapshots and requiring the decoded integers
to be CONSECUTIVE -- both early and again in a LATE window at large counter
values (a decode that works at value 6 but breaks at 10^3 is not a decode).

Encoding families found in this residue, all = "interleaved counter with stride
k" (the emitter's stride parameter, COUNTER_EMITTER_WAVE8.md WAVE-2):

  KCOPY<k>   each bit stored in k IDENTICAL copies   (k=3 => "3x wider counter")
  SEP<k>     one data cell per k-cell block, the rest a constant separator
             (k=2, separator 1 => "a counter with 1s between bits")
  ...i       suffix: the data bit is INVERTED (0 = set).  This is the complement
             encoding already formalized in theories/Counters/JpCounter.v, whose
             value DESCENDS -- so descending unit runs count as a decode too.

Every design decision below was earned by a wrong answer this tool used to give,
each time corrected by a human reading one machine on bbchallenge:

  * the anchor cell is NOT the tape extreme -- the extreme is often visited once
    while the real per-lap turnaround sits 1-2 cells inward (the wall "gets some
    activity" when the low bit is incremented), so candidate refs are searched;
  * BOTH sides are tried as the anchor side; the growth test is only a hint
    ("no wall on the left" is a real configuration);
  * every state seen at the anchor is tried, not just the most frequent one;
  * the frontier (highest) digit group may be ragged -- it is mid-construction;
  * the anchor can fire several times per increment, so runs of equal decodes
    are collapsed before consecutiveness is judged;
  * bits may be INVERTED and the decoded value may DESCEND;
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
    pref = 'R' if (dl > 3 and dl > 3*dr) else ('L' if (dr > 3 and dr > 3*dl) else '?')
    return pref, mn1, mx1

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

def dec_kcopy(s, k, off, msb, minb=3, inv=False):
    s = s[off:]; bits = []
    one = '0' if inv else '1'
    for i in range(0, len(s)-k+1, k):
        b = s[i:i+k]
        if b.count(b[0]) != k: break
        bits.append(1 if b[0] == one else 0)
    if len(bits) < minb: return None
    if msb: bits = bits[::-1]
    v = 0
    for i, b in enumerate(bits): v |= b << i
    return v

def dec_sep(s, k, off, dpos, msb, minb=3, inv=False):
    """Separator value is INFERRED (may be 1: "1s between bits"); the data bit
    may be INVERTED (inv=True), i.e. the complement encoding of JpCounter.v."""
    s = s[off:]; bits = []; sv = None
    one = '0' if inv else '1'
    for i in range(0, len(s)-k+1, k):
        b = s[i:i+k]
        seps = [b[j] for j in range(k) if j != dpos]
        if sv is None and seps: sv = seps[0]
        if seps and any(c != sv for c in seps): break
        bits.append(1 if b[dpos] == one else 0)
    if len(bits) < minb: return None
    if msb: bits = bits[::-1]
    v = 0
    for i, b in enumerate(bits): v |= b << i
    return v

def candidates():
    c = []
    for inv in (False, True):
        for k in (1, 2, 3, 4):
            for off in range(0, k+3):
                for msb in (False, True):
                    c.append(('KCOPY%d' % k + ('i' if inv else ''),
                              k, off, None, msb, inv))
        for k in (2, 3, 4):
            for off in range(0, k+3):
                for dpos in range(k):
                    for msb in (False, True):
                        c.append(('SEP%d' % k + ('i' if inv else ''),
                                  k, off, dpos, msb, inv))
    return c

def score(segs, wall, kind, k, off, dpos, msb, inv=False):
    vals = []
    for seg in segs:
        s = seg[::-1] if wall == 'R' else seg
        v = (dec_kcopy(s, k, off, msb, inv=inv) if dpos is None
             else dec_sep(s, k, off, dpos, msb, inv=inv))
        if v is not None: vals.append(v)
    if len(vals) < 6: return None
    # The anchor can fire several times per counter increment (many visits per
    # lap), so collapse runs of equal consecutive decodes before judging
    # consecutiveness.
    ded = [vals[0]]
    for v in vals[1:]:
        if v != ded[-1]: ded.append(v)
    if len(ded) < 4: return None
    d = [ded[i+1]-ded[i] for i in range(len(ded)-1)]
    up = sum(1 for x in d if x == 1)
    dn = sum(1 for x in d if x == -1)      # complement counters DESCEND
    unit = max(up, dn)
    return unit, sum(1 for x in d if x != 0), ded

def classify(m, late_skip=3000):
    """Try BOTH sides as the fixed/anchor side and several reference cells
    inward from each extreme.  The growth test is only a hint: a machine can
    have "no wall on the left" and still anchor cleanly on the right, and the
    extreme cell itself is often visited once while the real per-lap turnaround
    sits 1-2 cells inward."""
    pref, mn1, mx1 = wall_side(m)
    if mn1 is None: return dict(m=m, verdict='HALTS')
    res = dict(m=m, wall_hint=pref)
    best = None
    sides = ['L', 'R'] if pref == '?' else [pref] + [s for s in ('L','R') if s != pref]
    for wall in sides:
        ext = mn1 if wall == 'L' else mx1
        step_in = 1 if wall == 'L' else -1
        for j in range(0, 5):
            ref = ext + j*step_in
            early = collect(m, wall, ref, per_state=24, skip=0)
            for q, segs in early.items():
                if len(segs) < 8: continue
                for kind, k, off, dpos, msb, inv in candidates():
                    sc = score(segs[-16:], wall, kind, k, off, dpos, msb, inv)
                    if sc is None: continue
                    unit, nz, vals = sc
                    if best is None or (unit, nz) > best[0]:
                        best = ((unit, nz), kind, k, off, dpos, msb, inv, q,
                                vals[:8], wall, ref)
            if best is not None and best[0][0] >= 8:
                break
        if best is not None and best[0][0] >= 8:
            break
    if best is None:
        return dict(res, verdict='MIXED')
    (unit, nz), kind, k, off, dpos, msb, inv, q, vals, wall, ref = best
    if unit < 4:
        return dict(res, verdict='MIXED', best_unit=unit)
    # Late-window confirmation, with a fallback: if the anchor's visits are
    # sparse late, retry at a smaller skip over a longer horizon.
    lsc = None
    for skip, steps in ((late_skip, 6_000_000), (800, 12_000_000)):
        late = collect(m, wall, ref, per_state=24, skip=skip, steps=steps)
        c = score(late.get(q, [])[-16:], wall, kind, k, off, dpos, msb, inv)
        if c is not None and c[0] >= 3:
            lsc = c; break
        lsc = lsc or c
    late_ok = lsc is not None and lsc[0] >= 3
    return dict(res, verdict=kind if late_ok else kind + '_EARLY_ONLY',
                wall=wall, k=k, off=off, dpos=dpos, msb=msb, inv=inv,
                anchor_state=chr(65+q), unit=unit, vals=vals,
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
                 f" inv={r.get('inv')} anchor={r['anchor_state']} early={r['vals']}"
                 f" late_unit={r.get('late_unit')} late={r.get('late_vals')}")
        print(f"{m}\t{r['verdict']}\twall={r.get('wall', r.get('wall_hint'))}{x}", flush=True)
    print("TALLY:", dict(t), file=sys.stderr)
