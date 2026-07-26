#!/usr/bin/env python3
"""UNTRUSTED: does the anchor FRAME alternate with the msb's parity?

WAVE13_FINDINGS.md section 10b records John's reading of
0RB---_0RC0LD_1LD1RC_0LA1LB -- "1's to the LEFT of the bits when the msb is
even and 1's to the RIGHT when the msb is odd" -- and states plainly that it
is NOT verified: the crude classifier was inconclusive because all-ones words
satisfy both patterns, and the snapshots caught were all of one bit-length
parity.  That is exactly the wave-12 section 4.1 / wave-13 section 4 failure
mode, so this file makes the measurement instead of assuming it.

The two frames, for m with binary digits b0 (lsb) .. b_{k-1} = 1 (msb), both
written LSB-END-FIRST (nearest the head first), both of length 2k-1:

    MB  (marker BEFORE each bit)  [1,b0, 1,b1, ..., 1,b_{k-2}, 1]   == Ip
    MA  (marker AFTER  each bit)  [b0,1, b1,1, ..., b_{k-2},1, 1]

MB is ILCounter.Ip verbatim.  MA is the one-cell shift of it -- the Ip/Mp
frame shift of WAVE12_FINDINGS.md section 7.  A word of all ones (m = 2^k-1)
matches BOTH; those rows are reported as AMBIG and never counted as evidence.

For every snapshot of the anchor shape (head blank, far side empty) it
decodes the near word under every frame and every short fixed tail, and
prints the resulting (m, bitlen, frame) sequence.  The hypothesis predicts
frame to be a function of bitlen(m) mod 2 that actually takes both values.
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


def bits(m):
    out = []
    while m:
        out.append(m & 1)
        m >>= 1
    return out                       # lsb first, top entry 1


def MB(m):
    """marker BEFORE each bit -- ILCounter.Ip."""
    b = bits(m)
    out = []
    for x in b[:-1]:
        out += [1, x]
    return out + [1]


def MA(m):
    """marker AFTER each bit -- the one-cell frame shift of MB."""
    b = bits(m)
    out = []
    for x in b[:-1]:
        out += [x, 1]
    return out + [1]


FRAMES = {'MB': MB, 'MA': MA}


def tables(bound):
    """word -> (m, frame) for both frames, with collisions kept."""
    tab = collections.defaultdict(list)
    for name, f in FRAMES.items():
        for m in range(1, bound):
            tab[tuple(f(m))].append((m, name))
    return tab


def snapshots(spec, T, side):
    """Configurations with a blank head and an EMPTY far side -- the shape
    every counter anchor has.  Returns (t, state, near-word) with the near
    word read HEAD-FIRST."""
    tab = parse(spec)
    cfg = (0, (), 0, ())
    out = []
    for t in range(T):
        q, l, h, r = cfg
        ls, rs = LC.rstrip0(l), LC.rstrip0(r)
        if h == 0:
            if side in ('R', 'both') and not ls and rs:
                out.append((t, q, 'R', rs))
            if side in ('L', 'both') and not rs and ls:
                out.append((t, q, 'L', ls))
        try:
            cfg = LC.wstep(tab, False, False, cfg)
        except LC.Halt:
            break
    return out


def decode(word, tab, maxtail):
    """All (m, frame, tail) with word = frame(m) ++ tail, |tail| <= maxtail."""
    hits = []
    for k in range(maxtail + 1):
        head = word[:len(word) - k] if k else word
        if not head:
            continue
        for (m, name) in tab.get(tuple(head), ()):
            hits.append((m, name, word[len(word) - k:] if k else ()))
    return hits


def run(spec, T, side, maxtail, bound, quiet=False):
    tab = tables(bound)
    rows = collections.defaultdict(list)         # (state, side) -> readings
    for (t, q, sd, word) in snapshots(spec, T, side):
        hits = decode(word, tab, maxtail)
        if hits:
            rows[(LAB[q], sd)].append((t, word, hits))
    report = {}
    for key, rs in sorted(rows.items()):
        # group by the tail that occurs most often -- the anchor's fixed tail
        cnt = collections.Counter(h[2] for (_, _, hits) in rs for h in hits)
        if not cnt:
            continue
        tail = cnt.most_common(1)[0][0]
        seq = []
        for (t, word, hits) in rs:
            hs = [h for h in hits if h[2] == tail]
            if not hs:
                continue
            ms = sorted({h[0] for h in hs})
            frames = sorted({h[1] for h in hs})
            if len(ms) == 1:
                seq.append((t, ms[0], ms[0].bit_length(),
                            'AMBIG' if len(frames) > 1 else frames[0], word))
            else:
                for m in ms:
                    fr = [h[1] for h in hs if h[0] == m]
                    seq.append((t, m, m.bit_length(),
                                'AMBIG' if len(fr) > 1 else fr[0], word))
        if len(seq) >= 3:
            report[key] = (tail, seq)
    if not quiet:
        for key, (tail, seq) in report.items():
            print('=== state %s, %s-side, tail=%s, %d readings' % (
                key[0], key[1], ''.join(map(str, tail)) or '-', len(seq)))
            for (t, m, bl, fr, word) in seq[:200]:
                print('  t=%-8d m=%-6d bitlen=%-3d %-6s %s' % (
                    t, m, bl, fr, ''.join(map(str, word))))
    return report


def verdict(report):
    """Per anchor family: is the frame CONSTANT, or a function of bitlen
    parity that genuinely takes both values?"""
    out = {}
    for key, (tail, seq) in report.items():
        firm = [(m, bl, fr) for (_, m, bl, fr, _) in seq if fr != 'AMBIG']
        if len(firm) < 4:
            out[key] = ('too-few-firm', len(firm))
            continue
        fs = {fr for (_, _, fr) in firm}
        if len(fs) == 1:
            out[key] = ('CONSTANT-' + fs.pop(), len(firm))
            continue
        byp = collections.defaultdict(set)
        for (_, bl, fr) in firm:
            byp[bl % 2].add(fr)
        if all(len(v) == 1 for v in byp.values()) and len(byp) == 2:
            out[key] = ('ALTERNATES-by-bitlen-parity', len(firm))
        else:
            byl = collections.defaultdict(set)
            for (_, bl, fr) in firm:
                byl[bl].add(fr)
            bad = sorted(b for b, v in byl.items() if len(v) > 1)
            out[key] = ('MIXED (bitlens with both frames: %s)' % bad,
                        len(firm))
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--spec', required=True)
    ap.add_argument('-T', type=int, default=2000000)
    ap.add_argument('--side', default='both', choices=('L', 'R', 'both'))
    ap.add_argument('--maxtail', type=int, default=3)
    ap.add_argument('--bound', type=int, default=1 << 12)
    ap.add_argument('--quiet', action='store_true')
    a = ap.parse_args()
    rep = run(a.spec, a.T, a.side, a.maxtail, a.bound, a.quiet)
    print('\n=== verdict: %s' % a.spec)
    for key, (v, n) in sorted(verdict(rep).items()):
        print('  state %s %s-side: %-46s (%d firm readings)'
              % (key[0], key[1], v, n))


if __name__ == '__main__':
    main()


# ---------------------------------------------------------------------------
# Absolute-column mode.
#
# The head-relative decode above answers "which frame does the word at THIS
# state parse in", and its answer is partly an artifact: moving the head one
# cell re-parses the same tape from marker-before to marker-after.  A claim
# that the frame ALTERNATES WITH THE MSB is a claim about ABSOLUTE COLUMN
# PARITY -- which cells hold the constant marker -- and survives no matter
# where the head is.  So measure that directly:
#
#   * sample the run at one canonical phase (a fixed state at a fixed
#     absolute head position, the left edge for a left-anchored machine);
#   * group the snapshots into EPOCHS by the width of the written tape --
#     one epoch per msb bump;
#   * inside an epoch, the cells that VARY across snapshots are the bits and
#     the cells that stay 1 are the markers;
#   * report the column parity of each set.
#
# The hypothesis predicts that parity to flip from epoch to epoch.
# ---------------------------------------------------------------------------

def abs_snapshots(spec, T, state, pos0):
    """Tape (as a dict col -> sym) each time the run is in [state] with the
    head at absolute column [pos0]."""
    tab = parse(spec)
    cfg = (0, (), 0, ())
    pos, tape, out = 0, {}, []
    for t in range(T):
        q, l, h, r = cfg
        tape[pos] = h
        if q == state and pos == pos0:
            out.append((t, dict(tape)))
        tr = tab.get((q, h))
        if tr is None:
            break
        tape[pos] = tr[0]
        pos += tr[1]
        try:
            cfg = LC.wstep(tab, False, False, cfg)
        except LC.Halt:
            break
    return out


def epochs(snaps):
    """Group snapshots by the width of the written region."""
    by = collections.defaultdict(list)
    for (t, tape) in snaps:
        cols = [c for c, v in tape.items() if v]
        if not cols:
            continue
        by[max(cols) - min(cols) + 1].append((t, tape))
    return by


def column_parity(spec, T=200000, state=0, pos0=0, minsnaps=3):
    out = []
    for w, rows in sorted(epochs(abs_snapshots(spec, T, state, pos0)).items()):
        if len(rows) < minsnaps:
            continue
        cols = sorted({c for _, tape in rows for c in tape})
        var, mark = [], []
        for c in cols:
            vals = {tape.get(c, 0) for _, tape in rows}
            if len(vals) > 1:
                var.append(c)
            elif vals == {1}:
                mark.append(c)
        if not var or not mark:
            continue
        vp = {c % 2 for c in var}
        mp = {c % 2 for c in mark}
        out.append(dict(width=w, n=len(rows), bits=var, markers=mark,
                        bit_parity=sorted(vp), marker_parity=sorted(mp),
                        first_bit=var[0], first_marker=mark[0]))
    return out


def main_abs():
    ap = argparse.ArgumentParser()
    ap.add_argument('--spec', required=True)
    ap.add_argument('-T', type=int, default=400000)
    ap.add_argument('--state', default='A')
    ap.add_argument('--pos', type=int, default=0)
    a = ap.parse_args()
    rows = column_parity(a.spec, a.T, LAB.index(a.state), a.pos)
    print('epoch (state %s @ col %d): which ABSOLUTE columns hold the bits, '
          'which hold the constant markers' % (a.state, a.pos))
    for r in rows:
        rel = 'marker AFTER  bit' if r['first_marker'] > r['first_bit'] \
              else 'marker BEFORE bit'
        print('  width=%-4d n=%-4d bits@%s markers@%s  bit-par=%s '
              'marker-par=%s  %s'
              % (r['width'], r['n'], r['bits'][:6], r['markers'][:6],
                 r['bit_parity'], r['marker_parity'], rel))
    pars = [tuple(r['bit_parity']) for r in rows]
    print('\nbit-column parity by epoch: %s' % (pars,))
    print('VERDICT: %s' % ('ALTERNATES' if len(set(pars)) > 1 and
                           all(pars[i] != pars[i + 1]
                               for i in range(len(pars) - 1))
                           else 'CONSTANT / not alternating'))
