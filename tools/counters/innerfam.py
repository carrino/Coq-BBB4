#!/usr/bin/env python3
"""UNTRUSTED probe: find the INNER anchor family inside an overflow phase.

This is the Stage-A measurement of docs/NESTED_LAP_PLAN.md, and the search
step that a nested-lap emitter needs.  Nothing here is trusted: it PROPOSES an
inner family; the Coq kernel re-checks every chain built from one.

Usage:  innerfam.py LISTFILE OUTJSON

For a machine with a known OUTER anchor family (st0, enc, tail, far), take the
all-ones outer value p = 2^K - 1, build Cc(p), and simulate forward to
Cc(2^K).  Every blank-head configuration in between is a candidate INNER
anchor.  Decode each under every known alphabet at every (state, tail, far)
split, and ask whether some key's decoded values form the consecutive run
2^(K-1) .. 2^K-1 -- which is what the IXP reference board's inner counter does.

That answers the plan's gate questions directly:
  (1) does an inner family exist at all;
  (2) is it in the alphabet zoo;
  (3) is its range 2^(K-1)..2^K-1 (what pow2/fill assume).
"""
import sys, os, collections, json
sys.path.insert(0, '/home/user/Coq-BBB4/tools/counters')
os.chdir('/home/user/Coq-BBB4')
import emit_lapcert as EL
from emit_interleave import parse
from mirror_common import mirror_spec
import lapcert as LC
LAB = 'ABCD'

def decode(word, A, B, C):
    """word = E(v) -> v, by stripping A/B off the front until C remains."""
    w, bits = tuple(word), []
    for _ in range(64):
        if w == C:
            v = 1
            for b in reversed(bits):
                v = 2 * v + b
            return v
        if len(w) >= len(A) and w[:len(A)] == A:
            bits.append(0); w = w[len(A):]
        elif len(w) >= len(B) and w[:len(B)] == B:
            bits.append(1); w = w[len(B):]
        else:
            return None
    return None

def phase_probe(spec, K=6, maxT=400000, maxtail=3):
    tab = parse(spec)
    out = []
    for (edge, tail, p0, enc, far) in EL.anchors(spec):
        st0, encf = LAB.index(edge), EL.ENC[enc]
        p, pn = 2 ** K - 1, 2 ** K
        start = (st0, tuple(encf(p)) + tuple(tail), 0, tuple(far))
        want = (st0, tuple(encf(pn)) + tuple(tail), 0, tuple(far))
        cfg, mid, steps = start, [], None
        for t in range(1, maxT + 1):
            try:
                cfg = LC.wstep(tab, False, False, cfg)
            except LC.Halt:
                break
            q, l, h, r = cfg
            if LC.rstrip0(l) == LC.rstrip0(want[1]) and q == want[0] \
               and h == want[2] and LC.rstrip0(r) == LC.rstrip0(want[3]):
                steps = t; break
            if h == 0:
                mid.append((q, LC.rstrip0(l), LC.rstrip0(r)))
        if steps is None:
            continue
        # decode every mid config under every alphabet at every split
        hits = collections.defaultdict(list)
        for (q, l, r) in mid:
            for name in EL.ENCS:
                d = EL.ENCDATA[name]
                A, B, C = tuple(d['uD']), tuple(d['uS']), tuple(d['soD'])
                for k in range(maxtail + 1):
                    if k > len(l) - 1: break
                    head = l[:len(l) - k] if k else l
                    tl = l[len(l) - k:] if k else ()
                    v = decode(head, A, B, C)
                    if v is not None:
                        hits[(name, q, tl, r)].append(v)
        res = []
        for key, vs in hits.items():
            want_run = list(range(2 ** (K - 1), 2 ** K))
            if vs == want_run:
                res.append(dict(key=key, kind='EXACT-2^(K-1)..2^K-1', n=len(vs)))
            elif len(vs) >= 4 and vs == list(range(vs[0], vs[0] + len(vs))):
                res.append(dict(key=key, kind='consecutive %d..%d' % (vs[0], vs[-1]),
                                n=len(vs)))
        res.sort(key=lambda r: -r['n'])
        return dict(spec=spec, enc=enc, st0=edge, tail=list(tail),
                    far=list(far), steps=steps, nmid=len(mid), inner=res)
    return None

rows = []
for line in open(sys.argv[1]):
    spec = line.strip()
    if not spec: continue
    r = None
    for s in (spec, mirror_spec(spec)):
        try:
            r = phase_probe(s)
        except Exception:
            r = None
        if r: break
    if r is None:
        print('%s\tNO-OUTER-PHASE' % spec, flush=True); rows.append((spec, None)); continue
    best = r['inner'][0] if r['inner'] else None
    print('%s\touter=%s@%s\tsteps=%d\tmid=%d\tinner=%s' % (
        spec, r['enc'], r['st0'], r['steps'], r['nmid'],
        ('%s %s n=%d' % (best['key'][0], best['kind'], best['n'])) if best else 'NONE'),
        flush=True)
    rows.append((spec, r))

ok = [r for _, r in rows if r and r['inner']]
exact = [r for r in ok if any(i['kind'].startswith('EXACT') for i in r['inner'])]
print('\n=== %d/%d machines: an overflow phase was simulated ===' % (
    sum(1 for _, r in rows if r), len(rows)))
print('=== %d have an INNER consecutive family inside it ===' % len(ok))
print('=== %d of those run EXACTLY 2^(K-1)..2^K-1 (what pow2/fill assume) ===' % len(exact))
json.dump([{'spec': s, 'r': r} for s, r in rows], open(sys.argv[2], 'w'), indent=1, default=str)
