#!/usr/bin/env python3
"""
recon_F normalization mapper: census TNF  ->  upstream (bbchallenge) TNF.

Semantics (bbchallenge standard, from src/tm.h + src/enumerate.c):
  - 4 states A,B,C,D (0..3), 2 symbols 0,1, blank=0, start state A, head at origin.
  - text: 6 chars/state, two 3-char transitions "<write><dir><next>" for read 0
    then read 1; states joined by '_'; "---" = undefined (halt).
  - upstream TNF (enumerate.c): simulate from blank; states labelled in
    first-visit order (A=start); A0 fixed to a start instruction; unreached
    transitions stay '---' (don't-care); first move fixed R by mirror symmetry.

We implement:
  parse / fmt
  mirror(M)                      : left-right reflection (dir L<->R), behaviour-mirrored
  canon(M, start=0)              : behaviour-preserving canonicalisation:
                                     ensure first move R (mirror if A0 moves L),
                                     relabel visited states in first-visit order,
                                     unreached slots -> '---'.  Returns (string, info).
  reroot(M)                      : find first step that writes a 1 (state q*, on a
                                     0-cell); return machine re-started at q* (or None
                                     if it never writes a 1 within the cap).
  upstream_tnf(M)                : the census->upstream map.  For a machine whose
                                     canonical A0 writes 1 -> canon.  For first-write-0
                                     -> canon(reroot).  Also returns prefix/loss info
                                     used for the bridge analysis.
"""
import sys

UNDEF = None
STEP_CAP_VISIT = 100000   # hard cap for first-visit-order simulation
STEP_CAP_1WRITE = 64      # first 1-write is always within ~4 steps for a 0RB prefix

def parse(text):
    """Return M: list over 4 states of [t0, t1]; each t is None or (w,d,nx).
       w in {0,1}, d in {-1,+1}, nx in 0..3."""
    parts = text.strip().split('_')
    M = []
    for p in parts:
        st = []
        for k in (0, 3):
            tr = p[k:k+3]
            if tr == '---' or tr[0] == '-':
                st.append(None)
            else:
                w = int(tr[0])
                d = -1 if tr[1] == 'L' else +1
                nx = ord(tr[2]) - ord('A')
                st.append((w, d, nx))
        M.append(st)
    return M

def fmt(M):
    out = []
    for st in M:
        s = ''
        for tr in st:
            if tr is None:
                s += '---'
            else:
                w, d, nx = tr
                s += '%d%s%s' % (w, 'R' if d == +1 else 'L', chr(ord('A') + nx))
        out.append(s)
    return '_'.join(out)

def mirror(M):
    """Left-right reflection: flip every move direction; states/writes unchanged.
       Behaviourally mirrors the from-blank run (same states, same first-visit order)."""
    R = []
    for st in M:
        row = []
        for tr in st:
            if tr is None:
                row.append(None)
            else:
                w, d, nx = tr
                row.append((w, -d, nx))
        R.append(row)
    return R

def simulate(M, start=0, cap=STEP_CAP_VISIT):
    """Simulate from blank starting in state `start`.
       Returns dict with:
         first_visit: {state: config-index of first visit}
         fired: set of (state, sym) transitions actually fired
         first1_state, first1_step: state and step index of first 1-write (or None)
         halted: bool (hit undefined)
         steps: number of steps simulated
         hit_cap: bool (ran to cap without firing all defined slots)
       config-index: state at time t (0 = start config).
       Early-stop: once every DEFINED slot has fired, no new slot/state can appear."""
    ndef = sum(1 for st in M for tr in st if tr is not None)
    tape = {}
    pos = 0
    st = start
    first_visit = {st: 0}
    fired = set()
    first1_state = None
    first1_step = None
    halted = False
    steps = 0
    hit_cap = False
    t = 0
    while True:
        if len(fired) >= ndef:
            break
        if t >= cap:
            hit_cap = True
            break
        sym = tape.get(pos, 0)
        tr = M[st][sym]
        if tr is None:
            halted = True
            break
        w, d, nx = tr
        fired.add((st, sym))
        if w == 1 and sym == 0 and first1_state is None:
            first1_state = st
            first1_step = t
        tape[pos] = w
        pos += d
        st = nx
        steps = t + 1
        if st not in first_visit:
            first_visit[st] = t + 1
        t += 1
    return dict(first_visit=first_visit, fired=fired,
                first1_state=first1_state, first1_step=first1_step,
                halted=halted, steps=steps, hit_cap=hit_cap)

def canon(M, start=0):
    """Behaviour-preserving canonical form: first-move-R (mirror if needed),
       relabel visited states first-visit order, unreached -> '---'.
       Returns (canon_string, info)."""
    # first move: transition from `start` reading 0
    a0 = M[start][0]
    info = {}
    Mc = M
    if a0 is not None and a0[1] == -1:
        Mc = mirror(M)
    sim = simulate(Mc, start=start)
    fv = sim['first_visit']
    # order visited states by first-visit config-index; assign labels 0..k-1
    order = sorted(fv.keys(), key=lambda q: fv[q])
    label = {q: i for i, q in enumerate(order)}
    k = len(order)
    # build canonical table over k states, in visited order
    rows = []
    for i in range(k):
        q = order[i]           # original state with canonical label i
        row = []
        for sym in (0, 1):
            if (q, sym) in sim['fired']:
                w, d, nx = Mc[q][sym]
                # nx must be visited (it was entered); relabel
                row.append((w, d, label[nx]))
            else:
                row.append(None)
        rows.append(row)
    info['nstates'] = k
    info['halted'] = sim['halted']
    info['steps'] = sim['steps']
    info['visited'] = set(order)
    return fmt(rows), info

def first_one_write(M, start=0):
    """Return state q* whose read-0 transition performs the first 1-write from blank,
       or None."""
    sim = simulate(M, start=start, cap=STEP_CAP_1WRITE)
    return sim['first1_state']

def upstream_tnf(text):
    """Map a census machine string to its upstream-convention TNF representative.
       Returns dict:
         tnf         : canonical 1RB (or fixed-point) string, or None
         mode        : 'direct1' (already writes 1 first) | 'reroot' (0-first, re-rooted)
                       | 'never1' (never writes a 1 within cap -> no upstream rep)
         a0          : the canonical A0 field ('1RB' etc.)
         prefix_states, revisited, dropped_states, nstates_before, nstates_after
    """
    M = parse(text)
    # canonical behaviour form of the machine itself (to read its true A0 write bit)
    c0, i0 = canon(M, start=0)
    a0field = c0[0:3]
    res = dict(tnf=None, mode=None, a0=a0field,
               prefix_states=None, revisited=None, dropped_states=None,
               nstates_before=i0['nstates'], nstates_after=None)
    if a0field[0] == '1':
        # already first-write-1 in canonical (behaviour) form => direct upstream TNF
        res['tnf'] = c0
        res['mode'] = 'direct1'
        res['nstates_after'] = i0['nstates']
        return res
    # first-write-0: re-root at the first 1-write
    qstar = first_one_write(M, start=0)
    if qstar is None:
        res['mode'] = 'never1'
        return res
    # states visited in the prefix (before reaching q* config) vs after
    simfull = simulate(M, start=0)
    # prefix states = states whose ONLY visits are before first1_step's config
    # re-root: canonicalise machine with start=qstar
    cr, ir = canon(M, start=qstar)
    res['tnf'] = cr
    res['mode'] = 'reroot'
    res['a0'] = cr[0:3]
    res['nstates_after'] = ir['nstates']
    # prefix / drop analysis
    visited_before = set(simfull['first_visit'].keys())
    visited_after = ir['visited']  # in original-state ids (canon used original ids internally)
    # canon returns visited as original state ids of the re-rooted sim
    res['dropped_states'] = sorted(visited_before - visited_after)
    res['prefix_states'] = sorted(visited_before)
    res['revisited'] = sorted(visited_after)
    return res

if __name__ == '__main__':
    # quick self-test
    tests = [
        "1RB1LA_1LC0RA_1LD0LD_0RB0LC",   # a holdout (1RB) -> should be fixed point
        "0RB---_0LC---_0LD0RC_1RC1LD",   # a 0RB residue machine
    ]
    for t in tests:
        r = upstream_tnf(t)
        print(t, '->', r['mode'], r['a0'], '=>', r['tnf'])
