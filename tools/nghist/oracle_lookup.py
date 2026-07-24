#!/usr/bin/env python3
"""UNTRUSTED TNF oracle lookup for (4,2) machines (wave-7).

Maps any BBB4 machine string to mxdys' BB4_verified_enumeration.csv decision
(status + decider + params) by reconstructing the bbchallenge / Coq-BB5 Tree
Normal Form.

THE KEY FINDING (wave-7, correcting the wave-6 hand-off hypothesis):
mxdys' CSV contains ONLY TNF nodes with >=1 undefined transition -- i.e. the
bbchallenge enumeration space of machines that use at most 2n-1 = 7 of the 8
transitions from the blank tape.  A machine that uses ALL 8 transitions is
OUTSIDE that space: mxdys' cnt>=1 pruning never fills the last-reached
transition, so such a machine's TNF ancestor is a HALT node, and no oracle
row exists for the (nonhalt) completion.  Measured: the CSV has 0 full
machines; residue splits 1,535 partial (map to nonhalt NGRAM_CPS_*) vs 3,594
full (no oracle); holdouts split 114 (<=7, map) vs 3,599 (=8, no oracle).

So the useful oracle target is exactly the <=7-transition machines.  For them
`oracle_of` returns mxdys' exact decider + params (history, gram, gas), which
`params_for` turns into NGramHist sweep parameters.  UNTRUSTED: only picks
params; the Coq kernel re-checks every emitted certificate.
"""
import sys, os

STATES = "ABCDE"
_CSV_CACHE = {}

def default_csv():
    for p in (os.environ.get('BB4_CSV', ''),
              '/tmp/claude-0/-home-user-Coq-BBB4/'
              'c1c69455-87df-50ba-a799-5e74c6d43b33/scratchpad/'
              'BB4_verified_enumeration.csv'):
        if p and os.path.exists(p):
            return p
    return None

def load_csv(path=None):
    path = path or default_csv()
    if path in _CSV_CACHE:
        return _CSV_CACHE[path]
    d = {}
    with open(path) as f:
        next(f)
        for line in f:
            p = line.rstrip('\n').split(',')
            d[p[0]] = (p[1], p[2])
    _CSV_CACHE[path] = d
    return d

def decode(mstr):
    g = mstr.strip().split('_')
    n = len(g)
    tm = {}
    for si, grp in enumerate(g):
        st = STATES[si]
        tm[st] = {}
        for b in (0, 1):
            c = grp[b*3:b*3+3]
            tm[st][b] = None if c == '---' else (int(c[0]), c[1], c[2])
    return tm, n

def reached_canon(mstr, T=12000):
    """Simulate from the blank tape; return (nused, reached_canonical_string,
    halted).  The canonical string is the machine relabelled into first-visit
    order with every UNREACHED transition blanked to '---' -- exactly mxdys'
    TNF node form for the reached behaviour.  A machine using all 2n
    transitions comes back full (no '---')."""
    tm, n = decode(mstr)
    tape = {}
    head = 0
    s = 'A'
    used = set()
    label = {'A': 0}
    order = ['A']
    halted = False
    for i in range(T):
        sym = tape.get(head, 0)
        used.add((s, sym))
        tr = tm[s][sym]
        if tr is None:
            halted = True
            break
        w, d, nx = tr
        tape[head] = w
        head += 1 if d == 'R' else -1
        if nx not in label:
            label[nx] = len(order)
            order.append(nx)
        s = nx
        if len(used) == 2*n:
            break
    for st in STATES[:n]:
        if st not in label:
            label[st] = len(order)
            order.append(st)
    inv = {i: order[i] for i in range(n)}
    def cell(ci, b):
        orig = inv[ci]
        if (orig, b) not in used:
            return '---'
        tr = tm[orig][b]
        if tr is None:
            return '---'
        w, dr, nx = tr
        return '{}{}{}'.format(w, dr, STATES[label[nx]])
    canon = '_'.join(cell(i, 0) + cell(i, 1) for i in range(n))
    return len(used), canon, halted

def oracle_of(mstr, csv=None):
    """Return (status, decider) for mstr per mxdys' CSV, or None if the
    machine is outside the enumeration (uses all 2n transitions)."""
    csv = csv if csv is not None else load_csv()
    _, canon, _ = reached_canon(mstr)
    return csv.get(canon)

def parse_params(decider):
    """Split 'NGRAM_CPS_IMPL1_params_2_2_2_1600' ->
    ('NGRAM_CPS_IMPL1', [2,2,2,1600]).  Returns (family, [ints])."""
    if '_params_' not in decider:
        return decider, []
    fam, rest = decider.split('_params_', 1)
    nums = []
    for tok in rest.split('_'):
        try:
            nums.append(int(tok))
        except ValueError:
            pass
    return fam, nums

def params_for(mstr, csv=None):
    """Map mxdys' NGRAM decision to NGramHist sweep params.

    IMPL1_params_h_g_?_gas   -> history=h, gram=g, gas
    IMPL2_params_g_?_gas     -> history=1 (none), gram=g, gas
    Returns dict(family, history, gram, gas) or None (not an NGRAM nonhalt
    row, or outside the enumeration)."""
    o = oracle_of(mstr, csv)
    if o is None or o[0] != 'nonhalt':
        return None
    fam, nums = parse_params(o[1])
    if fam == 'NGRAM_CPS_IMPL1' and len(nums) >= 4:
        return dict(family=fam, history=nums[0], gram=nums[1], gas=nums[-1])
    if fam == 'NGRAM_CPS_IMPL2' and len(nums) >= 2:
        return dict(family=fam, history=1, gram=nums[0], gas=nums[-1])
    if fam.startswith('NGRAM'):
        return dict(family=fam, history=1, gram=nums[1] if len(nums) > 1 else 2,
                    gas=nums[-1] if nums else 1600)
    return None

if __name__ == '__main__':
    csv = load_csv()
    for m in sys.argv[1:]:
        nu, canon, halted = reached_canon(m)
        o = csv.get(canon)
        print("{}  used={} canon={}  oracle={}  params={}".format(
            m, nu, canon, o, params_for(m, csv)))
