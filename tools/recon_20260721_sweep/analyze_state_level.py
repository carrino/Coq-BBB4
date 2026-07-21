#!/usr/bin/env python3
"""State-level (census/BBB beeping) classification of caught reps.

The census QH split (listB/listC) is STATE-level. A cert's `claim_qh` is
TRANSITION-level; we instead derive the state-level verdict from the
authoritative per-transition classification (`claim_trans Q S CLASS n last`)
that every VERIFIED cert carries, plus the explicit `quiet_state` /
`claim_qh_state` fields.

  state q QUIET  (visited then silent) : >=1 transition F, 0 I  -> state-QH
  state q SILENT (never visited)       : all transitions N
  state q LIVE                         : >=1 transition I
  machine state-QH   iff some visited state is QUIET
  machine state-nQH  iff every visited state is LIVE (no quiet, ignore silent)

Usage: analyze_state_level.py <sample.tsv> <suppl|prim-base-dir>
"""
import os, re, csv, sys

BASE = sys.argv[2] if len(sys.argv) > 2 else "/home/user/BBB/results/certs_residue_sample/suppl"
SAMPLE = sys.argv[1] if len(sys.argv) > 1 else "/home/user/Coq-BBB4/tools/recon_20260721_sweep/suppl_listC_400.tsv"
SW = "/home/user/Coq-BBB4/tools/recon_20260721_sweep"
reps = list(csv.DictReader(open(SAMPLE), delimiter='\t'))
DIRS = ["ngram_quiet", "ngram_rank", "rwlrank", "irules", "bouncer", "quietfar", "quietctl"]

# state-level boardable-neverQH cert types (landed Coq checkers)
NQH_LANDED = {"neverqh_rank", "neverqh", "neverqh_fuel", "neverqh_drift", "neverqh_rwl"}
IRULES = {"irules", "irulesk", "irulesblk", "irulesblkpfx"}
# state-level boardable-QH: only Wrap.v ngram_check_quiet_sound (wrapngram)
QH_LANDED = {"wrapngram"}

def load(p):
    if not os.path.exists(p):
        return None
    t = open(p).read()
    typ = (re.search(r'^type (\S+)', t, re.M) or [None, '?'])[1]
    qs = re.search(r'^quiet_state (\w)', t, re.M)
    qhs = re.search(r'^claim_qh_state (\w)', t, re.M)
    trans = {}
    for mm in re.finditer(r'^claim_trans (\w)(\d) (\w) (\d+) (\d+)', t, re.M):
        q, s, cls, n, last = mm.group(1), mm.group(2), mm.group(3), int(mm.group(4)), int(mm.group(5))
        trans[(q, s)] = cls
    return {'type': typ, 'quiet_state': qs.group(1) if qs else None,
            'qh_state': qhs.group(1) if qhs else None, 'trans': trans}

def state_verdict(cert):
    """Return ('QH'|'nQH'|'?', witness_state_or_None) from a cert."""
    if cert['quiet_state']:
        return 'QH', cert['quiet_state']
    if cert['qh_state'] == 'F':
        return 'nQH', None
    if cert['qh_state'] == 'T':
        return 'QH', None
    tr = cert['trans']
    if not tr:
        return '?', None
    states = sorted(set(q for q, s in tr))
    quiet = None
    all_decided = all(c in ('N', 'F', 'I') for c in tr.values())
    for q in states:
        cls = [tr[(q, s)] for s in ('0', '1') if (q, s) in tr]
        if any(c == 'I' for c in cls):
            continue  # live
        if any(c == 'F' for c in cls):
            quiet = q  # visited then silent
    if quiet:
        return 'QH', quiet
    if all_decided:
        return 'nQH', None
    return '?', None

def board(cert, verdict):
    typ = cert['type']
    if verdict == 'nQH':
        if typ in NQH_LANDED:
            return True, typ
        if typ in IRULES:
            return True, "irules(nQH)"
        return False, typ
    if verdict == 'QH':
        if typ in QH_LANDED:
            return True, "wrap(Wrap.v)"
        return False, typ + "(QH,no-checker)"
    return False, typ

out = []
contra = 0
for r in reps:
    m = r['rep']
    certs = {}
    for d in DIRS:
        c = load(os.path.join(BASE, d, m + ".cert"))
        if c:
            certs[d] = c
    verds = {}
    for d, c in certs.items():
        v, w = state_verdict(c)
        verds[d] = (v, w, c)
    svs = set(v for v, w, c in verds.values() if v != '?')
    if 'QH' in svs and 'nQH' in svs:
        contra += 1
    # priority: nQH-boardable, QH-boardable, then any decided
    ranked = []
    for d, (v, w, c) in verds.items():
        b, ck = board(c, v)
        pr = 0 if (b and v == 'nQH') else (1 if (b and v == 'QH') else (2 if b else (3 if v != '?' else 4)))
        ranked.append((pr, d, c['type'], v, w, b, ck))
    verdict = 'undecided'; prover = '-'; ctype = '-'; wit = '-'; b = False; ck = '-'
    if ranked:
        ranked.sort(key=lambda x: x[0])
        _, prover, ctype, verdict, wit, b, ck = ranked[0]
    out.append({'rep': m, 'mult': r['mult'] if 'mult' in r else '1',
                'census_list': r.get('list', 'C'),
                'state_verdict': verdict, 'prover': prover, 'cert_type': ctype,
                'quiet_state': wit or '-', 'boardable': 'Y' if b else 'N',
                'checker': ck if verdict != 'undecided' else '-', 'n_caught': len(certs)})

cols = ['rep', 'mult', 'census_list', 'state_verdict', 'prover', 'cert_type',
        'quiet_state', 'boardable', 'checker', 'n_caught']
outpath = f"{SW}/suppl_state_results.tsv" if 'suppl' in BASE else f"{SW}/prim_state_results.tsv"
with open(outpath, "w", newline="") as f:
    w = csv.DictWriter(f, fieldnames=cols, delimiter='\t'); w.writeheader()
    for o in out:
        w.writerow(o)

from collections import Counter
N = len(out)
caught = [o for o in out if o['state_verdict'] != 'undecided']
nqh = [o for o in out if o['state_verdict'] == 'nQH']
qh = [o for o in out if o['state_verdict'] == 'QH']
by = [o for o in out if o['boardable'] == 'Y']
qh_nb = [o for o in qh if o['boardable'] == 'N']
unc = [o for o in out if o['state_verdict'] == 'undecided']
print(f"=== STATE-LEVEL classification: {N} reps  ({outpath}) ===")
print(f"state-verdict contradictions (QH & nQH both claimed): {contra}")
print(f"caught (state-decided) : {len(caught):3}/{N} = {100*len(caught)/N:.1f}%")
print(f"  state-neverQH        : {len(nqh):3}/{N} = {100*len(nqh)/N:.1f}%   (boardable NGram/Fuel/Drift/RepWL/IRules)")
print(f"  state-QH             : {len(qh):3}/{N} = {100*len(qh)/N:.1f}%")
print(f"     QH boardable (Wrap.v): {sum(1 for o in qh if o['boardable']=='Y')}")
print(f"     QH not boardable     : {len(qh_nb)}   (wraprwl/wrapfar/wrapctl/bouncer/irules-QH)")
print(f"(a) boardable via LANDED checker : {len(by):3}/{N} = {100*len(by)/N:.1f}%")
print(f"(b) caught but NO checker        : {len(caught)-len(by):3}/{N} = {100*(len(caught)-len(by))/N:.1f}%")
print(f"(c) uncaught                     : {len(unc):3}/{N} = {100*len(unc)/N:.1f}%")
print("winning cert_type:", dict(Counter(o['cert_type'] for o in caught)))
print("nQH winning checker:", dict(Counter(o['checker'] for o in nqh)))
print("QH-not-boardable cert_type:", dict(Counter(o['cert_type'] for o in qh_nb)))
def mw(lst): return sum(int(o['mult']) for o in lst)
print(f"mult: total={mw(out)} nQH={mw(nqh)} QH={mw(qh)} board={mw(by)} uncaught={mw(unc)}")
