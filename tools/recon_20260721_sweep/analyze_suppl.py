#!/usr/bin/env python3
"""Union / boardability analysis of the representative 400-rep listC sample.

Reads certs under BBB/results/certs_residue_sample/suppl/<prover>/ and
classifies each rep: verdict (QH / neverQH / undecided), catching provers,
and whether the emitted cert family has a LANDED Coq checker.
Writes suppl_results_400.tsv and prints the catch-rate tables.
"""
import os, re, csv
from collections import Counter

BASE = "/home/user/BBB/results/certs_residue_sample/suppl"
SW = "/home/user/Coq-BBB4/tools/recon_20260721_sweep"
reps = [r for r in csv.DictReader(open(f"{SW}/suppl_listC_400.tsv"), delimiter='\t')]

DIRS = ["ngram_quiet", "ngram_rank", # incomplete on 400 (excluded):
        "rwlrank", "irules", "bouncer", "quietfar", "quietctl"]

# landed-checker verdict rules (from NEXT_SESSION.md landed families + theories/Checkers)
NEVERQH_LANDED = {"neverqh", "neverqh_fuel", "neverqh_drift", "neverqh_rwl"}
IRULES = {"irules", "irulesk", "irulesblk", "irulesblkpfx"}
QH_LANDED = {"wrapngram"}          # Wrap.v ngram_check_quiet_sound

def read_cert(p):
    if not os.path.exists(p):
        return None
    t = open(p).read()
    typ = (re.search(r'^type (\S+)', t, re.M) or [None, '?'])[1]
    qh = re.search(r'^claim_qh (\w)', t, re.M)
    qhs = re.search(r'^claim_qh_state (\w)', t, re.M)
    q = qh.group(1) if qh else (qhs.group(1) if qhs else '?')
    sc = re.search(r'claim_score (\d+)', t)
    return (typ, q, sc.group(1) if sc else '-')

def board(typ, qh):
    if qh == 'F':
        if typ in NEVERQH_LANDED:
            return True, typ
        if typ in IRULES:
            return True, "irules(neverqh)"
        return False, typ
    if qh == 'T':
        if typ in QH_LANDED:
            return True, "wrap(Wrap.v)"
        return False, typ + "(QH,no-checker)"
    return False, typ

out = []
for r in reps:
    m = r['rep']
    certs = {}
    for d in DIRS:
        c = read_cert(os.path.join(BASE, d, m + ".cert"))
        if c:
            certs[d] = c
    ranked = []
    for d, (typ, qh, sc) in certs.items():
        b, ck = board(typ, qh)
        pr = 0 if (b and qh == 'F') else (1 if (b and qh == 'T') else (2 if b else 3))
        ranked.append((pr, d, typ, qh, sc, b, ck))
    verdict = 'undecided'; prover = '-'; ctype = '-'; qhf = '-'; sc = '-'; b = False; ck = '-'
    if ranked:
        ranked.sort(key=lambda x: x[0])
        _, prover, ctype, qhf, sc, b, ck = ranked[0]
        verdict = 'QH' if qhf == 'T' else ('neverQH' if qhf == 'F' else 'halt/cycle')
    out.append({'rep': m, 'mult': r['mult'], 'verdict': verdict, 'prover': prover,
                'cert_type': ctype, 'qh': qhf, 'score': sc,
                'boardable': 'Y' if b else 'N', 'checker': ck if verdict != 'undecided' else '-',
                'n_caught': len(certs),
                'all': ';'.join(f"{d}={v[0]}/qh{v[1]}" for d, v in certs.items())})

cols = ['rep', 'mult', 'verdict', 'prover', 'cert_type', 'qh', 'score',
        'boardable', 'checker', 'n_caught', 'all']
with open(f"{SW}/suppl_results_400.tsv", "w", newline="") as f:
    w = csv.DictWriter(f, fieldnames=cols, delimiter='\t'); w.writeheader()
    for o in out:
        w.writerow(o)

N = len(out)
caught = [o for o in out if o['verdict'] != 'undecided']
neverqh = [o for o in out if o['verdict'] == 'neverQH']
qh = [o for o in out if o['verdict'] == 'QH']
board_yes = [o for o in out if o['boardable'] == 'Y']
qh_board = [o for o in qh if o['boardable'] == 'Y']
qh_noboard = [o for o in qh if o['boardable'] == 'N']
uncaught = [o for o in out if o['verdict'] == 'undecided']

print(f"=== REPRESENTATIVE listC sample: {N} reps (seed 20260721) ===")
print(f"caught by ANY prover : {len(caught):3}/{N} = {100*len(caught)/N:.1f}%")
print(f"  neverQH verdict    : {len(neverqh):3}/{N} = {100*len(neverqh)/N:.1f}%  (all boardable via NGram/Fuel/Drift/RepWL/IRules)")
print(f"  QH verdict         : {len(qh):3}/{N} = {100*len(qh)/N:.1f}%")
print(f"     QH boardable (Wrap.v ngram-quiet): {len(qh_board)}")
print(f"     QH NOT boardable (needs new quiet checker): {len(qh_noboard)}")
print(f"boardable via LANDED checker (a): {len(board_yes):3}/{N} = {100*len(board_yes)/N:.1f}%")
print(f"caught but NO checker (b)       : {len(caught)-len(board_yes):3}/{N} = {100*(len(caught)-len(board_yes))/N:.1f}%")
print(f"uncaught (c)                    : {len(uncaught):3}/{N} = {100*len(uncaught)/N:.1f}%")
print()
print("cert_type of caught (winning prover):", Counter(o['cert_type'] for o in caught))
print("per-prover raw catch counts:")
for d in DIRS:
    cnt = sum(1 for o in out if d in o['all'])
    print(f"   {d:12} {cnt}")
# mult-weighted (census machines)
def mw(lst):
    return sum(int(o['mult']) for o in lst)
print()
print(f"mult sums: total={mw(out)} caught={mw(caught)} neverQH={mw(neverqh)} QH={mw(qh)} board={mw(board_yes)} uncaught={mw(uncaught)}")
