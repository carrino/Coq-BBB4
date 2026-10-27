"""Measure a two-sided marker recurrence proposal; no proof claims.

A checked two-step prefix establishes a marked left cell, or a marked head
in B. Left moves enter B and B reads of a marker move right and rewrite it.
This independent left wall complements the existing right-marker invariant.
"""
import json
from pathlib import Path
from generate_pipeline_examples import codes
from marker_state_profile_v2 import ROOT,REPO,sha,marker_check
from marker_state_potential_profile import invariant_conditions,capacity_weights
from marker_state_trail_profile import trail_check


def walls_check(table,mask):
    if not invariant_conditions(table,mask):return False
    if not all(v%2==1 for v in table if v//2%2==0):return False
    if not all(v//2%2==1 and ((mask>>(v//4))&1)
               for s,v in enumerate(table[4:]) if (mask>>s)&1):return False
    def rank(s,fuel=4):
        v=table[4+s]
        return 0 if not fuel or v%2==0 or v//2%2==0 else 1+rank(v//4,fuel-1)
    if not all(v%2==0 or v//2%2==0 or rank(v//4)<rank(s)
               for s,v in enumerate(table[4:])):return False
    tape={};state=position=0
    for _ in range(2):
        v=table[4*state+tape.get(position,0)]
        tape[position]=v//4;state=v%2;position+=1 if v//2%2 else -1
    return bool((state==1 and (mask>>tape.get(position,0))&1) or
                any(i<position and (mask>>s)&1 for i,s in tape.items()))


def main():
    source=ROOT/'build/state-pipeline/history-full/not-accepted.txt'
    machines=source.read_text().splitlines();rows=[]
    if len(set(machines))!=len(machines):raise ValueError('Repeated input')
    for machine in machines:
        table=codes(machine);masks=[m for m in range(2,16,2) if walls_check(table,m)]
        if not masks:continue
        old=any(marker_check(table,m) or trail_check(table,m) for m in masks) or capacity_weights(table) is not None
        rows.append(dict(machine=machine,marker_mask=masks[0],covered_by_prior=old))
    paths=[Path(__file__).resolve(),ROOT/'tools/marker_state_profile_v2.py',
           ROOT/'tools/marker_state_potential_profile.py',ROOT/'tools/marker_state_trail_profile.py',
           ROOT/'tools/generate_pipeline_examples.py']
    report=dict(status='untrusted_two_sided_marker_measurement',input_families=len(machines),
        candidates=len(rows),new_beyond_prior=sum(not r['covered_by_prior'] for r in rows),rows=rows,
        input_sha256=sha(source),source_sha256={str(p.relative_to(REPO)):sha(p) for p in paths},
        kernel_checked=0,census_linked=0,scope='State recurrence proposal only; generic checker and census replay required.')
    dest=ROOT/'research/state-marker-walls-profile.json';dest.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:report[k] for k in ['input_families','candidates','new_beyond_prior']}))


if __name__=='__main__':main()
