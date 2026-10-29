"""Reproduce the targeted partial-family selection; this is not a proof.

The existing Python classifiers propose state recurrence for defined children.
Their union does not discharge a parent: the separate halting choice remains.
"""
from collections import Counter
import argparse
import json
from pathlib import Path
from generate_pipeline_examples import codes
from marker_state_profile_v2 import ROOT,REPO,sha,marker_check,ore_goal
from marker_state_potential_profile import invariant_conditions,capacity_weights
from marker_state_trail_profile import trail_check


def child_kind(table):
    if all(any(ore_goal(table,q,m) for m in (0,1)) for q in (0,1)):
        return 'ore'
    for mask in range(2,16,2):
        if marker_check(table,mask):return 'marker'
        if invariant_conditions(table,mask) and capacity_weights(table) is not None:
            return 'potential'
        if trail_check(table,mask):return 'trail'
    return None


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--check',action='store_true');a=p.parse_args()
    source=ROOT/'build/state-pipeline/history-full/not-accepted.txt'
    frontier=ROOT/'research/branch-frontier.json'
    excluded={r['family'] for r in json.loads(frontier.read_text())['rows']}
    machines=[m for m in source.read_text().splitlines() if '---' in m and m not in excluded]
    if len(machines)!=len(set(machines)):raise ValueError('Repeated original family')
    rows=[];hist=Counter();undefined=Counter()
    for machine in machines:
        table=codes(machine);undefined[table.count(16)]+=1
        if table.count(16)!=1:continue
        slot=table.index(16);children=[]
        for v in range(16):
            child=table.copy();child[slot]=v;children.append(child_kind(child))
        count=sum(k is not None for k in children);hist[count]+=1
        rows.append(dict(machine=machine,undefined_cell=slot,proposed_children=count,kinds=children))
    reached='1LB2RA1LA1LA_1RB1RA3LB---'
    selected=[r['machine'] for r in rows if r['proposed_children']==16 and r['machine']!=reached]
    build=ROOT/'build/state-partial-walk';build.mkdir(parents=True,exist_ok=True)
    outputs={build/'input.txt':'\n'.join(machines)+'\n',
             build/'allchildren-184.txt':'\n'.join(selected)+'\n',
             build/'static-children.json':json.dumps(rows,indent=2)+'\n'}
    for path,text in outputs.items():
        if a.check and (not path.exists() or path.read_text()!=text):raise ValueError('Selection changed: '+str(path))
        if not a.check:path.write_text(text)
    tools=['profile_partial_state_children.py','marker_state_profile_v2.py',
           'marker_state_potential_profile.py','marker_state_trail_profile.py','generate_pipeline_examples.py']
    report=dict(status='untrusted_static_child_selection',partial_families=len(machines),
        undefined_count_histogram=dict(sorted(undefined.items())),
        proposed_defined_child_histogram=dict(sorted(hist.items())),all_defined_proposed=hist[16],
        selected_for_late_prefix=len(selected),separate_halting_choices=len(rows),
        input_sha256={str(x.relative_to(REPO)):sha(x) for x in [source,frontier]},
        source_sha256={str((ROOT/'tools'/x).relative_to(REPO)):sha(ROOT/'tools'/x) for x in tools},
        selection_sha256={str(x.relative_to(REPO)):sha(x) for x in outputs},kernel_checked=0,census_linked=0,
        accounting='Original partial families. Every defined child is only an untrusted recurrence proposal; the None halting choice is separate and no parent is discharged here.')
    path=ROOT/'research/state-partial-child-profile.json';text=json.dumps(report,indent=2)+'\n'
    if a.check and path.read_text()!=text:raise ValueError('Selection report changed')
    if not a.check:path.write_text(text)
    print(json.dumps({k:report[k] for k in ['partial_families','all_defined_proposed','selected_for_late_prefix']}))


if __name__=='__main__':main()
