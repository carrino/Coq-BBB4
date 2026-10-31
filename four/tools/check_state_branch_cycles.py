"""Compile state-only joins of nine reached partial families.

Fifteen defined children use OneStateReach; one uses a checked cycle.
The separate undefined/halting choice is bounded by the checked prefix.
"""
import argparse
import json
from pathlib import Path
import subprocess
import time
from check_state_branches import ROOT,REPO,SOURCES,sha,generate as ore_generate
from check_late_cycles import cert_text
from generate_pipeline_examples import codes

BUILD=ROOT/'build/state-branch-cycles'
INPUT=ROOT/'research/state-branch-cycle-families.json'

def generate(rows):
 entries=[]
 for row in rows:
  children=';'.join('('+str(c['value'])+', '+cert_text(c['certificate'])+')' for c in row['cycles'])
  entries.append('  (['+';'.join(map(str,codes(row['machine'])))+'], '+str(row['anchor'])+', ['+children+'])')
 text=ore_generate([])
 text=text.replace('check_state_branches.py','check_state_branch_cycles.py').replace('StateBranchCloseout.','StateBranchCycles.')
 text=text.replace('StateBranchRows','StateMixedBranchRows').replace('state_branch_batch_check','state_mixed_branch_batch_check')
 text=text.replace('state_branch_board rows','state_mixed_branch_board rows').replace('state_branch_board_sound _','state_mixed_branch_board_sound _')
 text=text.replace(':= [\n\n].',':= [\n'+';\n'.join(entries)+'\n].')
 return text

def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--prepare',action='store_true');p.add_argument('--refresh',action='store_true')
 p.add_argument('--timeout',type=int,default=3600);a=p.parse_args()
 rows=json.loads(INPUT.read_text())['rows'];machines=[r['machine'] for r in rows]
 if not rows or len(set(machines))!=len(machines):raise ValueError('Empty or repeated roots')
 for row in rows:
  if row['machine'].count('---')!=1 or type(row['anchor']) is not int or not 0<=row['anchor']<8192:raise ValueError('Invalid partial root')
  codes(row['machine']);values=[]
  for child in row['cycles']:
   if type(child['value']) is not int or not 0<=child['value']<16:raise ValueError('Invalid child slot')
   values.append(child['value']);cert_text(child['certificate'])
  if len(values)!=len(set(values)):raise ValueError('Repeated child certificate')
 BUILD.mkdir(parents=True,exist_ok=True);source=BUILD/'StateBranchCycles.v';source.write_text(generate(rows))
 members=BUILD/'machines.txt';members.write_text('\n'.join(machines)+'\n')
 flags=['-Q',str(ROOT/'theories'),'BBB24','-Q',str(BUILD),'BBB24StateBranchCycles'];module='BBB24StateBranchCycles.StateBranchCycles'
 commands=[(['coqc','-w','-abstract-large-number','-native-compiler','no',*flags,str(ROOT/'theories/StateBranchCycles.v')],'bridge.log'),
           (['coqc','-w','-abstract-large-number','-native-compiler','no',*flags,str(source)],'compile.log')]
 if not a.prepare:commands.append((['coqchk','-silent','-bytecode-compiler','yes',*flags,module],'coqchk.log'))
 start=time.monotonic()
 for command,log in commands:
  with (BUILD/log).open('w') as out:subprocess.run(['nice','-n','10',*command],cwd=REPO,stdout=out,stderr=subprocess.STDOUT,check=True,timeout=a.timeout)
 descriptor=dict(kind='state_only',module=module,board=module+'.branch_state_board',state_sound=module+'.branch_state_board_sound',
  state_small_sound=module+'.branch_state_board_small_sound',was_pending=module+'.branch_state_board_was_pending',
  state_discharge=module+'.branch_families_state_discharged',state_coverage=module+'.bootstrap_branch_state_coverage',
  state_bound=8192,members=str(members.relative_to(ROOT)),flags=['-Q','four/theories','BBB24','-Q','four/build/state-branch-cycles','BBB24StateBranchCycles'])
 sources=SOURCES+['four/theories/StateBranchCycles.v','four/theories/CycleBatch.v','four/theories/CycleCensus.v',
  'four/theories/Checkers/Cycle.v','four/theories/Checkers/TCycler.v','four/tools/check_state_branch_cycles.py','four/tools/check_late_cycles.py']
 report=dict(status='queued_for_combined_audit' if a.prepare else 'recursive_coqchk_passed',scope='state_only',families=len(rows),
  partial=len(rows),concrete=0,defined_children=16*len(rows),halting_choices=len(rows),cycle_child_certificates=sum(len(r['cycles']) for r in rows),
  state_bound=8192,instruction_bound=None,state_census_linked=None if a.prepare else len(rows),descriptor=descriptor,
  input_sha256=sha(INPUT),member_ids_sha256=sha(members),generated_source_sha256=sha(source),source_sha256={x:sha(REPO/x) for x in sources},
  proof_object_sha256={str(x.relative_to(ROOT)):sha(x) for x in [ROOT/'theories/StateBranchCycles.vo',BUILD/'StateBranchCycles.vo']},
  accounting='Original partial families. All sixteen defined and the separate halting choice are checked. No root NonHalt or instruction claim.',
  validation='Compiled state/cycle child checks, reached undefined prefix and exact bootstrap membership; '+('queued for combined recursive audit.' if a.prepare else 'recursive coqchk passed.'))
 dest=ROOT/'research'/('state-branch-cycles-queued.json' if a.prepare else 'state-branch-cycles-checked.json');text=json.dumps(report,indent=2)+'\n'
 if not dest.exists() or a.refresh:dest.write_text(text)
 elif dest.read_text()!=text:raise ValueError('Frozen report differs')
 print(json.dumps(dict(status=report['status'],families=len(rows),seconds=round(time.monotonic()-start,2))))
if __name__=='__main__':main()
