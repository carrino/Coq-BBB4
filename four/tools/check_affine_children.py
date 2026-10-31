"""Compile a compact affine child board without census-membership claims.

The completion-safe child theorems are intended for an explicit parent branch
join. Child count is never promoted to a count of discharged original roots.
"""
import argparse
import json
from pathlib import Path
import re
import subprocess
import time
from check_affine_wave import ROOT,load_bundle,shard,sha,source_hashes

REPO=ROOT.parent

def main():
 p=argparse.ArgumentParser(description=__doc__)
 p.add_argument('--input',type=Path,required=True);p.add_argument('--name',required=True)
 p.add_argument('--report',type=Path,required=True);p.add_argument('--prepare',action='store_true')
 p.add_argument('--timeout',type=int,default=3600);a=p.parse_args()
 if not re.fullmatch('[A-Z][A-Za-z0-9_]*',a.name):raise ValueError('Invalid module name')
 build=ROOT/'build/affine-children'/a.name;build.mkdir(parents=True,exist_ok=True)
 data,paths=load_bundle(a.input,build/'certificates')
 text=shard(paths,data['bound'],data['cfuel'],data['fuel']).split('Lemma board_pending_checked',1)[0]
 text+='\nFrom BBB24 Require Import StateOnlyCloseout.\n'
 text+=f'''Lemma state_small_sound : StateBoardSound (N.to_nat {data['bound']}%N) board.
Proof. intros family Hin tm Hle. exact (proj1 (board_small_sound family Hin tm Hle)). Qed.
Lemma state_sound : StateBoardSound score board.
Proof. intros family Hin tm Hle. exact (proj1 (board_sound family Hin tm Hle)). Qed.
Print Assumptions board_small_sound.
'''
 source=build/'Children.v';source.write_text(text)
 members=build/'machines.txt';members.write_text('\n'.join(p.stem for p in paths)+'\n')
 flags=['-Q',str(ROOT/'theories'),'BBB24','-Q',str(ROOT/'build/affine-children'),'BBB24AffineChildren']
 module='BBB24AffineChildren.'+a.name+'.Children'
 commands=[(['coqc','-w','-abstract-large-number','-native-compiler','no',*flags,str(source)],'compile.log')]
 if not a.prepare:commands.append((['coqchk','-silent','-bytecode-compiler','yes',*flags,module],'coqchk.log'))
 start=time.monotonic()
 for cmd,log in commands:
  with (build/log).open('w') as out:subprocess.run(['nice','-n','10',*cmd],cwd=REPO,stdout=out,stderr=subprocess.STDOUT,check=True,timeout=a.timeout)
 sources=source_hashes();sources[str(Path(__file__).resolve().relative_to(REPO))]=sha(Path(__file__))
 report=dict(status='queued_for_combined_audit' if a.prepare else 'recursive_coqchk_passed',scope='child_bounds_only',
  children=len(paths),original_roots_discharged=0,census_linked=0,bound=data['bound'],
  descriptor=dict(module=module,board=module+'.board',small_sound=module+'.board_small_sound',sound=module+'.board_sound',
   state_sound=module+'.state_sound',nonhalt=module+'.board_nonhalt',members=str(members.relative_to(ROOT)),
   flags=['-Q','four/theories','BBB24','-Q','four/build/affine-children','BBB24AffineChildren']),
  input_sha256=sha(a.input),member_ids_sha256=sha(members),generated_source_sha256=sha(source),
  proof_object_sha256=sha(source.with_suffix('.vo')),source_sha256=sources,
  accounting='Every affine child has a completion-safe bound. No direct bootstrap membership or parent discharge is inferred.')
 serialized=json.dumps(report,indent=2)+'\n'
 if a.report.exists() and a.report.read_text()!=serialized:raise ValueError('Frozen child report differs')
 a.report.write_text(serialized)
 print(json.dumps(dict(status=report['status'],children=len(paths),seconds=round(time.monotonic()-start,2))))
if __name__=='__main__':main()
