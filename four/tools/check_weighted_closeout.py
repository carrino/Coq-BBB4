"""Attach a checked weighted board to the frozen bootstrap census.

This wrapper leaves the weighted search, checker and historical pilot audit
untouched. It separately checks actual pending-set membership and transports
4096 bounds to the champion bound, then exports a reusable board descriptor.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT=Path(__file__).resolve().parents[1]

def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()

def source(namespace):
    return f'''From Coq Require Import List NArith.
From BBB24 Require Import Statement Spec Bounds Census Bootstrap Closeout CertifiedBoard.
From {namespace} Require Import WeightedBoard.
Import ListNotations.
Definition weighted_board := WeightedBoard.weighted_board.
Lemma weighted_board_small_sound : BoardSound 4096%N 4096%N weighted_board.
Proof. apply WeightedBoard.weighted_board_sound. Qed.
Lemma weighted_board_nonhalt : forall tm, In tm weighted_board -> NonHalt tm.
Proof. apply WeightedBoard.weighted_board_nonhalt. Qed.
Lemma weighted_board_sound : BoardSound scoreN scoreN weighted_board.
Proof.
 intros family Hin tm Hle.
 eapply (bounds_weaken 4096%N 4096%N scoreN scoreN tm).
 - vm_compute. discriminate.
 - vm_compute. discriminate.
 - exact (weighted_board_small_sound family Hin tm Hle).
Qed.
Lemma weighted_pending_checked : forallb (pending_check 9 empty bootstrap) weighted_board = true.
Proof. vm_compute. reflexivity. Qed.
Lemma weighted_board_was_pending : forall tm, In tm weighted_board -> bootstrap_pending tm.
Proof.
 intros tm Hin. apply pending_check_sound.
 pose proof weighted_pending_checked as H.
 apply forallb_forall with (x:=tm) in H; assumption.
Qed.
Definition weighted_pending := remaining bootstrap_pending weighted_board.
Theorem weighted_coverage : forall tm, Bounds scoreN scoreN tm \/ weighted_pending tm.
Proof. exact (closeout_coverage _ _ _ _ bootstrap_coverage weighted_board_sound). Qed.
Theorem weighted_families_discharged : forall family,
 In family weighted_board -> forall tm, TM_le family tm ->
 bootstrap_pending tm /\ Bounds scoreN scoreN tm /\ ~ weighted_pending tm.
Proof. exact (board_families_discharged _ _ _ _ _ weighted_board_was_pending weighted_board_sound). Qed.
Print Assumptions weighted_families_discharged.
'''

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--weighted-report',type=Path,required=True)
    parser.add_argument('--proof-dir',type=Path,required=True)
    parser.add_argument('--report',type=Path,required=True)
    parser.add_argument('--inventory',type=Path,required=True)
    parser.add_argument('--check',action='store_true')
    args=parser.parse_args()
    audit=json.loads(args.weighted_report.read_text())
    namespace=audit['manifest']['namespace']
    if not re.fullmatch(r'[A-Z][A-Za-z0-9_]*(\.[A-Z][A-Za-z0-9_]*)*',namespace):
        raise ValueError('Invalid source namespace')
    if audit['manifest']['state_bound']!=4096 or audit['manifest']['instruction_bound']!=4096:
        raise ValueError('Expected both source bounds at 4096')
    for name,digest in audit['artifacts_sha256'].items():
        if sha(args.proof_dir/name)!=digest:raise ValueError('Changed source proof artifact '+name)
    rows=[r for r in audit['results'] if r['status']=='coq_checked']
    names=[r['machine'] for r in rows]
    if (args.proof_dir/'machines.txt').read_text()!=''.join(m+'\n' for m in names):
        raise ValueError('Source board inventory differs')
    text=source(namespace)
    path=args.proof_dir/'WeightedCloseout.v'
    inventory={'rows':[{'machine':m}for m in names]}
    inputs={'source_report_sha256':sha(args.weighted_report),
            'wrapper_tool_sha256':sha(Path(__file__)),
            'bootstrap_sha256':sha(ROOT/'theories/Bootstrap.v'),
            'closeout_sha256':sha(ROOT/'theories/Closeout.v'),
            'certified_board_sha256':sha(ROOT/'theories/CertifiedBoard.v')}
    if args.check:
        report=json.loads(args.report.read_text())
        if report['inputs']!=inputs or report['families_discharged']!=len(names):raise ValueError('Saved closeout inputs differ')
        if path.read_text()!=text or json.loads(args.inventory.read_text())!=inventory:raise ValueError('Generated wrapper or inventory differs')
        for name,digest in report['proof_artifacts_sha256'].items():
            if sha(args.proof_dir/name)!=digest:raise ValueError('Changed closeout artifact '+name)
        print(f'Validated {len(names)} census-linked weighted families.')
        return
    path.write_text(text)
    flags=['-Q',str(ROOT/'theories'),'BBB24','-Q',str(args.proof_dir.resolve()),namespace]
    for command,logname in [(['coqc','-native-compiler','no',*flags,str(path)],'WeightedCloseout.log'),
                            (['coqchk','-silent','-bytecode-compiler','yes',*flags,namespace+'.WeightedCloseout'],'closeout-coqchk.log')]:
        with (args.proof_dir/logname).open('w') as log:
            subprocess.run(command,stdout=log,stderr=subprocess.STDOUT,check=True,timeout=3600)
    args.inventory.parent.mkdir(parents=True,exist_ok=True)
    args.inventory.write_text(json.dumps(inventory,indent=2)+'\n')
    descriptor={'module':namespace+'.WeightedCloseout','board':'weighted_board',
                'nonhalt':'weighted_board_nonhalt','small_sound':'weighted_board_small_sound',
                'sound':'weighted_board_sound','was_pending':'weighted_board_was_pending',
                'discharged':'weighted_families_discharged',
                'proof_source':str(path.resolve().relative_to(ROOT)),
                'machine_inputs':[{'path':str(args.inventory.resolve().relative_to(ROOT)),'format':'json_rows'}],
                'load_paths':[{'path':str(args.proof_dir.resolve().relative_to(ROOT)),'namespace':namespace}]}
    report={'inputs':inputs,'families_discharged':len(names),'validation':'coqc plus recursive coqchk',
            'descriptor':descriptor,'inventory_sha256':sha(args.inventory),
            'proof_artifacts_sha256':{p.name:sha(p)for p in [path,path.with_suffix('.vo')]}}
    args.report.parent.mkdir(parents=True,exist_ok=True)
    args.report.write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
    print(f'{len(names)} weighted families linked to the frozen census.',flush=True)

if __name__=='__main__':main()
