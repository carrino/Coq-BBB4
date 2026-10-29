"""Expose a completed stream-proof prefix for a later combined kernel audit.

This does not publish an audited proof count. It checks the prefix's literal
inventory and its bounds/membership interfaces in Coq, freezes source/object
hashes, and reports that independent campaign kernel validation is required.
Existing stream Part sources and objects are never rewritten.
"""
import argparse
import io
import csv
import json
from pathlib import Path
import re
import subprocess

from check_weighted_stream_reuse import COMMON,groups,join_board
from check_campaign import packed
from kernel_audit_cache import digest,snapshot

ROOT=Path(__file__).resolve().parents[1]
FOOTER='''Lemma small_sound : BoardSound 4096%N 4096%N board.
Proof. apply strong_board_completions,strong. Qed.
Lemma nonhalt : forall family, In family board -> NonHalt family.
Proof. intros family H;exact(proj1(strong family H)). Qed.
Lemma sound : BoardSound scoreN scoreN board.
Proof. intros family Hin tm Hle;eapply(bounds_weaken 4096%N 4096%N scoreN scoreN).
 - vm_compute. discriminate.
 - vm_compute. discriminate.
 - exact(small_sound family Hin tm Hle).
Qed.
Lemma was_pending : forall family, In family board -> bootstrap_pending family.
Proof. intros family Hin;apply pending_check_sound. pose proof pending_checked as H.
 apply forallb_forall with(x:=family)in H;assumption.
Qed.
Definition pending := remaining bootstrap_pending board.
Theorem coverage : forall tm, Bounds scoreN scoreN tm \/ pending tm.
Proof. exact(closeout_coverage _ _ _ _ bootstrap_coverage sound). Qed.
Theorem discharged : forall family, In family board -> forall tm, TM_le family tm ->
 bootstrap_pending tm /\\ Bounds scoreN scoreN tm /\\ ~ pending tm.
Proof. exact(board_families_discharged _ _ _ _ _ was_pending sound). Qed.
'''


def frozen(path,text):
    if path.exists()and path.read_text()!=text:raise ValueError('Frozen prefix changed; use a new prefix name')
    path.parent.mkdir(parents=True,exist_ok=True);path.write_text(text)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--batch',required=True);parser.add_argument('--parts',type=int,required=True)
    args=parser.parse_args()
    if not re.fullmatch('[a-z][a-z0-9_]*',args.batch)or args.parts<1:raise ValueError('Invalid prefix')
    source_dir=ROOT/'build/weighted-stream'/args.batch
    source_input=ROOT/'research/weighted-stream-reuse'/(args.batch+'-input.json')
    source=json.loads(source_input.read_text());chunks=groups(source['rows'])
    if args.parts*16>len(chunks)+15:raise ValueError('Prefix exceeds the full stream')
    rows=[r for chunk in chunks[:args.parts*16]for r in chunk]
    part_names=[f'Part{i:04}'for i in range(args.parts)]
    artifacts={}
    for name in part_names:
        for suffix in ['.v','.vo']:
            path=source_dir/(name+suffix)
            if not path.is_file():raise ValueError('Prefix part has not compiled: '+str(path))
            artifacts[str(path.relative_to(ROOT))]=digest(path)
    tag=args.batch+f'_prefix{args.parts:04}'
    build=ROOT/'build/weighted-stream-prefix'/tag;build.mkdir(parents=True,exist_ok=True)
    namespace='BBB24WeightedPrefix'+args.batch.capitalize()+f'P{args.parts:04}'
    original='BBB24WeightedStream'+args.batch.capitalize()
    input_path=ROOT/'research/weighted-stream-prefix'/(tag+'-input.json')
    input_data=dict(description='Exact inventory of a compiled proof prefix; queued for independent campaign audit.',
                    full_input=str(source_input.relative_to(ROOT)),full_input_sha256=digest(source_input),parts=args.parts,
                    columns=source['columns'],rows=rows)
    frozen(input_path,json.dumps(input_data,separators=(',',':'))+'\n')
    body=COMMON+'From BBB24 Require Import BoardManifest.\n'+f'From {original} Require Import '+' '.join(part_names)+'.\n'
    body+=join_board(part_names)+FOOTER
    body+='Definition inventory : list N := ['+';'.join(str(packed(r[0]))+'%N'for r in rows)+'].\n'
    body+='''Lemma inventory_checked : manifest_check inventory board=true.
Proof. vm_compute. reflexivity. Qed.
Theorem exact_inventory : manifest_board inventory=board.
Proof. apply manifest_check_sound,inventory_checked. Qed.
'''
    path=build/'PrefixAll.v';frozen(path,body)
    loadpaths=[(ROOT/'theories','BBB24'),(source_dir,original),(build,namespace)]
    flags=[arg for directory,name in loadpaths for arg in ['-Q',str(directory),name]]
    with(build/'compile.log').open('w')as log:
        subprocess.run(['coqc','-native-compiler','no',*flags,str(path)],stdout=log,stderr=subprocess.STDOUT,check=True)
    snap=snapshot([path],loadpaths);snapshot_path=build/'compiled-snapshot.json'
    frozen(snapshot_path,json.dumps(snap,indent=2)+'\n')
    if any(digest(ROOT/p)!=h for p,h in artifacts.items()):raise ValueError('Imported proof artifact changed')
    ledger=io.StringIO();writer=csv.writer(ledger,delimiter='\t',lineterminator='\n')
    writer.writerow(['machine','state_bound','instruction_bound','status']);writer.writerows([r[0],4096,4096,'compiled_queued_campaign_audit']for r in rows)
    ledger_path=input_path.with_name(tag+'.tsv');frozen(ledger_path,ledger.getvalue())
    report_path=input_path.with_name(tag+'-compiled.json')
    descriptor=dict(module=namespace+'.PrefixAll',board='board',nonhalt='nonhalt',small_sound='small_sound',sound='sound',was_pending='was_pending',bound=4096,
                    proof_source=str(path.relative_to(ROOT)),load_paths=[dict(path=str(p.relative_to(ROOT)),namespace=n)for p,n in loadpaths[1:]],
                    machine_inputs=[dict(path=str(input_path.relative_to(ROOT)),format='json_columns')],compiled_report=str(report_path.relative_to(ROOT)))
    report=dict(status='compiled_queued_campaign_audit',checked_canonical_cores=0,compiled_canonical_cores=len(rows),descriptor=descriptor,
                input_sha256=digest(input_path),source_artifacts_sha256=artifacts,
                compiled_snapshot=str(snapshot_path.relative_to(ROOT)),compiled_snapshot_sha256=digest(snapshot_path),
                tool_sha256=digest(Path(__file__)),ledger_sha256=digest(ledger_path),
                promotion_requirement='The combined campaign must independently validate every transitive proof object, directly or through exact-artifact audit receipts, before publishing this prefix as checked.')
    frozen(report_path,json.dumps(report,indent=2)+'\n')
    print(json.dumps(dict(compiled_canonical_cores=len(rows),checked_canonical_cores=0,descriptor=str(report_path))))


if __name__=='__main__':main()
