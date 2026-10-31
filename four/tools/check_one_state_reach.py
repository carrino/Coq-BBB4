"""Replay a state-only one-state-avoidance closeout. No instruction claims.

--select chooses qualifying direct cores from the frozen advanced remainder.
Default replay uses only the compact tracked packed-table input. Generated proof
shards and the per-machine ledger stay under build/one-state-reach. Every input
gets a kernel-checked state bound0 and original census pending membership;
all table completions are covered by the state-only closeout theorem.
"""
import argparse
from collections import Counter
import csv
import functools
import hashlib
import io
import itertools
import json
from pathlib import Path
import subprocess
import time

from check_shadow_links import dependency_hashes
from generate_pipeline_examples import codes

ROOT = Path(__file__).resolve().parents[1]
BUILD = ROOT/'build/one-state-reach'
INPUT = ROOT/'research/one-state-reach-input.json'
REPORT = ROOT/'research/one-state-reach-summary.json'
SOURCE = ROOT/'build/advanced/full/not-accepted.txt'
SOURCE_REPORT = ROOT/'research/advanced-full.json'
SHARD_SIZE = 1024
LOADPATH = ['-Q',str(ROOT/'theories'),'BBB24','-Q',str(BUILD),'BBB24StateReach']
PERMS = [(0,)+p for p in itertools.permutations((1,2,3))]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def unpack(packed):
    if type(packed) is not int or not 0<=packed<2**32:
        raise ValueError('Expected exactly eight 4-bit transition codes')
    cells=[]
    for i in range(8):
        v=(packed>>(4*i))&15
        cells.append(f'{v//4}{"R" if v&2 else "L"}{"B" if v&1 else "A"}')
    return ''.join(cells[:4])+'_'+''.join(cells[4:])


def pack(machine):
    cells=codes(machine)
    if 16 in cells:
        raise ValueError('The packed state batch contains only total tables')
    packed=sum(v<<(4*i) for i,v in enumerate(cells))
    if unpack(packed)!=machine:
        raise ValueError('Packed machine round trip failed')
    return packed


def avoiding(cells, other):
    return tuple(-2 if v==16 else -1 if v%2!=other else (v//4)*2+(v//2)%2
                 for v in cells[4*other:4*other+4])


def rank(table, direction):
    ranks=[None]*4
    def visit(s,seen):
        if s in seen:
            return None
        if ranks[s] is not None:
            return ranks[s]
        v=table[s]
        if v<0 or v%2!=direction:
            ranks[s]=0
        else:
            previous=visit(v//2,seen|{s})
            if previous is None:
                return None
            ranks[s]=previous+1
        return ranks[s]
    for s in range(4):
        if visit(s,set()) is None:
            return None
    return ranks


def category(table):
    if -2 in table:
        return 'undefined'
    if table[0]!=-1:
        return 'blank_spinout'
    if rank(table,0) is not None or rank(table,1) is not None:
        return 'uniform_reach_candidate'
    return 'two_cell_trap'


@functools.lru_cache(None)
def canonical(table):
    images=[]
    for p in PERMS:
        for mirrored in (0,1):
            result=[None]*4
            for s,v in enumerate(table):
                result[p[s]]=v if v<0 else 2*p[v//2]+((v%2)^mirrored)
            images.append(tuple(result))
    return min(images)


def select():
    prior=json.loads(SOURCE_REPORT.read_text())
    if sha(SOURCE)!=prior['not_accepted_sha256']:
        raise ValueError('Remainder differs from the frozen advanced report')
    machines=SOURCE.read_text().splitlines()
    if len(machines)!=prior['not_accepted_rows'] or len(machines)!=len(set(machines)):
        raise ValueError('Remainder inventory is incomplete or duplicated')
    accepted=[]; pair_counts=Counter(); combinations=Counter(); patterns=Counter()
    for machine in machines:
        cells=codes(machine)
        tables=[avoiding(cells,q) for q in range(2)]
        classes=tuple(category(t) for t in tables)
        pair_counts.update(classes); combinations[','.join(classes)]+=1
        patterns.update(canonical(t) for t in tables)
        if classes==('uniform_reach_candidate','uniform_reach_candidate'):
            accepted.append(pack(machine))
    accepted.sort(key=unpack)
    data={
        'encoding':'Eight total transitions; A0 in lowest nibble. Code=4*write+2*right+next_B.',
        'source_report_sha256':sha(SOURCE_REPORT),'source_input_sha256':sha(SOURCE),
        'source_rows':len(machines),'selected_rows':len(accepted),
        'selection':'Both state-avoiding rows have a blank exit and an acyclic write graph in at least one direction.',
        'state_target_pair_categories':dict(sorted(pair_counts.items())),
        'machine_categories':dict(sorted(combinations.items())),
        'canonical_avoid_patterns':len(patterns),'rows':accepted}
    prefix=json.dumps({k:v for k,v in data.items() if k!='rows'},indent=2)[:-2]
    lines=[', '.join(map(str,accepted[i:i+32])) for i in range(0,len(accepted),32)]
    INPUT.write_text(prefix+',\n  "rows": [\n    '+',\n    '.join(lines)+'\n  ]\n}\n')


def load():
    data=json.loads(INPUT.read_text())
    prior=json.loads(SOURCE_REPORT.read_text())
    if data['source_report_sha256']!=sha(SOURCE_REPORT) or data['source_input_sha256']!=prior['not_accepted_sha256']:
        raise ValueError('State batch belongs to another frozen remainder')
    rows=data['rows']
    if len(rows)!=data['selected_rows'] or len(rows)!=len(set(rows)) or not rows:
        raise ValueError('State batch is empty, duplicated, or incomplete')
    machines=[unpack(n) for n in rows]
    if machines!=sorted(machines):
        raise ValueError('Keep the packed input in deterministic machine order')
    for machine in machines:
        cells=codes(machine)
        if any(category(avoiding(cells,q))!='uniform_reach_candidate' for q in range(2)):
            raise ValueError('State batch contains a failed search criterion')
    return data,rows


HEADER='''(** GENERATED by four/tools/check_one_state_reach.py; STATE only. *)
From Coq Require Import List NArith.
From BBB24 Require Import Statement Spec Census Bootstrap Closeout
  OneStateReach StateOnlyCloseout OneStateBatch.
Import ListNotations.
'''


def shard_text(rows):
    body=';\n  '.join(';'.join(f'{v}%N' for v in rows[i:i+16]) for i in range(0,len(rows),16))
    return HEADER+f'''
Definition rows : list N := [
  {body}].
Lemma rows_checked : ore_batch_check rows=true.
Proof. vm_compute. reflexivity. Qed.
Definition board := ore_board rows.
Theorem board_state_sound : StateBoardSound 0 board.
Proof. apply ore_batch_state_sound; exact rows_checked. Qed.
Theorem board_nonhalt : forall family, In family board -> NonHalt family.
Proof. apply ore_batch_nonhalt; exact rows_checked. Qed.
Lemma pending_checked : forallb (pending_check 9 empty bootstrap) board=true.
Proof. vm_compute. reflexivity. Qed.
Theorem board_pending : forall family, In family board -> bootstrap_pending family.
Proof.
  intros family Hin. apply pending_check_sound.
  pose proof pending_checked as H. apply forallb_forall with (x:=family) in H; assumption.
Qed.
Example board_count : length board={len(rows)}.
Proof. reflexivity. Qed.
'''


def forall_proof(modules,theorem):
    return '\n'.join(f'  apply Forall_cons; [exact {m}.{theorem}|].' for m in modules)+'\n  apply Forall_nil.'


def aggregate(modules,count):
    boards=';\n  '.join(m+'.board' for m in modules)
    return HEADER+f'''From BBB24 Require Import CensusUnion.
From BBB24StateReach Require Import {' '.join(modules)}.
Definition state_boards := [
  {boards}].
Definition state_board := concat state_boards.
Theorem state_board_zero : StateBoardSound 0 state_board.
Proof. apply state_boards_sound. unfold state_boards.
{forall_proof(modules,'board_state_sound')}
Qed.
Theorem state_board_bound : StateBoardSound score state_board.
Proof. apply state_board_zero_weaken, state_board_zero. Qed.
Theorem state_board_pending : forall family, In family state_board -> bootstrap_pending family.
Proof. apply boards_pending. unfold state_boards.
{forall_proof(modules,'board_pending')}
Qed.
Example state_board_count :
  fold_left (fun count (_ : TM) => N.succ count) state_board 0%N = {count}%N.
Proof. vm_compute. reflexivity. Qed.
Definition state_pending := remaining bootstrap_pending state_board.
Theorem state_coverage : forall tm, QHBound score tm \\/ state_pending tm.
Proof. exact (state_closeout_coverage _ _ _ bootstrap_state_coverage state_board_bound). Qed.
Theorem state_families_discharged : forall family, In family state_board ->
  forall tm, TM_le family tm -> bootstrap_pending tm /\\ QHBound 0 tm /\\ ~state_pending tm.
Proof. exact (state_board_discharge _ _ state_board_pending state_board_zero). Qed.
Theorem state_upper_if_remaining :
  (forall tm, state_pending tm -> QHBound score tm) -> forall tm, QHBound score tm.
Proof. intros H tm. destruct (state_coverage tm); auto. Qed.
Print Assumptions state_families_discharged.
'''


def run(command,log,timeout):
    start=time.monotonic()
    with log.open('w') as stream:
        subprocess.run(command,cwd=ROOT.parent,stdout=stream,stderr=subprocess.STDOUT,check=True,timeout=timeout)
    return round(time.monotonic()-start,3)


def source_hashes():
    roots=[ROOT/'theories/OneStateBatch.v',ROOT/'theories/CensusUnion.v']
    dependencies=dependency_hashes(roots,LOADPATH)
    return {**dependencies,'tools/check_one_state_reach.py':sha(Path(__file__)),
            'tools/generate_pipeline_examples.py':sha(ROOT/'tools/generate_pipeline_examples.py'),
            'tools/check_shadow_links.py':sha(ROOT/'tools/check_shadow_links.py')}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--select',action='store_true')
    parser.add_argument('--refresh',action='store_true')
    parser.add_argument('--pilot',type=int,default=0,help='Check only this many rows, without publishing evidence')
    parser.add_argument('--resume',action='store_true')
    parser.add_argument('--timeout',type=int,default=300)
    args=parser.parse_args()
    if args.select:
        if not args.refresh: raise ValueError('--select requires --refresh')
        select()
    data,rows=load()
    if args.pilot:
        rows=rows[:args.pilot]
    BUILD.mkdir(parents=True,exist_ok=True)
    sources=source_hashes(); input_hash=sha(INPUT)
    if not args.refresh and not args.pilot:
        old=json.loads(REPORT.read_text())
        if old['source_sha256']!=sources or old['input_sha256']!=input_hash:
            raise ValueError('State proof evidence changed; refresh and re-audit')
    paths=[]; modules=[]
    for offset in range(0,len(rows),SHARD_SIZE):
        module=f'StateReach{offset//SHARD_SIZE:03}'
        path=BUILD/(module+'.v'); path.write_text(shard_text(rows[offset:offset+SHARD_SIZE]))
        evidence={'source_sha256':sha(path),'dependencies_sha256':{k:v for k,v in sources.items() if k.endswith('.v')}}
        receipt=path.with_suffix('.checked.json');vo=path.with_suffix('.vo')
        reuse=False
        if args.resume and receipt.exists() and vo.exists():
            previous=json.loads(receipt.read_text())
            previous['dependencies_sha256']={k:v for k,v in previous['dependencies_sha256'].items() if k.endswith('.v')}
            reuse=previous=={**evidence,'vo_sha256':sha(vo)}
        if reuse:
            seconds=0
        else:
            seconds=run(['coqc','-native-compiler','no',*LOADPATH,str(path)],path.with_suffix('.log'),args.timeout)
            receipt.write_text(json.dumps({**evidence,'vo_sha256':sha(vo)},indent=2)+'\n')
        print(f'{"Reused" if reuse else "Checked"} {module}: {seconds}s',flush=True)
        paths.append(path);modules.append(module)
    all_path=BUILD/'StateReachAll.v';all_path.write_text(aggregate(modules,len(rows)))
    run(['coqc','-native-compiler','no',*LOADPATH,str(all_path)],BUILD/'aggregate.log',args.timeout)
    paths.append(all_path)
    if args.pilot:
        print(f'Pilot compiled {len(rows)} rows; no audit/report publication.',flush=True)
        return
    run(['coqchk','-silent','-bytecode-compiler','yes',*LOADPATH,'BBB24StateReach.StateReachAll'],BUILD/'coqchk.log',args.timeout*len(paths))
    if input_hash!=sha(INPUT) or sources!=source_hashes():
        raise ValueError('State proof inputs changed during audit')
    stream=io.StringIO();writer=csv.writer(stream,delimiter='\t',lineterminator='\n')
    writer.writerow(['machine','state_bound','instruction_bound','state_census_linked','instruction_census_linked','proof'])
    writer.writerows((unpack(n),0,'','yes','no','BBB24StateReach.StateReachAll.state_families_discharged') for n in rows)
    ledger=stream.getvalue()
    report={'scope':'State-only direct-core closeout; no instruction-bound or raw-table-count claim.',
            'source_rows':data['source_rows'],'state_checked_families':len(rows),
            'state_census_linked_families':len(rows),'instruction_checked_families':0,
            'state_bound':0,'instruction_bound':None,
            'state_coverage_theorem':'BBB24StateReach.StateReachAll.state_coverage',
            'state_discharge_theorem':'BBB24StateReach.StateReachAll.state_families_discharged',
            'state_residual_predicate':'BBB24StateReach.StateReachAll.state_pending',
            'validation':'VM checker and pending-membership proofs for every input, plus recursive coqchk.',
            'input_sha256':input_hash,'source_sha256':sources,
            'shard_sha256':{p.name:sha(p) for p in paths},
            'generated_ledger':'build/one-state-reach/families.tsv',
            'ledger_sha256':hashlib.sha256(ledger.encode()).hexdigest()}
    contents=json.dumps(report,indent=2)+'\n'
    if args.refresh:
        REPORT.write_text(contents)
    elif REPORT.read_text()!=contents:
        raise ValueError('State replay differs from its recorded report')
    (BUILD/'families.tsv').write_text(ledger)
    print(json.dumps({k:report[k] for k in ('state_checked_families','state_census_linked_families','instruction_checked_families')}),flush=True)


if __name__=='__main__':main()
