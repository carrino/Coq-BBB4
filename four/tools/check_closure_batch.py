"""Replay a bounded closure batch and attach it to the frozen census.

The tracked input contains machine tables and checker parameters only. All
successes and original pending-set memberships are checked in generated Coq
shards under build/closure-batch; coqchk audits the aggregate before this tool
writes its ledger. Existing proof sources and reports are never modified.

Run `make -C four` first. `--select 1024` or `--select 4096` selects the lowest
SHA256 machine hashes from the frozen full candidate TSV, excluding the pilot.
`--resume` reuses compiled shards only when source, dependency and .vo hashes
match a successful compile receipt; the complete kernel audit always runs.
With no selection/refresh flag the recorded input and outputs must reproduce.
"""
import argparse
import csv
import hashlib
import io
import json
import re
import subprocess
import time
from collections import Counter
from pathlib import Path

import generate_pipeline_examples as generator

ROOT = Path(__file__).resolve().parents[1]
BUILD = ROOT/'build/closure-batch'
INPUT = ROOT/'research/closure-batch-input.json'
REPORT = ROOT/'research/closure-batch-summary.json'
LEDGER = ROOT/'research/closure-batch.tsv'
SEARCH = ROOT/'research/pipeline-low-budget.json'
PILOT = ROOT/'research/pipeline-examples.json'
CANDIDATES = ROOT/'build/pipeline/low-budget/candidates.tsv'
SHARD_SIZE = 64
FIELDS = ['machine', 'stage', 'mode', 'bound', 'size', 'anchor', 'fuel', 'extra']


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def source_hashes():
    paths = {Path(__file__).resolve(), Path(generator.__file__).resolve(), SEARCH, PILOT}
    todo = ['PipelineExamples', 'ClosureBatch']
    seen = set()
    while todo:
        module = todo.pop()
        if module in seen:
            continue
        seen.add(module)
        path = ROOT/'theories'/Path(*module.split('.')).with_suffix('.v')
        paths.add(path)
        for prefix, names in re.findall(
                r'From\s+(BBB24[\w.]*)\s+Require\s+(?:Import|Export)\s+([\w\s]+)\.',
                path.read_text()):
            base = prefix.split('.')[1:]
            todo.extend('.'.join(base+[name]) for name in names.split())
    return {str(p.relative_to(ROOT.parent)): sha(p) for p in sorted(paths)}


def machine_hash(row):
    return hashlib.sha256(row['machine'].encode()).digest()


def selected_rows(size):
    frozen = json.loads(SEARCH.read_text())
    if sha(CANDIDATES) != frozen['candidate_tsv_sha256']:
        raise ValueError('Full candidate TSV differs from the frozen search report')
    with CANDIDATES.open() as f:
        rows = list(csv.DictReader(f, delimiter='\t'))
    if len(rows) != 93792 or len({r['machine'] for r in rows}) != len(rows):
        raise ValueError('Expected exactly 93,792 distinct candidate families')
    excluded = {r['machine'] for r in json.loads(PILOT.read_text())['rows']}
    rows = sorted((r for r in rows if r['machine'] not in excluded), key=machine_hash)[:size]
    for row in rows:
        for key in set(FIELDS)-{'machine', 'mode'}:
            row[key] = int(row[key])
    return rows


def select(size):
    rows = selected_rows(size)
    data = {'selection': 'Lowest SHA256(machine UTF-8) hashes, excluding the 76 checked pilot families',
            'candidate_tsv_sha256': sha(CANDIDATES), 'pilot_sha256': sha(PILOT),
            'selected_rows': size, 'columns': FIELDS, 'rows': [[r[k] for k in FIELDS] for r in rows]}
    # One compact array per family; do not commit large generated proof text.
    prefix = json.dumps({k:v for k,v in data.items() if k != 'rows'}, indent=2)[:-2]
    INPUT.write_text(prefix + ',\n  "rows": [\n    '
                     + ',\n    '.join(json.dumps(r) for r in data['rows']) + '\n  ]\n}\n')


def load_inputs():
    data = json.loads(INPUT.read_text())
    frozen = json.loads(SEARCH.read_text())
    if data['candidate_tsv_sha256'] != frozen['candidate_tsv_sha256'] or data['pilot_sha256'] != sha(PILOT):
        raise ValueError('Selection provenance differs from the frozen source reports')
    if data['columns'] != FIELDS or data['selected_rows'] not in (1024, 4096):
        raise ValueError('Unexpected input schema or batch size')
    if any(not isinstance(r, list) or len(r) != len(FIELDS) for r in data['rows']):
        raise ValueError('Malformed input row')
    rows = [dict(zip(FIELDS, r)) for r in data['rows']]
    if len(rows) != data['selected_rows'] or len({r['machine'] for r in rows}) != len(rows):
        raise ValueError('Incomplete or duplicate batch input')
    if rows != sorted(rows, key=machine_hash):
        raise ValueError('Batch must retain deterministic hash order')
    excluded = {r['machine'] for r in json.loads(PILOT.read_text())['rows']}
    for row in rows:
        generator.codes(row['machine'])
        if row['machine'] in excluded:
            raise ValueError('Already checked pilot family in new batch')
        if any(type(row[k]) is not int or row[k] < 0 for k in set(FIELDS)-{'machine', 'mode'}):
            raise ValueError('Invalid numerical checker parameter')
        stage = row['stage']
        if row['bound'] != 4096 or stage >= len(frozen['manifest']['stages']):
            raise ValueError('Unsupported checker bound/stage')
        if any(row[k] != v for k,v in frozen['manifest']['stages'][stage].items()):
            raise ValueError('Checker parameters differ from the recorded stage budget')
    if CANDIDATES.exists() and rows != selected_rows(len(rows)):
        raise ValueError('Input differs from deterministic full-queue selection')
    return rows


NONHALT = '''
From BBB24 Require Import ClosureBatch.
Lemma closure_board_nonhalt : forall family,
  In family pipeline_board -> NonHalt family.
Proof.
  intros family Hin. unfold pipeline_board in Hin.
  apply in_map_iff in Hin as ([codes cert] & <- & Hin).
  eapply batch_nonhalt; [exact pipeline_rows_checked|exact Hin].
Qed.
Print Assumptions closure_board_nonhalt.
'''


def forall_proof(modules, theorem):
    return '\n'.join(f'  apply Forall_cons; [exact {m}.{theorem}|].' for m in modules) + '\n  apply Forall_nil.'


def aggregate(modules, count):
    boards = ';\n  '.join(m+'.pipeline_board' for m in modules)
    return f'''(** Generated by check_closure_batch.py. *)
From Coq Require Import List NArith.
From BBB24 Require Import Statement Spec Bounds Census Bootstrap Closeout AffineCloseout PipelineExamples.
From BBB24ClosureBatch Require Import {' '.join(modules)}.
Import ListNotations.
Definition closure_batch_boards : list (list TM) := [
  {boards}].
Definition closure_batch_board := concat closure_batch_boards.

Lemma concat_sound : forall bs bi boards,
  Forall (BoardSound bs bi) boards -> BoardSound bs bi (concat boards).
Proof.
  intros bs bi boards H. induction H; simpl.
  - intros family Hin. contradiction.
  - apply board_sound_app; assumption.
Qed.
Lemma concat_all : forall (P:TM->Prop) boards,
  Forall (fun b => forall family, In family b -> P family) boards ->
  forall family, In family (concat boards) -> P family.
Proof.
  intros P boards H. induction H; intros family Hin; simpl in Hin.
  - contradiction.
  - apply in_app_iff in Hin as [Hin|Hin]; auto.
Qed.
Lemma concat_pending_check : forall boards,
  Forall (fun b => forallb (pending_check 9 empty bootstrap) b = true) boards ->
  forallb (pending_check 9 empty bootstrap) (concat boards) = true.
Proof.
  intros boards H. induction H; [reflexivity|].
  cbn [concat].
  rewrite forallb_app, H, IHForall. reflexivity.
Qed.
Lemma checked_board_pending : forall board,
  forallb (pending_check 9 empty bootstrap) board = true ->
  forall family, In family board -> bootstrap_pending family.
Proof.
  intros board H family Hin. apply pending_check_sound.
  apply forallb_forall with (x:=family) in H; assumption.
Qed.
Lemma closure_batch_board_small_sound : BoardSound 4096%N 4096%N closure_batch_board.
Proof.
  apply concat_sound.
{forall_proof(modules, 'pipeline_board_small_sound')}
Qed.
Lemma closure_batch_board_sound : BoardSound scoreN scoreN closure_batch_board.
Proof.
  apply concat_sound.
{forall_proof(modules, 'pipeline_board_sound')}
Qed.
Lemma closure_batch_board_nonhalt : forall family,
  In family closure_batch_board -> NonHalt family.
Proof.
  apply concat_all.
{forall_proof(modules, 'closure_board_nonhalt')}
Qed.
Lemma closure_batch_pending_checked :
  forallb (pending_check 9 empty bootstrap) closure_batch_board = true.
Proof.
  apply concat_pending_check.
{forall_proof(modules, 'pipeline_board_pending_checked')}
Qed.
Example closure_batch_count : length closure_batch_board = {count}.
Proof. vm_compute. reflexivity. Qed.

Definition bootstrap_closure_batch_pending :=
  remaining PipelineExamples.bootstrap_pipeline_pending closure_batch_board.
Theorem bootstrap_closure_batch_coverage : forall tm,
  Bounds scoreN scoreN tm \\/ bootstrap_closure_batch_pending tm.
Proof.
  exact (closeout_coverage _ _ _ _
    PipelineExamples.bootstrap_pipeline_coverage closure_batch_board_sound).
Qed.
Lemma closure_batch_board_pending : forall family,
  In family closure_batch_board -> bootstrap_pending family.
Proof.
  eapply checked_board_pending; exact closure_batch_pending_checked.
Qed.
Theorem closure_batch_families_discharged : forall family,
  In family closure_batch_board -> forall tm, TM_le family tm ->
  bootstrap_pending tm /\\ Bounds scoreN scoreN tm /\\ ~ bootstrap_closure_batch_pending tm.
Proof.
  intros family Hin tm Hle. split.
  - destruct (closure_batch_board_pending family Hin) as (leaf & Hleaf & Hlf).
    exists leaf. split; [exact Hleaf|]. eapply closeout_tm_le_trans; eauto.
  - split; [exact (closure_batch_board_sound family Hin tm Hle)|].
    intros [_ Hremaining].
    assert (Hhit : board_check closure_batch_board tm = true).
    {{ apply existsb_exists. exists family. split; [exact Hin|].
       apply table_leb_spec. exact Hle. }}
    congruence.
Qed.
Print Assumptions bootstrap_closure_batch_coverage.
Print Assumptions closure_batch_families_discharged.
Print Assumptions closure_batch_board_nonhalt.
'''


def run(args, log, timeout):
    start = time.monotonic()
    with log.open('w') as f:
        subprocess.run(args, cwd=ROOT.parent, stdout=f, stderr=subprocess.STDOUT,
                       timeout=timeout, check=True)
    return time.monotonic()-start


def compile_shard(path, dependencies, timeout, resume):
    receipt = path.with_suffix('.checked.json')
    vo = path.with_suffix('.vo')
    # Generator edits cannot alter an identical generated source. Receipt
    # reuse therefore pins the Coq dependencies and .v/.vo identities, while
    # the final report separately pins all generator and provenance sources.
    theory_dependencies = {k:v for k,v in dependencies.items() if k.endswith('.v')}
    evidence = {'source_sha256': sha(path), 'dependencies_sha256': theory_dependencies}
    if resume and receipt.exists() and vo.exists():
        previous = json.loads(receipt.read_text())
        previous['dependencies_sha256'] = {k:v for k,v in previous['dependencies_sha256'].items()
                                          if k.endswith('.v')}
        if previous == {**evidence, 'vo_sha256': sha(vo)}:
            print(f'Reused {path.stem}', flush=True)
            return 0
    elapsed = run(['coqc', '-w', '-abstract-large-number', '-native-compiler', 'no',
                   '-Q', str(ROOT/'theories'), 'BBB24', '-Q', str(BUILD), 'BBB24ClosureBatch', str(path)],
                  path.with_suffix('.log'), timeout)
    receipt.write_text(json.dumps({**evidence, 'vo_sha256': sha(vo)}, indent=2)+'\n')
    print(f'Checked {path.stem} ({elapsed:.2f}s)', flush=True)
    return elapsed


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--select', type=int, choices=(1024,4096))
    parser.add_argument('--refresh', action='store_true')
    parser.add_argument('--resume', action='store_true')
    parser.add_argument('--timeout', type=int, default=300, help='Seconds per shard')
    args = parser.parse_args()
    BUILD.mkdir(parents=True, exist_ok=True)
    if args.select:
        select(args.select)
    rows = load_inputs()
    dependencies = source_hashes()
    if not (args.select or args.refresh):
        recorded = json.loads(REPORT.read_text())
        if recorded['input_sha256'] != sha(INPUT) or recorded['source_sha256'] != dependencies:
            raise ValueError('Input/proof hashes changed; --refresh is required')
    modules = []
    shards = []
    elapsed = 0
    for start in range(0, len(rows), SHARD_SIZE):
        module = f'ClosureBatch{start//SHARD_SIZE:03}'
        path = BUILD/f'{module}.v'
        path.write_text(generator.generate({'rows':rows[start:start+SHARD_SIZE]}) + NONHALT)
        elapsed += compile_shard(path, dependencies, args.timeout, args.resume)
        modules.append(module); shards.append(path)
    all_path = BUILD/'ClosureBatchAll.v'
    all_path.write_text(aggregate(modules, len(rows)))
    elapsed += compile_shard(all_path, dependencies, args.timeout, args.resume)
    shards.append(all_path)
    audit_time = run(['coqchk', '-silent', '-bytecode-compiler', 'yes',
                     '-Q', str(ROOT/'theories'), 'BBB24', '-Q', str(BUILD), 'BBB24ClosureBatch',
                     'BBB24ClosureBatch.ClosureBatchAll'], BUILD/'coqchk.log', args.timeout*len(shards))
    machines = {r['machine'] for r in rows}
    with (ROOT/'research/affine-batch.tsv').open() as f:
        affine = {r['machine'] for r in csv.DictReader(f, delimiter='\t') if r['status']=='coq_checked'}
    pilot = {r['machine'] for r in json.loads(PILOT.read_text())['rows']}
    report = {
        'scope': 'Selected core families from the full low-budget closure sweep, not a population rate estimate',
        'coq_version': subprocess.check_output(['coqc','--version'], text=True).splitlines()[0],
        'input_sha256': sha(INPUT), 'selection': json.loads(INPUT.read_text())['selection'],
        'checked_families': len(rows), 'census_linked_families': len(rows),
        'stage_counts': dict(sorted(Counter(str(r['stage']) for r in rows).items())),
        'bounds': {'state':4096,'instruction':4096},
        'overlap': {'affine_628':len(machines & affine), 'pipeline_pilot_76':len(machines & pilot),
                    'distinct_union_with_affine_and_pilot':len(machines|affine|pilot)},
        'overlap_sources_sha256': {'research/affine-batch.tsv':sha(ROOT/'research/affine-batch.tsv'),
                                   'research/pipeline-examples.json':sha(PILOT)},
        'coverage_theorem': 'BBB24ClosureBatch.ClosureBatchAll.bootstrap_closure_batch_coverage',
        'discharge_theorem': 'BBB24ClosureBatch.ClosureBatchAll.closure_batch_families_discharged',
        'residual_predicate': 'BBB24ClosureBatch.ClosureBatchAll.bootstrap_closure_batch_pending',
        'accounting': 'Every selected family and completion is excluded from the refined residual; original bootstrap structural weights are not recomputed',
        'source_sha256': dependencies, 'shard_sha256': {p.name:sha(p) for p in shards},
        'validation': 'VM proofs of stage checks and pending membership, plus recursive coqchk of the aggregate',
    }
    buffer = io.StringIO(newline='')
    writer = csv.DictWriter(buffer, fieldnames=FIELDS+['status','census_linked','theorem'],
                            delimiter='\t', lineterminator='\n')
    writer.writeheader()
    writer.writerows({**r,'status':'coq_checked','census_linked':'yes','theorem':report['discharge_theorem']} for r in rows)
    summary = json.dumps(report, indent=2)+'\n'
    if args.select or args.refresh:
        REPORT.write_text(summary); LEDGER.write_text(buffer.getvalue())
    elif REPORT.read_text()!=summary or LEDGER.read_text()!=buffer.getvalue():
        raise ValueError('Recorded closure evidence differs from audited output')
    print(json.dumps({'checked':len(rows),'linked':len(rows),'compile_seconds':round(elapsed,2),
                      'audit_seconds':round(audit_time,2),'overlap':report['overlap']}))


if __name__ == '__main__':
    main()
