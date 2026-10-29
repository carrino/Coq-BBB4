"""Replay larger mixed closure batches against the fixed eight-step census.

Selection reads extracted-search logs; ordinary replay needs only the tracked
compact bundle. Each row is checked by Coq, including original pending-set
membership. Generated proof shards stay ignored. No ledger is published until
the aggregate passes recursive coqchk.
"""
import argparse
import base64
from collections import Counter
import csv
import hashlib
import io
import json
from pathlib import Path
import subprocess
import time
import zlib

from generate_pipeline_examples import codes
from check_shadow_links import dependency_hashes

ROOT = Path(__file__).resolve().parents[1]
FIELDS = ['machine', 'mode', 'bound', 'size', 'anchor', 'fuel', 'extra', 'history']
SHARD_SIZE = 64


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def machine_hash(row):
    return hashlib.sha256(row['machine'].encode()).digest()


def validate_row(row):
    codes(row['machine'])
    if set(row) != set(FIELDS) or row['mode'] not in ('ng', 'rw', 'finite', 'hist'):
        raise ValueError('Invalid closure row schema/mode')
    if any(type(row[k]) is not int or row[k] < 0 for k in FIELDS[2:]):
        raise ValueError('Invalid numerical checker parameter')
    if not 0 < row['bound'] <= 65536 or not 0 < row['size'] <= 32:
        raise ValueError('Unsupported bound/window size')
    if row['mode'] != 'hist' and row['history'] != 0:
        raise ValueError('History is only valid for history n-grams')


def select_input(args):
    excluded = set()
    provenance = {}
    for path in args.exclude:
        provenance[str(path.relative_to(ROOT.parent))] = sha(path)
        with path.open() as stream:
            excluded.update(row['machine'] for row in csv.DictReader(stream, delimiter='\t'))
    pool = {}
    sources = []
    for report_path, candidate_path in args.search:
        report = json.loads(report_path.read_text())
        if report['candidate_tsv_sha256'] != sha(candidate_path):
            raise ValueError(f'Search log differs from report: {candidate_path}')
        seen = set()
        with candidate_path.open() as stream:
            for raw in csv.DictReader(stream, delimiter='\t'):
                if raw['machine'] in seen:
                    raise ValueError('Duplicate machine within a search result')
                seen.add(raw['machine'])
                row = {k: raw[k] if k in ('machine', 'mode') else int(raw.get(k, 0)) for k in FIELDS}
                validate_row(row)
                if row['machine'] not in excluded:
                    pool.setdefault(row['machine'], row)
        sources.append({'report': str(report_path.relative_to(ROOT.parent)),
                        'report_sha256': sha(report_path),
                        'candidate_tsv_sha256': sha(candidate_path), 'candidate_rows': len(seen)})
    rows = sorted(pool.values(), key=machine_hash)
    if args.select:
        rows = rows[:args.select]
    if not rows:
        raise ValueError('Empty selected batch')
    data = {'selection': 'Lowest machine SHA256 hashes after excluding recorded proved IDs; first successful search source wins',
            'search_sources': sources, 'excluded_ledgers_sha256': provenance,
            'columns': FIELDS, 'selected_rows': len(rows), 'rows': [[r[k] for k in FIELDS] for r in rows]}
    prefix = json.dumps({k:v for k,v in data.items() if k != 'rows'}, indent=2)[:-2]
    args.input.write_text(prefix + ',\n  "rows": [\n    ' + ',\n    '.join(json.dumps(r) for r in data['rows']) + '\n  ]\n}\n')


def load_input(path):
    data = json.loads(path.read_text())
    if data.get('encoding') == 'zlib-base64':
        raw = zlib.decompress(base64.b64decode(data['data'], validate=True))
        if hashlib.sha256(raw).hexdigest() != data['uncompressed_sha256']:
            raise ValueError('Compressed closure input hash mismatch')
        data = json.loads(raw)
    if data['columns'] != FIELDS:
        raise ValueError('Wrong input columns')
    for source in data['search_sources']:
        report_path = ROOT.parent/source['report']
        if sha(report_path) != source['report_sha256']:
            raise ValueError('Selection search report changed')
        if json.loads(report_path.read_text())['candidate_tsv_sha256'] != source['candidate_tsv_sha256']:
            raise ValueError('Selection log hash differs from recorded report')
    excluded = set()
    for name, expected in data['excluded_ledgers_sha256'].items():
        path = ROOT.parent/name
        if sha(path) != expected:
            raise ValueError('Exclusion ledger changed')
        with path.open() as stream:
            excluded.update(row['machine'] for row in csv.DictReader(stream, delimiter='\t'))
    if any(not isinstance(row,list) or len(row) != len(FIELDS) for row in data['rows']):
        raise ValueError('Malformed compact row')
    rows = [dict(zip(FIELDS,row)) for row in data['rows']]
    if not rows or len(rows) != data['selected_rows'] or len({r['machine'] for r in rows}) != len(rows):
        raise ValueError('Empty/incomplete/duplicate batch')
    if rows != sorted(rows, key=machine_hash):
        raise ValueError('Batch hash ordering changed')
    for row in rows:
        validate_row(row)
        if row['machine'] in excluded:
            raise ValueError('Previously proved family in new batch')
    if len({r['bound'] for r in rows}) != 1:
        raise ValueError('Each batch uses one common bound')
    return data, rows


def certificate(row):
    n,t,f,e,k = (row[x] for x in ('size','anchor','fuel','extra','history'))
    return {'ng': f'ExistingStage (NGram {n} {t} {f} {e})',
            'rw': f'ExistingStage (RepeatedWord {n} {e} {t} {f})',
            'finite': f'Finite {n} {t} {f} {e}',
            'hist': f'History {k} {n} {t} {f} {e}'}[row['mode']]


def shard_source(rows):
    bound = rows[0]['bound']
    entries = ';\n'.join('  (['+';'.join(map(str,codes(r['machine'])))+'], '+certificate(r)+')' for r in rows)
    return f'''(** Generated by check_closure_wave.py; each table and certificate is checked. *)
From Coq Require Import List NArith.
From BBB24 Require Import Statement Spec Bounds Census Bootstrap Closeout
  CertifiedBoard Pipeline AdvancedPipeline.
Import ListNotations.
Definition rows : AdvancedBatch := [
{entries}].
Lemma checked : advanced_batch_check {bound}%N {bound}%N rows = true.
Proof. vm_compute. reflexivity. Qed.
Definition board := advanced_board rows.
Lemma small_sound : BoardSound {bound}%N {bound}%N board.
Proof. apply advanced_board_sound; exact checked. Qed.
Lemma nonhalt : forall family, In family board -> NonHalt family.
Proof. apply (advanced_board_nonhalt {bound}%N {bound}%N); exact checked. Qed.
Lemma sound : BoardSound scoreN scoreN board.
Proof.
  intros family Hin tm Hle.
  eapply (bounds_weaken {bound}%N {bound}%N scoreN scoreN tm).
  - vm_compute. discriminate.
  - vm_compute. discriminate.
  - exact (small_sound family Hin tm Hle).
Qed.
Lemma pending_checked : forallb (pending_check 9 empty bootstrap) board = true.
Proof. vm_compute. reflexivity. Qed.
Lemma was_pending : forall family, In family board -> bootstrap_pending family.
Proof.
  intros family Hin. apply pending_check_sound.
  pose proof pending_checked as H.
  apply forallb_forall with (x:=family) in H; assumption.
Qed.
'''


def forall_proof(modules, name):
    return '\n'.join(f'  apply Forall_cons; [exact {m}.{name}|].' for m in modules) + '\n  apply Forall_nil.'


def aggregate_source(modules, namespace, bound, count):
    boards = '; '.join(m+'.board' for m in modules)
    return f'''(** Generated by check_closure_wave.py. *)
From Coq Require Import List NArith.
From BBB24 Require Import Statement Spec Bounds Census Bootstrap Closeout CertifiedBoard CensusUnion.
From {namespace} Require Import {' '.join(modules)}.
Import ListNotations.
Definition boards : list (list TM) := [{boards}].
Definition board := concat boards.
Lemma small_sound : BoardSound {bound}%N {bound}%N board.
Proof. apply boards_sound. unfold boards.
{forall_proof(modules,'small_sound')}
Qed.
Lemma sound : BoardSound scoreN scoreN board.
Proof. apply boards_sound. unfold boards.
{forall_proof(modules,'sound')}
Qed.
Lemma nonhalt : forall family, In family board -> NonHalt family.
Proof.
  assert (H : Forall (fun b => forall family, In family b -> NonHalt family) boards).
  {{ unfold boards.
{forall_proof(modules,'nonhalt')}
  }}
  intros family Hin. apply in_concat in Hin as (b & Hb & Hin).
  apply Forall_forall with (x:=b) in H; [exact (H family Hin)|exact Hb].
Qed.
Lemma was_pending : forall family, In family board -> bootstrap_pending family.
Proof. apply boards_pending. unfold boards.
{forall_proof(modules,'was_pending')}
Qed.
Example count_checked : fold_left (fun n (_:TM) => N.succ n) board 0%N = {count}%N.
Proof. vm_compute. reflexivity. Qed.
Definition pending := remaining bootstrap_pending board.
Theorem coverage : forall tm, Bounds scoreN scoreN tm \\/ pending tm.
Proof. exact (closeout_coverage _ _ _ _ bootstrap_coverage sound). Qed.
Theorem discharged : forall family, In family board -> forall tm, TM_le family tm ->
  bootstrap_pending tm /\\ Bounds scoreN scoreN tm /\\ ~ pending tm.
Proof. exact (board_families_discharged _ _ _ _ _ was_pending sound). Qed.
Print Assumptions coverage.
Print Assumptions discharged.
'''


def run(command, log, timeout):
    start = time.monotonic()
    with log.open('w') as stream:
        subprocess.run(command, cwd=ROOT.parent, stdout=stream, stderr=subprocess.STDOUT,
                       timeout=timeout, check=True)
    return time.monotonic()-start


def compile_source(path, flags, dependencies, args):
    receipt, vo = path.with_suffix('.checked.json'), path.with_suffix('.vo')
    evidence = {'source_sha256': sha(path), 'dependencies_sha256': dependencies,
                'coq_version': subprocess.check_output(['coqc','--version'],text=True)}
    if args.resume and receipt.exists() and vo.exists():
        if json.loads(receipt.read_text()) == {**evidence, 'vo_sha256': sha(vo)}:
            print(f'Reused {path.stem}', flush=True)
            return
    elapsed = run(['coqc','-w','-abstract-large-number','-native-compiler','no',*flags,str(path)],
                  path.with_suffix('.log'),args.timeout)
    receipt.write_text(json.dumps({**evidence,'vo_sha256':sha(vo)},indent=2)+'\n')
    print(f'Checked {path.stem}: {elapsed:.2f}s',flush=True)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input',type=Path,default=ROOT/'research/closure-wave3-input.json')
    parser.add_argument('--build-dir',type=Path,default=ROOT/'build/closure-wave3')
    parser.add_argument('--report',type=Path,default=ROOT/'research/closure-wave3-summary.json')
    parser.add_argument('--ledger',type=Path,default=ROOT/'research/closure-wave3.tsv')
    parser.add_argument('--namespace',default='BBB24ClosureWave3')
    parser.add_argument('--select',type=int,help='Select this many rows; 0 selects all')
    parser.add_argument('--search',nargs=2,type=Path,action='append',default=[],metavar=('REPORT','CANDIDATES'))
    parser.add_argument('--exclude',type=Path,action='append',default=[])
    parser.add_argument('--refresh',action='store_true')
    parser.add_argument('--resume',action='store_true')
    parser.add_argument('--timeout',type=int,default=600)
    args=parser.parse_args()
    if not args.namespace.isidentifier() or (args.select is not None and args.select < 0):
        parser.error('Invalid namespace or selection size')
    for key in ('input','build_dir','report','ledger'):
        setattr(args,key,getattr(args,key).resolve())
    args.search=[(a.resolve(),b.resolve()) for a,b in args.search]
    args.exclude=[p.resolve() for p in args.exclude]
    args.build_dir.mkdir(parents=True,exist_ok=True)
    if args.select is not None:
        if not args.search:
            parser.error('--select requires --search')
        select_input(args)
    data,rows=load_input(args.input)
    theory_flags=['-Q',str(ROOT/'theories'),'BBB24']
    flags=theory_flags+['-Q',str(args.build_dir),args.namespace]
    roots=[ROOT/'theories'/f'{name}.v' for name in ('AdvancedPipeline','CertifiedBoard','CensusUnion','Bootstrap','Spec')]
    dependencies=dependency_hashes(roots,theory_flags)
    sources={**dependencies, 'tools/check_closure_wave.py':sha(Path(__file__)),
             'tools/generate_pipeline_examples.py':sha(ROOT/'tools/generate_pipeline_examples.py'),
             'tools/check_shadow_links.py':sha(ROOT/'tools/check_shadow_links.py')}
    input_hash=sha(args.input)
    if not(args.refresh or args.select is not None):
        old=json.loads(args.report.read_text())
        if old['input_sha256']!=input_hash or old['source_sha256']!=sources:
            raise ValueError('Input/source evidence changed; explicit refresh required')
    modules,paths=[],[]
    for start in range(0,len(rows),SHARD_SIZE):
        name=f'ClosureWave{start//SHARD_SIZE:04}'
        path=args.build_dir/f'{name}.v'
        path.write_text(shard_source(rows[start:start+SHARD_SIZE]))
        compile_source(path,flags,dependencies,args)
        modules.append(name);paths.append(path)
    path=args.build_dir/'ClosureWaveAll.v'
    path.write_text(aggregate_source(modules,args.namespace,rows[0]['bound'],len(rows)))
    compile_source(path,flags,dependencies,args);paths.append(path)
    module=args.namespace+'.ClosureWaveAll'
    audit=run(['coqchk','-silent','-bytecode-compiler','yes',*flags,module],args.build_dir/'coqchk.log',args.timeout*len(paths))
    if (sha(args.input)!=input_hash or dependency_hashes(roots,theory_flags)!=dependencies
            or any(sha(ROOT/name)!=expected for name,expected in sources.items())):
        raise ValueError('Proof inputs changed during audit')
    report={'scope':'Distinct selected family IDs; all completions covered; original census weights unchanged',
            'checked_families':len(rows),'census_linked_families':len(rows),'bound':rows[0]['bound'],
            'mode_counts':dict(sorted(Counter(r['mode'] for r in rows).items())),
            'board':module+'.board','small_sound':module+'.small_sound','nonhalt':module+'.nonhalt',
            'coverage_theorem':module+'.coverage','discharge_theorem':module+'.discharged',
            'input_sha256':input_hash,'source_sha256':sources,
            'generated_sha256':{p.name:sha(p) for p in paths},
            'validation':'VM computation of every certificate and pending membership, followed by recursive coqchk'}
    buffer=io.StringIO()
    writer=csv.DictWriter(buffer,FIELDS+['census_linked','bounds_theorem','census_theorem'],delimiter='\t',lineterminator='\n')
    writer.writeheader()
    writer.writerows({**row,'census_linked':'yes','bounds_theorem':report['small_sound'],
                     'census_theorem':report['discharge_theorem']} for row in rows)
    report['ledger_sha256']=hashlib.sha256(buffer.getvalue().encode()).hexdigest()
    outputs={args.report:json.dumps(report,indent=2)+'\n',args.ledger:buffer.getvalue()}
    for path,contents in outputs.items():
        if args.refresh or args.select is not None:
            path.write_text(contents)
        elif path.read_text()!=contents:
            raise ValueError('Audited output differs from recorded evidence')
    print(json.dumps({'checked':len(rows),'audit_seconds':round(audit,2),'mode_counts':report['mode_counts']}),flush=True)


if __name__=='__main__':
    main()
