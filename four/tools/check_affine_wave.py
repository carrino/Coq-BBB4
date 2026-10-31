"""Check a versioned affine certificate bundle with batch reflection.

Input certificates are untrusted. Each generated shard evaluates every affine
check and every original-census membership check. The aggregate proves both
bounds, non-halting, coverage and exclusion of all family completions from its
refined residual. Generated proof files and compile receipts stay under build/.
"""
import argparse
import base64
import csv
import hashlib
import io
import json
import re
import subprocess
import time
import zlib
from pathlib import Path

import generate_affine as generator
import generate_pipeline_examples as tables

ROOT = Path(__file__).resolve().parents[1]
BUILD = ROOT/'build/affine-wave/proofs'
SHARD_SIZE = 64


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def source_hashes():
    paths = {Path(__file__).resolve(), Path(generator.__file__).resolve(),
             Path(tables.__file__).resolve(), ROOT.parent/'tools/gen_irulesblkpfx_certs.py'}
    todo, seen = ['AffineWave', 'CertifiedBoard'], set()
    while todo:
        module = todo.pop()
        if module in seen:
            continue
        seen.add(module)
        path = ROOT/'theories'/Path(*module.split('.')).with_suffix('.v')
        paths.add(path)
        for prefix, names in re.findall(r'From\s+(BBB24[\w.]*)\s+Require\s+(?:Import|Export)\s+([\w\s]+)\.', path.read_text()):
            todo.extend('.'.join(prefix.split('.')[1:]+[name]) for name in names.split())
    return {str(p.relative_to(ROOT.parent)):sha(p) for p in sorted(paths)}


def load_bundle(path, destination):
    data = json.loads(path.read_text())
    if data.get('encoding') == 'zlib-base64':
        raw = zlib.decompress(base64.b64decode(data['data'], validate=True))
        if hashlib.sha256(raw).hexdigest() != data['uncompressed_sha256']:
            raise ValueError('Compressed input hash mismatch')
        data = json.loads(raw)
    for field in ('bound','cfuel','fuel'):
        if type(data[field]) is not int or not 1 <= data[field] <= 10000000:
            raise ValueError(f'Invalid checker budget: {field}')
    certificates = data['certificates']
    if not certificates or not isinstance(certificates, dict):
        raise ValueError('Empty/malformed certificate bundle')
    destination.mkdir(parents=True, exist_ok=True)
    paths = []
    for machine in sorted(certificates, key=lambda m:hashlib.sha256(m.encode()).digest()):
        tables.codes(machine)
        text = certificates[machine]
        if not isinstance(text,str) or text.splitlines().count('machine '+machine) != 1:
            raise ValueError(f'Certificate identity mismatch: {machine}')
        if any(line.split()[0] in {'nvar','mmrow','xmin','x0','tplrunmv'}
               for line in text.splitlines() if line.split()):
            raise ValueError(f'Multivariable certificate is unsupported: {machine}')
        p = destination/f'{machine}.cert'; p.write_text(text)
        c = generator.shared.parse_cert(p)
        if c.get('machine') != machine or c.get('type') != 'irules':
            raise ValueError(f'Invalid certificate header: {machine}')
        if c['tpl_state'] not in 'AB' or c['tpl_hsym'] not in range(4):
            raise ValueError(f'Invalid template carrier: {machine}')
        if not 0 <= c['anchor_step'] <= data['bound']:
            raise ValueError(f'Anchor exceeds bound: {machine}')
        paths.append(p)
    return data, paths


def shard(paths, bound, cfuel, fuel):
    definitions = ''.join(generator.emit(p).split('Lemma checked_',1)[0] for p in paths)
    entries = ';\n'.join(f'(tm_{generator.shared.cname(p.stem)},cert_{generator.shared.cname(p.stem)})' for p in paths)
    return generator.HEADER + 'From BBB24 Require Import Bootstrap Closeout AffineWave.\n' + definitions + f'''
Definition rows : AffineRows := [{entries}].
Lemma checked : affine_rows_check {bound}%N {bound}%N {cfuel} {fuel} rows = true.
Proof. vm_compute. reflexivity. Qed.
Definition board := affine_rows_board rows.
Lemma board_small_sound : BoardSound {bound}%N {bound}%N board.
Proof. eapply affine_rows_board_sound; exact checked. Qed.
Lemma board_nonhalt : forall family, In family board -> NonHalt family.
Proof. eapply affine_rows_board_nonhalt; exact checked. Qed.
Lemma board_sound : BoardSound scoreN scoreN board.
Proof.
  intros family Hin tm Hle.
  eapply (bounds_weaken {bound}%N {bound}%N scoreN scoreN tm).
  - vm_compute. discriminate.
  - vm_compute. discriminate.
  - exact (board_small_sound family Hin tm Hle).
Qed.
Lemma board_pending_checked : forallb (pending_check 9 empty bootstrap) board = true.
Proof. vm_compute. reflexivity. Qed.
Lemma board_pending : forall family, In family board -> bootstrap_pending family.
Proof. eapply affine_pending_sound; exact board_pending_checked. Qed.
Print Assumptions board_small_sound.
'''


def forall_proof(parts, theorem):
    return '\n'.join(f'  apply Forall_cons; [exact {p}.{theorem}|].' for p in parts)+'\n  apply Forall_nil.'


def aggregate(name, parts, bound, count):
    boards = ';\n'.join(p+'.board' for p in parts)
    return f'''(** Generated affine wave closeout. *)
From Coq Require Import List NArith.
From BBB24 Require Import Statement Spec Bounds Census Bootstrap Closeout CertifiedBoard AffineWave.
From BBB24AffineWave.{name} Require Import {' '.join(parts)}.
Import ListNotations.
Definition affine_wave_boards : list (list TM) := [{boards}].
Definition affine_wave_board := concat affine_wave_boards.
Lemma affine_wave_board_small_sound : BoardSound {bound}%N {bound}%N affine_wave_board.
Proof.
  apply affine_concat_sound.
{forall_proof(parts,'board_small_sound')}
Qed.
Lemma affine_wave_board_sound : BoardSound scoreN scoreN affine_wave_board.
Proof.
  apply affine_concat_sound.
{forall_proof(parts,'board_sound')}
Qed.
Lemma affine_wave_board_nonhalt : forall family,
  In family affine_wave_board -> NonHalt family.
Proof.
  apply affine_concat_all.
{forall_proof(parts,'board_nonhalt')}
Qed.
Lemma affine_wave_pending_checked :
  forallb (pending_check 9 empty bootstrap) affine_wave_board = true.
Proof.
  apply affine_concat_checks.
{forall_proof(parts,'board_pending_checked')}
Qed.
Lemma affine_wave_board_pending : forall family,
  In family affine_wave_board -> bootstrap_pending family.
Proof. apply affine_pending_sound. exact affine_wave_pending_checked. Qed.
Example affine_wave_count : length affine_wave_board = {count}.
Proof. vm_compute. reflexivity. Qed.
Definition bootstrap_affine_wave_pending := remaining bootstrap_pending affine_wave_board.
Theorem bootstrap_affine_wave_coverage : forall tm,
  Bounds scoreN scoreN tm \\/ bootstrap_affine_wave_pending tm.
Proof.
  exact (closeout_coverage _ _ _ _ bootstrap_coverage affine_wave_board_sound).
Qed.
Theorem affine_wave_families_discharged : forall family,
  In family affine_wave_board -> forall tm, TM_le family tm ->
  bootstrap_pending tm /\\ Bounds scoreN scoreN tm /\\ ~ bootstrap_affine_wave_pending tm.
Proof.
  exact (board_families_discharged _ _ _ _ _
    affine_wave_board_pending affine_wave_board_sound).
Qed.
Print Assumptions bootstrap_affine_wave_coverage.
Print Assumptions affine_wave_families_discharged.
'''


def run(command, log, timeout):
    start = time.monotonic()
    with log.open('w') as out:
        subprocess.run(command, cwd=ROOT.parent, stdout=out, stderr=subprocess.STDOUT,
                       check=True, timeout=timeout)
    return time.monotonic()-start


def compile_file(path, dependencies, timeout, resume):
    receipt = path.with_suffix('.checked.json'); vo = path.with_suffix('.vo')
    expected = {'source_sha256':sha(path), 'dependencies_sha256':
                {k:v for k,v in dependencies.items() if k.endswith('.v')}}
    if resume and receipt.exists() and vo.exists():
        if json.loads(receipt.read_text()) == {**expected,'vo_sha256':sha(vo)}:
            print(f'Reused {path.stem}',flush=True); return 0
    elapsed = run(['coqc','-w','-abstract-large-number','-native-compiler','no',
                   '-Q',str(ROOT/'theories'),'BBB24','-Q',str(BUILD),'BBB24AffineWave',str(path)],
                  path.with_suffix('.log'), timeout)
    receipt.write_text(json.dumps({**expected,'vo_sha256':sha(vo)},indent=2)+'\n')
    print(f'Checked {path.stem} ({elapsed:.2f}s)',flush=True)
    return elapsed


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input',type=Path,required=True)
    parser.add_argument('--name',required=True,help='Stable Coq submodule name')
    parser.add_argument('--report-prefix',type=Path,required=True)
    parser.add_argument('--refresh',action='store_true')
    parser.add_argument('--resume',action='store_true')
    parser.add_argument('--timeout',type=int,default=300)
    args = parser.parse_args()
    if not re.fullmatch(r'[A-Z][A-Za-z0-9_]*',args.name):
        raise ValueError('Invalid Coq submodule name')
    destination = BUILD/args.name; destination.mkdir(parents=True,exist_ok=True)
    input_hash = sha(args.input)
    data, paths = load_bundle(args.input,destination/'certs')
    sources = source_hashes()
    report_path = args.report_prefix.with_suffix('.json')
    ledger_path = args.report_prefix.with_suffix('.tsv')
    if not args.refresh:
        old = json.loads(report_path.read_text())
        if old['input_sha256'] != input_hash or old['source_sha256'] != sources:
            raise ValueError('Input/proof source hashes changed; use --refresh')
    parts, files, elapsed = [], [], 0
    for start in range(0,len(paths),SHARD_SIZE):
        part = f'Part{start//SHARD_SIZE:04}'
        path = destination/f'{part}.v'
        path.write_text(shard(paths[start:start+SHARD_SIZE],data['bound'],data['cfuel'],data['fuel']))
        elapsed += compile_file(path,sources,args.timeout,args.resume)
        parts.append(part);files.append(path)
    all_path = destination/'All.v'
    all_path.write_text(aggregate(args.name,parts,data['bound'],len(paths)))
    elapsed += compile_file(all_path,sources,args.timeout,args.resume);files.append(all_path)
    audit = run(['coqchk','-silent','-bytecode-compiler','yes','-Q',str(ROOT/'theories'),'BBB24',
                 '-Q',str(BUILD),'BBB24AffineWave',f'BBB24AffineWave.{args.name}.All'],
                destination/'coqchk.log',args.timeout*len(files))
    if sha(args.input)!=input_hash or source_hashes()!=sources:
        raise ValueError('Input/proof sources changed during checking')
    module = f'BBB24AffineWave.{args.name}.All'
    report = {
        'scope':'Checked affine families from a declared search wave; no raw-table weight recomputation',
        'coq_version':subprocess.check_output(['coqc','--version'],text=True).splitlines()[0],
        'input_sha256':input_hash,'provenance':data.get('provenance',{}),
        'checked_families':len(paths),'census_linked_families':len(paths),
        'parameters':{k:data[k] for k in ('bound','cfuel','fuel')},
        'module':module,'board':module+'.affine_wave_board',
        'coverage_theorem':module+'.bootstrap_affine_wave_coverage',
        'discharge_theorem':module+'.affine_wave_families_discharged',
        'source_sha256':sources,'shard_sha256':{p.name:sha(p) for p in files},
        'validation':'Batch VM proofs of affine checks and original pending membership; recursive coqchk',
    }
    buffer=io.StringIO(newline='')
    writer=csv.DictWriter(buffer,fieldnames=['machine','proof_index','certificate_sha256','status',
        'state_bound','instruction_bound','census_linked','theorem'],delimiter='\t',lineterminator='\n')
    writer.writeheader()
    writer.writerows({'machine':p.stem,'proof_index':i,'certificate_sha256':sha(p),'status':'coq_checked',
        'state_bound':data['bound'],'instruction_bound':data['bound'],'census_linked':'yes',
        'theorem':report['discharge_theorem']} for i,p in enumerate(paths))
    serialized=json.dumps(report,indent=2)+'\n'
    if args.refresh:
        report_path.write_text(serialized);ledger_path.write_text(buffer.getvalue())
    elif report_path.read_text()!=serialized or ledger_path.read_text()!=buffer.getvalue():
        raise ValueError('Recorded report/ledger differs from checked result')
    print(json.dumps({'checked':len(paths),'census_linked':len(paths),
                      'compile_seconds':round(elapsed,2),'audit_seconds':round(audit,2)}))


if __name__=='__main__':
    main()
