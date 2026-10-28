"""Reuse checked proof boards across the frozen survey's relabelings and shadows.

Source descriptors name Coq boards with nonhalting and both-bound theorems; the
JSON machine lists only select witnesses. Every selected image, prefix link,
and frozen-census membership is replayed in Coq. Reports are replaced only after
recursive coqchk. Generated sources remain under ignored build/family-transport.

Run the source-board reproduction commands first, then this tool with Coq on
PATH. Default mode verifies the existing report; --refresh records a new audited
checkpoint. Add independently checked sources in research/transport-sources.json.
`--select --refresh` regenerates the compact selected rows from the full ignored
survey. Default replay needs only tracked inputs and built source proof boards.
"""
import argparse
import csv
import hashlib
import io
import json
import re
import subprocess
import time
from pathlib import Path

import group_families as grouping
from generate_pipeline_examples import codes
from check_shadow_links import table, command, sha, dependency_hashes

ROOT = Path(__file__).resolve().parents[1]
BUILD = ROOT/'build/family-transport'
CONFIG = ROOT/'research/transport-sources.json'
INPUT = ROOT/'research/family-transport-input.json'
LEDGER = ROOT/'research/family-transport.tsv'
REPORT = ROOT/'research/family-transport-summary.json'
SHARD_SIZE = 128


def load_sources():
    config = json.loads(CONFIG.read_text())
    machines = []
    inputs = {str(CONFIG.relative_to(ROOT)): sha(CONFIG)}
    for source in config['sources']:
        for key in ('module', 'board', 'nonhalt', 'small_sound'):
            if not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9.]*', source[key]):
                raise ValueError(f'Invalid Coq identifier: {source[key]}')
        for entry in source['machine_inputs']:
            path = ROOT/entry['path']; inputs[entry['path']] = sha(path)
            if entry['format'] == 'checked_affine_tsv':
                with path.open() as f:
                    new = [r['machine'] for r in csv.DictReader(f, delimiter='\t')
                           if r['status'] == 'coq_checked']
            elif entry['format'] == 'json_rows':
                new = [r['machine'] for r in json.loads(path.read_text())['rows']]
            elif entry['format'] == 'json_columns':
                data = json.loads(path.read_text())
                columns = data['columns']
                if len(columns)!=len(set(columns)) or 'machine' not in columns:
                    raise ValueError('Malformed column-based source inventory')
                if any(len(row)!=len(columns) for row in data['rows']):
                    raise ValueError('Source row has the wrong number of columns')
                new = [row[columns.index('machine')] for row in data['rows']]
            else:
                raise ValueError('Unknown source inventory format')
            for machine in new:
                codes(machine)
            machines.extend(new)
        path = ROOT/source['proof_source']
        if not path.with_suffix('.vo').exists():
            raise ValueError(f'Build the source proof board first: {path}')
        inputs[source['proof_source']] = sha(path)
    return config, machines, inputs


def choices(machines):
    result = {}
    for index, machine in enumerate(machines):
        for perm in grouping.PERMS:
            for mirrored in (False, True):
                image = grouping.render(grouping.rename(grouping.parse(machine), perm,
                                                       mirror=mirrored))
                result.setdefault(image, (index, 'P'+''.join(map(str, perm[1:])),
                                          str(mirrored).lower()))
    return result


def select(machines):
    baseline = json.loads((ROOT/'research/burndown-summary.json').read_text())
    survey = set()
    for name in ('blank', 'nonblank'):
        path = ROOT/f'build/triage/{name}.unresolved.txt'
        if sha(path) != baseline['roots'][name]['inventory_sha256']:
            raise ValueError(f'Survey input hash changed: {name}')
        survey.update(path.read_text().splitlines())
    images = choices(machines)
    image_rows = [(m, *images[m]) for m in sorted(survey & images.keys())]
    with (ROOT/'research/shadow-links.tsv').open() as f:
        links = list(csv.DictReader(f, delimiter='\t'))
    matched = [r for r in links if r['core'] in images]
    ready = [(r['machine'], *images[r['core']], r['permutation'], r['mirrored'])
             for r in matched if r['machine'] not in images]
    shadow_images = choices([r[0] for r in ready])
    shadow_rows = [(m, *shadow_images[m]) for m in sorted((survey & shadow_images.keys())-images.keys())]
    return dict(
        description='Untrusted transport witnesses selected from the frozen survey; every relation and pending membership is checked in Coq.',
        source_inventory_sha256=hashlib.sha256(('\n'.join(machines)+'\n').encode()).hexdigest(),
        survey_input_sha256={label:baseline['roots'][label]['inventory_sha256']
                             for label in ('blank','nonblank')},
        images=image_rows, ready_shadows=ready, shadow_images=shadow_rows)


def compact_input(data):
    parts = []
    for key, value in data.items():
        if key in {'images','ready_shadows','shadow_images'}:
            text = '[\n'+',\n'.join('    '+json.dumps(row,separators=(',',':')) for row in value)+'\n  ]'
        else:
            text = json.dumps(value, sort_keys=True)
        parts.append('  '+json.dumps(key)+': '+text)
    return '{\n'+',\n'.join(parts)+'\n}\n'


def validate_input(data, machines):
    expected = hashlib.sha256(('\n'.join(machines)+'\n').encode()).hexdigest()
    if data['source_inventory_sha256'] != expected:
        raise ValueError('Ordered proof-source inventory differs; regenerate selection explicitly')
    baseline = json.loads((ROOT/'research/burndown-summary.json').read_text())
    if data['survey_input_sha256'] != {label:baseline['roots'][label]['inventory_sha256']
                                      for label in ('blank','nonblank')}:
        raise ValueError('Selected rows refer to a different frozen survey')
    perms = {'P'+''.join(map(str,p[1:])) for p in grouping.PERMS}
    images, ready, shadows = (data[key] for key in ('images','ready_shadows','shadow_images'))
    for rows, length, bound in ((images,4,len(machines)), (ready,6,len(machines)),
                               (shadows,4,len(ready))):
        for row in rows:
            if len(row)!=length:
                raise ValueError('Malformed transport witness')
            codes(row[0])
            if type(row[1]) is not int or not 0<=row[1]<bound:
                raise ValueError('Source index out of range')
            for p,mirror in zip(row[2::2],row[3::2]):
                if p not in perms or mirror not in {'true','false'}:
                    raise ValueError('Invalid permutation/reflection witness')
        if len({row[0] for row in rows}) != len(rows):
            raise ValueError('Duplicate transported family')
    if {r[0] for r in images}&{r[0] for r in shadows}:
        raise ValueError('Symmetry and new-shadow inventories overlap')
    with (ROOT/'research/shadow-links.tsv').open() as f:
        links = list(csv.DictReader(f,delimiter='\t'))
    available = choices(machines)
    matched = [r for r in links if r['core'] in available]
    expected_ready = {r['machine'] for r in matched if r['machine'] not in available}
    if {r[0] for r in ready} != expected_ready:
        raise ValueError('Ready-shadow inventory differs from proved-core matches')
    return images, ready, shadows, matched


HEADER = '''(** GENERATED by four/tools/check_family_transport.py. *)
From Coq Require Import List NArith.
From BBB24 Require Import Statement Spec Bounds Census Bootstrap Closeout
  Symmetry Shadow Pipeline FamilyTransport.
Import ListNotations.
'''


def source_module(config, source_count):
    imports = '\n'.join('Require Import '+s['module']+'.' for s in config['sources'])
    boards = [s['module']+'.'+s['board'] for s in config['sources']]
    board = ' ++ '.join(boards)
    proofs = []
    for index, source in enumerate(config['sources']):
        prefix = source['module']+'.'
        proofs.append(f'''Lemma source_{index}_strong : StrongBoard 4096%N 4096%N {boards[index]}.
Proof.
  intros tm Hin. split.
  - exact ({prefix+source['nonhalt']} tm Hin).
  - apply ({prefix+source['small_sound']} tm Hin tm).
    intros q s; right; reflexivity.
Qed.''')
    proof = f'source_{len(boards)-1}_strong'
    for index in reversed(range(len(boards)-1)):
        proof = f'(strong_board_app _ _ _ _ source_{index}_strong {proof})'
    text = HEADER+imports+'\n'+'\n'.join(proofs)+f'''
Definition source_board : list TM := {board}.
Lemma source_board_strong : StrongBoard 4096%N 4096%N source_board.
Proof. exact {proof}. Qed.
Example source_board_count : length source_board={source_count}.
Proof. vm_compute. reflexivity. Qed.
'''
    path = BUILD/'SourceBoards.v'; path.write_text(text); return path


def image_entries(rows):
    return ';\n'.join(f'  image_row {table(m)} {index} {p} {mirrored}'
                      for m,index,p,mirrored in rows)


def image_shards(rows, source, source_sound, bound, stem):
    paths = []
    for offset in range(0, len(rows), SHARD_SIZE):
        chunk = rows[offset:offset+SHARD_SIZE]
        path = BUILD/f'{stem}{offset//SHARD_SIZE:03}.v'
        text = HEADER+'From BBB24Transport Require Import SourceBoards ReadyShadows.\n'+f'''
Definition rows : list ImageRow := [
{image_entries(chunk)}
].
Lemma rows_checked : forallb (image_row_check {source}) rows=true.
Proof. vm_compute. reflexivity. Qed.
Definition board := map image_row_tm rows.
Lemma board_strong : StrongBoard {bound}%N {bound}%N board.
Proof. exact (image_batch_sound _ _ _ _ {source_sound} rows_checked). Qed.
Lemma pending_checked : forallb (pending_check 9 empty bootstrap) board=true.
Proof. vm_compute. reflexivity. Qed.
'''
        path.write_text(text); paths.append(path)
    return paths


def ready_module(rows):
    body = ';\n'.join(f'  ready_shadow {table(m)} {i} {p} {mirror} {sp} {sm}'
                      for m,i,p,mirror,sp,sm in rows)
    path = BUILD/'ReadyShadows.v'
    path.write_text(HEADER+'From BBB24Transport Require Import SourceBoards.\n'+f'''
Definition rows : list ReadyShadow := [
{body}
].
Lemma rows_checked : forallb (ready_check source_board) rows=true.
Proof. vm_compute. reflexivity. Qed.
Definition ready_board := map ready_tm rows.
Lemma ready_board_strong : StrongBoard 4097%N 4097%N ready_board.
Proof. exact (ready_shadows_sound _ _ _ _ source_board_strong rows_checked). Qed.
''')
    return path


def aggregate(images, shadows, family_count):
    paths = images+shadows
    imports = ' '.join(p.stem for p in paths)
    boards = ' ++ '.join(p.stem+'.board' for p in paths) or '[]'
    sound = []
    for p in images:
        sound.append(f'''  - eapply (strong_board_weaken 4096%N 4096%N 4097%N 4097%N).
    + vm_compute. discriminate.
    + vm_compute. discriminate.
    + exact {p.stem}.board_strong.''')
    sound += [f'  - exact {p.stem}.board_strong.' for p in shadows]
    pending = '\n'.join('  rewrite '+p.stem+'.pending_checked.' for p in paths)
    path = BUILD/'FamilyTransportCloseout.v'
    path.write_text(HEADER+f'From BBB24Transport Require Import {imports}.\n'+f'''
Definition transport_board : list TM := {boards}.
Example transport_board_count : length transport_board={family_count}.
Proof. vm_compute. reflexivity. Qed.
Lemma transport_board_strong : StrongBoard 4097%N 4097%N transport_board.
Proof.
  unfold transport_board. repeat apply strong_board_app.
{chr(10).join(sound)}
Qed.
Lemma transport_board_small_sound : BoardSound 4097%N 4097%N transport_board.
Proof. apply strong_board_completions, transport_board_strong. Qed.
Lemma transport_board_nonhalt : forall family, In family transport_board -> NonHalt family.
Proof. intros family H. exact (proj1 (transport_board_strong family H)). Qed.
Lemma transport_board_sound : BoardSound scoreN scoreN transport_board.
Proof.
  intros family Hin tm Hle.
  eapply (bounds_weaken 4097%N 4097%N scoreN scoreN).
  - vm_compute. discriminate.
  - vm_compute. discriminate.
  - exact (transport_board_small_sound family Hin tm Hle).
Qed.
Lemma transport_pending_checked : forallb (pending_check 9 empty bootstrap) transport_board=true.
Proof.
  unfold transport_board. repeat rewrite forallb_app.
{pending}
  reflexivity.
Qed.
Lemma transport_board_was_pending : forall family,
  In family transport_board -> bootstrap_pending family.
Proof.
  intros family Hin. apply pending_check_sound.
  pose proof transport_pending_checked as H.
  apply forallb_forall with (x:=family) in H; assumption.
Qed.
Definition bootstrap_transport_pending := remaining bootstrap_pending transport_board.
Theorem bootstrap_transport_coverage : forall tm,
  Bounds scoreN scoreN tm \\/ bootstrap_transport_pending tm.
Proof. exact (closeout_coverage _ _ _ _ bootstrap_coverage transport_board_sound). Qed.
Theorem transport_families_discharged : forall family,
  In family transport_board -> forall tm, TM_le family tm ->
  bootstrap_pending tm /\\ Bounds scoreN scoreN tm /\\ ~ bootstrap_transport_pending tm.
Proof.
  intros family Hin tm Hle. split.
  - assert (Hp : bootstrap_pending family).
    {{ apply pending_check_sound. pose proof transport_pending_checked as H.
      apply forallb_forall with (x:=family) in H; assumption. }}
    destruct Hp as (leaf & Hleaf & Hlf). exists leaf. split; [exact Hleaf|].
    eapply BBB24.AffineCloseout.closeout_tm_le_trans; eauto.
  - split; [exact (transport_board_sound family Hin tm Hle)|].
    intros [_ Hremaining].
    assert (Hhit : board_check transport_board tm=true).
    {{ apply existsb_exists. exists family; split; [exact Hin|].
      apply table_leb_spec. exact Hle. }}
    congruence.
Qed.
Print Assumptions transport_families_discharged.
''')
    return path


def source_hashes(config, inputs):
    paths = [Path(__file__).resolve(), ROOT/'tools/group_families.py',
             ROOT/'tools/check_shadow_links.py', ROOT/'tools/generate_pipeline_examples.py']
    # The full conditional-link report is independent evidence. This batch
    # checks its selected links again, so it depends on their input TSV only.
    paths += [ROOT/'research/shadow-links.tsv', ROOT/'research/burndown-summary.json']
    roots = [ROOT/'theories/FamilyTransport.v']
    roots += [ROOT/s['proof_source'] for s in config['sources']]
    loadpath = ['-Q', str(ROOT/'theories'), 'BBB24']
    for path, namespace in config['loadpaths']:
        loadpath += ['-Q', str(ROOT/path), namespace]
    local = dependency_hashes(roots, loadpath)
    return {**inputs, **local, **{str(p.relative_to(ROOT)):sha(p) for p in paths}}


def ledger(images, ready, shadows, machines):
    rows = []
    for m,i,p,mirrored in images:
        rows.append(dict(machine=m, route='symbol_reflection', source=machines[i],
                         permutation=p, mirrored=mirrored, state_bound=4096,
                         instruction_bound=4096, census_linked='yes'))
    for m,i,p,mirrored in shadows:
        rows.append(dict(machine=m, route='blank_prefix_then_symbols', source=ready[i][0],
                         permutation=p, mirrored=mirrored, state_bound=4097,
                         instruction_bound=4097, census_linked='yes'))
    if len({r['machine'] for r in rows}) != len(rows):
        raise ValueError('Duplicate transported family')
    out = io.StringIO()
    writer = csv.DictWriter(out, list(rows[0]), delimiter='\t', lineterminator='\n')
    writer.writeheader(); writer.writerows(sorted(rows, key=lambda r:r['machine']))
    return out.getvalue()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--refresh', action='store_true')
    parser.add_argument('--select', action='store_true',
                        help='Regenerate compact witnesses from ignored survey files; requires --refresh')
    parser.add_argument('--timeout', type=int, default=600)
    args = parser.parse_args()
    if args.select and not args.refresh:
        raise ValueError('--select requires --refresh; publish only after checking')
    config, machines, inputs = load_sources()
    data = select(machines) if args.select else json.loads(INPUT.read_text())
    images, ready, shadows, matched = validate_input(data,machines)
    frozen_input = compact_input(data)
    pinned = source_hashes(config, inputs)
    if not args.refresh and json.loads(REPORT.read_text())['source_sha256'] != pinned:
        raise ValueError('Proof inputs changed; refresh and recheck')
    BUILD.mkdir(parents=True, exist_ok=True)
    source = source_module(config,len(machines)); ready_path = ready_module(ready)
    image_paths = image_shards(images, 'source_board', 'source_board_strong', 4096, 'ImageFamilies')
    shadow_paths = image_shards(shadows, 'ready_board', 'ready_board_strong', 4097, 'ShadowFamilies')
    closeout = aggregate(image_paths, shadow_paths, len(images)+len(shadows))
    paths = [source, ready_path, *image_paths, *shadow_paths, closeout]
    loadpath = ['-Q', str(ROOT/'theories'), 'BBB24', '-Q', str(BUILD), 'BBB24Transport']
    for path, namespace in config['loadpaths']:
        loadpath += ['-Q', str(ROOT/path), namespace]
    start = time.monotonic()
    for path in paths:
        command(['coqc', '-native-compiler', 'no', *loadpath, str(path)], path.with_suffix('.log'), args.timeout)
        print(f'Checked {path.stem}', flush=True)
    command(['coqchk', '-silent', '-bytecode-compiler', 'yes', *loadpath,
             'BBB24Transport.FamilyTransportCloseout'], BUILD/'coqchk.log', args.timeout*len(paths))
    if pinned != source_hashes(config, load_sources()[2]):
        raise ValueError('Proof inputs changed during audit')
    all_families = {r[0] for r in images+shadows}
    report = dict(
        scope='Exact symbol/reflection images in the frozen survey, then proved-core blank-prefix shadows and their images',
        coq_version=subprocess.check_output(['coqc','--version'],text=True).splitlines()[0],
        input_sha256=hashlib.sha256(frozen_input.encode()).hexdigest(),
        counts=dict(source_entries=len(machines), distinct_sources=len(set(machines)),
                    symmetry_families=len(images), additional_symmetry_families=len({r[0] for r in images}-set(machines)),
                    conditional_links_with_proved_core=len(matched), new_shadow_representatives=len(ready),
                    additional_shadow_families=len(shadows), census_linked_families=len(all_families),
                    newly_linked_beyond_sources=len(all_families-set(machines))),
        state_bounds=[4096,4097], instruction_bounds=[4096,4097],
        validation='coqc vm_compute checks and recursive coqchk; all completions bounded, frozen-census membership checked',
        coverage_theorem='BBB24Transport.FamilyTransportCloseout.bootstrap_transport_coverage',
        discharge_theorem='BBB24Transport.FamilyTransportCloseout.transport_families_discharged',
        residual_predicate='BBB24Transport.FamilyTransportCloseout.bootstrap_transport_pending',
        structural_accounting='Original bootstrap weights unchanged; family counts are distinct survey identifiers, not disjoint raw-table weights',
        source_sha256=pinned, generated_sha256={p.name:sha(p) for p in paths})
    rendered = json.dumps(report, indent=2)+'\n'
    inventory = ledger(images, ready, shadows, machines)
    if args.refresh:
        INPUT.write_text(frozen_input); REPORT.write_text(rendered); LEDGER.write_text(inventory)
    elif INPUT.read_text()!=frozen_input or REPORT.read_text()!=rendered or LEDGER.read_text()!=inventory:
        raise ValueError('Checked transport evidence differs from recorded report')
    print(json.dumps(dict(counts=report['counts'], checking_seconds=round(time.monotonic()-start,2))))


if __name__ == '__main__':
    main()
