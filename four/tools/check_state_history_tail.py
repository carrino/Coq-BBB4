"""Replay supplied history certificates for the exact suffix of a state board.

The prefix descriptor pins the original full input. Bounded compressed bundles
must match every suffix row, in order, with no gap or duplication. Default replay
needs only those tracked inputs; native search is used only with --select.
"""
import argparse
import base64
import csv
import hashlib
import io
import json
from pathlib import Path
import subprocess
from types import SimpleNamespace
import zlib

import check_state_pipeline_batch as base
import check_state_pipeline_prefix as prefix
import state_work_assignment as assignment
from check_shadow_links import dependency_hashes

ROOT = base.ROOT
BUNDLE_ROWS = 64


def expected(prefix_input):
    desc, full, selected, tail = prefix.load(SimpleNamespace(input=prefix_input))
    bundles = []
    for shard in tail:
        if shard['certificate']['mode'] != 'hist':
            raise ValueError('Supplied history tail contains a non-history stage')
        for offset in range(0, len(shard['rows']), BUNDLE_ROWS):
            bundles.append({'stage': shard['stage'], 'certificate': shard['certificate'],
                            'rows': shard['rows'][offset:offset+BUNDLE_ROWS]})
    if sum(len(b['rows']) for b in bundles)+desc['selected_rows'] != full['selected_rows']:
        raise ValueError('Prefix and tail do not partition the complete original inventory')
    return desc, full, bundles


def partition(prefix_input, assignment_input, preserved):
    desc, full, groups = expected(prefix_input)
    _, checked, queued = assignment.load(assignment_input)
    if type(preserved) is not int or not 0 <= preserved <= len(groups):
        raise ValueError('Invalid preserved-export prefix')
    retained, deferred = [], []
    for i, group in enumerate(groups):
        rows = []
        for row in group['rows']:
            status = assignment.classify(base.unpack(row), checked, queued)
            if i < preserved or status == 'unassigned':
                rows.append(row)
            else:
                deferred.append((row, status))
        if rows:
            retained.append({**group, 'rows': rows, 'original_chunk': i})
    if desc['selected_rows']+sum(len(g['rows']) for g in retained)+len(deferred) != full['selected_rows']:
        raise ValueError('Prefix, supplied, and deferred assignments do not partition the full input')
    return desc, full, retained, deferred


def encode_cells(cells, radix):
    return sum(v*radix**i for i, v in enumerate(cells))


def packed_row(data, cert):
    k, n = cert['history'], cert['size']
    radix = 4*sum(8**j for j in range(k+1))
    def cells(xs):
        if len(xs) != n or any(type(x) is not int or not 0 <= x < radix for x in xs):
            raise ValueError('Native producer emitted an invalid fixed-width window')
        return encode_cells(xs, radix)
    nodes = []
    for q, left, head, right in data['nodes']:
        if q not in (0, 1) or not 0 <= head < radix:
            raise ValueError('Invalid native node')
        cells(left); cells(right)
        nodes.append(q+2*encode_cells(left+[head]+right, radix))
    return [base.pack(data['machine']), nodes, [cells(x) for x in data['ls']],
            [cells(x) for x in data['rs']], data['ca'], data['cb']]


def payload(bundle):
    raw = zlib.decompress(base64.b64decode(''.join(bundle['zlib_base64']), validate=True))
    if hashlib.sha256(raw).hexdigest() != bundle['payload_sha256']:
        raise ValueError('Supplied certificate payload digest differs')
    rows = json.loads(raw)
    if not isinstance(rows, list) or len(rows) != bundle['row_count']:
        raise ValueError('Supplied certificate bundle row count differs')
    return rows


def build_exporter(args):
    work = args.output_dir/'producer'
    work.mkdir(parents=True, exist_ok=True)
    extraction = work/'ExtractHistoryCertificate.v'
    extraction.write_text('From Coq Require Import Extraction ExtrOcamlBasic ExtrOcamlNatInt.\n'
                          'From BBB24 Require Import StatePipeline.\n'
                          f'Extraction "{work.resolve()}/checkers.ml" stp_check.\n')
    commands = [
        ['coqc', '-native-compiler', 'no', '-Q', str(ROOT/'theories'), 'BBB24', str(extraction)],
        ['ocamlopt', '-w', '-a', '-I', str(work), '-c', str(work/'checkers.mli')],
        ['ocamlopt', '-w', '-a', '-I', str(work), '-c', str(work/'checkers.ml')],
        ['ocamlopt', '-w', '-a', '-I', str(work), '-c', '-o', str(work/'export.cmx'),
         str(ROOT/'tools/state_history_certificate_export.ml')],
        ['ocamlopt', '-w', '-a', '-I', str(work), 'unix.cmxa', str(work/'checkers.cmx'),
         str(work/'export.cmx'), '-o', str(work/'export')],
    ]
    for command in commands:
        subprocess.run(command, cwd=ROOT.parent, check=True)
    return work/'export'


def select(args):
    if not args.refresh or args.prefix_input is None or args.bundle_dir is None or args.assignment_input is None:
        raise ValueError('--select requires --refresh, --prefix-input, --assignment-input, and --bundle-dir')
    desc, full, groups, deferred = partition(args.prefix_input, args.assignment_input, args.preserve_exported_chunks)
    args.bundle_dir.mkdir(parents=True, exist_ok=True)
    args.output_dir.mkdir(parents=True, exist_ok=True)
    exporter = build_exporter(args)
    manifest = []
    for i, group in enumerate(groups):
        cert = group['certificate']
        original_chunk = group['original_chunk']
        path = args.bundle_dir/f'bundle{original_chunk:03}.json'
        if args.resume and path.exists():
            old = json.loads(path.read_text())
            rows = payload(old)
            if (old['stage'] != group['stage'] or old['certificate'] != cert
                    or [r[0] for r in rows] != group['rows']):
                raise ValueError('Existing supplied bundle differs from the exact tail assignment')
        else:
            machine_path = args.output_dir/'producer/machines.txt'
            machine_path.write_text(''.join(base.unpack(x)+'\n' for x in group['rows']))
            result = subprocess.run([str(exporter), str(cert['history']), str(cert['size']),
                                     str(cert['anchor']), str(cert['fuel']), str(cert['extra']),
                                     str(machine_path)], check=True, capture_output=True, text=True)
            rows = [packed_row(json.loads(line), cert) for line in result.stdout.splitlines()]
            if [r[0] for r in rows] != group['rows']:
                raise ValueError('Producer omitted, duplicated, or reordered a family')
            raw = json.dumps(rows, separators=(',', ':')).encode()
            encoded = base64.b64encode(zlib.compress(raw, 9)).decode()
            bundle = {'encoding': 'zlib-base64 canonical JSON; packed machine, nodes, left, right, A/B ranks',
                      'stage': group['stage'], 'certificate': cert, 'row_count': len(rows),
                      'payload_sha256': hashlib.sha256(raw).hexdigest(),
                      'zlib_base64': [encoded[j:j+4096] for j in range(0, len(encoded), 4096)]}
            path.write_text(json.dumps(bundle, indent=2)+'\n')
        manifest.append({'file': prefix.relative(path), 'sha256': base.sha(path), 'original_chunk': original_chunk,
                         'stage': group['stage'], 'rows': len(group['rows'])})
        print(f'Prepared certificate bundle {i}: {len(group["rows"])} rows', flush=True)
    data = {'scope': 'Exact state-only history suffix; supplied certificates still require kernel replay.',
            'prefix_input': prefix.relative(args.prefix_input), 'prefix_input_sha256': base.sha(args.prefix_input),
            'assignment_input': prefix.relative(args.assignment_input), 'assignment_input_sha256': base.sha(args.assignment_input),
            'preserved_exported_chunks': args.preserve_exported_chunks,
            'supplied_rows': sum(len(g['rows']) for g in groups),
            'deferred_checked_both': sum(status == 'checked_both' for _, status in deferred),
            'deferred_queued_both': sum(status == 'queued_both' for _, status in deferred),
            'full_input': desc['full_input'], 'full_input_sha256': desc['full_input_sha256'],
            'full_candidate_rows': full['selected_rows'], 'prefix_rows': desc['selected_rows'],
            'tail_rows': full['selected_rows']-desc['selected_rows'],
            'state_bound': full['state_bound'], 'instruction_bound': None,
            'bundle_rows': BUNDLE_ROWS, 'bundles': manifest}
    args.input.parent.mkdir(parents=True, exist_ok=True)
    args.input.write_text(json.dumps(data, indent=2)+'\n')


def load(args):
    data = json.loads(args.input.read_text())
    p = ROOT/data['prefix_input']
    if base.sha(p) != data['prefix_input_sha256']:
        raise ValueError('Original completed-prefix assignment changed')
    assignment_input = ROOT/data['assignment_input']
    if base.sha(assignment_input) != data['assignment_input_sha256']:
        raise ValueError('BOTH assignment snapshot changed')
    desc, full, groups, deferred = partition(p, assignment_input, data['preserved_exported_chunks'])
    if (data['full_input'] != desc['full_input'] or data['full_input_sha256'] != desc['full_input_sha256']
            or data['full_candidate_rows'] != full['selected_rows'] or data['prefix_rows'] != desc['selected_rows']
            or data['tail_rows'] != full['selected_rows']-desc['selected_rows']
            or data['state_bound'] != full['state_bound'] or data['instruction_bound'] is not None
            or data['bundle_rows'] != BUNDLE_ROWS or len(data['bundles']) != len(groups)
            or data['supplied_rows'] != sum(len(g['rows']) for g in groups)
            or data['deferred_checked_both'] != sum(status == 'checked_both' for _, status in deferred)
            or data['deferred_queued_both'] != sum(status == 'queued_both' for _, status in deferred)):
        raise ValueError('Supplied tail inventory does not partition the original full input')
    loaded = []
    for item, group in zip(data['bundles'], groups):
        path = ROOT/item['file']
        if base.sha(path) != item['sha256']:
            raise ValueError('Supplied compact bundle changed')
        bundle = json.loads(path.read_text())
        rows = payload(bundle)
        if (item['original_chunk'] != group['original_chunk'] or item['stage'] != group['stage'] or item['rows'] != len(group['rows'])
                or bundle['stage'] != group['stage'] or bundle['certificate'] != group['certificate']
                or [r[0] for r in rows] != group['rows']):
            raise ValueError('Supplied bundle IDs/certificate differ from the exact original suffix')
        loaded.append((group, rows))
    return data, loaded, deferred


def nlist(xs):
    if any(type(x) is not int or x < 0 for x in xs):
        raise ValueError('Expected binary natural literal')
    return '['+';'.join(f'{x}%N' for x in xs)+']'


def phi(xs):
    if any(type(i) is not int or type(r) is not int or i < 0 or r < 0 for i, r in xs):
        raise ValueError('Expected natural node indices and ranks')
    return '['+';'.join(f'({i}%N,{r}%N)' for i, r in xs)+']'


def component(c):
    if c[0] == 0 and len(c) == 2:
        return '(ShRank '+phi(c[1])+')'
    if c[0] != 1 or len(c) != 6:
        raise ValueError('Invalid supplied rank component')
    _, measure, kind, constant, ranks, gate = c
    if type(measure) is not int or not 0 <= measure < 3 or type(kind) is not int or not 0 <= kind < 4:
        raise ValueError('Invalid supplied measure')
    if type(constant) is not int or constant < 0:
        raise ValueError('Invalid measure constant')
    measure = ['MAll', 'MLeft', 'MRight'][measure]+' '+['C1', 'C2', 'C3', 'CN'][kind]
    return f'(ShMeas ({measure}) {constant}%N {phi(ranks)} {nlist(gate)})'


def components(xs):
    return '['+';'.join(component(x) for x in xs)+']'


def shard_text(rows, cert, bound):
    k, n, t = cert['history'], cert['size'], cert['anchor']
    radix = 4*sum(8**j for j in range(k+1))
    terms = []
    for machine, nodes, left, right, ca, cb in rows:
        terms.append(f'(SHData {machine}%N {nlist(nodes)}\n {nlist(left)} {nlist(right)}\n {components(ca)}\n {components(cb)})')
    body = ';\n'.join(terms)
    return base.HEADER+f'''From BBB24 Require Import StateHistoryCertificate.
From BBB24.Checkers Require Import NGram.
Definition rows : list sh_data := [
{body}].
Lemma rows_checked : sh_batch_check {bound}%N {k} {n} {t} {radix}%N rows=true.
Proof. vm_compute. reflexivity. Qed.
Definition board := sh_board rows.
Theorem board_state_sound : StateBoardSound (N.to_nat {bound}%N) board.
Proof. apply (sh_batch_state_sound {bound}%N {k} {n} {t} {radix}%N); exact rows_checked. Qed.
Theorem board_nonhalt : forall family, In family board -> NonHalt family.
Proof. apply (sh_batch_nonhalt {bound}%N {k} {n} {t} {radix}%N); exact rows_checked. Qed.
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


def source_hashes(loadpath):
    deps = dependency_hashes([ROOT/'theories/StateHistoryCertificate.v',
                             ROOT/'theories/StateHistoryCertificateRegression.v',
                             ROOT/'theories/CensusUnion.v'], loadpath)
    names = ['check_state_history_tail.py', 'state_history_certificate_export.ml',
             'check_state_pipeline_prefix.py', 'check_state_pipeline_batch.py',
             'generate_pipeline_examples.py', 'check_shadow_links.py', 'state_work_assignment.py', 'check_campaign.py']
    return {**deps, **{'tools/'+name: base.sha(ROOT/'tools'/name) for name in names}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--select', action='store_true')
    parser.add_argument('--refresh', action='store_true')
    parser.add_argument('--resume', action='store_true')
    parser.add_argument('--input', type=Path, default=ROOT/'research/state-history-tail-input.json')
    parser.add_argument('--report', type=Path, default=ROOT/'research/state-history-tail-summary.json')
    parser.add_argument('--output-dir', type=Path, default=ROOT/'build/state-history-tail')
    parser.add_argument('--namespace', default='BBB24StateHistoryTail')
    parser.add_argument('--prefix-input', type=Path)
    parser.add_argument('--bundle-dir', type=Path)
    parser.add_argument('--assignment-input', type=Path)
    parser.add_argument('--preserve-exported-chunks', type=int, default=0)
    parser.add_argument('--timeout', type=int, default=1800)
    parser.add_argument('--limit-bundles', type=int, default=0,
                        help='Check an initial bounded subset; retain all omitted candidate IDs')
    parser.add_argument('--select-only', action='store_true')
    args = parser.parse_args()
    if not args.namespace.isidentifier() or args.timeout <= 0 or args.limit_bundles < 0:
        raise ValueError('Invalid namespace, timeout or bundle limit')
    if args.select:
        select(args)
    data, groups, deferred = load(args)
    if args.select_only:
        print(f'Exact partition validated: {data["prefix_rows"]} prefix + {data["supplied_rows"]} supplied + {len(deferred)} deferred', flush=True)
        return
    limit = args.limit_bundles or len(groups)
    if not 0 < limit <= len(groups):
        raise ValueError('Invalid nonempty bundle limit')
    selected, unselected = groups[:limit], groups[limit:]
    args.output_dir.mkdir(parents=True, exist_ok=True)
    loadpath = ['-Q', str(ROOT/'theories'), 'BBB24', '-Q', str(args.output_dir.resolve()), args.namespace]
    sources = source_hashes(loadpath)
    input_hash = base.sha(args.input)
    if not args.refresh:
        old = json.loads(args.report.read_text())
        if old['source_sha256'] != sources or old['input_sha256'] != input_hash:
            raise ValueError('Supplied history proof inputs changed; refresh and re-audit')
    paths, modules = [], []
    for i, (group, rows) in enumerate(selected):
        module = f'HistoryCertificate{i:03}'
        path = args.output_dir/(module+'.v')
        text = shard_text(rows, group['certificate'], data['state_bound'])
        reuse = args.resume and prefix.reusable(path, text, sources)
        if not reuse:
            path.write_text(text)
            seconds = base.run(['coqc', '-native-compiler', 'no', *loadpath, str(path.resolve())],
                               path.with_suffix('.log'), args.timeout)
            path.with_suffix('.checked.json').write_text(json.dumps(
                {**prefix.evidence(path, sources), 'vo_sha256': base.sha(path.with_suffix('.vo'))}, indent=2)+'\n')
        else:
            seconds = 0
        print(f'{"Reused" if reuse else "Checked"} {module}: {seconds}s', flush=True)
        paths.append(path); modules.append(module)
    count = sum(len(rows) for _, rows in selected)
    aggregate_name = 'HistoryCertificateAll' if limit == len(groups) else f'HistoryCertificatePrefix{limit:03}'
    aggregate = args.output_dir/(aggregate_name+'.v')
    aggregate.write_text(base.aggregate(modules, count, data['state_bound'], args.namespace))
    base.run(['coqc', '-native-compiler', 'no', *loadpath, str(aggregate.resolve())],
             args.output_dir/(aggregate_name+'.log'), args.timeout)
    module = args.namespace+'.'+aggregate_name
    base.run(['coqchk', '-silent', '-bytecode-compiler', 'yes', *loadpath, module,
              'BBB24.StateHistoryCertificateRegression'],
             args.output_dir/(aggregate_name+'.coqchk.log'), args.timeout*(len(paths)+1))
    if input_hash != base.sha(args.input) or sources != source_hashes(loadpath):
        raise ValueError('Supplied proof source/input changed during audit')
    data2, groups2, deferred2 = load(args)
    if data != data2 or groups != groups2 or deferred != deferred2:
        raise ValueError('Original partition or supplied certificate bundle changed during audit')
    theorem = module+'.state_families_discharged'
    stream = io.StringIO(); writer = csv.writer(stream, delimiter='\t', lineterminator='\n')
    writer.writerow(['machine', 'state_bound', 'instruction_bound', 'state_census_linked',
                     'instruction_census_linked', 'stage', 'proof'])
    writer.writerows((base.unpack(row[0]), data['state_bound'], '', 'yes', 'no', group['stage'], theorem)
                     for group, rows in selected for row in rows)
    ledger = stream.getvalue()
    remaining_codes = {row[0] for _, rows in unselected for row in rows} | {row for row, _ in deferred}
    _, _, all_tail = expected(ROOT/data['prefix_input'])
    remainder = ''.join(base.unpack(row)+'\n' for g in all_tail for row in g['rows'] if row in remaining_codes)
    deferred_text = 'machine\tstatus\n'+''.join(base.unpack(row)+'\t'+status+'\n' for row, status in deferred)
    paths.append(aggregate)
    report = {'scope': 'State-only supplied-history suffix closeout; no instruction or raw-table count claim.',
              'full_candidate_rows': data['full_candidate_rows'], 'original_prefix_rows': data['prefix_rows'],
              'tail_candidate_rows': data['tail_rows'], 'supplied_candidate_rows': data['supplied_rows'],
              'deferred_checked_both': data['deferred_checked_both'],
              'deferred_queued_both': data['deferred_queued_both'], 'state_checked_families': count,
              'state_census_linked_families': count, 'instruction_checked_families': 0,
              'state_bound': data['state_bound'], 'instruction_bound': None,
              'state_coverage_theorem': module+'.state_coverage', 'state_discharge_theorem': theorem,
              'state_residual_predicate': module+'.state_pending',
              'validation': 'Supplied certificate VM checks, actual pending membership, recursive coqchk including corruption regressions.',
              'input_sha256': input_hash, 'source_sha256': sources,
              'shard_sha256': {p.name: base.sha(p) for p in paths},
              'generated_ledger': prefix.relative(args.output_dir/(aggregate_name+'.tsv')),
              'ledger_sha256': hashlib.sha256(ledger.encode()).hexdigest(),
              'unselected_rows': data['tail_rows']-count,
              'generated_unselected': prefix.relative(args.output_dir/(aggregate_name+'.unselected.txt')),
              'unselected_sha256': hashlib.sha256(remainder.encode()).hexdigest(),
              'generated_deferred': prefix.relative(args.output_dir/(aggregate_name+'.deferred.tsv')),
              'deferred_sha256': hashlib.sha256(deferred_text.encode()).hexdigest()}
    contents = json.dumps(report, indent=2)+'\n'
    if args.refresh:
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(contents)
    elif args.report.read_text() != contents:
        raise ValueError('Supplied history replay differs from recorded report')
    (ROOT/report['generated_ledger']).write_text(ledger)
    (ROOT/report['generated_unselected']).write_text(remainder)
    (ROOT/report['generated_deferred']).write_text(deferred_text)
    print(json.dumps({k: report[k] for k in ('state_checked_families', 'unselected_rows',
                                           'instruction_checked_families')}), flush=True)


if __name__ == '__main__':
    main()
