#!/usr/bin/env python3
"""Measure native instruction-walk loading and computation before/after the split.

All library prerequisites must already be built with the same native-enabled
Coq. By default both samples use this tree's identical computation and data:
the before sample imports the proof-bearing RunTr_Split, and the after sample
imports only RunTr_WalkCompute. This isolates the library-loading change and
remains reproducible after a squash merge. An optional historical baseline
compiles that revision's original RunTr/RunTr_Split in a temporary namespace.
Every native test is forcibly recompiled. Run without other heavy jobs. This
is a phase benchmark, not the required complete census re-walk.
"""
import argparse
import json
from pathlib import Path
import platform
import resource
import subprocess
import sys
import time

REPO = Path(__file__).resolve().parents[2]


def worker(command, log_path, result_path):
    """One fresh process per sample: RUSAGE_CHILDREN's RSS is cumulative."""
    start = time.monotonic()
    with Path(log_path).open('w') as log:
        result = subprocess.run(command, cwd=REPO, stdout=log,
                                stderr=subprocess.STDOUT)
    usage = resource.getrusage(resource.RUSAGE_CHILDREN)
    rss_bytes = usage.ru_maxrss * (1 if sys.platform == 'darwin' else 1024)
    record = dict(command=command, wall_seconds=time.monotonic()-start,
                  user_seconds=usage.ru_utime, system_seconds=usage.ru_stime,
                  max_rss_bytes=rss_bytes, exit_code=result.returncode)
    Path(result_path).write_text(json.dumps(record, indent=2)+'\n')
    return result.returncode


def prepare(output, baseline):
    for name, dest in [('RunTr', 'BeforeRunTr'),
                       ('RunTr_Split', 'BeforeRunTrSplit')]:
        source = subprocess.check_output(
            ['git', 'show', f'{baseline}:theories/CensusTr/{name}.v'],
            cwd=REPO, text=True)
        if 'RunTr_WalkCompute' in source or 'Require Export RunTr_Compute' in source:
            raise ValueError('baseline already contains the lean split')
        if name == 'RunTr':
            # Current RepWL wrappers contain concatenated parts. The old
            # tactic unfolds those wrappers before trying their existing
            # certificates. Repair only proof assembly, preserving every
            # baseline computation definition and original machine list.
            for theorem in ['prov_tr_all', 'provqh_tr_all']:
                start = source.index('Lemma ' + theorem + ' :')
                end = source.index('Qed.', start) + len('Qed.')
                body = source[start:end]
                old = 'repeat (apply Forall_app; split);\n    first ['
                if old in body:
                    if body.count(old) != 1 or not body.endswith('].\nQed.'):
                        raise ValueError('unexpected baseline list-assembly proof')
                    body = body.replace(old, 'repeat first [')
                    body = body[:-len('].\nQed.')] + ' | (apply Forall_app; split)].\nQed.'
                    source = source[:start] + body + source[end:]
        if name == 'RunTr_Split':
            original = 'From BBB4.CensusTr Require Import TNF_QHTr DecideTr RunTr.'
            replacement = ('From BBB4.CensusTr Require Import TNF_QHTr DecideTr.\n'
                           'From Baseline Require Import BeforeRunTr.')
            if source.count(original) != 1:
                raise ValueError('unexpected baseline RunTr_Split import')
            source = source.replace(original, replacement)
        (output/(dest+'.v')).write_text(source)


def main():
    # Internal helper is launched separately for every measurement, including
    # native code generation. It avoids inherited peak-RSS measurements.
    if len(sys.argv) > 1 and sys.argv[1] == '--worker':
        raise SystemExit(worker(sys.argv[4:], sys.argv[2], sys.argv[3]))
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--baseline-ref',
                    help='optional pre-split revision; default: full imports in this tree')
    ap.add_argument('--output', required=True, type=Path)
    ap.add_argument('--coqc', default='coqc')
    ap.add_argument('--coqnative', default='coqnative')
    ap.add_argument('--units', nargs='+', type=int, default=[10])
    ap.add_argument('--prepare-only', action='store_true')
    ap.add_argument('--skip-baseline-build', action='store_true',
                    help='reuse baseline libraries built by a previous invocation')
    args = ap.parse_args()
    if any(i < 0 or i >= 96 for i in args.units):
        ap.error('--units must be indices in the unchanged 96-unit walk')
    if (args.prepare_only or args.skip_baseline_build) and not args.baseline_ref:
        ap.error('--prepare-only and --skip-baseline-build require --baseline-ref')
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    baseline = (subprocess.check_output(
        ['git', 'rev-parse', args.baseline_ref], cwd=REPO, text=True).strip()
        if args.baseline_ref else None)
    stamp = output/'baseline-built.txt'
    if args.skip_baseline_build and (not stamp.exists() or stamp.read_text().strip() != baseline):
        ap.error('--skip-baseline-build requires a successful build of this baseline')
    if args.baseline_ref:
        prepare(output, args.baseline_ref)
    if args.prepare_only:
        return
    flags = ['-Q', str(REPO/'theories'), 'BBB4', '-Q', str(output), 'Baseline']
    record = dict(platform=platform.platform(), baseline_ref=baseline,
                  baseline_kind=('historical-source' if baseline else 'proof-bearing-imports'),
                  baseline_assembly_adjustment=(
                      'try stage certificates before splitting append wrappers; computation unchanged'
                      if baseline else None),
                  revision=subprocess.check_output(
                      ['git', 'rev-parse', 'HEAD'], cwd=REPO, text=True).strip(),
                  source_status=subprocess.check_output(
                      ['git', 'status', '--porcelain', '--', '_CoqProject',
                       'theories', 'tools/censustr'], cwd=REPO, text=True).splitlines(),
                  compiler=subprocess.check_output([args.coqc, '--version'],
                                                   text=True).strip(),
                  units=args.units, jobs=1, prerequisites_prebuilt=True,
                  baseline_build=[], samples=[])

    def save():
        (output/'lean_timings.json').write_text(json.dumps(record, indent=2)+'\n')

    def measured(name, command):
        result_path = output/(name+'.json')
        result = subprocess.run([sys.executable, str(Path(__file__).resolve()),
                                 '--worker', str(output/(name+'.log')),
                                 str(result_path), *command], cwd=REPO)
        value = json.loads(result_path.read_text())
        value['name'] = name
        if result.returncode:
            save()
            raise SystemExit(f'{name} failed; see {output/(name+".log")}')
        print(json.dumps(value), flush=True)
        return value

    if args.baseline_ref and not args.skip_baseline_build:
        for name in ['BeforeRunTr', 'BeforeRunTrSplit']:
            record['baseline_build'].append(measured(name, [
                args.coqc, '-native-compiler', 'no', *flags,
                str(output/(name+'.v'))]))
            record['baseline_build'].append(measured(name+'_native', [
                args.coqnative, *flags, str(output/(name+'.vo'))]))
            save()
        stamp.write_text(baseline+'\n')
    before_library = ('Baseline.BeforeRunTrSplit' if args.baseline_ref
                      else 'BBB4.CensusTr.RunTr_Split')
    for phase, library in [('before', before_library),
                            ('after', 'BBB4.CensusTr.RunTr_WalkCompute')]:
        for unit in [None, *args.units]:
            label = 'load' if unit is None else f'unit_{unit:02d}'
            name = f'{phase}_{label}'
            claim = ('List.length frontier_nodes_tr = 1792' if unit is None
                     else f'unit_ok 96 {unit} 0 frontier_nodes_tr = true')
            witness = '1792' if unit is None else 'true'
            source = output/(name+'.v')
            source.write_text(
                'From Coq Require Import Arith List.\n'
                f'Require Import {library}.\n'
                f'Lemma measured_check : {claim}.\n'
                f'Proof. native_cast_no_check (eq_refl {witness}). Qed.\n'
                'Print Assumptions measured_check.\n')
            value = measured(name, [args.coqc, '-native-compiler', 'ondemand',
                                    *flags, str(source)])
            value.update(phase=phase, unit=unit)
            record['samples'].append(value)
            save()


if __name__ == '__main__':
    main()
