#!/usr/bin/env python3
"""Bounded, deterministic UNTRUSTED C-candidate -> checked Coq replay.

Example (requires already compiled BBB4 / BBBWait42 dependencies):
  PATH=/workspace/.opam/census/bin:$PATH python3 wait42/tools/replay_rank_samples.py \
    --ledger /tmp/bbb-wait42-tail/census.ledger.tsv \
    --output wait42/build/rank-replay-sample

Select the smallest SHA256(machine + ledger index) in each (n,t,full)
stratum. All candidate rows are scanned, but only a bounded sample is kept.
The C context count controls search fuel only; it supplies no proof premise.
Each false gate is retained with a kernel-checked rejection equation. Each
true gate gets a WindowBound theorem, universally quantified over B >= t.
No census coverage or uniform upper bound follows from these sampled proofs.
"""
import argparse
from collections import Counter
import csv
import hashlib
import heapq
import json
from pathlib import Path
import re
import resource
import subprocess
import time

ROOT = Path(__file__).resolve().parents[2]
RUNGS = ((2, 100), (3, 200), (4, 400), (6, 800), (8, 1600))
MACHINE = re.compile(r'(?:---|[01][LR][ABCD]){2}(?:_(?:---|[01][LR][ABCD]){2}){3}')
HEADER = '''From Coq Require Import Arith Lia Bool List ZArith.
From BBB4 Require Import BBB4_Statement.
From BBB4.Census Require Import Deferred_Defs.
From BBB4.Census Require Import TNF_QH.
From BBBWait42 Require Import Spec Ranked RankedCompletion.
Import ListNotations.
'''


def validate_row(row):
    if MACHINE.fullmatch(row['machine']) is None:
        raise ValueError('invalid machine table')
    for key in ('index', 'ngram_n', 'ngram_t', 'full', 'contexts', 'candidate_wait_upper'):
        if not re.fullmatch(r'[0-9]+', row[key]):
            raise ValueError('invalid numeric field: ' + key)
    if int(row['full']) != int('---' not in row['machine']):
        raise ValueError('inconsistent full flag at index ' + row['index'])
    if not 1 <= int(row['ngram_n']) <= 8 or int(row['ngram_t']) > 8192:
        raise ValueError('anchor or ngram width exceeds bounded replay')
    if int(row['contexts']) > 65536 or int(row['candidate_wait_upper']) > 65537:
        raise ValueError('finite graph exceeds bounded replay')


def select_samples(ledger, per_stratum=1):
    """Streaming bottom-k hash selection; ties break by unique ledger index."""
    heaps, counts = {}, Counter()
    with Path(ledger).open(newline='') as stream:
        for row in csv.DictReader(stream, delimiter='\t'):
            if row['kind'] != 'tail_ngram_candidate':
                continue
            validate_row(row)
            key = (int(row['ngram_n']), int(row['ngram_t']), int(row['full']))
            if key[:2] not in RUNGS:
                continue
            counts[key] += 1
            digest = int.from_bytes(hashlib.sha256(
                (row['machine'] + '\t' + row['index']).encode()).digest(), 'big')
            item = (-digest, -int(row['index']), json.dumps(row, sort_keys=True))
            heap = heaps.setdefault(key, [])
            if len(heap) < per_stratum:
                heapq.heappush(heap, item)
            elif item[:2] > heap[0][:2]:
                heapq.heapreplace(heap, item)
    samples = [json.loads(item[2]) for key in sorted(heaps)
               for item in sorted(heaps[key], key=lambda item: (-item[0], -item[1]))]
    if len({r['index'] for r in samples}) != len(samples):
        raise ValueError('duplicate selected ledger indices')
    return samples, {':'.join(map(str, key)): counts[key] for key in sorted(counts)}


def source(row, fuel, rounds):
    validate_row(row)
    slots = row['machine'].replace('_', '')
    table = '; '.join('tN' if slots[i:i+3] == '---' else 't' + slots[i:i+3]
                      for i in range(0, 24, 3))
    n, t, w = (int(row[k]) for k in ('ngram_n', 'ngram_t', 'candidate_wait_upper'))
    return HEADER + f'''(* Ledger index {int(row['index'])}; UNTRUSTED C candidate. *)
Definition machine : TM := row_to_tm [{table}].
Definition verdict : bool := ngram_ranked_search machine {n} {t} {fuel} {rounds} {w}.
Eval vm_compute in verdict.
'''


def proof_source(row, fuel, rounds, accepted):
    src = source(row, fuel, rounds).replace('Eval vm_compute in verdict.\n', '')
    verdict = 'true' if accepted else 'false'
    src += f'''Example replay_gate : verdict = {verdict}.
Proof. native_compute. reflexivity. Qed.
'''
    if accepted:
        n, t, w = (int(row[k]) for k in ('ngram_n', 'ngram_t', 'candidate_wait_upper'))
        src += f'''(* The gate above was computed; subsequent proofs reuse its theorem. *)
Local Opaque ngram_ranked_search.
Theorem replay_window : forall B, {t} <= B -> WindowBound machine B {w}.
Proof.
  intros B Ht. apply (ngram_ranked_search_sound machine {n} {t} {fuel} {rounds} {w} B);
    [exact Ht|exact replay_gate].
Qed.
Print Assumptions replay_window.
Theorem replay_all_completions : forall B tm',
 {t} <= B -> TM_le machine tm' -> NonHalt tm' /\\ WindowBound tm' B {w}.
Proof.
  intros B tm' Ht Hle.
  exact (ngram_ranked_search_completion machine {n} {t} {fuel} {rounds} {w}
    B Ht replay_gate tm' Hle).
Qed.
Print Assumptions replay_all_completions.
'''
    return src


def limits(memory_mb):
    def apply():
        bound = memory_mb * 1024 * 1024
        resource.setrlimit(resource.RLIMIT_AS, (bound, bound))
    return apply


def file_sha256(path):
    with Path(path).open('rb') as stream:
        h = hashlib.sha256()
        for chunk in iter(lambda: stream.read(1 << 20), b''):
            h.update(chunk)
        return h.hexdigest()


def run(command, log, timeout, memory_mb):
    start = time.monotonic()
    try:
        result = subprocess.run(command, cwd=ROOT, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, text=True, timeout=timeout,
                                preexec_fn=limits(memory_mb))
        text, code = result.stdout, result.returncode
        status = 'ok' if code == 0 else 'error'
    except subprocess.TimeoutExpired as exc:
        text = exc.stdout or b''
        if isinstance(text, bytes):
            text = text.decode(errors='replace')
        code, status = None, 'timeout'
    log.write_text(text)
    return {'status': status, 'returncode': code,
            'seconds': round(time.monotonic() - start, 3), 'log': str(log)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--ledger', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--per-stratum', type=int, default=1)
    parser.add_argument('--timeout', type=float, default=30)
    parser.add_argument('--memory-mb', type=int, default=2048)
    parser.add_argument('--fuel-factor', type=int, default=4)
    parser.add_argument('--select-only', action='store_true')
    parser.add_argument('--coqc', default='coqc')
    parser.add_argument('--coqchk', default='coqchk')
    parser.add_argument('--expect-accepted', type=int, help='Regression gate for a frozen sample')
    args = parser.parse_args()
    if not 1 <= args.per_stratum <= 8 or args.fuel_factor < 3:
        parser.error('per-stratum must be 1..8; fuel-factor must be >=3')
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=True)
    samples, counts = select_samples(args.ledger, args.per_stratum)
    report = {'trust': 'sampled proof replay; no census coverage claim',
              'ledger': str(args.ledger.resolve()), 'stratum_population': counts,
              'ledger_sha256': file_sha256(args.ledger),
              'generator_sha256': file_sha256(__file__),
              'selection': 'bottom SHA256(machine TAB index) per (n,t,full)', 'samples': []}
    flags = ['-Q', str(ROOT / 'theories'), 'BBB4', '-Q',
             str(ROOT / 'wait42/theories'), 'BBBWait42', '-Q', str(out), 'RankReplay']
    modules = []
    for i, row in enumerate(samples):
        fuel = args.fuel_factor * int(row['contexts']) + 16
        rounds = 2 ** (int(row['ngram_n']) + 1) + 2
        name = f'RankReplay{i:03d}'
        path = out / (name + '.v')
        path.write_text(source(row, fuel, rounds))
        entry = {'ledger_row': row, 'fuel': fuel, 'rounds': rounds,
                 'source': str(path), 'status': 'selected'}
        report['samples'].append(entry)
        if not args.select_only:
            probe = run([args.coqc, *flags, str(path)], out / (name + '.probe.log'),
                        args.timeout, args.memory_mb)
            entry['evaluation'] = probe
            if probe['status'] == 'ok':
                text = Path(probe['log']).read_text()
                values = re.findall(r'=\s*(true|false)\s*:\s*bool', text)
                if len(values) != 1:
                    entry['status'] = 'unparsed'
                else:
                    accepted = values[0] == 'true'
                    path.write_text(proof_source(row, fuel, rounds, accepted))
                    proof = run([args.coqc, *flags, str(path)], out / (name + '.proof.log'),
                                args.timeout, args.memory_mb)
                    entry['proof'] = proof
                    entry['status'] = ('accepted' if accepted else 'rejected') if proof['status'] == 'ok' else 'proof_' + proof['status']
                    if proof['status'] == 'ok':
                        modules.append('RankReplay.' + name)
            else:
                entry['status'] = 'evaluation_' + probe['status']
        (out / 'results.json').write_text(json.dumps(report, indent=2) + '\n')
        print(row['index'], row['ngram_n'], row['full'], entry['status'], flush=True)
    if modules:
        report['kernel_audit'] = run([args.coqchk, '-silent', '-bytecode-compiler', 'yes', *flags, *modules],
                                    out / 'coqchk.log', max(60, args.timeout), args.memory_mb)
    report['status_counts'] = dict(Counter(e['status'] for e in report['samples']))
    report['proof_status'] = ('PASSED' if modules and report.get('kernel_audit', {}).get('status') == 'ok'
                              and all(e['status'] in ('accepted', 'rejected') for e in report['samples']) else 'NOT_PASSED')
    (out / 'results.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report['status_counts']), flush=True)
    if any(e['status'] not in ('accepted', 'rejected', 'selected') for e in report['samples']):
        return 1
    if report.get('kernel_audit', {}).get('status', 'ok') != 'ok':
        return 1
    if args.expect_accepted is not None and report['status_counts'].get('accepted', 0) != args.expect_accepted:
        return 1
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
