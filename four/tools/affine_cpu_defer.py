"""CPU-bounded affine search with explicit deferrals to other search queues.

This wraps the frozen CPU search without modifying it. Weighted snapshots are
validated and archived before any candidate can suppress a C invocation. All
deferred rows remain undecided in the affine residual; candidate assignments
are never interpreted as proofs. Resume by choosing a fresh output directory
and passing the interrupted directory as --prefix-search.
"""
import argparse
import csv
import hashlib
import json
import sys
from pathlib import Path

import affine_cpu_sweep as core
from weighted_codec_v2 import bundle_decode

ROOT = Path(__file__).resolve().parents[1]


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


class WeightedDeferrals:
    def __init__(self, cohort, cohort_hash, index, archive):
        self.cohort, self.cohort_hash = cohort, cohort_hash
        self.index, self.archive = index, archive
        self.archive.mkdir()
        self.seen, self.machines, self.snapshots = {}, {}, []
        self.descriptors, self.bundle_hashes = {}, {}
        self.index_hash = None

    def refresh(self):
        raw = self.index.read_bytes()
        index_hash = hashlib.sha256(raw).hexdigest()
        if index_hash == self.index_hash:
            return
        data = json.loads(raw)
        if data['input_rows'] != len(self.cohort):
            raise ValueError('Weighted index has a different cohort size')
        cursor, total = 0, 0
        additions, new_sources = {}, {}
        listed = set()
        for entry in data['snapshots']:
            lo, hi = entry['input_range']
            if lo != cursor or not lo < hi <= len(self.cohort):
                raise ValueError('Weighted snapshot ranges are not a complete prefix')
            cursor = hi
            registry = Path(entry['registry']).resolve()
            registry.relative_to(ROOT)
            key = str(registry)
            if key in listed:
                raise ValueError('Repeated weighted registry')
            listed.add(key)
            expected = entry['registry_sha256']
            descriptor = (expected, lo, hi, entry['candidate_rows'])
            if key in self.seen:
                if self.descriptors[key] != descriptor:
                    raise ValueError('An immutable weighted registry changed')
                total += entry['candidate_rows']
                continue
            if sha(registry) != expected:
                raise ValueError('Weighted registry hash mismatch')
            record = json.loads(registry.read_text())
            if (record['source']['input_sha256'] != self.cohort_hash or
                    record['source']['input_range'] != [lo, hi]):
                raise ValueError('Weighted registry cohort or range mismatch')
            allowed, local, count = set(self.cohort[lo:hi]), set(), 0
            for bundle in record['bundles']:
                path = (ROOT/bundle['path']).resolve()
                path.relative_to(ROOT)
                if sha(path) != bundle['sha256'] or path.stat().st_size != bundle['bytes']:
                    raise ValueError('Weighted bundle hash or size mismatch')
                self.bundle_hashes[str(path)] = bundle['sha256']
                rows = bundle_decode(path.read_text())
                if len(rows) != bundle['rows']:
                    raise ValueError('Weighted bundle row count mismatch')
                for row in rows:
                    machine = row['machine']
                    if machine not in allowed or machine in local:
                        raise ValueError('Duplicate or out-of-range weighted candidate')
                    local.add(machine)
                    additions[machine] = (str(registry), expected)
                count += len(rows)
            if count != record['rows'] or count != entry['candidate_rows']:
                raise ValueError('Weighted registry candidate count mismatch')
            total += count
            new_sources[key] = expected
            self.descriptors[key] = descriptor
        if not set(self.seen) <= listed:
            raise ValueError('Weighted index discarded an earlier snapshot')
        if cursor != data['exported_input_rows'] or total != data['snapshot_rows']:
            raise ValueError('Weighted index totals disagree with its snapshots')
        path = self.archive/('index-'+index_hash+'.json')
        if path.exists() and path.read_bytes() != raw:
            raise ValueError('Archived weighted index changed')
        path.write_bytes(raw)
        self.machines.update(additions)
        self.seen.update(new_sources)
        self.index_hash = index_hash
        self.snapshots.append(dict(path=str(path), sha256=index_hash))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--weighted-index', type=Path, required=True)
    parser.add_argument('--defer-remaining', type=Path, required=True)
    own, rest = parser.parse_known_args()
    if '--resume' in rest:
        raise ValueError('Use a fresh output and --prefix-search to resume deferring searches')
    def argument(name):
        if rest.count(name) != 1:
            raise ValueError('Expected exactly one '+name)
        return Path(rest[rest.index(name)+1])
    source, output, report = map(argument, ['--input', '--output', '--report'])
    if output.exists() or report.exists():
        raise ValueError('Deferring search requires fresh output and report paths')
    cohort = core.affine_sweep.read_input(source)
    remaining = core.affine_sweep.read_input(own.defer_remaining)
    if not set(remaining) <= set(cohort):
        raise ValueError('Closure remainder contains machines outside the cohort')
    closure = set(cohort)-set(remaining)
    output.mkdir(parents=True)
    weighted = WeightedDeferrals(cohort, sha(source), own.weighted_index, output/'weighted-snapshots')
    weighted.refresh()
    manifest = {'source_sha256': sha(__file__), 'core_source_sha256': sha(core.__file__),
                'codec_source_sha256': sha(Path(__file__).with_name('weighted_codec_v2.py')),
                'input_sha256': sha(source), 'closure_remaining': str(own.defer_remaining),
                'closure_remaining_sha256': sha(own.defer_remaining),
                'closure_candidates': len(closure),
                'status': 'Selection bookkeeping only; every deferred machine remains unresolved.'}
    (output/'deferral-process.json').write_text(json.dumps(manifest, indent=2)+'\n')
    original = core.run_one
    calls, deferred = 0, 0
    with (output/'deferred.tsv').open('w', newline='') as stream:
        writer = csv.writer(stream, delimiter='\t', lineterminator='\n')
        writer.writerow(['machine', 'reason', 'source', 'source_sha256'])
        def run_one(binary, machine, certdir, steps, tape, seconds):
            nonlocal calls, deferred
            if calls % 256 == 0:
                weighted.refresh()
            calls += 1
            if machine in closure:
                reason = 'deferred_closure_candidate'
                origin = (str(own.defer_remaining), manifest['closure_remaining_sha256'])
            elif machine in weighted.machines:
                reason, origin = 'deferred_weighted_candidate', weighted.machines[machine]
            else:
                return original(binary, machine, certdir, steps, tape, seconds)
            writer.writerow([machine, reason, *origin]); stream.flush()
            deferred += 1
            return [machine, 'undecided', '0', '0', '0', '0', '0', '0', '?', '0', reason], reason, None, 0., 0.
        core.run_one = run_one
        private_report = output/'core-report.json'
        forwarded = list(rest)
        forwarded[forwarded.index('--report')+1] = str(private_report)
        old_argv = sys.argv
        try:
            sys.argv = [str(Path(core.__file__)), *forwarded]
            core.main()
        finally:
            sys.argv = old_argv
            core.run_one = original
    if (sha(__file__) != manifest['source_sha256'] or
            sha(core.__file__) != manifest['core_source_sha256'] or
            sha(Path(__file__).with_name('weighted_codec_v2.py')) != manifest['codec_source_sha256'] or
            sha(own.defer_remaining) != manifest['closure_remaining_sha256'] or
            any(sha(path) != expected for path, expected in
                {**weighted.seen, **weighted.bundle_hashes}.items())):
        raise ValueError('Deferral source or input changed during search')
    data = json.loads(private_report.read_text())
    rows = core.affine_sweep.read_output(output/'search.csv', cohort)
    total_deferred = sum(len(r) > 10 and r[10].startswith('deferred_') for r in rows)
    data.update(status='Complete cohort accounting; assigned candidates explicitly deferred without a C search',
                deferral_parameters=manifest, deferred_rows=total_deferred,
                this_run_deferred_rows=deferred,
                weighted_snapshot_archives=weighted.snapshots,
                weighted_registries_sha256=weighted.seen,
                deferred_ledger_sha256=sha(output/'deferred.tsv'),
                proof_accounting='Deferred and failed rows remain in the affine residual. Search assignments are not proofs.')
    report.write_text(json.dumps(data, indent=2)+'\n')


if __name__ == '__main__':
    main()
