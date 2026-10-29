"""Selected replay with exact-object audit reuse and recursive fallback.

Proof generation and the frozen producer manifest are unchanged. Each audit
root is checked separately, avoiding the cached-independent-root edge case.
New modules are always checked; only a matching recursively audited dependency
closure may be reused. The report explicitly records this audit method.
"""
import argparse
from pathlib import Path
import sys
import time

import check_weighted_selected_v5 as producer
import kernel_audit_cache as audit_cache
from record_weighted_audit import audit_arguments


def main():
    parser = argparse.ArgumentParser(add_help=False)
    parser.add_argument('--audit-cache', type=Path, action='append', default=[])
    args, remaining = parser.parse_known_args()
    sys.argv = [sys.argv[0], *remaining]
    engine = producer.configure()
    previous_run, previous_write = engine.run, engine.write_json
    receipts = []

    def run(command, log, timeout):
        if command[0] != 'coqchk':
            return previous_run(command, log, timeout)
        modules, roots, loadpaths = audit_arguments(command)
        caches = [path for path in args.audit_cache if path.exists()]
        started = time.monotonic()
        for index, (module, root) in enumerate(zip(modules, roots)):
            stem = 'kernel-audit' if index == 0 else f'kernel-audit-root{index}'
            receipt, recorded_log = audit_cache.fresh_paths(Path(log).parent, stem)
            result = audit_cache.audit([module], [root], loadpaths, receipt, recorded_log,
                                       cache=caches, recursive=not caches, timeout=timeout)
            receipts.append({'path': str(receipt.resolve().relative_to(engine.ROOT)),
                             'sha256': engine.sha(receipt), 'kind': result['kind'],
                             'checked_modules': len(result['checked_modules']),
                             'reused_modules': len(result['reused_modules'])})
            caches.append(receipt)
        print('Recorded exact-object kernel audits: '+str(receipts), flush=True)
        return 0, round(time.monotonic()-started, 3)

    def write(path, value):
        if isinstance(value, dict) and 'descriptor' in value and 'artifacts_sha256' in value:
            if not receipts:
                raise ValueError('No kernel audit receipt was produced')
            value = dict(value)
            value['validation'] = ('coqc vm_compute for bounds and actual pending membership, '
                                   'plus exact-object kernel audits with recursive ancestry')
            value['kernel_audit'] = {
                'method': 'Every new module checked; exact dependency reuse or full recursive fallback.',
                'adapter_sha256': engine.sha(Path(__file__)),
                'receipts': receipts,
                'portability': 'Local cache metadata; recorded replay performs a fresh recursive audit.'}
        previous_write(path, value)

    engine.run, engine.write_json = run, write
    engine.main()


if __name__ == '__main__':
    main()
