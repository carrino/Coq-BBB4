"""Replay the frozen affine checker with reusable full kernel-audit receipts.

Generation, compilation, reports, and ledgers are delegated unchanged.  Only
the final recursive coqchk invocation is replaced by the receipt-producing
auditor.  This adapter always requests a full recursive audit, preserving the
frozen report's validation statement.  Later combined audits can reuse the
exact source/object/dependency closure recorded here.
"""
import json
import re
import time
from pathlib import Path

import check_affine_wave as checker
from kernel_audit_cache import audit, digest, fresh_paths


def main():
    original_run = checker.run
    adapter_hash = digest(__file__)
    auditor_path = Path(__file__).with_name('kernel_audit_cache.py')
    auditor_hash = digest(auditor_path)
    receipts = []

    def checked_run(command, log, timeout):
        if command[0] != 'coqchk':
            return original_run(command, log, timeout)
        module = command[-1]
        match = re.fullmatch(r'BBB24AffineWave\.([A-Z][A-Za-z0-9_]*)\.All', module)
        if not match:
            raise ValueError('Unexpected affine audit module')
        loadpaths = [(checker.ROOT/'theories', 'BBB24'),
                     (checker.BUILD, 'BBB24AffineWave')]
        expected = ['coqchk', '-silent', '-bytecode-compiler', 'yes',
                    '-Q', str(loadpaths[0][0]), 'BBB24',
                    '-Q', str(loadpaths[1][0]), 'BBB24AffineWave', module]
        source = checker.BUILD/match.group(1)/'All.v'
        if command != expected or Path(log) != source.with_name('coqchk.log'):
            raise ValueError('Unexpected affine audit command or output path')
        receipt, audit_log = fresh_paths(source.parent)
        started = time.monotonic()
        result = audit([module], [source], loadpaths, receipt, audit_log,
                       recursive=True, timeout=timeout)
        if digest(__file__) != adapter_hash or digest(auditor_path) != auditor_hash:
            raise ValueError('Audit adapter or auditor source changed during replay')
        evidence = dict(adapter_sha256=adapter_hash, auditor_sha256=auditor_hash,
                        frozen_checker_sha256=digest(checker.__file__),
                        receipt=str(receipt), receipt_sha256=digest(receipt),
                        kind=result['kind'], module=module)
        receipt.with_suffix('.adapter.json').write_text(json.dumps(evidence, indent=2)+'\n')
        receipts.append(receipt)
        print('Full kernel audit receipt: '+str(receipt), flush=True)
        return time.monotonic()-started

    checker.run = checked_run
    try:
        checker.main()
        if len(receipts) != 1:
            raise ValueError('Expected exactly one complete affine audit')
    finally:
        checker.run = original_run


if __name__ == '__main__':
    main()
