"""Replay a state-only repeated-word board with a reusable recursive audit.

The frozen board generator and report semantics are unchanged. This adapter
records the first full recursive audit's exact source/object/runtime closure,
so the final campaign can reuse that checked evidence without repeating it.
"""
from pathlib import Path
import json
import time

import check_state_repwl_batch as engine
from check_state_pipeline_cached import audit_arguments
from kernel_audit_cache import audit, fresh_paths


def configure():
    original_run, original_sources = engine.run, engine.source_hashes

    def sources(loadpath):
        hashes = original_sources(loadpath)
        for name in ('check_state_repwl_recorded.py', 'check_state_pipeline_cached.py',
                     'kernel_audit_cache.py'):
            hashes['tools/'+name] = engine.sha(Path(__file__).with_name(name))
        return hashes

    def run(command, log, timeout):
        if command[0] != 'coqchk':
            return original_run(command, log, timeout)
        log = Path(log)
        modules, roots, loadpaths = audit_arguments(command)
        receipt, actual_log = fresh_paths(log.parent/'kernel-audits', log.stem)
        start = time.monotonic()
        audit(modules, roots, loadpaths, receipt, actual_log, recursive=True, timeout=timeout)
        pointer = {'mode': 'recursive', 'requested_modules': modules,
                   'receipt': str(receipt.resolve().relative_to(engine.ROOT)),
                   'receipt_sha256': engine.sha(receipt),
                   'log': str(actual_log.resolve().relative_to(engine.ROOT)),
                   'log_sha256': engine.sha(actual_log)}
        pointer_path, _ = fresh_paths(log.parent, log.stem+'.audit-receipt')
        pointer_path.write_text(json.dumps(pointer, indent=2)+'\n')
        print('Completed recursive kernel audit receipt: '+str(receipt), flush=True)
        return round(time.monotonic()-start, 3)

    engine.run, engine.source_hashes = run, sources
    return engine


if __name__ == '__main__':
    configure().main()
