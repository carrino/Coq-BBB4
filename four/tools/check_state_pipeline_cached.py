"""Run a frozen state-board generator with a reusable recursive audit receipt.

Only the generator's coqchk invocation is adapted. Every first audit remains
fully recursive; exact source/object/runtime/dependency receipts can later avoid
rechecking these same artifacts in a larger combined audit. Existing logs are
preserved and each receipt uses a fresh path.
"""
import argparse
import importlib
import json
from pathlib import Path
import shutil
import sys
import time

import check_state_pipeline_batch as base
from kernel_audit_cache import audit, fresh_paths

ROOT = base.ROOT


def audit_arguments(command):
    loadpaths, modules = [], []
    i = 1
    while i < len(command):
        if command[i] == '-Q':
            loadpaths.append((Path(command[i+1]), command[i+2])); i += 3
        elif command[i] == '-silent':
            i += 1
        elif command[i] == '-bytecode-compiler':
            if command[i+1] != 'yes':
                raise ValueError('State audit must enable bytecode compilation')
            i += 2
        elif command[i].startswith('-'):
            raise ValueError(f'Unsupported audit option: {command[i]}')
        else:
            modules.append(command[i]); i += 1
    roots = []
    for module in modules:
        matches = [(path, namespace) for path, namespace in loadpaths if module.startswith(namespace+'.')]
        if not matches:
            raise ValueError('Audit module has no source mapping')
        path, namespace = max(matches, key=lambda pair: len(pair[1]))
        roots.append(path/Path(*module[len(namespace)+1:].split('.')).with_suffix('.v'))
    if not modules or any(not path.exists() for path in roots):
        raise ValueError('Missing state audit module source')
    return modules, roots, loadpaths


def main():
    parser = argparse.ArgumentParser(add_help=False)
    parser.add_argument('--kind', choices=['prefix', 'selected', 'history'], required=True)
    own, rest = parser.parse_known_args()
    name = {'prefix': 'check_state_pipeline_prefix', 'selected': 'check_state_pipeline_selected',
            'history': 'check_state_history_tail'}[own.kind]
    target = importlib.import_module(name)
    original_run, original_sources = base.run, target.source_hashes

    def sources(loadpath):
        return {**original_sources(loadpath),
                'tools/check_state_pipeline_cached.py': base.sha(Path(__file__)),
                'tools/kernel_audit_cache.py': base.sha(ROOT/'tools/kernel_audit_cache.py')}

    def run(command, log, timeout):
        log = Path(log)
        if command[0] != 'coqchk':
            if log.exists():
                archive = log.parent/'prior-logs'
                archive.mkdir(parents=True, exist_ok=True)
                _, saved = fresh_paths(archive, log.stem)
                shutil.copyfile(log, saved)
            return original_run(command, log, timeout)
        modules, roots, loadpaths = audit_arguments(command)
        receipt, actual_log = fresh_paths(log.parent/'kernel-audits', log.stem)
        start = time.monotonic()
        audit(modules, roots, loadpaths, receipt, actual_log, recursive=True, timeout=timeout)
        pointer = {'mode': 'recursive', 'requested_modules': modules,
                   'receipt': str(receipt.resolve().relative_to(ROOT)), 'receipt_sha256': base.sha(receipt),
                   'log': str(actual_log.resolve().relative_to(ROOT)), 'log_sha256': base.sha(actual_log)}
        (log.parent/(log.stem+'.audit-receipt.json')).write_text(json.dumps(pointer, indent=2)+'\n')
        print(f'Completed recursive kernel audit receipt: {receipt}', flush=True)
        return round(time.monotonic()-start, 3)

    target.source_hashes = sources
    base.run = run
    sys.argv = [sys.argv[0], *rest]
    target.main()


if __name__ == '__main__':
    main()
