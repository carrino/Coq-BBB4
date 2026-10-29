"""Run the frozen V4 producer with a recorded full recursive kernel audit.

Generated proofs, manifests and reports retain the V4 format and hashes.
The only replaced operation is the existing recursive coqchk invocation:
kernel_audit_cache additionally records its exact source/object dependency
closure and verbose audit log for later incremental combined-audit reuse.
Fresh-checkout reproduction remains replay_recorded_weighted.py.
"""
from pathlib import Path
import time

import check_weighted_v4 as producer
import kernel_audit_cache as audit_cache


def audit_arguments(command):
    loadpaths, modules = [], []
    index = 1
    while index < len(command):
        item = command[index]
        if item == '-silent':
            index += 1
        elif item == '-bytecode-compiler' and command[index+1] == 'yes':
            index += 2
        elif item == '-Q':
            loadpaths.append((Path(command[index+1]).resolve(), command[index+2]))
            index += 3
        elif item.startswith('-'):
            raise ValueError('Unexpected frozen weighted audit option: '+item)
        else:
            modules.append(item)
            index += 1
    if not loadpaths or not modules:
        raise ValueError('Missing weighted audit roots/loadpaths')
    roots = []
    for module in modules:
        matches = [(path, prefix) for path, prefix in loadpaths
                   if module.startswith(prefix+'.')]
        if not matches:
            raise ValueError('Missing root loadpath: '+module)
        path, prefix = max(matches, key=lambda entry:len(entry[1]))
        roots.append(path/Path(*module[len(prefix)+1:].split('.')).with_suffix('.v'))
    return modules, roots, loadpaths


def configure():
    engine = producer.configure()
    previous_run = engine.run

    def run(command, log, timeout):
        if command[0] != 'coqchk':
            return previous_run(command, log, timeout)
        modules, roots, loadpaths = audit_arguments(command)
        receipt, recorded_log = audit_cache.fresh_paths(Path(log).parent, 'kernel-audit')
        started = time.monotonic()
        audit_cache.audit(modules, roots, loadpaths, receipt, recorded_log,
                          recursive=True, timeout=timeout)
        print('Recorded full recursive kernel audit: '+str(receipt), flush=True)
        return 0, round(time.monotonic()-started, 3)

    engine.run = run
    return engine


if __name__ == '__main__':
    configure().main()
