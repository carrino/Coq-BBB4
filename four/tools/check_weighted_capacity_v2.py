"""Replay capacity witnesses with explicit direct-branch theorem arguments."""
from pathlib import Path
import sys

import check_weighted_capacity as previous
from weighted_capacity_render_v2 import render

engine = previous.engine
previous_sources = previous.sources


def sources(flags):
    hashes = previous_sources(flags)
    for filename in ('check_weighted_capacity_v2.py', 'weighted_capacity_render_v2.py'):
        hashes['tools/'+filename] = engine.sha(Path(__file__).with_name(filename))
    return hashes


def configure():
    previous.configure()
    engine.render = render
    engine.sources = sources
    previous_run = engine.run

    def run(command, log, timeout):
        code, seconds = previous_run(command, log, timeout)
        if command[0] == 'coqc' and code not in (0, 124):
            raise RuntimeError('Capacity proof compilation failed; no report published: '+str(log))
        return code, seconds

    engine.run = run
    return engine


if __name__ == '__main__':
    import record_weighted_audit as recorded
    recorded.producer = sys.modules[__name__]
    recorded.configure().main()
