"""Replay compact complementary instruction-recurrence portfolios.

Each row checks the full eight-instruction coverage and each target witness,
then exports both bounds, actual census membership and completion discharge.
"""
from pathlib import Path
import sys

import check_weighted_v4 as previous
from weighted_portfolio_render import HEADER, render

engine = previous.engine
previous_configure = previous.configure
previous_unpack = engine.unpack


def unpack(row):
    return {'machine': row['machine'], 'choices': row['choices'],
            'variants': [previous_unpack(variant) for variant in row['portfolio']]}


def sources(flags):
    hashes = previous.sources(flags)
    hashes.update(engine.dependency_hashes([engine.ROOT/'theories/InstructionPortfolio.v'], flags))
    for filename in ('check_weighted_portfolio.py', 'weighted_portfolio_render.py'):
        hashes['tools/'+filename] = engine.sha(Path(__file__).with_name(filename))
    return hashes


def configure():
    previous_configure()
    engine.HEADER = HEADER
    engine.unpack = unpack
    engine.render = render
    engine.sources = sources
    previous_run = engine.run

    def run(command, log, timeout):
        code, seconds = previous_run(command, log, timeout)
        if command[0] == 'coqc' and code:
            raise RuntimeError('Portfolio proof compilation failed; no result published: '+str(log))
        return code, seconds

    engine.run = run
    return engine


if __name__ == '__main__':
    import record_weighted_audit as recorded
    recorded.producer = sys.modules[__name__]
    recorded.configure().main()
