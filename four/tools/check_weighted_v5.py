"""Replay direct weighted batches using the proved-equal FastWall checker."""
from pathlib import Path

import check_weighted_v4 as previous
from weighted_render_v5 import render

engine = previous.engine
previous_configure = previous.configure


def sources(flags):
    hashes = previous.sources(flags)
    hashes.update(engine.dependency_hashes([engine.ROOT/'theories/FastWall.v'], flags))
    for filename in ('check_weighted_v5.py', 'weighted_render_v5.py'):
        path = Path(__file__).resolve().parent/filename
        hashes['tools/'+filename] = engine.sha(path)
    return hashes


def configure():
    previous_configure()
    engine.render = render
    engine.sources = sources
    return engine


if __name__ == '__main__':
    configure().main()
