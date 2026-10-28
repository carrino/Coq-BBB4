"""V2 batch replay with an exhaustive-target renderer fix; old tools stay frozen."""
from pathlib import Path
import hashlib

import check_weighted_v2 as engine
from weighted_render_v3 import render

original_sources=engine.sources


def sources(flags):
    hashes=original_sources(flags)
    for filename in ('check_weighted_v3.py','weighted_render_v3.py'):
        path=Path(__file__).resolve().parent/filename
        hashes['tools/'+filename]=hashlib.sha256(path.read_bytes()).hexdigest()
    return hashes


def configure():
    engine.render=render
    engine.sources=sources
    return engine


if __name__=='__main__':configure().main()
