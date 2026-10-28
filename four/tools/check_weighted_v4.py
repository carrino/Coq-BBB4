"""Recorded V3 replay with dense boolean gates and no unused glob output."""
from pathlib import Path
import hashlib

import check_weighted_v3 as previous
from weighted_render_v4 import render

engine=previous.engine
original_run=engine.run


def sources(flags):
    hashes=previous.sources(flags)
    for filename in ('check_weighted_v4.py','weighted_render_v4.py'):
        path=Path(__file__).resolve().parent/filename
        hashes['tools/'+filename]=hashlib.sha256(path.read_bytes()).hexdigest()
    return hashes


def run(command,log,timeout):
    if command[0]=='coqc' and '-noglob' not in command:
        command=[command[0],'-noglob',*command[1:]]
    return original_run(command,log,timeout)


def configure():
    previous.configure()
    engine.render=render
    engine.sources=sources
    engine.run=run
    return engine


if __name__=='__main__':configure().main()
