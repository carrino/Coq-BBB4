"""Replay compact capacity certificates with both bounds and census membership.

The existing compact bundle format carries one additional capacities table.
Each row proves the new checker accepts, the old supplied certificate rejects,
and two mutations (zero scale and missing count weights) are rejected.
"""
from pathlib import Path
import sys

import check_weighted_v4 as previous
from weighted_capacity_render import HEADER, render

engine = previous.engine
previous_configure = previous.configure
previous_unpack = engine.unpack


def unpack(row):
    value = previous_unpack(row)
    if not isinstance(row.get('capacities'), dict) or not row['capacities']:
        raise ValueError('A nonempty capacity table is required')
    value['capacities'] = row['capacities']
    return value


def sources(flags):
    hashes = previous.sources(flags)
    hashes.update(engine.dependency_hashes([engine.ROOT/'theories/WeightedCapacity.v'], flags))
    for filename in ('check_weighted_capacity.py', 'weighted_capacity_render.py'):
        hashes['tools/'+filename] = engine.sha(Path(__file__).with_name(filename))
    return hashes


def configure():
    previous_configure()
    engine.HEADER = HEADER
    engine.unpack = unpack
    engine.render = render
    engine.sources = sources
    return engine


if __name__ == '__main__':
    import record_weighted_audit as recorded
    recorded.producer = sys.modules[__name__]
    recorded.configure().main()
