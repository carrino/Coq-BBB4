"""Replay a fully partitioned scheduling selection using the FastWall checker."""
import argparse
from pathlib import Path
import sys

import check_weighted_v5 as previous
import weighted_selection as selection

engine = previous.engine
previous_configure = previous.configure
registry_path = None


def sources(flags):
    hashes = previous.sources(flags)
    _, dependencies, _ = selection.load(registry_path)
    hashes.update(dependencies)
    for filename in ('check_weighted_selected_v5.py', 'weighted_selection.py'):
        hashes['tools/'+filename] = engine.sha(Path(__file__).with_name(filename))
    return hashes


def configure():
    global registry_path
    parser = argparse.ArgumentParser(add_help=False)
    parser.add_argument('--registry', type=Path)
    args, _ = parser.parse_known_args()
    if args.registry is None:
        return previous_configure()
    registry_path = args.registry
    _, _, decode = selection.load(registry_path)
    previous_configure()
    engine.bundle_decode = decode
    engine.sources = sources
    return engine


if __name__ == '__main__':
    import record_weighted_audit as recorded
    recorded.producer = sys.modules[__name__]
    recorded.configure().main()
