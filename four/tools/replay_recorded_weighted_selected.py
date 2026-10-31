"""Reproduce selected weighted reports without changing their frozen metadata."""
import argparse
import json
from pathlib import Path

import check_weighted_v4
import check_weighted_selected_v5 as selected
import replay_recorded_weighted as recorded


def main():
    parser = argparse.ArgumentParser(add_help=False)
    parser.add_argument('--report', type=Path)
    parser.add_argument('--registry', type=Path)
    args, _ = parser.parse_known_args()
    if args.report is None:
        return recorded.main()
    report = json.loads(args.report.read_text())
    if 'tools/check_weighted_selected_v5.py' not in report['manifest']['sources_sha256']:
        raise ValueError('This adapter requires a recorded selected report')
    if args.registry is None:
        raise ValueError('A selected registry is required')
    _, _, decode = selected.selection.load(args.registry)
    recorded.bundle_decode = decode
    check_weighted_v4.configure = selected.configure
    recorded.main()


if __name__ == '__main__':
    main()
