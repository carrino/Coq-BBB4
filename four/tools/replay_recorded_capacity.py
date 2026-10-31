"""Reconstruct an immutable capacity report using exact recorded proof bytes."""
import argparse
import json
from pathlib import Path

import check_weighted_v4
import check_weighted_capacity
import replay_recorded_weighted as recorded


def main():
    parser = argparse.ArgumentParser(add_help=False)
    parser.add_argument('--report', type=Path)
    args, _ = parser.parse_known_args()
    if args.report is None:
        return recorded.main()
    report = json.loads(args.report.read_text())
    if 'tools/check_weighted_capacity.py' not in report['manifest'].get('sources_sha256', {}):
        raise ValueError('This adapter requires a recorded capacity report')
    check_weighted_v4.configure = check_weighted_capacity.configure
    recorded.main()


if __name__ == '__main__':
    main()
