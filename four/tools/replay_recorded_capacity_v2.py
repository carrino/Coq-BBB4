"""Reconstruct a frozen V2 capacity report without rewriting its metadata."""
import argparse
import json
from pathlib import Path

import check_weighted_v4
import check_weighted_capacity_v2
import replay_recorded_weighted as recorded


def main():
    parser = argparse.ArgumentParser(add_help=False)
    parser.add_argument('--report', type=Path)
    args, _ = parser.parse_known_args()
    if args.report is None:
        return recorded.main()
    report = json.loads(args.report.read_text())
    if 'tools/check_weighted_capacity_v2.py' not in report['manifest'].get('sources_sha256', {}):
        raise ValueError('This adapter requires a recorded V2 capacity report')
    check_weighted_v4.configure = check_weighted_capacity_v2.configure
    recorded.main()


if __name__ == '__main__':
    main()
