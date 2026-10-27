"""Reconstruct exact portfolio proofs while preserving the recorded report."""
import argparse
import json
from pathlib import Path

import check_weighted_v4
import check_weighted_portfolio
import replay_recorded_weighted as recorded


def main():
    parser = argparse.ArgumentParser(add_help=False)
    parser.add_argument('--report', type=Path)
    args, _ = parser.parse_known_args()
    if args.report is None:
        return recorded.main()
    report = json.loads(args.report.read_text())
    if 'tools/check_weighted_portfolio.py' not in report['manifest'].get('sources_sha256', {}):
        raise ValueError('This adapter requires a recorded portfolio report')
    check_weighted_v4.configure = check_weighted_portfolio.configure
    recorded.main()


if __name__ == '__main__':
    main()
