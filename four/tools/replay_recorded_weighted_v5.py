"""Reconstruct frozen V5 or earlier reports without changing their bytes.

The original exact-artifact reconstruction and recursive audit remain intact.
This adapter adds V5 renderer selection before delegating to that workflow.
"""
import argparse
import json
from pathlib import Path

import check_weighted_v4
import check_weighted_v5
import replay_recorded_weighted as recorded


def main():
    parser = argparse.ArgumentParser(add_help=False)
    parser.add_argument('--report', type=Path)
    args, _ = parser.parse_known_args()
    if args.report is None:
        return recorded.main()
    report = json.loads(args.report.read_text())
    sources = report['manifest'].get('sources_sha256', {})
    if 'tools/check_weighted_v5.py' in sources:
        check_weighted_v4.configure = check_weighted_v5.configure
    recorded.main()


if __name__ == '__main__':
    main()
