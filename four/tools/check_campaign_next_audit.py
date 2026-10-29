"""Run the frozen next checker with local-loadpath receipt normalization.

Only the compilation-receipt projection hook is replaced. The original
checker's source/object/compiler receipt checks, complete kernel snapshots,
runtime checks, audit phases, input pins, reports, and ledgers all run through
its unchanged main function. This entrypoint is restricted to --audit-only.
"""
import argparse
from functools import partial
from pathlib import Path

import check_campaign_next as original
from campaign_snapshot_dependencies import snapshot_dependencies


def main():
    parser = argparse.ArgumentParser(description=__doc__, add_help=False)
    parser.add_argument('--manifest', type=Path,
                        default=original.ROOT / 'research/next-campaign-input.json')
    parser.add_argument('--output-dir', type=Path,
                        default=original.ROOT / 'build/next-campaign')
    parser.add_argument('--namespace', default='BBB24NextCampaign')
    parser.add_argument('--audit-only', action='store_true')
    args, _ = parser.parse_known_args()
    if not args.audit_only:
        parser.error('This compatibility entrypoint requires --audit-only')
    _, _, paths, _ = original.load_manifest(args.manifest.resolve())
    paths[str(args.output_dir.resolve().relative_to(original.ROOT))] = args.namespace
    loadpaths = [(original.ROOT / path, prefix) for path, prefix in paths.items()]
    previous = original.snapshot_dependencies
    original.snapshot_dependencies = partial(snapshot_dependencies,
                                             loadpaths=loadpaths, root=original.ROOT)
    try:
        original.main()
    finally:
        original.snapshot_dependencies = previous


if __name__ == '__main__':
    main()
