"""Invoke the reviewed PURE preparer, then verify its exact selected source graph.

This wrapper invokes only a pinned Python source preparer. It never invokes Coq,
never fabricates a theorem, and never emits Value.v. Pin values are publication
inputs; the unproved private light graph is not shipped as a completed proof.
"""
from __future__ import annotations

import argparse
from pathlib import Path
import subprocess
import sys

from proof24_common import Graph, clean_environment, sha
from proof24_resources import check_disk


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-input', type=Path, required=True)
    parser.add_argument('--spec', type=Path, required=True)
    parser.add_argument('--spec-sha256', required=True)
    parser.add_argument('--preparer', type=Path, required=True)
    parser.add_argument('--preparer-sha256', required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--frozen-manifest-sha256', required=True)
    parser.add_argument('--extra-input', type=Path, action='append', default=[])
    parser.add_argument('--resume', action='store_true')
    parser.add_argument('--disk-reserve-gib', type=int, default=8)
    args = parser.parse_args()
    for path, expected in [(args.spec, args.spec_sha256), (args.preparer, args.preparer_sha256)]:
        if sha(path) != expected:
            raise ValueError('Pure preparer or source spec differs from reviewed pin: ' + str(path))
    output = args.output.resolve()
    if args.disk_reserve_gib < 1:
        raise ValueError('Disk reserve must be positive')
    check_disk(output, args.disk_reserve_gib)
    if args.resume:
        if not output.is_dir():
            raise ValueError('Resume requires an existing prepared output')
    else:
        if output.exists() and (not output.is_dir() or any(output.iterdir())):
            raise ValueError('Fresh pure preparation requires an empty output directory')
        env = clean_environment()
        env['PYTHONDONTWRITEBYTECODE'] = '1'
        command = [sys.executable, '-I', '-S', '-X', 'utf8', str(args.preparer.resolve()), '--prepare-only',
                   '--source-input', str(args.source_input.resolve()), '--manifest', str(args.spec.resolve()),
                   '--output', str(output)]
        for pool in args.extra_input:
            command.extend(['--extra-input', str(pool.resolve())])
        subprocess.run(command, env=env, check=True)
    graph = Graph(output / 'tree', output / 'frozen-prepare-manifest.json',
                  args.frozen_manifest_sha256, allow_value=args.resume)
    graph.verify_sources()
    graph.verify_no_unselected(allow_value=args.resume)
    if not args.resume:
        graph.verify_empty_objects()
    print('Verified exact selected source preparation; Coq/kernel proof credit: 0.', flush=True)
    return 0


if __name__ == '__main__':
    try:
        sys.exit(main())
    except (OSError, ValueError, RuntimeError, subprocess.CalledProcessError) as error:
        print(str(error), file=sys.stderr)
        sys.exit(2)
