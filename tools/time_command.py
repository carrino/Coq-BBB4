#!/usr/bin/env python3
"""Run a build phase, preserving its exit status and appending timing evidence."""
import argparse
from datetime import datetime, timezone
import json
from pathlib import Path
import resource
import subprocess
import sys
import time


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--log', type=Path, required=True)
    parser.add_argument('--phase', required=True)
    parser.add_argument('command', nargs=argparse.REMAINDER)
    args = parser.parse_args()
    command = args.command[1:] if args.command[:1] == ['--'] else args.command
    if not command:
        parser.error('a command is required')
    args.log.parent.mkdir(parents=True, exist_ok=True)
    started = datetime.now(timezone.utc).isoformat()
    before = resource.getrusage(resource.RUSAGE_CHILDREN)
    start = time.monotonic()
    # Inherit the jobserver descriptors when make invokes this wrapper in a
    # recursive recipe. Stdin/stdout/stderr stay attached to the original build.
    result = subprocess.run(command, close_fds=False)
    elapsed = time.monotonic() - start
    after = resource.getrusage(resource.RUSAGE_CHILDREN)
    record = dict(phase=args.phase, started_utc=started, wall_seconds=elapsed,
                  user_seconds=after.ru_utime - before.ru_utime,
                  system_seconds=after.ru_stime - before.ru_stime,
                  max_child_rss_bytes=after.ru_maxrss * (1 if sys.platform == 'darwin' else 1024),
                  exit_code=result.returncode, command=command)
    with args.log.open('a') as stream:
        stream.write(json.dumps(record) + '\n')
    print(f'>>> {args.phase}: {elapsed:.1f} s wall, '
          f'{record["user_seconds"] + record["system_seconds"]:.1f} s CPU, '
          f'exit {result.returncode} (timings: {args.log})', flush=True)
    return result.returncode if result.returncode >= 0 else 128 - result.returncode


if __name__ == '__main__':
    raise SystemExit(main())
