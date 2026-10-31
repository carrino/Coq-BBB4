"""Use exact-object audit reuse for future selected batches only."""
import argparse
from pathlib import Path
import subprocess
import sys

import weighted_replay_stream_selected as stream


def main():
    parser = argparse.ArgumentParser(add_help=False)
    parser.add_argument('--audit-cache', type=Path, action='append', default=[])
    args, remaining = parser.parse_known_args()
    sys.argv = [sys.argv[0], *remaining]
    previous_run = subprocess.run

    def run(command, *positional, **keywords):
        if (isinstance(command, list) and len(command) > 1
                and Path(command[1]).name == 'check_weighted_selected_v5.py'):
            cache_args = [item for path in args.audit_cache for item in ('--audit-cache', str(path))]
            command = [command[0], str(Path(__file__).with_name('record_weighted_selected_cached.py')),
                       *cache_args, *command[2:]]
        return previous_run(command, *positional, **keywords)

    subprocess.run = run
    stream.main()


if __name__ == '__main__':
    main()
