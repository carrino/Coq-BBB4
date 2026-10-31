"""Use recorded recursive audits in future frozen V4 snapshot batches.

The existing stream scheduling and V4 producer are unchanged. Only their
subprocess entrypoint is redirected to record_weighted_audit.py.
"""
from pathlib import Path
import subprocess

import weighted_replay_stream as stream


def main():
    previous_run = subprocess.run

    def run(command, *args, **kwargs):
        if (isinstance(command, list) and len(command) > 1
                and Path(command[1]).name == 'check_weighted_v4.py'):
            command = [command[0], str(Path(__file__).with_name('record_weighted_audit.py')),
                       *command[2:]]
        return previous_run(command, *args, **kwargs)

    subprocess.run = run
    stream.main()


if __name__ == '__main__':
    main()
