"""Give Coq aggregate proofs at least 64 MiB of process stack, then exec."""
from __future__ import annotations

import os
import resource
import sys

STACK_BYTES = 64 * 1024 * 1024


def ensure_stack():
    soft, hard = resource.getrlimit(resource.RLIMIT_STACK)
    if soft == resource.RLIM_INFINITY or soft >= STACK_BYTES:
        return
    if hard != resource.RLIM_INFINITY and hard < STACK_BYTES:
        raise ValueError('Selected Coq build needs a process-stack hard limit of at least 64 MiB')
    resource.setrlimit(resource.RLIMIT_STACK, (STACK_BYTES, hard))


def main():
    if len(sys.argv) < 2:
        raise ValueError('Usage: with_coq_stack.py command [arguments ...]')
    ensure_stack()
    os.execvp(sys.argv[1], sys.argv[1:])


if __name__ == '__main__':
    try:
        main()
    except (OSError, ValueError) as error:
        print(str(error), file=sys.stderr)
        sys.exit(2)
