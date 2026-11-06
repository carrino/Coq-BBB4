#!/usr/bin/env python3
"""Exec a command with at least 64 MiB soft stack, when its hard limit permits.

Only the soft stack limit is raised. Existing higher or unlimited limits are
preserved; a finite hard limit clamps the requested increase.
"""
from __future__ import annotations

import os
import resource
import sys

STACK_BYTES = 64 * 1024 * 1024


def raise_stack_limit() -> None:
    soft, hard = resource.getrlimit(resource.RLIMIT_STACK)
    if soft == resource.RLIM_INFINITY or soft >= STACK_BYTES:
        return
    requested = STACK_BYTES if hard == resource.RLIM_INFINITY else min(STACK_BYTES, hard)
    if requested > soft:
        resource.setrlimit(resource.RLIMIT_STACK, (requested, hard))


def main(argv: list[str] | None = None) -> int:
    args = sys.argv[1:] if argv is None else argv
    if args[:1] == ["--"]:
        args = args[1:]
    if not args:
        print("usage: with_coq_stack.py [--] command [argument ...]", file=sys.stderr)
        return 2
    try:
        raise_stack_limit()
        os.execvp(args[0], args)
    except (OSError, ValueError) as exc:
        print(f"with_coq_stack: {exc}", file=sys.stderr)
        return 1
    return 0  # execvp replaces the process on success.


if __name__ == "__main__":
    raise SystemExit(main())
