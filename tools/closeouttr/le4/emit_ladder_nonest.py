#!/usr/bin/env python3
"""`emit_ladder.py` without its nested-program SEARCH (UNTRUSTED; LE4's fast
first pass, `try_emit.py --nonest`).  A chain that lands off its target only
by blanks beside a known-empty tail is still wrapped as a one-segment
program ([ceqL]); only `nest.derive_nested`, which costs seconds an arm, is
stubbed out.  Same arguments as emit_ladder.py."""
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'ladder'))
import emit_ladder as E  # noqa: E402

E.nest.derive_nested = lambda *a, **k: None
if __name__ == '__main__':
    sys.argv[0] = E.__file__
    sys.exit(E.main())
