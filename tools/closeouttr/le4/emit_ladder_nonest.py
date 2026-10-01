#!/usr/bin/env python3
"""`emit_ladder.py` with its nested-program search off (UNTRUSTED; LE4's fast
first pass, `try_emit.py --nonest`).  Same arguments as emit_ladder.py."""
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'ladder'))
import emit_ladder as E  # noqa: E402

E.NEST = False
if __name__ == '__main__':
    sys.argv[0] = E.__file__
    sys.exit(E.main())
