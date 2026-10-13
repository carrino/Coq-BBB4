#!/usr/bin/env python3
"""Give already-built dependencies of native-compiled targets their native code.

proof-all and proof-tr-all compile their computation closures with
`-native-compiler yes' (coqc, then coqnative) and proof-only files with
`ondemand' (coqc only, no native code).  Make tracks the .vo, not the native
mode it was built in, so a .vo built `ondemand' by one target looks up to date
to the other, and the first native-compiled file that imports it fails:

    Error: Unbound module NBBB4_Checkers_TCyclerN

(proof-all after proof-tr-all in one tree, 2026-10-13.)  This runs coqnative
-- the same step Makefile.coq runs after coqc in `yes' mode -- on every
up-to-date .vo in the targets' dependency closure that has no .cmxs, in
dependency order.  Stale .vo are left for make to rebuild.

Untrusted build tooling: it only produces native code for files Coq has
already checked; it carries no proof weight.

Usage: ensure_native.py TARGET.vo...   (from the repo root).  Without
       .Makefile.coq.d nothing has been built yet, so there is nothing to do.
"""
import os
import re
import subprocess
import sys

DEPFILE = '.Makefile.coq.d'
PREFIX = ('theories', 'BBB4')     # -Q theories BBB4 (_CoqProject)


def native_enabled():
    try:
        out = subprocess.run(['coqc', '-config'], capture_output=True, text=True).stdout
    except OSError:
        return False
    m = re.search(r'^COQ_NATIVE_COMPILER_DEFAULT=(\S+)', out, re.M)
    return bool(m) and m.group(1) != 'no'


def read_deps(path=DEPFILE):
    deps = {}
    for line in open(path):
        head, sep, tail = line.partition(':')
        if not sep:
            continue
        outs = head.split()
        if not outs or not outs[0].endswith('.vo'):
            continue
        deps[outs[0]] = [d for d in tail.split() if d.endswith('.vo')]
    return deps


def cmxs_of(vo):
    d, base = os.path.split(vo[:-3])
    rel = os.path.relpath(d, PREFIX[0])
    parts = [PREFIX[1]] + ([] if rel == '.' else rel.split(os.sep)) + [base]
    return os.path.join(d, '.coq-native', 'N' + '_'.join(parts) + '.cmxs')


def closure(targets, deps):
    order, seen = [], set()

    def visit(v):
        if v in seen:
            return
        seen.add(v)
        for d in deps.get(v, []):
            visit(d)
        order.append(v)

    for t in targets:
        visit(t)
    return order


def up_to_date(vo, deps):
    if not os.path.exists(vo):
        return False
    t = os.path.getmtime(vo)
    src = vo[:-1]
    if os.path.exists(src) and os.path.getmtime(src) > t:
        return False
    return all(os.path.exists(d) and os.path.getmtime(d) <= t for d in deps.get(vo, []))


def main():
    targets = sys.argv[1:]
    if not targets or not os.path.exists(DEPFILE) or not native_enabled():
        return 0
    deps = read_deps()
    done = 0
    for vo in closure(targets, deps):
        if up_to_date(vo, deps) and not os.path.exists(cmxs_of(vo)):
            print('COQNATIVE %s (built without native code)' % vo, flush=True)
            subprocess.run(['coqnative', '-Q', PREFIX[0], PREFIX[1], vo], check=True)
            done += 1
    if done:
        print('ensure_native: native code added for %d existing .vo' % done)
    return 0


if __name__ == '__main__':
    sys.exit(main())
