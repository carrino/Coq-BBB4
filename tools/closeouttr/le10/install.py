#!/usr/bin/env python3
"""LE10: install a hand proof as theories/Machines/LoopTr/LP_<spec>.v
(adds the doc comment, drops any Print line, lists it in _CoqProject).

    python3 tools/closeouttr/le10/install.py SPEC PROOF.v DOC.txt
"""
import os, sys
spec, src, doc = sys.argv[1:4]
REPO = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..'))
body = ''.join(l for l in open(src) if not l.startswith('Print Assumptions'))
dst = os.path.join(REPO, 'theories', 'Machines', 'LoopTr', 'LP_%s.v' % spec)
open(dst, 'w').write('(** * LP_%s (SCOPING_INSTR 7.4.LE10)\n\n' % spec + open(doc).read().rstrip() +
                     '\n\n    Hand-stated, kernel-checked.  Axiom footprint: [functional_extensionality_dep]. *)\n' + body)
cp = os.path.join(REPO, '_CoqProject')
lines = open(cp).read().split('\n')
ent = 'theories/Machines/LoopTr/LP_%s.v' % spec
if ent not in lines:
    i = lines.index('theories/Counters/LoopRunTr.v')
    lines.insert(i + 1, ent)
    open(cp, 'w').write('\n'.join(lines))
print(dst)
