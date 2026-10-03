#!/usr/bin/env python3
"""LE10: write a batch boarding rows whose hand-stated proofs live in
theories/Machines/LoopTr/LP_<spec>.v (never-QH: [nqhtr_<spec>]).

    python3 tools/closeouttr/le10/batch.py SPEC [SPEC ...] [--nn NN]
"""
import os
import sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from cbt import write_batch, next_free


def main():
    args = sys.argv[1:]
    nn = None
    if '--nn' in args:
        i = args.index('--nn')
        nn = int(args[i + 1])
        del args[i:i + 2]
    if nn is None:
        nn = next_free('LE10')
    req = ['From BBB4.Machines.LoopTr Require %s.' % ' '.join('LP_' + s for s in args)]
    ents = []
    for s in args:
        m = 'LP_' + s
        ents.append((s, 'apply (coversTr_nqh_at %s.tm_%s); [exact %s.nqhtr_%s | '
                        'intros q s; destruct q, s; reflexivity].' % (m, s, m, s)))
    print(write_batch('LE10', nn, req, ents,
                      blurb='counters with loops of inner counts, hand-stated laps (LoopRunTr)'))


if __name__ == '__main__':
    main()
