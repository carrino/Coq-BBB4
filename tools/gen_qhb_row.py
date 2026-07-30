#!/usr/bin/env python3
"""UNTRUSTED emitter: one QHBound board per row, for a residue QUASIHALTER.

`gen_qhbound_wrap.py` batches many machines into `QHBWrap_NN.v` files carrying
the census-grade triple.  A row leaving the CLOSEOUT residue wants the
explicit-bound stage shape instead -- `iqh_le B tm`, which
`tools/closeout/inventory.py` recognises as kind `iqhle:<B>` and admits up to
`B_board` = 66,349 -- and it wants its own file, so the board reads as a
statement about that machine.

The certificate is `Checkers/Wrap.ngram_check_qhbound`: wrap the quiet state to
a halt, close the n-gram abstraction of the configuration at index `t`, and
check that closure is halt-free and per-state ACYCLIC.  Halt-free gives
`NonHalt`; acyclicity of every appearing state's own avoiding subgraph gives
liveness, so no state other than the wrapped one can be quiet; and the wrapped
state's last visit is exhibited concretely at `s < t`.  That is `QHBound (S t)`.

Find `(q, s, n, t)` with `sweep_qhbound_deep.py`, which reads `t` off the
machine's measured last-visit index instead of from a fixed candidate list.

Usage
  gen_qhb_row.py SPEC QUIET_STATE S N T [--note TEXT] [--out DIR]
"""
import argparse
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, '..'))
sys.path.insert(0, HERE)

import gen_residue_wrap as gw                                      # noqa: E402

HEAD = '''(** * QHB_@ID@: machine @SPEC@, boarded as a QUASIHALTER.

    Emitted by tools/gen_qhb_row.py (UNTRUSTED emitter; the Coq kernel re-runs
    the checker below).@NOTE@

    [Checkers/Wrap.ngram_check_qhbound] is the decider: it wraps [St@Q@] to a
    halt, closes the @N@-gram abstraction of the configuration at index @T@
    (@NSEEN@ contexts), and checks that closure is halt-free and per-state
    ACYCLIC.  Halt-free gives [NonHalt]; acyclicity of every appearing state's
    own avoiding subgraph gives liveness, so no state other than [St@Q@] can be
    quiet; and [St@Q@]'s last visit is exhibited concretely at @S@ < @T@.
    Together that is [QHBound @B@], well inside the closeout's [B_board] =
    66,349.

    Axiom footprint: [functional_extensionality_dep] only, inherited from the
    imports; the certificate itself is one [vm_compute]. *)
From Coq Require Import Arith Lia List ZArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Census Require Import TNF_QH.
From BBB4.Checkers Require Import NGram Wrap.
Import ListNotations.

(** @SPEC@ *)
Definition tm_qhb_@ID@ : TM := fun q s =>
  match q, s with
@TABLE@  end.

(** The closeout's explicit-bound stage entry (kind [iqh_le]). *)
Definition iqh_le (B : nat) (tm : TM) : Prop :=
  NonHalt tm /\\ QHBound B tm /\\ QuasiHaltsSt tm.

Theorem iqhle_@ID@ : iqh_le @B@ tm_qhb_@ID@.
Proof.
  unfold iqh_le, QHBound.
  apply (ngram_check_qhbound_sound _ St@Q@ @S@ @N@ @T@ @FUEL@ @ROUNDS@).
  vm_compute. reflexivity.
Qed.

Print Assumptions iqhle_@ID@.
'''


def table(spec):
    """The transition table in the spelling `inventory.py` parses."""
    rows = []
    for si, part in enumerate(spec.split('_')):
        for y in range(2):
            e = part[3 * y:3 * y + 3]
            st = 'St' + 'ABCD'[si]
            rows.append('  | %s, S%d => None' % (st, y) if e == '---' else
                        '  | %s, S%d => Some (mkTrans S%s D%s St%s)'
                        % (st, y, e[0], e[1], e[2]))
    return '\n'.join(rows) + '\n'


def render(spec, q, s, n, t, note=''):
    sz = gw.closure_sizes(spec, ord(q) - 65, n, t)
    if sz is None:
        raise SystemExit('closure does not close for %s q=%s n=%d t=%d'
                         % (spec, q, n, t))
    nseen, nl, nr = sz
    reps = {'@ID@': spec, '@SPEC@': spec, '@Q@': q, '@S@': str(s),
            '@N@': str(n), '@T@': str(t), '@B@': str(t + 1),
            '@FUEL@': str(8 * nseen + 64), '@ROUNDS@': str(nl + nr + 4),
            '@NSEEN@': str(nseen), '@TABLE@': table(spec),
            '@NOTE@': ('\n\n    ' + note) if note else ''}
    out = HEAD
    for _ in range(3):
        for k, v in reps.items():
            out = out.replace(k, v)
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('spec')
    ap.add_argument('quiet_state')
    ap.add_argument('s', type=int)
    ap.add_argument('n', type=int)
    ap.add_argument('t', type=int)
    ap.add_argument('--note', default='')
    ap.add_argument('--out',
                    default=os.path.join(REPO, 'theories', 'Machines',
                                         'Counters'))
    a = ap.parse_args()
    path = os.path.join(a.out, 'QHB_%s.v' % a.spec)
    with open(path, 'w') as f:
        f.write(render(a.spec, a.quiet_state.upper(), a.s, a.n, a.t, a.note))
    print('wrote %s  (QHBound %d)' % (path, a.t + 1))
    return 0


if __name__ == '__main__':
    sys.exit(main())
