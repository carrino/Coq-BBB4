#!/usr/bin/env python3
"""UNTRUSTED emitter for the two NGX boards of docs/WAVE36_MXDYS_FOUR.md.

[tools/nghist/reachst_prove.py] emits a whole board, because on an RST_* row
the fourth state's liveness comes off the shelf ([ReachSt] + one flavour
lemma).  On rows 1 and 4 of the mxdys four it does not: [StD] recurs on a
[Theta(2^width)] schedule and the whole [ReachSt] tier is closed on it
(write-up section 3), so its liveness is a HAND proof living in the board
file itself.

This tool therefore emits only the OTHER half -- the [NGramHist] closure
data ([lset]/[rset]/[cert], with [qext] carrying no abstraction cert) plus
the final [NeverQuasiHaltsSt] theorem -- and appends it to the hand-written
prelude, replacing everything after the MARK line.  Re-running it is
idempotent.

  python3 tools/mxdys4/emit_ngx.py [-k K] [-n N] [-t T] [--fuel F]

Nothing here carries proof weight: the Coq kernel re-runs the checker on
every line emitted (via [vm_compute]), and the liveness premise is an
ordinary theorem.
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..'))
sys.path.insert(0, os.path.join(ROOT, 'tools', 'nghist'))

import nghist_prove as NP                                          # noqa: E402
import reachst_prove as RP                                         # noqa: E402

MARK = '(* --- generated below by tools/mxdys4/emit_ngx.py --- *)'

# (spec, qext, the hand liveness lemma the prelude proves)
ROWS = [
    ('1RB1LC_0LC0RB_1LA1RD_0LA0RD', 'D'),
    ('1RB1LD_1LC1RA_0RB0LC_0RA0LD', 'D'),
]

BODY = '''
(** The [NGramHist] closure at k={k} n={n} t={t} fuel={fuel} ({nctx}
    contexts).  It discharges the liveness of every state but [St{qext}];
    [St{qext}] is [recurD_{nm}] above. *)

Definition lset_{nm} : hgset :=
  {lset}.

Definition rset_{nm} : hgset :=
  {rset}.

{cert}

Theorem nqh_{nm} : NeverQuasiHaltsSt tm_{nm}.
Proof.
  apply (ngramhist_check_neverqh_lex_ext_sound tm_{nm} {k} {n} {t} {fuel}
           lset_{nm} rset_{nm} cert_{nm} St{qext} recurD_{nm}).
  vm_compute. reflexivity.
Qed.
'''


def main():
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument('-k', type=int, default=3)
    ap.add_argument('-n', type=int, default=2)
    ap.add_argument('-t', type=int, default=200)
    ap.add_argument('--fuel', type=int, default=40000)
    ap.add_argument('--outdir', default='theories/Machines/Mxdys4')
    args = ap.parse_args()

    rc = 0
    for mstr, qext in ROWS:
        path = os.path.join(ROOT, args.outdir, 'NGX_' + mstr + '.v')
        if not os.path.exists(path):
            print('MISS %s: no prelude at %s' % (mstr, path))
            rc = 1
            continue
        txt = open(path).read()
        if MARK not in txt:
            print('MISS %s: prelude has no MARK line' % mstr)
            rc = 1
            continue
        res, err = RP.prove_ext(mstr, args.k, args.n, args.t, args.fuel,
                                qext=qext)
        if res is None:
            print('MISS %s: %s' % (mstr, err))
            rc = 1
            continue
        body = BODY.format(
            nm=mstr, qext=qext, k=args.k, n=args.n, t=args.t, fuel=args.fuel,
            nctx=res['nctx'],
            lset=NP.c_gset(res['lset']), rset=NP.c_gset(res['rset']),
            cert=NP.c_cert(res['cert'], 'cert_' + mstr))
        head = txt[:txt.index(MARK) + len(MARK)]
        with open(path, 'w') as f:
            f.write(head + '\n' + body)
        print('OK   %s  nctx=%d  -> %s'
              % (mstr, res['nctx'], os.path.relpath(path, ROOT)))
    return rc


if __name__ == '__main__':
    sys.exit(main())
