#!/usr/bin/env python3
"""Generate theories/Tests/NGramHist_Corruption.v -- the MUST-fail controls.

  1. quasihalter: augmented set CLOSED (NonHalt) but never-QH gate REJECTS
     (the safety!=liveness trap);
  2. halter: rejected;
  3. mutated closure: rejected;
  4. control: plain NGram (no history) MISSES a machine NGramHist catches.
"""
import sys
import nghist_prove as P

COUNTER="0RB---_0LC0RA_0LD---_1RA1LC"   # closes only WITH history; boards never-QH
QH     ="1RB---_0LC1LD_1RC1RD_0LB0LD"   # quasihalter: A quiet at step 0
K,N,T,FUEL = 2,2,40,100000

def gset_lit(s, drop=None):
    ws = sorted(s)
    if drop is not None and 0 <= drop < len(ws):
        ws = ws[:drop] + ws[drop+1:]
    return '[' + ';\n   '.join(P.c_win(g) for g in ws) + ']'

def main():
    rc = P.prove(COUNTER, K, N, T, FUEL)
    assert rc is not None, "counter prover failed"
    gq = P.grow(P.decode(QH), K, N, T, FUEL)
    assert gq is not None, "qh grow failed"
    _, lq, rq, _, _ = gq

    L=[]
    L.append('(* wave-6 NGramHist corruption tests -- MUST-fail controls.')
    L.append('   UNTRUSTED-generated; the Coq kernel re-checks every claim. *)')
    L.append('From Coq Require Import List ZArith.')
    L.append('From BBB4 Require Import BBB4_Statement CTape.')
    L.append('From BBB4.Checkers Require Import NGram NGramHist.')
    L.append('Import ListNotations.\n')

    # --- machines ---
    L.append(P.c_tm(rc['tm'], 'tm_counter'))
    L.append(P.c_tm(P.decode(QH), 'tm_qh'))
    L.append('Definition tm_halt : TM := fun q s =>')
    L.append('  match q, s with StA, S0 => Some (mkTrans S1 DR StB) | _, _ => None end.\n')

    # --- counter data ---
    L.append('Definition lset_c : hgset :=\n  '+gset_lit(rc['lset'])+'.')
    L.append('Definition rset_c : hgset :=\n  '+gset_lit(rc['rset'])+'.')
    L.append('Definition lset_c_mut : hgset :=\n  '+gset_lit(rc['lset'], drop=0)+'.')
    L.append(P.c_cert(rc['cert'], 'cert_c'))

    # --- qh data ---
    L.append('Definition lset_qh : hgset :=\n  '+gset_lit(lq)+'.')
    L.append('Definition rset_qh : hgset :=\n  '+gset_lit(rq)+'.')

    P_ = dict(k=K,n=N,t=T,fuel=FUEL)
    def ex(name, lhs, val):
        L.append('Example {} : {} = {}.'.format(name, lhs, val))
        L.append('Proof. vm_compute. reflexivity. Qed.\n')

    L.append('(* --- Control 4: plain NGram MISSES; NGramHist CATCHES (history load-bearing) --- *)')
    ex('ctl_plain_misses',
       'ngram_check_neverqh tm_counter {n} {t} {fuel} 200'.format(**P_), 'false')
    ex('ctl_hist_closes',
       'ngramhist_closed tm_counter {k} {n} {t} {fuel} lset_c rset_c'.format(**P_), 'true')
    ex('ctl_hist_boards',
       'ngramhist_check_neverqh_lex tm_counter {k} {n} {t} {fuel} lset_c rset_c cert_c'.format(**P_), 'true')

    L.append('(* --- Control 1: quasihalter CLOSES (NonHalt) but never-QH REJECTS (the trap) --- *)')
    ex('qh_closes',
       'ngramhist_closed tm_qh {k} {n} {t} {fuel} lset_qh rset_qh'.format(**P_), 'true')
    ex('qh_rejected',
       'ngramhist_check_neverqh_lex tm_qh {k} {n} {t} {fuel} lset_qh rset_qh (fun _ => [])'.format(**P_), 'false')

    L.append('(* --- Control 2: halter rejected --- *)')
    ex('halt_rejected',
       'ngramhist_check_neverqh_lex tm_halt {k} {n} {t} {fuel} [] [] (fun _ => [])'.format(**P_), 'false')

    L.append('(* --- Control 3: mutated closure (one window dropped) rejected --- *)')
    ex('mut_rejected',
       'ngramhist_check_neverqh_lex tm_counter {k} {n} {t} {fuel} lset_c_mut rset_c cert_c'.format(**P_), 'false')

    out = sys.argv[1] if len(sys.argv)>1 else '/dev/stdout'
    open(out,'w').write('\n'.join(L)+'\n')
    sys.stderr.write('wrote {} (counter nctx={})\n'.format(out, rc['nctx']))

if __name__=='__main__':
    main()
