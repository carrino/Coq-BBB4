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
HPATT  ="0RB0LA_0RC1RC_1LD1RD_1LA1RB"   # boards never-QH via a PATTERN-only cert
K,N,T,FUEL = 2,2,40,100000

def patt_only_cands(tm, n):
    """Restrict the prover to HPatt candidates (drop count measures), so the
    resulting cert is genuinely pattern-load-bearing."""
    return [c for c in P._orig_meas_cands(tm, n) if c[0] == 'HPatt']

def mutate_first_hpatt(cert):
    """Return a copy of cert with the FIRST HPatt component's pattern replaced
    by [S0;S0] -- a pattern with NO S1, so pm_ok fails and the component
    denotes a sound no-op (never strict).  The lex check must then REJECT."""
    import copy
    c2 = copy.deepcopy(cert)
    for q in 'ABCD':
        for i, comp in enumerate(c2[q]):
            if comp[0] == 'HPatt':
                _, p, rg, Kk, phi, gate = comp
                c2[q][i] = ('HPatt', [0, 0], rg, Kk, phi, gate)
                return c2
    raise AssertionError("no HPatt component to mutate")

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

    # pattern-only cert for the HPatt controls
    P._orig_meas_cands = P.meas_cands
    P.meas_cands = patt_only_cands
    rp = P.prove(HPATT, K, N, T, FUEL)
    P.meas_cands = P._orig_meas_cands
    assert rp is not None, "HPatt pattern-only prover failed"
    assert any(c[0] == 'HPatt' for q in 'ABCD' for c in rp['cert'][q]), \
        "HPatt cert has no pattern component"
    rp_mut = mutate_first_hpatt(rp['cert'])

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

    # --- HPatt (pattern-measure) data ---
    L.append(P.c_tm(rp['tm'], 'tm_patt'))
    L.append('Definition lset_p : hgset :=\n  '+gset_lit(rp['lset'])+'.')
    L.append('Definition rset_p : hgset :=\n  '+gset_lit(rp['rset'])+'.')
    L.append(P.c_cert(rp['cert'], 'cert_p'))
    L.append(P.c_cert(rp_mut, 'cert_p_mut'))

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

    L.append('(* --- Control 5: HPatt pattern measure load-bearing + MUST-fail mutation ---')
    L.append('   cert_p uses ONLY pattern (HPatt) components; the correct one boards,')
    L.append('   but replacing one pattern [S1;S1] with [S0;S0] (no S1 => pm_ok false =>')
    L.append('   a sound no-op, never strict) makes the lex check REJECT. *)')
    ex('ctl_hpatt_boards',
       'ngramhist_check_neverqh_lex tm_patt {k} {n} {t} {fuel} lset_p rset_p cert_p'.format(**P_), 'true')
    ex('hpatt_mut_rejected',
       'ngramhist_check_neverqh_lex tm_patt {k} {n} {t} {fuel} lset_p rset_p cert_p_mut'.format(**P_), 'false')

    out = sys.argv[1] if len(sys.argv)>1 else '/dev/stdout'
    open(out,'w').write('\n'.join(L)+'\n')
    sys.stderr.write('wrote {} (counter nctx={})\n'.format(out, rc['nctx']))

if __name__=='__main__':
    main()
