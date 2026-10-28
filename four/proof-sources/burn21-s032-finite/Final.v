(** Eventual permanent B motion, exact last-A score, and a convenient2^56
    upper bound. The trace supplies a symbolic tape, never a huge list. *)
From Coq Require Import List Arith Lia NArith.
From BBB24 Require Import Statement Spec CTape Census.
From BBB24Burn21S032Finite Require Import CutMacros BinaryBridge Trace.
Import ListNotations.
Lemma sf_escape_successor : sf_count 67093892759901295%N=S(sf_count 67093892759901294%N).
Proof. unfold sf_count;change(N.to_nat(N.succ 67093892759901294%N)=S(N.to_nat 67093892759901294%N));apply N2Nat.inj_succ. Qed.
Opaque sf_count.
Theorem sf_B_forever : forall k,sf_count 67093892759901295%N<=k ->VisitsAt sc_tm StB k.
Proof. apply(sf_B_forever_from_escape _ _ sf_escape). Qed.
Theorem sf_A_quiet : QuietFrom sc_tm StA(sf_count 67093892759901295%N).
Proof.
 intros k Hk(c&Ec&Hs);destruct(sf_B_forever k Hk)as(c'&Ec'&Hs').
 rewrite Ec in Ec';injection Ec' as <-;congruence.
Qed.
Theorem sf_last_A_visit : VisitsAt sc_tm StA(sf_count 67093892759901294%N).
Proof.
 exists(lift(sc_Q(sf_count 530843044%N)[S3]));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift;exact sf_before_escape.
Qed.
Theorem sf_last_A : QuietAfter sc_tm StA(sf_count 67093892759901294%N).
Proof.
 split;[exact sf_last_A_visit|].
 intros k Hk;apply sf_A_quiet;rewrite sf_escape_successor;lia.
Qed.
Theorem sf_exact_bound : QHBound(sf_count 67093892759901295%N)sc_tm.
Proof. apply(sf_bound_from_escape _ _ sf_escape). Qed.
Theorem sf_attains : AttainsSt sc_tm(sf_count 67093892759901295%N).
Proof. exists StA,(sf_count 67093892759901294%N);split;[exact sf_last_A|symmetry;exact sf_escape_successor]. Qed.
Theorem sf_sound : NonHalt sc_tm /\ QHBound(sf_count 72057594037927936%N)sc_tm.
Proof.
 split;[exact sf_nonhalt|].
 intros q s H;pose proof(sf_exact_bound q s H)as Hb.
 eapply Nat.le_trans;[exact Hb|apply sf_count_le;easy].
Qed.
Theorem sf_quasihalts : QuasiHaltsSt sc_tm.
Proof.
 exists StA;split.
 - exists 0,InitES;split;reflexivity.
 - exists(sf_count 67093892759901295%N);exact sf_A_quiet.
Qed.
Theorem sf_below_champion : QHBound score sc_tm.
Proof.
 intros q s H;pose proof(proj2 sf_sound q s H)as Hb.
 eapply Nat.le_trans;[exact Hb|rewrite sf_score_count;apply sf_count_le;unfold scoreN;vm_compute;discriminate].
Qed.
Print Assumptions sf_exact_bound.
Print Assumptions sf_attains.
Print Assumptions sf_below_champion.
