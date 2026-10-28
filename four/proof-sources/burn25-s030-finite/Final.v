(** Exact last A and a permanent binary-tape B suffix. *)
From Coq Require Import List Arith Lia NArith.
From BBB24 Require Import Statement Spec CTape Census.
From BBB24Burn25S030Finite Require Import Counter BinaryBridge Trace.
Import ListNotations.
Lemma sf_escape_successor : sf_count 1367354345129%N=S(sf_count 1367354345128%N).
Proof. unfold sf_count;change(N.to_nat(N.succ 1367354345128%N)=S(N.to_nat 1367354345128%N));apply N2Nat.inj_succ. Qed.
Opaque sf_count.
Theorem sf_B_forever : forall k,sf_count 1367354345129%N<=k ->VisitsAt s30_tm StB k.
Proof.
 pose proof sf_after as E;unfold s30_back in E.
 apply(s30_B_forever_from_binary _ _ _ _ (s30_binary_exposed(sf_count 1383582%N))E).
Qed.
Theorem sf_A_quiet : QuietFrom s30_tm StA(sf_count 1367354345129%N).
Proof.
 intros k Hk(c&Ec&Hs);destruct(sf_B_forever k Hk)as(c'&Ec'&Hs').
 rewrite Ec in Ec';injection Ec' as <-;congruence.
Qed.
Theorem sf_last_A_visit : VisitsAt s30_tm StA(sf_count 1367354345128%N).
Proof.
 exists(lift(StA,(repeat S2(sf_count 1383582%N),S3,[S2])));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift;exact sf_before.
Qed.
Theorem sf_last_A : QuietAfter s30_tm StA(sf_count 1367354345128%N).
Proof.
 split;[exact sf_last_A_visit|].
 intros k Hk;apply sf_A_quiet;rewrite sf_escape_successor;lia.
Qed.
Theorem sf_exact_bound : QHBound(sf_count 1367354345129%N)s30_tm.
Proof.
 intros q s[Hv Hquiet];destruct(le_lt_dec(sf_count 1367354345129%N)s);[|lia].
 destruct q.
 - destruct Hv as(c&Ec&Hs);destruct(sf_B_forever s l)as(c'&Ec'&Hs').
   rewrite Ec in Ec';injection Ec' as <-;congruence.
 - exfalso;apply(Hquiet(S s));[lia|apply sf_B_forever;lia].
Qed.
Theorem sf_attains : AttainsSt s30_tm(sf_count 1367354345129%N).
Proof. exists StA,(sf_count 1367354345128%N);split;[exact sf_last_A|symmetry;exact sf_escape_successor]. Qed.
Theorem sf_sound : NonHalt s30_tm /\QHBound(sf_count 2199023255552%N)s30_tm.
Proof.
 split;[exact s30_nonhalt|].
 intros q s H;pose proof(sf_exact_bound q s H)as Hb.
 eapply Nat.le_trans;[exact Hb|apply sf_count_le;easy].
Qed.
Theorem sf_quasihalts : QuasiHaltsSt s30_tm.
Proof.
 exists StA;split.
 - exists 0,InitES;split;reflexivity.
 - exists(sf_count 1367354345129%N);exact sf_A_quiet.
Qed.
Theorem sf_below_champion : QHBound score s30_tm.
Proof.
 intros q s H;pose proof(proj2 sf_sound q s H)as Hb.
 eapply Nat.le_trans;[exact Hb|rewrite sf_score_count;apply sf_count_le;unfold scoreN;vm_compute;discriminate].
Qed.
Print Assumptions sf_exact_bound.
Print Assumptions sf_attains.
