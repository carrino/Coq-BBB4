From Coq Require Import List Arith Lia Bool NArith.
From BBB24 Require Import Statement Spec CTape Census.
From BBB24Burn33S064 Require Import Core Binary.
Import ListNotations.
Definition sk_runtime:N := 12762141566885339%N.
Definition sk_boundN:N := 18014398509481984%N.
Definition sk_mainfuel:nat := N.to_nat 262144%N.
Theorem sk_computed : sk_run sk_mainfuel 64 0 1 true 3=
 Some(sk_Finish 486158 false sk_runtime).
Proof. vm_compute;reflexivity. Qed.
Theorem sk_prefix : csteps sk_tm(sk_count sk_runtime)c0=Some(sk_DN 486158 false).
Proof. exact(sk_run_sound sk_mainfuel 64 0 1 true 3 486158 false sk_runtime c0 sk_blank_entry sk_computed). Qed.
Lemma sk_score_count : score=sk_count scoreN.
Proof. unfold score,sk_count;reflexivity. Qed.
Lemma sk_bound_count : sk_count sk_boundN=N.to_nat 18014398509481984%N.
Proof. unfold sk_count,sk_boundN;reflexivity. Qed.
Opaque sk_count.
Lemma sk_B_drift : forall t l,exists l',
 csteps sk_tm t(sk_drift l)=Some(sk_drift l').
Proof.
 induction t;intro l.
 - exists l;reflexivity.
 - change(exists l',csteps sk_tm t(sk_drift(S2::l))=Some(sk_drift l')).
   apply IHt.
Qed.
Lemma sk_after_run : forall d l,
 csteps sk_tm d c0=Some(sk_drift l) ->
 forall t,exists l',csteps sk_tm(d+t)c0=Some(sk_drift l').
Proof. intros d l E t;rewrite csteps_add,E;apply sk_B_drift. Qed.
Theorem sk_eventual_B_bound : forall d l,
 csteps sk_tm d c0=Some(sk_drift l) ->NonHalt sk_tm /\ QHBound d sk_tm.
Proof.
 intros d l E.
 assert(HB:forall n,d<=n ->VisitsAt sk_tm StB n).
 {intros n Hn;destruct(sk_after_run d l E(n-d))as(l'&Ek).
  replace(d+(n-d))with n in Ek by lia.
  exists(lift(sk_drift l'));split;[|reflexivity].
  rewrite <-lift_c0;apply csteps_lift;exact Ek. }
 assert(Hnh:NonHalt sk_tm).
 {intros n Hnone;destruct(le_lt_dec d n).
  - destruct(HB n l0)as(c&Ec&_);congruence.
  - pose proof(csteps_lift sk_tm d c0(sk_drift l)E)as E';rewrite lift_c0 in E'.
    destruct(stepn_prefix sk_tm n d InitES(lift(sk_drift l))ltac:(lia)E')as(c&Ec&_);congruence. }
 split;[exact Hnh|].
 intros q s[Hv Hquiet];destruct(le_lt_dec d s);[|lia].
 destruct q.
 - destruct Hv as(c&Ec&Hs);destruct(HB s l0)as(c'&Ec'&Hs');rewrite Ec in Ec'.
   injection Ec' as <-;congruence.
 - exfalso;apply(Hquiet(S s));[lia|apply HB;lia].
Qed.
Theorem sk_sound : NonHalt sk_tm /\ QHBound(sk_count sk_boundN)sk_tm.
Proof.
 destruct(sk_eventual_B_bound _ _ sk_prefix)as[Hnh Hb].
 split;[exact Hnh|].
 intros q s Hq;eapply Nat.le_trans;[exact(Hb q s Hq)|].
 apply sk_count_le;unfold sk_runtime,sk_boundN;vm_compute;discriminate.
Qed.
Theorem sk_B_forever : forall n,sk_count sk_runtime<=n ->VisitsAt sk_tm StB n.
Proof.
 intros n Hn;destruct(sk_after_run _ _ sk_prefix(n-sk_count sk_runtime))as(l&E).
 replace(sk_count sk_runtime+(n-sk_count sk_runtime))with n in E by lia.
 exists(lift(sk_drift l));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift;exact E.
Qed.
Theorem sk_A_quiet : QuietFrom sk_tm StA(sk_count sk_runtime).
Proof.
 intros n Hn(c&Ec&Hs);destruct(sk_B_forever n Hn)as(c'&Ec'&Hs').
 rewrite Ec in Ec';injection Ec' as <-;congruence.
Qed.
Theorem sk_quasihalts : QuasiHaltsSt sk_tm.
Proof.
 exists StA;split.
 - exists 0;exists InitES;split;reflexivity.
 - exists(sk_count sk_runtime);exact sk_A_quiet.
Qed.
Theorem sk_below_champion : QHBound score sk_tm.
Proof.
 intros q s Hq;pose proof(proj2 sk_sound q s Hq)as H.
 eapply Nat.le_trans;[exact H|].
 rewrite sk_score_count;apply sk_count_le.
 unfold sk_boundN,scoreN;vm_compute;discriminate.
Qed.
Print Assumptions sk_sound.
Print Assumptions sk_quasihalts.
