(** Transition closeout: binary reset conjugates with checked boots. *)
From Coq Require Import Arith List.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
From BBB4.Counters Require Import BinaryResetTr CConjugateTr CConjugateReachTr.
From BBB4.Census Require Import Deferred_Defs.
From BBB4.CloseoutTr Require Import CloseoutKitTr CBT_AST_81.
Import ListNotations.
Local Definition src := CBT_AST_81.tm.

Local Lemma progress : forall x:nat*br_value, exists y k,
 0<k /\ stepn src k (lift (br_anchor x))=Some (lift (br_anchor y)).
Proof.
 intros [n [w b]].
 assert (E : exists m v k, 0<k /\ csteps src k (br_anchor (n,(w,b)))=Some (br_anchor (m,v))).
 { apply br_progress;first [exact CBT_AST_81.sw|exact CBT_AST_81.reset|exact CBT_AST_81.finish|reflexivity]. }
 destruct E as (m&v&k&Hk&Ek). exists (m,v),k. split;[exact Hk|apply csteps_lift;exact Ek].
Qed.
Local Lemma fired : forall x t, TriReachTr.tri_reaches_fire src t (br_anchor x).
Proof.
 intros [n [w b]] t.
 assert (E : exists k c, csteps src k (br_anchor (n,(w,b)))=Some c /\ cinstr c=t).
 { apply br_fire;first [exact CBT_AST_81.reset|exact CBT_AST_81.finish|exact CBT_AST_81.fires|reflexivity]. }
 destruct E as (k&c&Ek&Et). exists k,(lift c). split;[apply csteps_lift;exact Ek|rewrite cinstr_lift;exact Et].
Qed.

(* spec 1RB0RD_1LC1LD_1LA0LB_1LB1RA *)
Definition r_AST_82_0000 : list (option Trans) := [t1RB;t0RD;t1LC;t1LD;t1LA;t0LB;t1LB;t1RA].
Local Definition p_0000 (q:St) : St := match q with StA=>StC|StB=>StA|StC=>StB|StD=>StD end.
Lemma cv_AST_82_0000 : coversTr (row_to_tm r_AST_82_0000).
Proof.
 apply coversTr_nqh.
 assert (Htable : forall q s, row_to_tm r_AST_82_0000 (p_0000 q) s =
   option_map (tconj p_0000 true) (src q s)) by (intros [] [];reflexivity).
 apply (cconj_reach_neverqhtr src (row_to_tm r_AST_82_0000) p_0000 true
   Htable (nat*br_value) br_anchor).
 - intros [];[exists StB|exists StC|exists StA|exists StD];reflexivity.
 - exists 12,(1,([],true)).
   assert (E : exists c, csteps (row_to_tm r_AST_82_0000) 12 c0=Some c /\
     ceqb c (cconj p_0000 true (br_anchor (1,([],true))))=true).
   { eexists. split;vm_compute;reflexivity. }
   destruct E as (c&Ec&El). rewrite <-lift_c0.
   rewrite (csteps_lift _ _ _ _ Ec),(ceqb_lift _ _ El). reflexivity.
 - exact progress.
 - exact fired.
Qed.

(* spec 1RB1LD_1RC1RA_1RD0RB_1LB0LA *)
Definition r_AST_82_0001 : list (option Trans) := [t1RB;t1LD;t1RC;t1RA;t1RD;t0RB;t1LB;t0LA].
Local Definition p_0001 (q:St) : St := match q with StA=>StC|StB=>StD|StC=>StB|StD=>StA end.
Lemma cv_AST_82_0001 : coversTr (row_to_tm r_AST_82_0001).
Proof.
 apply coversTr_nqh.
 assert (Htable : forall q s, row_to_tm r_AST_82_0001 (p_0001 q) s =
   option_map (tconj p_0001 false) (src q s)) by (intros [] [];reflexivity).
 apply (cconj_reach_neverqhtr src (row_to_tm r_AST_82_0001) p_0001 false
   Htable (nat*br_value) br_anchor).
 - intros [];[exists StD|exists StC|exists StA|exists StB];reflexivity.
 - exists 23,(1,([S0;S1],false)).
   assert (E : exists c, csteps (row_to_tm r_AST_82_0001) 23 c0=Some c /\
     ceqb c (cconj p_0001 false (br_anchor (1,([S0;S1],false))))=true).
   { eexists. split;vm_compute;reflexivity. }
   destruct E as (c&Ec&El). rewrite <-lift_c0.
   rewrite (csteps_lift _ _ _ _ Ec),(ceqb_lift _ _ El). reflexivity.
 - exact progress.
 - exact fired.
Qed.

(* spec 1RB1RD_1RC0RA_1LA0LD_1RA1LC *)
Definition r_AST_82_0002 : list (option Trans) := [t1RB;t1RD;t1RC;t0RA;t1LA;t0LD;t1RA;t1LC].
Local Definition p_0002 (q:St) : St := match q with StA=>StB|StB=>StC|StC=>StA|StD=>StD end.
Lemma cv_AST_82_0002 : coversTr (row_to_tm r_AST_82_0002).
Proof.
 apply coversTr_nqh.
 assert (Htable : forall q s, row_to_tm r_AST_82_0002 (p_0002 q) s =
   option_map (tconj p_0002 false) (src q s)) by (intros [] [];reflexivity).
 apply (cconj_reach_neverqhtr src (row_to_tm r_AST_82_0002) p_0002 false
   Htable (nat*br_value) br_anchor).
 - intros [];[exists StC|exists StA|exists StB|exists StD];reflexivity.
 - exists 27,(3,([],true)).
   assert (E : exists c, csteps (row_to_tm r_AST_82_0002) 27 c0=Some c /\
     ceqb c (cconj p_0002 false (br_anchor (3,([],true))))=true).
   { eexists. split;vm_compute;reflexivity. }
   destruct E as (c&Ec&El). rewrite <-lift_c0.
   rewrite (csteps_lift _ _ _ _ Ec),(ceqb_lift _ _ El). reflexivity.
 - exact progress.
 - exact fired.
Qed.

Definition cbtrows_AST_82 : list (list (option Trans)) := [r_AST_82_0000;r_AST_82_0001;r_AST_82_0002].
Lemma cbt_AST_82_covers : Forall coversTr (map row_to_tm cbtrows_AST_82).
Proof. constructor;[exact cv_AST_82_0000|]. constructor;[exact cv_AST_82_0001|]. constructor;[exact cv_AST_82_0002|constructor]. Qed.
