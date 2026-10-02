(** Transition closeout: stack-cube conjugates with independently checked boots. *)
From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape Mirror.
From BBB4.Census Require Import Deferred_Defs.
From BBB4.CloseoutTr Require Import CloseoutKitTr.
From BBB4.Counters Require Import StackCubeTr CConjugateTr CConjugateReachTr.
Import ListNotations.

Local Definition V := (nat * nat * nat * list nat)%type.
Local Definition Cf (x:V) := let '(a,b,r,w) := x in sc_C a b r w.

(* spec 0RB0RD_1RC1LB_0RD0RA_1LD0LB *)
Definition r_AST_78_0000 : list (option Trans) := [t0RB;t0RD;t1RC;t1LB;t0RD;t0RA;t1LD;t0LB].
Local Definition src_0000 := mirror_tm (row_to_tm [t1RB;t1LA;t0RC;t0RD;t1LC;t0LA;t0RA;t0RC]).
Local Definition p_0000 (q:St) : St := match q with StA=>StB|StB=>StC|StC=>StD|StD=>StA end.
Lemma cv_AST_78_0000 : coversTr (row_to_tm r_AST_78_0000).
Proof.
 apply coversTr_nqh.
 assert (Htable : forall q s, row_to_tm r_AST_78_0000 (p_0000 q) s =
   option_map (tconj p_0000 true) (src_0000 q s)) by (intros [] [];reflexivity).
 assert (HD0 : forall L R, csteps src_0000 3 (StD,(S1::L,S0,R)) =
   Some (StB,(L,S1,S1::R))) by (intros;reflexivity).
 apply (cconj_reach_neverqhtr src_0000 (row_to_tm r_AST_78_0000)
   p_0000 true Htable V Cf).
 - intros [];[exists StD|exists StA|exists StB|exists StC];reflexivity.
 - exists 20,(1,0,0,[]).
   assert (E : exists c, csteps (row_to_tm r_AST_78_0000) 20 c0 = Some c /\
     ceqb c (cconj p_0000 true (Cf (1,0,0,[]))) = true).
   { eexists. split;vm_compute;reflexivity. }
   destruct E as (c&Ec&El). rewrite <-lift_c0.
   rewrite (csteps_lift _ _ _ _ Ec), (ceqb_lift _ _ El). reflexivity.
 - intros [[[a b] r] w].
   destruct (sc_progress src_0000 eq_refl eq_refl eq_refl eq_refl
     eq_refl eq_refl eq_refl 3 HD0 w a b r) as (v&x&y&s&k&Hk&Ek).
   exists (x,y,s,v),k. exact (conj Hk Ek).
 - intros [[[a b] r] w] t.
   exact (sc_all_fire src_0000 eq_refl eq_refl eq_refl eq_refl
     eq_refl eq_refl eq_refl 3 HD0 w a b r t).
Qed.

(* spec 1RB0RC_0RC0RA_1LC0LD_1RB1LD *)
Definition r_AST_78_0001 : list (option Trans) := [t1RB;t0RC;t0RC;t0RA;t1LC;t0LD;t1RB;t1LD].
Local Definition src_0001 := mirror_tm (row_to_tm [t1RB;t1LA;t0RC;t0RD;t1LC;t0LA;t1RB;t0RC]).
Local Definition p_0001 (q:St) : St := match q with StA=>StD|StB=>StB|StC=>StC|StD=>StA end.
Lemma cv_AST_78_0001 : coversTr (row_to_tm r_AST_78_0001).
Proof.
 apply coversTr_nqh.
 assert (Htable : forall q s, row_to_tm r_AST_78_0001 (p_0001 q) s =
   option_map (tconj p_0001 true) (src_0001 q s)) by (intros [] [];reflexivity).
 assert (HD0 : forall L R, csteps src_0001 1 (StD,(S1::L,S0,R)) =
   Some (StB,(L,S1,S1::R))) by (intros;reflexivity).
 apply (cconj_reach_neverqhtr src_0001 (row_to_tm r_AST_78_0001)
   p_0001 true Htable V Cf).
 - intros [];[exists StD|exists StB|exists StC|exists StA];reflexivity.
 - exists 19,(1,0,0,[]).
   assert (E : exists c, csteps (row_to_tm r_AST_78_0001) 19 c0 = Some c /\
     ceqb c (cconj p_0001 true (Cf (1,0,0,[]))) = true).
   { eexists. split;vm_compute;reflexivity. }
   destruct E as (c&Ec&El). rewrite <-lift_c0.
   rewrite (csteps_lift _ _ _ _ Ec), (ceqb_lift _ _ El). reflexivity.
 - intros [[[a b] r] w].
   destruct (sc_progress src_0001 eq_refl eq_refl eq_refl eq_refl
     eq_refl eq_refl eq_refl 1 HD0 w a b r) as (v&x&y&s&k&Hk&Ek).
   exists (x,y,s,v),k. exact (conj Hk Ek).
 - intros [[[a b] r] w] t.
   exact (sc_all_fire src_0001 eq_refl eq_refl eq_refl eq_refl
     eq_refl eq_refl eq_refl 1 HD0 w a b r t).
Qed.

Definition cbtrows_AST_78 : list (list (option Trans)) :=
 [r_AST_78_0000;r_AST_78_0001].
Lemma cbt_AST_78_covers : Forall coversTr (map row_to_tm cbtrows_AST_78).
Proof. constructor;[exact cv_AST_78_0000|]. constructor;[exact cv_AST_78_0001|constructor]. Qed.
