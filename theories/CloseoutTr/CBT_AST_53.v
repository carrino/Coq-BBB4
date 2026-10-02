(** Transition-level closeout batch AST_53: Two-phase parity counter over repeated 10 blocks.
    Collected by gen_closeout_tr.py. *)
From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Counters Require Import ParityTokenTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
Import ListNotations.
From BBB4.Census Require Import Deferred_Defs.
From BBB4.CloseoutTr Require Import CloseoutKitTr.
(* spec 1RB1LD_0RC1RA_1LD1RB_1LB0LD *)
Definition r_AST_53_0000 : list (option Trans) :=
 [t1RB;t1LD;t0RC;t1RA;t1LD;t1RB;t1LB;t0LD].
Lemma cv_AST_53_0000 : coversTr (row_to_tm r_AST_53_0000).
Proof.
 apply coversTr_nqh. apply pt_neverqhtr with (w0:=[S1;S1]);try reflexivity.
 exists 27. rewrite <- lift_c0.
 eapply eq_trans;[apply csteps_lift;reflexivity|].
 reflexivity.
Qed.
From BBB4.Counters Require Import CConjugateTr.
Local Definition parity_tm := row_to_tm r_AST_53_0000.
Local Lemma parity_conj_covers : forall dst p flip k0 w0 boot,
  0 < k0 ->
  (forall q s, dst (p q) s = option_map (tconj p flip) (parity_tm q s)) ->
  (forall q, exists q0, p q0 = q) ->
  (match csteps dst boot c0 with
   | Some c => ceqb c (cconj p flip (pt_even k0 w0))
   | None => false end) = true -> coversTr dst.
Proof.
 intros dst p flip k0 w0 boot Hk Htable Honto Hb.
 apply coversTr_nqh.
 apply (cconj_value_neverqhtr parity_tm dst p flip Htable
   (list Sym) pt_next (fun n w => pt_even (n+k0) w) w0).
 - exact Honto.
 - exists boot. destruct (csteps dst boot c0) as [c|] eqn:E;[|discriminate].
   rewrite <- lift_c0,(csteps_lift _ _ _ _ E). f_equal.
   apply ceqb_lift. exact Hb.
 - intros n w. exists (12*(n+k0)+8+pt_uc (S0::w)). split;[|lia].
   replace (S n+k0) with (S (n+k0)) by lia.
   apply pt_lap;reflexivity.
 - intros n w t. destruct (n+k0) as [|k] eqn:E;[lia|].
   apply pt_fire;reflexivity.
Qed.
(* spec 0RB1RD_1LC1RA_1LA0LC_1RA1LC *)
Definition r_AST_53_0001 : list (option Trans) :=
 [t0RB;t1RD;t1LC;t1RA;t1LA;t0LC;t1RA;t1LC].
Local Definition parity_perm2 (q : St) : St :=
 match q with StA=>StD|StB=>StA|StC=>StB|StD=>StC end.
Lemma cv_AST_53_0001 : coversTr (row_to_tm r_AST_53_0001).
Proof.
 apply (parity_conj_covers _ parity_perm2 false 1 [S1;S1] 16).
 - lia.
 - intros [] [];reflexivity.
 - intros [];[exists StB|exists StC|exists StD|exists StA];reflexivity.
 - vm_cast_no_check (eq_refl true).
Qed.
(* spec 1RB0RA_0LC1LD_1RA1LB_1LB1RA *)
Definition r_AST_53_0002 : list (option Trans) :=
 [t1RB;t0RA;t0LC;t1LD;t1RA;t1LB;t1LB;t1RA].
Local Definition parity_perm3 (q : St) : St :=
 match q with StA=>StD|StB=>StB|StC=>StC|StD=>StA end.
Lemma cv_AST_53_0002 : coversTr (row_to_tm r_AST_53_0002).
Proof.
 apply (parity_conj_covers _ parity_perm3 true 1 [] 1).
 - lia.
 - intros [] [];reflexivity.
 - intros [];[exists StD|exists StB|exists StC|exists StA];reflexivity.
 - vm_cast_no_check (eq_refl true).
Qed.

Definition cbtrows_AST_53 : list (list (option Trans)) := [r_AST_53_0000; r_AST_53_0001; r_AST_53_0002].

Lemma cbt_AST_53_covers : Forall coversTr (map row_to_tm cbtrows_AST_53).
Proof. exact (Forall_cons _ cv_AST_53_0000 (Forall_cons _ cv_AST_53_0001 (Forall_cons _ cv_AST_53_0002 (Forall_nil _)))). Qed.
