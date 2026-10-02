(** Transition-level closeout batch AST_54: Two-phase parity counter with a C-state carry entry.
    Collected by gen_closeout_tr.py. *)
From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Counters Require Import ParityCTokenTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
Import ListNotations.
From BBB4.Census Require Import Deferred_Defs.
From BBB4.CloseoutTr Require Import CloseoutKitTr.
Local Definition pcgen_row : list (option Trans) := [t1RC;t1LD;t0RC;t1RA;t1LD;t1RB;t1LB;t0LD].
From BBB4.Counters Require Import CConjugateTr.
Local Definition pcgen_tm := row_to_tm pcgen_row.
Local Lemma pcgen_conj_covers : forall dst p flip k0 w0 boot,
  0 < k0 ->
  (forall q s, dst (p q) s = option_map (tconj p flip) (pcgen_tm q s)) ->
  (forall q, exists q0, p q0 = q) ->
  (match csteps dst boot c0 with
   | Some c => ceqb c (cconj p flip (pc_even k0 w0))
   | None => false end) = true -> coversTr dst.
Proof.
 intros dst p flip k0 w0 boot Hk Htable Honto Hb.
 apply coversTr_nqh.
 apply (cconj_value_neverqhtr pcgen_tm dst p flip Htable
   (list Sym) pc_next (fun n w => pc_even (n+k0) w) w0).
 - exact Honto.
 - exists boot. destruct (csteps dst boot c0) as [c|] eqn:E;[|discriminate].
   rewrite <- lift_c0,(csteps_lift _ _ _ _ E). f_equal.
   apply ceqb_lift. exact Hb.
 - intros n w. exists (12*(n+k0)+8+pc_uc (S0::w)). split;[|lia].
   replace (S n+k0) with (S (n+k0)) by lia.
   apply pc_lap;reflexivity.
 - intros n w t. destruct (n+k0) as [|k] eqn:E;[lia|].
   apply pc_fire;reflexivity.
Qed.
(* spec 0RB1RD_1LC1RA_1LA0LC_1RB1LC *)
Definition r_AST_54_0000 : list (option Trans) := [t0RB;t1RD;t1LC;t1RA;t1LA;t0LC;t1RB;t1LC].
Local Definition pcp0 (q:St) := match q with StA=>StD|StB=>StA|StC=>StB|StD=>StC end.
Lemma cv_AST_54_0000 : coversTr (row_to_tm r_AST_54_0000).
Proof.
 apply (pcgen_conj_covers _ pcp0 false 1 [S1] 12).
 - lia.
 - intros [] [];reflexivity.
 - intros [];[exists StB|exists StC|exists StD|exists StA];reflexivity.
 - vm_cast_no_check (eq_refl true).
Qed.
(* spec 1RB0RA_0LC1LD_1RA1LB_1LC1RA *)
Definition r_AST_54_0001 : list (option Trans) := [t1RB;t0RA;t0LC;t1LD;t1RA;t1LB;t1LC;t1RA].
Local Definition pcp1 (q:St) := match q with StA=>StD|StB=>StB|StC=>StC|StD=>StA end.
Lemma cv_AST_54_0001 : coversTr (row_to_tm r_AST_54_0001).
Proof.
 apply (pcgen_conj_covers _ pcp1 true 1 [] 1).
 - lia.
 - intros [] [];reflexivity.
 - intros [];[exists StD|exists StB|exists StC|exists StA];reflexivity.
 - vm_cast_no_check (eq_refl true).
Qed.
(* spec 1RB1LC_1LC1RD_1LD0LC_0RB1RA *)
Definition r_AST_54_0002 : list (option Trans) := [t1RB;t1LC;t1LC;t1RD;t1LD;t0LC;t0RB;t1RA].
Local Definition pcp2 (q:St) := match q with StA=>StA|StB=>StD|StC=>StB|StD=>StC end.
Lemma cv_AST_54_0002 : coversTr (row_to_tm r_AST_54_0002).
Proof.
 apply (pcgen_conj_covers _ pcp2 false 2 [] 4).
 - lia.
 - intros [] [];reflexivity.
 - intros [];[exists StA|exists StC|exists StD|exists StB];reflexivity.
 - vm_cast_no_check (eq_refl true).
Qed.
(* spec 1RB1LC_1RC0RB_0LA1LD_1LA1RB *)
Definition r_AST_54_0003 : list (option Trans) := [t1RB;t1LC;t1RC;t0RB;t0LA;t1LD;t1LA;t1RB].
Local Definition pcp3 (q:St) := match q with StA=>StD|StB=>StC|StC=>StA|StD=>StB end.
Lemma cv_AST_54_0003 : coversTr (row_to_tm r_AST_54_0003).
Proof.
 apply (pcgen_conj_covers _ pcp3 true 1 [S1] 11).
 - lia.
 - intros [] [];reflexivity.
 - intros [];[exists StC|exists StD|exists StB|exists StA];reflexivity.
 - vm_cast_no_check (eq_refl true).
Qed.

Definition cbtrows_AST_54 : list (list (option Trans)) := [r_AST_54_0000; r_AST_54_0001; r_AST_54_0002; r_AST_54_0003].

Lemma cbt_AST_54_covers : Forall coversTr (map row_to_tm cbtrows_AST_54).
Proof. exact (Forall_cons _ cv_AST_54_0000 (Forall_cons _ cv_AST_54_0001 (Forall_cons _ cv_AST_54_0002 (Forall_cons _ cv_AST_54_0003 (Forall_nil _))))). Qed.
