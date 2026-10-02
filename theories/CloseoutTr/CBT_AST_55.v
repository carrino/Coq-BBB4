(** Transition-level closeout batch AST_55: Three-phase parity counter over repeated 100 blocks.
    Collected by gen_closeout_tr.py. *)
From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Counters Require Import ParityGateTokenTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
Import ListNotations.
From BBB4.Census Require Import Deferred_Defs.
From BBB4.CloseoutTr Require Import CloseoutKitTr.
Local Definition qggen_source (port:bool) := row_to_tm (if port then [t1RB;t1LD;t0RC;t1RA;t1LC;t1RA;t1LB;t0LD] else [t1RB;t1LD;t0RC;t1RA;t1LD;t1RA;t1LB;t0LD]).
From BBB4.Counters Require Import CConjugateTr.
Local Lemma qggen_conj_covers : forall port dst p flip k0 w0 boot,
  0 < k0 ->
  (forall q s, dst (p q) s = option_map (tconj p flip) ((qggen_source port) q s)) ->
  (forall q, exists q0, p q0 = q) ->
  (match csteps dst boot c0 with
   | Some c => ceqb c (cconj p flip (qg_even k0 w0))
   | None => false end) = true -> coversTr dst.
Proof.
 intros port dst p flip k0 w0 boot Hk Htable Honto Hb.
 apply coversTr_nqh.
 apply (cconj_value_neverqhtr (qggen_source port) dst p flip Htable
   (list Sym) qg_next (fun n w => qg_even (n+k0) w) w0).
 - exact Honto.
 - exists boot. destruct (csteps dst boot c0) as [c|] eqn:E;[|discriminate].
   rewrite <- lift_c0,(csteps_lift _ _ _ _ E). f_equal.
   apply ceqb_lift. exact Hb.
 - intros n w. exists (24*(n+k0)+15+qg_uc (S0::w)). split;[|lia].
   replace (S n+k0) with (S (n+k0)) by lia.
   apply qg_lap with (port:=port);try lia;destruct port;reflexivity.
 - intros n w t. destruct (n+k0) as [|k] eqn:E;[lia|].
   apply qg_fire with (port:=port);destruct port;reflexivity.
Qed.
(* spec 0RB1RD_1LC1RD_1LA0LC_1RA1LC *)
Definition r_AST_55_0000 : list (option Trans) := [t0RB;t1RD;t1LC;t1RD;t1LA;t0LC;t1RA;t1LC].
Local Definition qgp0 (q:St) := match q with StA=>StD|StB=>StA|StC=>StB|StD=>StC end.
Lemma cv_AST_55_0000 : coversTr (row_to_tm r_AST_55_0000).
Proof.
 apply (qggen_conj_covers false _ qgp0 false 1 [S1;S1] 23).
 - lia.
 - intros [] [];reflexivity.
 - intros [];[exists StB|exists StC|exists StD|exists StA];reflexivity.
 - vm_cast_no_check (eq_refl true).
Qed.
(* spec 1RB0RA_0LC1LD_1RA1LD_1LB1RA *)
Definition r_AST_55_0001 : list (option Trans) := [t1RB;t0RA;t0LC;t1LD;t1RA;t1LD;t1LB;t1RA].
Local Definition qgp1 (q:St) := match q with StA=>StD|StB=>StB|StC=>StC|StD=>StA end.
Lemma cv_AST_55_0001 : coversTr (row_to_tm r_AST_55_0001).
Proof.
 apply (qggen_conj_covers false _ qgp1 true 1 [] 1).
 - lia.
 - intros [] [];reflexivity.
 - intros [];[exists StD|exists StB|exists StC|exists StA];reflexivity.
 - vm_cast_no_check (eq_refl true).
Qed.
(* spec 1RB0RA_0LC1LD_1RC1LD_1LB1RA *)
Definition r_AST_55_0002 : list (option Trans) := [t1RB;t0RA;t0LC;t1LD;t1RC;t1LD;t1LB;t1RA].
Local Definition qgp2 (q:St) := match q with StA=>StD|StB=>StB|StC=>StC|StD=>StA end.
Lemma cv_AST_55_0002 : coversTr (row_to_tm r_AST_55_0002).
Proof.
 apply (qggen_conj_covers true _ qgp2 true 1 [] 1).
 - lia.
 - intros [] [];reflexivity.
 - intros [];[exists StD|exists StB|exists StC|exists StA];reflexivity.
 - vm_cast_no_check (eq_refl true).
Qed.

Definition cbtrows_AST_55 : list (list (option Trans)) := [r_AST_55_0000; r_AST_55_0001; r_AST_55_0002].

Lemma cbt_AST_55_covers : Forall coversTr (map row_to_tm cbtrows_AST_55).
Proof. exact (Forall_cons _ cv_AST_55_0000 (Forall_cons _ cv_AST_55_0001 (Forall_cons _ cv_AST_55_0002 (Forall_nil _)))). Qed.
