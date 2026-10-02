(** Transition-level closeout batch AST_50: token machines with different
    initial-state boots.  Finite runs and liveness are transported through
    state permutations and optional reflection by CConjugateTr. *)
From Coq Require Import Arith Lia List Bool.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Census Require Import Deferred_Defs.
From BBB4.CloseoutTr Require Import CloseoutKitTr CBT_AST_04 CBT_AST_30.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
From BBB4.Counters Require Import MutualTokenTr MovingTokenTr TokenLapTr CConjugateTr.
Import ListNotations.

Local Definition src0 := row_to_tm r_AST_04_0000.
Local Definition srcm (slow : bool) :=
  row_to_tm (if slow then r_AST_30_0001 else r_AST_30_0000).
Local Definition kc (slow : bool) := if slow then 3 else 1.

Local Lemma src0_lap : forall k w,
  csteps src0 (18*k+44+6*mt_depth w) (tkl_anchor k w) =
  Some (tkl_anchor (k+2) (mt_succ w)).
Proof. apply token_lap; reflexivity. Qed.
Local Lemma src0_fire : forall k w t,
  exists j c, csteps src0 j (tkl_anchor k w) = Some c /\ cinstr c = t.
Proof. apply token_lap_fire; reflexivity. Qed.
Local Lemma srcm_lap : forall slow k w,
  csteps (srcm slow) (mv_fcost (kc slow) w+(12*k+12)) (mvl_anchor k w) =
  Some (mvl_anchor (S k) (mv_f w)).
Proof. intro slow; destruct slow; apply moving_lap; reflexivity. Qed.
Local Lemma srcm_fire : forall slow k w t,
  exists j c, csteps (srcm slow) j (mvl_anchor k w) = Some c /\ cinstr c = t.
Proof. intro slow; destruct slow.
  - apply moving_lap_fire with (kc:=3); reflexivity.
  - apply moving_lap_fire with (kc:=1); reflexivity.
Qed.

Local Lemma primary_conj_cover : forall dst p flip k0 boot,
  (forall q s, dst (p q) s = option_map (tconj p flip) (src0 q s)) ->
  (forall q, exists q0, p q0 = q) ->
  (match csteps dst boot c0 with
   | Some c => ceqb c (cconj p flip (tkl_anchor k0 []))
   | None => false end) = true -> coversTr dst.
Proof.
  intros dst p flip k0 boot Htable Honto Hboot. apply coversTr_nqh.
  apply (cconj_value_neverqhtr src0 dst p flip Htable (list mt_digit) mt_succ
    (fun n w => tkl_anchor (2*n+k0) w) []).
  - exact Honto.
  - exists boot. destruct (csteps dst boot c0) as [c|] eqn:E; [|discriminate].
    rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal.
    apply ceqb_lift. exact Hboot.
  - intros n w. exists (18*(2*n+k0)+44+6*mt_depth w). split; [|lia].
    replace (2*S n+k0) with ((2*n+k0)+2) by lia. apply src0_lap.
  - intros n w t. apply src0_fire.
Qed.

Local Lemma moving_conj_cover : forall slow dst p flip k0 boot,
  (forall q s, dst (p q) s = option_map (tconj p flip) (srcm slow q s)) ->
  (forall q, exists q0, p q0 = q) ->
  (match csteps dst boot c0 with
   | Some c => ceqb c (cconj p flip (mvl_anchor k0 []))
   | None => false end) = true -> coversTr dst.
Proof.
  intros slow dst p flip k0 boot Htable Honto Hboot. apply coversTr_nqh.
  apply (cconj_value_neverqhtr (srcm slow) dst p flip Htable (list Sym) mv_f
    (fun n w => mvl_anchor (n+k0) w) []).
  - exact Honto.
  - exists boot. destruct (csteps dst boot c0) as [c|] eqn:E; [|discriminate].
    rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal.
    apply ceqb_lift. exact Hboot.
  - intros n w. exists (mv_fcost (kc slow) w+(12*(n+k0)+12)). split; [|lia].
    replace (S n+k0) with (S (n+k0)) by lia. apply srcm_lap.
  - intros n w t. apply srcm_fire.
Qed.

(* spec 0RB0RA_1RC1RD_0LD0LC_1RA1LC *)
Definition r_AST_50_0000 : list (option Trans) :=
  [t0RB;t0RA;t1RC;t1RD;t0LD;t0LC;t1RA;t1LC].
Local Definition p_AST_50_0000 (q : St) : St :=
  match q with StA => StC | StB => StD | StC => StA | StD => StB end.
Lemma cv_AST_50_0000 : coversTr (row_to_tm r_AST_50_0000).
Proof.
  apply (primary_conj_cover (row_to_tm r_AST_50_0000) p_AST_50_0000 true 2 26).
  - intros q s; destruct q,s; reflexivity.
  - intro q; destruct q; [exists StC | exists StD | exists StA | exists StB]; reflexivity.
  - reflexivity.
Qed.

(* spec 1RB1LD_0RC0RB_1RD1RA_0LA0LD *)
Definition r_AST_50_0001 : list (option Trans) :=
  [t1RB;t1LD;t0RC;t0RB;t1RD;t1RA;t0LA;t0LD].
Local Definition p_AST_50_0001 (q : St) : St :=
  match q with StA => StD | StB => StA | StC => StB | StD => StC end.
Lemma cv_AST_50_0001 : coversTr (row_to_tm r_AST_50_0001).
Proof.
  apply (primary_conj_cover (row_to_tm r_AST_50_0001) p_AST_50_0001 true 1 12).
  - intros q s; destruct q,s; reflexivity.
  - intro q; destruct q; [exists StB | exists StC | exists StD | exists StA]; reflexivity.
  - reflexivity.
Qed.

(* spec 1RB1RC_0LC0LB_1RD1LB_0RA0RD *)
Definition r_AST_50_0002 : list (option Trans) :=
  [t1RB;t1RC;t0LC;t0LB;t1RD;t1LB;t0RA;t0RD].
Local Definition p_AST_50_0002 (q : St) : St :=
  match q with StA => StB | StB => StC | StC => StD | StD => StA end.
Lemma cv_AST_50_0002 : coversTr (row_to_tm r_AST_50_0002).
Proof.
  apply (primary_conj_cover (row_to_tm r_AST_50_0002) p_AST_50_0002 true 2 25).
  - intros q s; destruct q,s; reflexivity.
  - intro q; destruct q; [exists StD | exists StA | exists StB | exists StC]; reflexivity.
  - reflexivity.
Qed.

(* spec 0RB1RA_1LC1RD_0LD0LC_1RA1LC *)
Definition r_AST_50_0003 : list (option Trans) :=
  [t0RB;t1RA;t1LC;t1RD;t0LD;t0LC;t1RA;t1LC].
Local Definition p_AST_50_0003 (q : St) : St :=
  match q with StA => StC | StB => StD | StC => StA | StD => StB end.
Lemma cv_AST_50_0003 : coversTr (row_to_tm r_AST_50_0003).
Proof.
  apply (moving_conj_cover false (row_to_tm r_AST_50_0003) p_AST_50_0003 true 2 22).
  - intros q s; destruct q,s; reflexivity.
  - intro q; destruct q; [exists StC | exists StD | exists StA | exists StB]; reflexivity.
  - reflexivity.
Qed.

(* spec 1RB1LC_0RC0RB_1LD1RB_0LA1LD *)
Definition r_AST_50_0004 : list (option Trans) :=
  [t1RB;t1LC;t0RC;t0RB;t1LD;t1RB;t0LA;t1LD].
Local Definition p_AST_50_0004 (q : St) : St :=
  match q with StA => StB | StB => StC | StC => StD | StD => StA end.
Lemma cv_AST_50_0004 : coversTr (row_to_tm r_AST_50_0004).
Proof.
  apply (moving_conj_cover false (row_to_tm r_AST_50_0004) p_AST_50_0004 false 2 21).
  - intros q s; destruct q,s; reflexivity.
  - intro q; destruct q; [exists StD | exists StA | exists StB | exists StC]; reflexivity.
  - reflexivity.
Qed.

(* spec 1RB1LD_0RC1RB_1LD1RA_0LA0LD *)
Definition r_AST_50_0005 : list (option Trans) :=
  [t1RB;t1LD;t0RC;t1RB;t1LD;t1RA;t0LA;t0LD].
Local Definition p_AST_50_0005 (q : St) : St :=
  match q with StA => StD | StB => StA | StC => StB | StD => StC end.
Lemma cv_AST_50_0005 : coversTr (row_to_tm r_AST_50_0005).
Proof.
  apply (moving_conj_cover false (row_to_tm r_AST_50_0005) p_AST_50_0005 true 1 10).
  - intros q s; destruct q,s; reflexivity.
  - intro q; destruct q; [exists StB | exists StC | exists StD | exists StA]; reflexivity.
  - reflexivity.
Qed.

(* spec 1RB1LC_0RC0RB_1LD1RB_0LA0RA *)
Definition r_AST_50_0006 : list (option Trans) :=
  [t1RB;t1LC;t0RC;t0RB;t1LD;t1RB;t0LA;t0RA].
Local Definition p_AST_50_0006 (q : St) : St :=
  match q with StA => StB | StB => StC | StC => StD | StD => StA end.
Lemma cv_AST_50_0006 : coversTr (row_to_tm r_AST_50_0006).
Proof.
  apply (moving_conj_cover true (row_to_tm r_AST_50_0006) p_AST_50_0006 false 2 21).
  - intros q s; destruct q,s; reflexivity.
  - intro q; destruct q; [exists StD | exists StA | exists StB | exists StC]; reflexivity.
  - reflexivity.
Qed.

(* spec 1RB1LD_0RC0LC_1LD1RA_0LA0LD *)
Definition r_AST_50_0007 : list (option Trans) :=
  [t1RB;t1LD;t0RC;t0LC;t1LD;t1RA;t0LA;t0LD].
Local Definition p_AST_50_0007 (q : St) : St :=
  match q with StA => StD | StB => StA | StC => StB | StD => StC end.
Lemma cv_AST_50_0007 : coversTr (row_to_tm r_AST_50_0007).
Proof.
  apply (moving_conj_cover true (row_to_tm r_AST_50_0007) p_AST_50_0007 true 1 10).
  - intros q s; destruct q,s; reflexivity.
  - intro q; destruct q; [exists StB | exists StC | exists StD | exists StA]; reflexivity.
  - reflexivity.
Qed.

Definition cbtrows_AST_50 : list (list (option Trans)) :=
  [r_AST_50_0000;r_AST_50_0001;r_AST_50_0002;r_AST_50_0003;r_AST_50_0004;r_AST_50_0005;r_AST_50_0006;r_AST_50_0007].

Lemma cbt_AST_50_covers : Forall coversTr (map row_to_tm cbtrows_AST_50).
Proof.
  constructor; [exact cv_AST_50_0000|].
  constructor; [exact cv_AST_50_0001|].
  constructor; [exact cv_AST_50_0002|].
  constructor; [exact cv_AST_50_0003|].
  constructor; [exact cv_AST_50_0004|].
  constructor; [exact cv_AST_50_0005|].
  constructor; [exact cv_AST_50_0006|].
  constructor; [exact cv_AST_50_0007|].
  constructor.
Qed.
