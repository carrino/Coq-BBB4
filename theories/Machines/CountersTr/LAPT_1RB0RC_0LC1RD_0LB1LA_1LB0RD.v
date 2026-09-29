(** * LAPT_1RB0RC_0LC1RD_0LB1LA_1LB0RD: TRANSITION-LEVEL board for machine 1RB0RC_0LC1RD_0LB1LA_1LB0RD, boarded by CERTIFICATE.

    Auto-emitted by tools/counters/emit_lapcert.py (UNTRUSTED emitter; the Coq
    kernel re-runs the checker on every line below).  Left-growth binary
    counter under the Kp digit alphabet (KpCounter.v), anchored at

      Cc p = (StD, (Kp p ++ [S0], S0, [S1;S1]))

    The lap is DATA, not a proof script: each branch is a list of steps for
    [Checkers/LapDecider.v], run by the kernel through [vm_compute] and
    discharged by the single theorem [srun_sound].

      interior  (cview p = (j, Some q0)):  split mod 2, 2 cases steps
      overflow  (cview p = (S j, None)):   split mod 2, 4 cases

    The interior branch closes EXACTLY (which is what feeds
    [LapCertGlue.reach_ovf]); the overflow branch closes one blank short of
    the anchor tail, hence up to [lift].

    Differentially validated against the raw simulator on BOTH branches --
    step counts AND exact configurations -- for 198 anchors (overflow split mod 2).
    Axiom footprint: [functional_extensionality_dep] (via [CTape.lift]). *)
From Coq Require Import Arith Lia Bool List PArith Wellfounded.
From BBB4 Require Import BBB4_Statement CTape Mirror.
From Coq Require Import FunctionalExtensionality.
From BBB4.Counters Require Import WTape LapGlue LapGlueQH LapGlueAbs
                                  MonoCounter JpCounter KpCounter LapCertGlue.
From BBB4.Census Require Import TNF_QH.
From BBB4.Checkers Require Import LapDecider.
From BBB4 Require Import BBBT4_Statement.
From BBB4.Checkers Require Import WrapTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
From BBB4.Counters Require Import LapGlueTr.
From BBB4.CensusTr Require Import TNF_QHTr.
Import ListNotations.

Definition mk_1RB0RC_0LC1RD_0LB1LA_1LB0RD (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_1RB0RC_0LC1RD_0LB1LA_1LB0RD.

(** 1RB0RC_0LC1RD_0LB1LA_1LB0RD *)
(** 1RB0RC_0LC1RD_0LB1LA_1LB0RD -- the real machine (its counter grows RIGHT). *)
Definition tm_1RB0RC_0LC1RD_0LB1LA_1LB0RD : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S0 DR StC
  | StB, S0 => mk S0 DL StC | StB, S1 => mk S1 DR StD
  | StC, S0 => mk S0 DL StB | StC, S1 => mk S1 DL StA
  | StD, S0 => mk S1 DL StB | StD, S1 => mk S0 DR StD end.

(** Its mirror 1LB0LC_0RC1LD_0RB1RA_1RB0LD: the same counter grown leftward.  Every
    lemma below runs on the MIRRORED table;
    [Mirror.mirror_never_qh] transfers the conclusion back. *)
Definition tmm_1RB0RC_0LC1RD_0LB1LA_1LB0RD : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DL StB | StA, S1 => mk S0 DL StC
  | StB, S0 => mk S0 DR StC | StB, S1 => mk S1 DL StD
  | StC, S0 => mk S0 DR StB | StC, S1 => mk S1 DR StA
  | StD, S0 => mk S1 DR StB | StD, S1 => mk S0 DL StD end.
(** the instructions the certificate claims NEVER fire; the lap
    argument runs on the machine WRAPPED at them
    ([WrapTr.tm_wrap_trs]), so a pinned instruction firing would
    halt it and every [srun] below would fail. *)
Definition pins_1RB0RC_0LC1RD_0LB1LA_1LB0RD : list Instr := [].
Definition tmw_1RB0RC_0LC1RD_0LB1LA_1LB0RD : TM := tm_wrap_trs tmm_1RB0RC_0LC1RD_0LB1LA_1LB0RD pins_1RB0RC_0LC1RD_0LB1LA_1LB0RD.
Local Notation tm := tmw_1RB0RC_0LC1RD_0LB1LA_1LB0RD.

Lemma mirror_ok_1RB0RC_0LC1RD_0LB1LA_1LB0RD : mirror_tm tm_1RB0RC_0LC1RD_0LB1LA_1LB0RD = tmm_1RB0RC_0LC1RD_0LB1LA_1LB0RD.
Proof.
  apply functional_extensionality; intro q;
    apply functional_extensionality; intro b; destruct q, b; reflexivity.
Qed.

Definition Cc_1RB0RC_0LC1RD_0LB1LA_1LB0RD (p : positive) : cconf := (StD, (Kp p ++ [S0], S0, [S1;S1])).
Local Notation Cc := Cc_1RB0RC_0LC1RD_0LB1LA_1LB0RD.

(** ** The certificate *)

(** j = 2*i + 0 *)
Definition P0_1RB0RC_0LC1RD_0LB1LA_1LB0RD0 : sconf := mkC StD (mkS [] [S1;S1] 1 0 [S0]) S0 (mkS [S1;S1] [] 0 0 []).
Definition P0_1RB0RC_0LC1RD_0LB1LA_1LB0RD1 : sconf := mkC StD (mkS [] [S0;S0] 1 0 [S1]) S0 (mkS [S1;S1] [] 0 0 []).
Definition chp0_1RB0RC_0LC1RD_0LB1LA_1LB0RD : list lstep := [SWin 2; SCycL 2 0; SWin 2; SCycR 2; SWin 6].

Lemma run_p0_1RB0RC_0LC1RD_0LB1LA_1LB0RD : srun tm false true chp0_1RB0RC_0LC1RD_0LB1LA_1LB0RD P0_1RB0RC_0LC1RD_0LB1LA_1LB0RD0 = Some (P0_1RB0RC_0LC1RD_0LB1LA_1LB0RD1, 4, 10).
Proof. vm_compute. reflexivity. Qed.

(** j = 2*i + 1 *)
Definition P1_1RB0RC_0LC1RD_0LB1LA_1LB0RD0 : sconf := mkC StD (mkS [] [S1;S1] 1 0 [S1;S0]) S0 (mkS [S1;S1] [] 0 0 []).
Definition P1_1RB0RC_0LC1RD_0LB1LA_1LB0RD1 : sconf := mkC StD (mkS [] [S0;S0] 1 0 [S0;S1]) S0 (mkS [S1;S1] [] 0 0 []).
Definition chp1_1RB0RC_0LC1RD_0LB1LA_1LB0RD : list lstep := [SWin 2; SCycL 2 0; SWin 4; SCycR 2; SWin 2].

Lemma run_p1_1RB0RC_0LC1RD_0LB1LA_1LB0RD : srun tm false true chp1_1RB0RC_0LC1RD_0LB1LA_1LB0RD P1_1RB0RC_0LC1RD_0LB1LA_1LB0RD0 = Some (P1_1RB0RC_0LC1RD_0LB1LA_1LB0RD1, 4, 8).
Proof. vm_compute. reflexivity. Qed.

Definition B0_1RB0RC_0LC1RD_0LB1LA_1LB0RD : sconf := mkC StD (mkS [S1;S1;S1] [S1;S1] 1 0 [S0]) S0 (mkS [S1;S1] [] 0 0 []).
Definition B1_1RB0RC_0LC1RD_0LB1LA_1LB0RD : sconf := mkC StD (mkS [S0;S0;S0] [S0;S0] 1 0 [S1]) S0 (mkS [S1;S1] [] 0 0 []).
(** j = 2*i + 2 *)
Definition O0_1RB0RC_0LC1RD_0LB1LA_1LB0RD0 : sconf := mkC StD (mkS [S1;S1;S1] [S1;S1] 1 0 [S0]) S0 (mkS [S1;S1] [] 0 0 []).
Definition O0_1RB0RC_0LC1RD_0LB1LA_1LB0RD1 : sconf := mkC StD (mkS [S0;S0;S0] [S0;S0] 1 0 [S1]) S0 (mkS [S1;S1] [] 0 0 []).
Definition cho0_1RB0RC_0LC1RD_0LB1LA_1LB0RD : list lstep := [SWin 5; SCycL 2 0; SWin 2; SCycR 2; SWin 5].

Lemma run_o0_1RB0RC_0LC1RD_0LB1LA_1LB0RD : srun tm true true cho0_1RB0RC_0LC1RD_0LB1LA_1LB0RD O0_1RB0RC_0LC1RD_0LB1LA_1LB0RD0 = Some (O0_1RB0RC_0LC1RD_0LB1LA_1LB0RD1, 4, 12).
Proof. vm_compute. reflexivity. Qed.

(** j = 0 (concrete) *)
Definition O1_1RB0RC_0LC1RD_0LB1LA_1LB0RD0 : sconf := mkC StD (mkS [S1;S0] [] 0 0 []) S0 (mkS [S1;S1] [] 0 0 []).
Definition O1_1RB0RC_0LC1RD_0LB1LA_1LB0RD1 : sconf := mkC StD (mkS [S0;S1] [] 0 0 []) S0 (mkS [S1;S1] [] 0 0 []).
Definition cho1_1RB0RC_0LC1RD_0LB1LA_1LB0RD : list lstep := [SWin 8].

Lemma run_o1_1RB0RC_0LC1RD_0LB1LA_1LB0RD : srun tm true true cho1_1RB0RC_0LC1RD_0LB1LA_1LB0RD O1_1RB0RC_0LC1RD_0LB1LA_1LB0RD0 = Some (O1_1RB0RC_0LC1RD_0LB1LA_1LB0RD1, 0, 8).
Proof. vm_compute. reflexivity. Qed.

(** j = 2*i + 3 *)
Definition O2_1RB0RC_0LC1RD_0LB1LA_1LB0RD0 : sconf := mkC StD (mkS [S1;S1;S1;S1] [S1;S1] 1 0 [S0]) S0 (mkS [S1;S1] [] 0 0 []).
Definition O2_1RB0RC_0LC1RD_0LB1LA_1LB0RD1 : sconf := mkC StD (mkS [S0;S0;S0;S0] [S0;S0] 1 0 [S1]) S0 (mkS [S1;S1] [] 0 0 []).
Definition cho2_1RB0RC_0LC1RD_0LB1LA_1LB0RD : list lstep := [SWin 6; SCycL 2 0; SWin 2; SCycR 2; SWin 10].

Lemma run_o2_1RB0RC_0LC1RD_0LB1LA_1LB0RD : srun tm true true cho2_1RB0RC_0LC1RD_0LB1LA_1LB0RD O2_1RB0RC_0LC1RD_0LB1LA_1LB0RD0 = Some (O2_1RB0RC_0LC1RD_0LB1LA_1LB0RD1, 4, 18).
Proof. vm_compute. reflexivity. Qed.

(** j = 1 (concrete) *)
Definition O3_1RB0RC_0LC1RD_0LB1LA_1LB0RD0 : sconf := mkC StD (mkS [S1;S1;S0] [] 0 0 []) S0 (mkS [S1;S1] [] 0 0 []).
Definition O3_1RB0RC_0LC1RD_0LB1LA_1LB0RD1 : sconf := mkC StD (mkS [S0;S0;S1] [] 0 0 []) S0 (mkS [S1;S1] [] 0 0 []).
Definition cho3_1RB0RC_0LC1RD_0LB1LA_1LB0RD : list lstep := [SWin 14].

Lemma run_o3_1RB0RC_0LC1RD_0LB1LA_1LB0RD : srun tm true true cho3_1RB0RC_0LC1RD_0LB1LA_1LB0RD O3_1RB0RC_0LC1RD_0LB1LA_1LB0RD0 = Some (O3_1RB0RC_0LC1RD_0LB1LA_1LB0RD1, 0, 14).
Proof. vm_compute. reflexivity. Qed.

(** ** Anchor glue -- the only per-machine mathematics *)

(** [rep] at [j = m*i + (c1 + c2)]: the residue cases' only algebra. *)
Lemma repeq_1RB0RC_0LC1RD_0LB1LA_1LB0RD : forall (u : list Sym) n m, n = m -> rep u n = rep u m.
Proof. intros u n m ->. reflexivity. Qed.

Lemma repmul_1RB0RC_0LC1RD_0LB1LA_1LB0RD : forall (u : list Sym) m i, rep u (m * i) = rep (rep u m) i.
Proof.
  intros u m i. induction i as [|i IH]; [rewrite Nat.mul_0_r; reflexivity|].
  replace (m * S i) with (m + m * i) by lia. rewrite rep_add, IH. reflexivity.
Qed.

Lemma repm_1RB0RC_0LC1RD_0LB1LA_1LB0RD : forall (u : list Sym) m i c1 c2,
  rep u (m * i + (c1 + c2)) = rep u c1 ++ rep (rep u m) i ++ rep u c2.
Proof.
  intros u m i c1 c2.
  replace (m * i + (c1 + c2)) with (c1 + (m * i + c2)) by lia.
  rewrite !rep_add, repmul_1RB0RC_0LC1RD_0LB1LA_1LB0RD. reflexivity.
Qed.

Lemma gpar0_1RB0RC_0LC1RD_0LB1LA_1LB0RD : forall p j q0 i, cview p = (j, Some q0) ->
  j = 2 * i + 0 ->
  Cc p = cden (Kp q0 ++ [S0]) [] i P0_1RB0RC_0LC1RD_0LB1LA_1LB0RD0 /\ cden (Kp q0 ++ [S0]) [] i P0_1RB0RC_0LC1RD_0LB1LA_1LB0RD1 = Cc (Pos.succ p).
Proof.
  intros p j q0 i E Hj. destruct (KpCounter.cview_some_K p j q0 E) as (H1 & H2).
  rewrite (repeq_1RB0RC_0LC1RD_0LB1LA_1LB0RD [S1] _ (2 * i + (0 + 0))) in H1 by lia.
  rewrite (repeq_1RB0RC_0LC1RD_0LB1LA_1LB0RD [S0] _ (2 * i + (0 + 0))) in H2 by lia.
  rewrite repm_1RB0RC_0LC1RD_0LB1LA_1LB0RD in H1, H2.
  unfold Cc_1RB0RC_0LC1RD_0LB1LA_1LB0RD, cden, P0_1RB0RC_0LC1RD_0LB1LA_1LB0RD0, P0_1RB0RC_0LC1RD_0LB1LA_1LB0RD1; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia.
  split; [rewrite H1 | rewrite H2]; cbn [rep app Nat.mul Nat.add]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity.
Qed.

Lemma gpar1_1RB0RC_0LC1RD_0LB1LA_1LB0RD : forall p j q0 i, cview p = (j, Some q0) ->
  j = 2 * i + 1 ->
  Cc p = cden (Kp q0 ++ [S0]) [] i P1_1RB0RC_0LC1RD_0LB1LA_1LB0RD0 /\ cden (Kp q0 ++ [S0]) [] i P1_1RB0RC_0LC1RD_0LB1LA_1LB0RD1 = Cc (Pos.succ p).
Proof.
  intros p j q0 i E Hj. destruct (KpCounter.cview_some_K p j q0 E) as (H1 & H2).
  rewrite (repeq_1RB0RC_0LC1RD_0LB1LA_1LB0RD [S1] _ (2 * i + (0 + 1))) in H1 by lia.
  rewrite (repeq_1RB0RC_0LC1RD_0LB1LA_1LB0RD [S0] _ (2 * i + (0 + 1))) in H2 by lia.
  rewrite repm_1RB0RC_0LC1RD_0LB1LA_1LB0RD in H1, H2.
  unfold Cc_1RB0RC_0LC1RD_0LB1LA_1LB0RD, cden, P1_1RB0RC_0LC1RD_0LB1LA_1LB0RD0, P1_1RB0RC_0LC1RD_0LB1LA_1LB0RD1; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia.
  split; [rewrite H1 | rewrite H2]; cbn [rep app Nat.mul Nat.add]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity.
Qed.

Lemma lapi_1RB0RC_0LC1RD_0LB1LA_1LB0RD : forall p j q0, cview p = (j, Some q0) ->
  exists n, 0 < n /\ csteps tm n (Cc p) = Some (Cc (Pos.succ p)).
Proof.
  intros p j q0 E.
  pose proof (Nat.div_mod_eq j 2) as Hd.
  pose proof (Nat.mod_upper_bound j 2 ltac:(discriminate)) as Hm.
  set (i := j / 2) in *. set (r := j mod 2) in *. clearbody i r.
  destruct r as [|[|r]]; [idtac | idtac | exfalso; lia].
  - destruct (gpar0_1RB0RC_0LC1RD_0LB1LA_1LB0RD p j q0 i E ltac:(lia)) as (HA & HB).
    exists (4 * i + 10). split; [lia|]. rewrite HA.
    rewrite (srun_sound tm false true chp0_1RB0RC_0LC1RD_0LB1LA_1LB0RD P0_1RB0RC_0LC1RD_0LB1LA_1LB0RD0 P0_1RB0RC_0LC1RD_0LB1LA_1LB0RD1 4 10
               run_p0_1RB0RC_0LC1RD_0LB1LA_1LB0RD (Kp q0 ++ [S0]) [] i ltac:(discriminate) ltac:(reflexivity)).
    f_equal. exact HB.
  - destruct (gpar1_1RB0RC_0LC1RD_0LB1LA_1LB0RD p j q0 i E ltac:(lia)) as (HA & HB).
    exists (4 * i + 8). split; [lia|]. rewrite HA.
    rewrite (srun_sound tm false true chp1_1RB0RC_0LC1RD_0LB1LA_1LB0RD P1_1RB0RC_0LC1RD_0LB1LA_1LB0RD0 P1_1RB0RC_0LC1RD_0LB1LA_1LB0RD1 4 8
               run_p1_1RB0RC_0LC1RD_0LB1LA_1LB0RD (Kp q0 ++ [S0]) [] i ltac:(discriminate) ltac:(reflexivity)).
    f_equal. exact HB.
Qed.

Lemma lbl_1RB0RC_0LC1RD_0LB1LA_1LB0RD : forall q l h r, lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.

Lemma gopar0_1RB0RC_0LC1RD_0LB1LA_1LB0RD : forall p j i, cview p = (S j, None) ->
  j = 2 * i + 2 ->
  Cc p = cden [] [] i O0_1RB0RC_0LC1RD_0LB1LA_1LB0RD0 /\
  lift (cden [] [] i O0_1RB0RC_0LC1RD_0LB1LA_1LB0RD1) = lift (Cc (Pos.succ p)).
Proof.
  intros p j i E Hj. destruct (KpCounter.cview_none_K p j E) as (H1 & H2).
  rewrite (repeq_1RB0RC_0LC1RD_0LB1LA_1LB0RD [S1] _ (2 * i + (3 + 0))) in H1 by lia.
  rewrite (repeq_1RB0RC_0LC1RD_0LB1LA_1LB0RD [S0] _ (2 * i + (3 + 0))) in H2 by lia.
  rewrite repm_1RB0RC_0LC1RD_0LB1LA_1LB0RD in H1, H2.
  split.
  - unfold Cc_1RB0RC_0LC1RD_0LB1LA_1LB0RD, cden, O0_1RB0RC_0LC1RD_0LB1LA_1LB0RD0; cbn [c_st c_l c_h c_r].
    unfold sden; cbn [s_pre s_u s_a s_b s_post].
    replace (1 * i + 0) with i by lia.
    rewrite H1; cbn [rep app Nat.mul Nat.add]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity.
  - assert (HD : cden [] [] i O0_1RB0RC_0LC1RD_0LB1LA_1LB0RD1 = (StD, ([S0;S0;S0] ++ rep [S0;S0] i ++ [S1], S0, [S1;S1]))).
    { unfold cden, O0_1RB0RC_0LC1RD_0LB1LA_1LB0RD1, sden; cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
      replace (1 * i + 0) with i by lia. cbn [rep app Nat.mul Nat.add]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity. }
    assert (HC : Cc (Pos.succ p) = (StD, (([S0;S0;S0] ++ rep [S0;S0] i ++ [S1]) ++ [S0], S0, [S1;S1]))).
    { unfold Cc_1RB0RC_0LC1RD_0LB1LA_1LB0RD. rewrite H2. cbn [rep app Nat.mul Nat.add]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity. }
    rewrite HD, HC. rewrite ?lift_app_blank_l, ?lift_app_blank. reflexivity.
Qed.

Lemma gopar1_1RB0RC_0LC1RD_0LB1LA_1LB0RD : forall p, cview p = (S 0, None) ->
  Cc p = cden [] [] 0 O1_1RB0RC_0LC1RD_0LB1LA_1LB0RD0 /\
  lift (cden [] [] 0 O1_1RB0RC_0LC1RD_0LB1LA_1LB0RD1) = lift (Cc (Pos.succ p)).
Proof.
  intros p E. destruct (KpCounter.cview_none_K p 0 E) as (H1 & H2).
  split.
  - unfold Cc_1RB0RC_0LC1RD_0LB1LA_1LB0RD, cden, O1_1RB0RC_0LC1RD_0LB1LA_1LB0RD0; cbn [c_st c_l c_h c_r].
    unfold sden; cbn [s_pre s_u s_a s_b s_post].
    rewrite H1; cbn [rep app Nat.mul Nat.add]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity.
  - assert (HD : cden [] [] 0 O1_1RB0RC_0LC1RD_0LB1LA_1LB0RD1 = (StD, ([S0;S1], S0, [S1;S1]))).
    { unfold cden, O1_1RB0RC_0LC1RD_0LB1LA_1LB0RD1, sden; cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
      cbn [rep app Nat.mul Nat.add]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity. }
    assert (HC : Cc (Pos.succ p) = (StD, (([S0;S1]) ++ [S0], S0, [S1;S1]))).
    { unfold Cc_1RB0RC_0LC1RD_0LB1LA_1LB0RD. rewrite H2. cbn [rep app Nat.mul Nat.add]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity. }
    rewrite HD, HC. rewrite ?lift_app_blank_l, ?lift_app_blank. reflexivity.
Qed.

Lemma gopar2_1RB0RC_0LC1RD_0LB1LA_1LB0RD : forall p j i, cview p = (S j, None) ->
  j = 2 * i + 3 ->
  Cc p = cden [] [] i O2_1RB0RC_0LC1RD_0LB1LA_1LB0RD0 /\
  lift (cden [] [] i O2_1RB0RC_0LC1RD_0LB1LA_1LB0RD1) = lift (Cc (Pos.succ p)).
Proof.
  intros p j i E Hj. destruct (KpCounter.cview_none_K p j E) as (H1 & H2).
  rewrite (repeq_1RB0RC_0LC1RD_0LB1LA_1LB0RD [S1] _ (2 * i + (4 + 0))) in H1 by lia.
  rewrite (repeq_1RB0RC_0LC1RD_0LB1LA_1LB0RD [S0] _ (2 * i + (4 + 0))) in H2 by lia.
  rewrite repm_1RB0RC_0LC1RD_0LB1LA_1LB0RD in H1, H2.
  split.
  - unfold Cc_1RB0RC_0LC1RD_0LB1LA_1LB0RD, cden, O2_1RB0RC_0LC1RD_0LB1LA_1LB0RD0; cbn [c_st c_l c_h c_r].
    unfold sden; cbn [s_pre s_u s_a s_b s_post].
    replace (1 * i + 0) with i by lia.
    rewrite H1; cbn [rep app Nat.mul Nat.add]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity.
  - assert (HD : cden [] [] i O2_1RB0RC_0LC1RD_0LB1LA_1LB0RD1 = (StD, ([S0;S0;S0;S0] ++ rep [S0;S0] i ++ [S1], S0, [S1;S1]))).
    { unfold cden, O2_1RB0RC_0LC1RD_0LB1LA_1LB0RD1, sden; cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
      replace (1 * i + 0) with i by lia. cbn [rep app Nat.mul Nat.add]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity. }
    assert (HC : Cc (Pos.succ p) = (StD, (([S0;S0;S0;S0] ++ rep [S0;S0] i ++ [S1]) ++ [S0], S0, [S1;S1]))).
    { unfold Cc_1RB0RC_0LC1RD_0LB1LA_1LB0RD. rewrite H2. cbn [rep app Nat.mul Nat.add]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity. }
    rewrite HD, HC. rewrite ?lift_app_blank_l, ?lift_app_blank. reflexivity.
Qed.

Lemma gopar3_1RB0RC_0LC1RD_0LB1LA_1LB0RD : forall p, cview p = (S 1, None) ->
  Cc p = cden [] [] 0 O3_1RB0RC_0LC1RD_0LB1LA_1LB0RD0 /\
  lift (cden [] [] 0 O3_1RB0RC_0LC1RD_0LB1LA_1LB0RD1) = lift (Cc (Pos.succ p)).
Proof.
  intros p E. destruct (KpCounter.cview_none_K p 1 E) as (H1 & H2).
  split.
  - unfold Cc_1RB0RC_0LC1RD_0LB1LA_1LB0RD, cden, O3_1RB0RC_0LC1RD_0LB1LA_1LB0RD0; cbn [c_st c_l c_h c_r].
    unfold sden; cbn [s_pre s_u s_a s_b s_post].
    rewrite H1; cbn [rep app Nat.mul Nat.add]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity.
  - assert (HD : cden [] [] 0 O3_1RB0RC_0LC1RD_0LB1LA_1LB0RD1 = (StD, ([S0;S0;S1], S0, [S1;S1]))).
    { unfold cden, O3_1RB0RC_0LC1RD_0LB1LA_1LB0RD1, sden; cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
      cbn [rep app Nat.mul Nat.add]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity. }
    assert (HC : Cc (Pos.succ p) = (StD, (([S0;S0;S1]) ++ [S0], S0, [S1;S1]))).
    { unfold Cc_1RB0RC_0LC1RD_0LB1LA_1LB0RD. rewrite H2. cbn [rep app Nat.mul Nat.add]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity. }
    rewrite HD, HC. rewrite ?lift_app_blank_l, ?lift_app_blank. reflexivity.
Qed.

Lemma lapo_1RB0RC_0LC1RD_0LB1LA_1LB0RD : forall p j, cview p = (S j, None) ->
  exists n c', csteps tm n (Cc p) = Some c'
          /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intros p j E.
  pose proof (Nat.div_mod_eq j 2) as Hd.
  pose proof (Nat.mod_upper_bound j 2 ltac:(discriminate)) as Hm.
  set (i := j / 2) in *. set (r := j mod 2) in *. clearbody i r.
  destruct r as [|[|r]]; [idtac | idtac | exfalso; lia].
  - destruct i as [|i].
    + assert (Ej : j = 0) by lia. subst j.
      destruct (gopar1_1RB0RC_0LC1RD_0LB1LA_1LB0RD p E) as (HA & HB).
      exists (0 * 0 + 8), (cden [] [] 0 O1_1RB0RC_0LC1RD_0LB1LA_1LB0RD1).
      split; [| split; [exact HB | lia]].
      rewrite HA. exact (srun_sound tm true true cho1_1RB0RC_0LC1RD_0LB1LA_1LB0RD O1_1RB0RC_0LC1RD_0LB1LA_1LB0RD0 O1_1RB0RC_0LC1RD_0LB1LA_1LB0RD1 0 8
                 run_o1_1RB0RC_0LC1RD_0LB1LA_1LB0RD [] [] 0 ltac:(reflexivity) ltac:(reflexivity)).
    + destruct (gopar0_1RB0RC_0LC1RD_0LB1LA_1LB0RD p j i E ltac:(lia)) as (HA & HB).
      exists (4 * i + 12), (cden [] [] i O0_1RB0RC_0LC1RD_0LB1LA_1LB0RD1).
      split; [| split; [exact HB | lia]].
      rewrite HA. exact (srun_sound tm true true cho0_1RB0RC_0LC1RD_0LB1LA_1LB0RD O0_1RB0RC_0LC1RD_0LB1LA_1LB0RD0 O0_1RB0RC_0LC1RD_0LB1LA_1LB0RD1 4 12
                 run_o0_1RB0RC_0LC1RD_0LB1LA_1LB0RD [] [] i ltac:(reflexivity) ltac:(reflexivity)).
  - destruct i as [|i].
    + assert (Ej : j = 1) by lia. subst j.
      destruct (gopar3_1RB0RC_0LC1RD_0LB1LA_1LB0RD p E) as (HA & HB).
      exists (0 * 0 + 14), (cden [] [] 0 O3_1RB0RC_0LC1RD_0LB1LA_1LB0RD1).
      split; [| split; [exact HB | lia]].
      rewrite HA. exact (srun_sound tm true true cho3_1RB0RC_0LC1RD_0LB1LA_1LB0RD O3_1RB0RC_0LC1RD_0LB1LA_1LB0RD0 O3_1RB0RC_0LC1RD_0LB1LA_1LB0RD1 0 14
                 run_o3_1RB0RC_0LC1RD_0LB1LA_1LB0RD [] [] 0 ltac:(reflexivity) ltac:(reflexivity)).
    + destruct (gopar2_1RB0RC_0LC1RD_0LB1LA_1LB0RD p j i E ltac:(lia)) as (HA & HB).
      exists (4 * i + 18), (cden [] [] i O2_1RB0RC_0LC1RD_0LB1LA_1LB0RD1).
      split; [| split; [exact HB | lia]].
      rewrite HA. exact (srun_sound tm true true cho2_1RB0RC_0LC1RD_0LB1LA_1LB0RD O2_1RB0RC_0LC1RD_0LB1LA_1LB0RD0 O2_1RB0RC_0LC1RD_0LB1LA_1LB0RD1 4 18
                 run_o2_1RB0RC_0LC1RD_0LB1LA_1LB0RD [] [] i ltac:(reflexivity) ltac:(reflexivity)).
Qed.

(** ** The lap *)

Lemma lap_1RB0RC_0LC1RD_0LB1LA_1LB0RD : forall p, exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:E. destruct oq as [q0|].
  - destruct (lapi_1RB0RC_0LC1RD_0LB1LA_1LB0RD p j q0 E) as (n & Hn & Hrun).
    exists n, (Cc (Pos.succ p)).
    split; [exact Hrun | split; [reflexivity | exact Hn]].
  - destruct (cview_pos p j E) as (j' & ->).
    exact (lapo_1RB0RC_0LC1RD_0LB1LA_1LB0RD p j' E).
Qed.

(** ** Bootstrap *)

Lemma boot_1RB0RC_0LC1RD_0LB1LA_1LB0RD : exists t0, stepn tm t0 InitES = Some (lift (Cc 1)).
Proof.
  exists 15.
  assert (H : match csteps tm 15 c0 with
              | Some c => ceqb c (Cc 1) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 15 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** ** Visits

    Every state fires inside the OVERFLOW lap, so one prefix chain per state
    plus [LapCertGlue.vis_via_ovf] (run interior laps until the counter
    overflows -- they close exactly) covers every anchor. *)

Lemma fireo_1RB0RC_0LC1RD_0LB1LA_1LB0RD : forall (l0 l1 l2 l3 : list lstep) (t : Instr),
  srun_instr tm true true l0 O0_1RB0RC_0LC1RD_0LB1LA_1LB0RD0 = Some t ->
  srun_instr tm true true l1 O1_1RB0RC_0LC1RD_0LB1LA_1LB0RD0 = Some t ->
  srun_instr tm true true l2 O2_1RB0RC_0LC1RD_0LB1LA_1LB0RD0 = Some t ->
  srun_instr tm true true l3 O3_1RB0RC_0LC1RD_0LB1LA_1LB0RD0 = Some t ->
  forall p j, cview p = (S j, None) ->
  exists k c, csteps tm k (Cc p) = Some c /\ cinstr c = t.
Proof.
  intros l0 l1 l2 l3 t H0 H1 H2 H3 p j E.
  pose proof (Nat.div_mod_eq j 2) as Hd.
  pose proof (Nat.mod_upper_bound j 2 ltac:(discriminate)) as Hm.
  set (i := j / 2) in *. set (r := j mod 2) in *. clearbody i r.
  destruct r as [|[|r]]; [idtac | idtac | exfalso; lia].
  - destruct i as [|i].
    + assert (Ej : j = 0) by lia. subst j.
      destruct (gopar1_1RB0RC_0LC1RD_0LB1LA_1LB0RD p E) as (HA & _).
      exact (fire_of_run_instr tm Cc true true l1 O1_1RB0RC_0LC1RD_0LB1LA_1LB0RD0 p 0 [] [] t
               H1 ltac:(reflexivity) ltac:(reflexivity) HA).
    + destruct (gopar0_1RB0RC_0LC1RD_0LB1LA_1LB0RD p j i E ltac:(lia)) as (HA & _).
      exact (fire_of_run_instr tm Cc true true l0 O0_1RB0RC_0LC1RD_0LB1LA_1LB0RD0 p i [] [] t
               H0 ltac:(reflexivity) ltac:(reflexivity) HA).
  - destruct i as [|i].
    + assert (Ej : j = 1) by lia. subst j.
      destruct (gopar3_1RB0RC_0LC1RD_0LB1LA_1LB0RD p E) as (HA & _).
      exact (fire_of_run_instr tm Cc true true l3 O3_1RB0RC_0LC1RD_0LB1LA_1LB0RD0 p 0 [] [] t
               H3 ltac:(reflexivity) ltac:(reflexivity) HA).
    + destruct (gopar2_1RB0RC_0LC1RD_0LB1LA_1LB0RD p j i E ltac:(lia)) as (HA & _).
      exact (fire_of_run_instr tm Cc true true l2 O2_1RB0RC_0LC1RD_0LB1LA_1LB0RD0 p i [] [] t
               H2 ltac:(reflexivity) ltac:(reflexivity) HA).
Qed.

(** ** Fires: every UNPINNED instruction fires from every anchor
    (inside the overflow lap; [LapGlueTr.fire_via_ovf] runs the
    interior laps until the counter overflows). *)

Lemma fire_1RB0RC_0LC1RD_0LB1LA_1LB0RD : forall t, ~ In t pins_1RB0RC_0LC1RD_0LB1LA_1LB0RD ->
  forall p, exists k c, csteps tm k (Cc p) = Some c /\ cinstr c = t.
Proof.
  intros t Hnp p.
  assert (Hi : forall p0 j q0, cview p0 = (j, Some q0) ->
            exists n, 0 < n /\ csteps tm n (Cc p0) = Some (Cc (Pos.succ p0)))
    by exact lapi_1RB0RC_0LC1RD_0LB1LA_1LB0RD.
  destruct t as [q b]; destruct q, b.
  - (* A0 *)
    apply (fire_via_ovf tm Cc Hi (StA, S0)), (fireo_1RB0RC_0LC1RD_0LB1LA_1LB0RD
      ([SWin 5; SCycL 2 0; SWin 2; SCycR 2; SWin 5; SWin 8])
      ([SWin 8; SWin 8])
      ([SWin 6; SCycL 2 0; SWin 2; SCycR 2; SWin 8])
      ([SWin 12])); vm_compute; reflexivity.
  - (* A1 *)
    apply (fire_via_ovf tm Cc Hi (StA, S1)), (fireo_1RB0RC_0LC1RD_0LB1LA_1LB0RD
      ([SWin 5; SCycL 2 0; SWin 2; SCycR 2; SWin 5; SWin 6])
      ([SWin 8; SWin 6])
      ([SWin 6; SCycL 2 0; SWin 2; SCycR 2; SWin 6])
      ([SWin 10])); vm_compute; reflexivity.
  - (* B0 *)
    apply (fire_via_ovf tm Cc Hi (StB, S0)), (fireo_1RB0RC_0LC1RD_0LB1LA_1LB0RD
      ([SWin 5; SCycL 2 0; SWin 2])
      ([SWin 5])
      ([SWin 6; SCycL 2 0; SWin 2])
      ([SWin 6])); vm_compute; reflexivity.
  - (* B1 *)
    apply (fire_via_ovf tm Cc Hi (StB, S1)), (fireo_1RB0RC_0LC1RD_0LB1LA_1LB0RD
      ([SWin 1])
      ([SWin 1])
      ([SWin 1])
      ([SWin 1])); vm_compute; reflexivity.
  - (* C0 *)
    apply (fire_via_ovf tm Cc Hi (StC, S0)), (fireo_1RB0RC_0LC1RD_0LB1LA_1LB0RD
      ([SWin 5; SCycL 2 0; SWin 2; SCycR 2; SWin 1])
      ([SWin 6])
      ([SWin 6; SCycL 2 0; SWin 2; SCycR 2; SWin 1])
      ([SWin 7])); vm_compute; reflexivity.
  - (* C1 *)
    apply (fire_via_ovf tm Cc Hi (StC, S1)), (fireo_1RB0RC_0LC1RD_0LB1LA_1LB0RD
      ([SWin 5; SCycL 2 0; SWin 2; SCycR 2; SWin 5; SWin 5])
      ([SWin 8; SWin 5])
      ([SWin 6; SCycL 2 0; SWin 2; SCycR 2; SWin 5])
      ([SWin 9])); vm_compute; reflexivity.
  - (* D0 *)
    apply (fire_via_ovf tm Cc Hi (StD, S0)), (fireo_1RB0RC_0LC1RD_0LB1LA_1LB0RD
      ([])
      ([])
      ([])
      ([])); vm_compute; reflexivity.
  - (* D1 *)
    apply (fire_via_ovf tm Cc Hi (StD, S1)), (fireo_1RB0RC_0LC1RD_0LB1LA_1LB0RD
      ([SWin 2])
      ([SWin 2])
      ([SWin 2])
      ([SWin 2])); vm_compute; reflexivity.
Qed.

Theorem nqhtrm_1RB0RC_0LC1RD_0LB1LA_1LB0RD : NeverQuasiHaltsTr tmm_1RB0RC_0LC1RD_0LB1LA_1LB0RD.
Proof.
  apply (glue_neverqhtr tmm_1RB0RC_0LC1RD_0LB1LA_1LB0RD pins_1RB0RC_0LC1RD_0LB1LA_1LB0RD Cc 1).
  - exact boot_1RB0RC_0LC1RD_0LB1LA_1LB0RD.
  - intros p _. apply lap_1RB0RC_0LC1RD_0LB1LA_1LB0RD.
  - intros t Ht p _. apply fire_1RB0RC_0LC1RD_0LB1LA_1LB0RD. exact Ht.
Qed.

Theorem nqhtr_1RB0RC_0LC1RD_0LB1LA_1LB0RD : NeverQuasiHaltsTr tm_1RB0RC_0LC1RD_0LB1LA_1LB0RD.
Proof. apply (neverqhtr_mirror tm_1RB0RC_0LC1RD_0LB1LA_1LB0RD). rewrite mirror_ok_1RB0RC_0LC1RD_0LB1LA_1LB0RD. exact nqhtrm_1RB0RC_0LC1RD_0LB1LA_1LB0RD. Qed.

Theorem nonhalt_1RB0RC_0LC1RD_0LB1LA_1LB0RD : NonHalt tm_1RB0RC_0LC1RD_0LB1LA_1LB0RD.
Proof. apply never_qh_tr_nonhalt, nqhtr_1RB0RC_0LC1RD_0LB1LA_1LB0RD. Qed.
