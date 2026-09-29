(** * LAPT_1RB1LC_0LC0RB_0RD1LA_0LA1RD: TRANSITION-LEVEL board for machine 1RB1LC_0LC0RB_0RD1LA_0LA1RD, boarded by CERTIFICATE.

    Auto-emitted by tools/counters/emit_lapcert.py (UNTRUSTED emitter; the Coq
    kernel re-runs the checker on every line below).  Left-growth binary
    counter under the Kp digit alphabet (KpCounter.v), anchored at

      Cc p = (StB, (Kp p ++ [S0], S0, []))

    The lap is DATA, not a proof script: each branch is a list of steps for
    [Checkers/LapDecider.v], run by the kernel through [vm_compute] and
    discharged by the single theorem [srun_sound].

      interior  (cview p = (j, Some q0)):  split mod 2, 3 cases steps
      overflow  (cview p = (S j, None)):   split mod 2, 4 cases

    The interior branch closes EXACTLY (which is what feeds
    [LapCertGlue.reach_ovf]); the overflow branch closes one blank short of
    the anchor tail, hence up to [lift].

    Differentially validated against the raw simulator on BOTH branches --
    step counts AND exact configurations -- for 198 anchors (overflow split mod 2).
    Axiom footprint: [functional_extensionality_dep] (via [CTape.lift]). *)
From Coq Require Import Arith Lia Bool List PArith Wellfounded.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape LapGlue LapGlueQH LapGlueAbs
                                  MonoCounter JpCounter KpCounter LapCertGlue.
From BBB4.Census Require Import TNF_QH.
From BBB4.Checkers Require Import LapDecider.
From BBB4 Require Import BBBT4_Statement.
From BBB4.Checkers Require Import WrapTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
From BBB4.Counters Require Import LapGlueTr.
Import ListNotations.

Definition mk_1RB1LC_0LC0RB_0RD1LA_0LA1RD (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_1RB1LC_0LC0RB_0RD1LA_0LA1RD.

(** 1RB1LC_0LC0RB_0RD1LA_0LA1RD *)
Definition tm_1RB1LC_0LC0RB_0RD1LA_0LA1RD : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S1 DL StC
  | StB, S0 => mk S0 DL StC | StB, S1 => mk S0 DR StB
  | StC, S0 => mk S0 DR StD | StC, S1 => mk S1 DL StA
  | StD, S0 => mk S0 DL StA | StD, S1 => mk S1 DR StD end.
(** the instructions the certificate claims NEVER fire; the lap
    argument runs on the machine WRAPPED at them
    ([WrapTr.tm_wrap_trs]), so a pinned instruction firing would
    halt it and every [srun] below would fail. *)
Definition pins_1RB1LC_0LC0RB_0RD1LA_0LA1RD : list Instr := [].
Definition tmw_1RB1LC_0LC0RB_0RD1LA_0LA1RD : TM := tm_wrap_trs tm_1RB1LC_0LC0RB_0RD1LA_0LA1RD pins_1RB1LC_0LC0RB_0RD1LA_0LA1RD.
Local Notation tm := tmw_1RB1LC_0LC0RB_0RD1LA_0LA1RD.

Definition Cc_1RB1LC_0LC0RB_0RD1LA_0LA1RD (p : positive) : cconf := (StB, (Kp p ++ [S0], S0, [])).
Local Notation Cc := Cc_1RB1LC_0LC0RB_0RD1LA_0LA1RD.

(** ** The certificate *)

(** j = 2*i + 2 *)
Definition P0_1RB1LC_0LC0RB_0RD1LA_0LA1RD0 : sconf := mkC StB (mkS [] [S1;S1] 1 0 [S1;S1;S0]) S0 (mkS [] [] 0 0 []).
Definition P0_1RB1LC_0LC0RB_0RD1LA_0LA1RD1 : sconf := mkC StB (mkS [] [S0;S0] 1 0 [S0;S0;S1]) S0 (mkS [] [] 0 0 []).
Definition chp0_1RB1LC_0LC0RB_0RD1LA_0LA1RD : list lstep := [SRotL 1; SWin 1; SCycL 2 0; SWin 4; SCycR 2; SWin 2; SCycL 2 0; SWin 4; SCycR 2; SWin 1; SUnrotL 1].

Lemma run_p0_1RB1LC_0LC0RB_0RD1LA_0LA1RD : srun tm false true chp0_1RB1LC_0LC0RB_0RD1LA_0LA1RD P0_1RB1LC_0LC0RB_0RD1LA_0LA1RD0 = Some (P0_1RB1LC_0LC0RB_0RD1LA_0LA1RD1, 8, 12).
Proof. vm_compute. reflexivity. Qed.

(** j = 0 (concrete) *)
Definition P1_1RB1LC_0LC0RB_0RD1LA_0LA1RD0 : sconf := mkC StB (mkS [S0] [] 0 0 []) S0 (mkS [] [] 0 0 []).
Definition P1_1RB1LC_0LC0RB_0RD1LA_0LA1RD1 : sconf := mkC StB (mkS [S1] [] 0 0 []) S0 (mkS [] [] 0 0 []).
Definition chp1_1RB1LC_0LC0RB_0RD1LA_0LA1RD : list lstep := [SWin 4].

Lemma run_p1_1RB1LC_0LC0RB_0RD1LA_0LA1RD : srun tm false true chp1_1RB1LC_0LC0RB_0RD1LA_0LA1RD P1_1RB1LC_0LC0RB_0RD1LA_0LA1RD0 = Some (P1_1RB1LC_0LC0RB_0RD1LA_0LA1RD1, 0, 4).
Proof. vm_compute. reflexivity. Qed.

(** j = 2*i + 1 *)
Definition P2_1RB1LC_0LC0RB_0RD1LA_0LA1RD0 : sconf := mkC StB (mkS [] [S1;S1] 1 0 [S1;S0]) S0 (mkS [] [] 0 0 []).
Definition P2_1RB1LC_0LC0RB_0RD1LA_0LA1RD1 : sconf := mkC StB (mkS [] [S0;S0] 1 0 [S0;S1]) S0 (mkS [] [] 0 0 []).
Definition chp2_1RB1LC_0LC0RB_0RD1LA_0LA1RD : list lstep := [SRotL 1; SWin 1; SCycL 2 0; SWin 2; SCycR 2; SWin 1; SUnrotL 1].

Lemma run_p2_1RB1LC_0LC0RB_0RD1LA_0LA1RD : srun tm false true chp2_1RB1LC_0LC0RB_0RD1LA_0LA1RD P2_1RB1LC_0LC0RB_0RD1LA_0LA1RD0 = Some (P2_1RB1LC_0LC0RB_0RD1LA_0LA1RD1, 4, 4).
Proof. vm_compute. reflexivity. Qed.

Definition B0_1RB1LC_0LC0RB_0RD1LA_0LA1RD : sconf := mkC StB (mkS [S1;S1;S1] [S1;S1] 1 0 [S0]) S0 (mkS [] [] 0 0 []).
Definition B1_1RB1LC_0LC0RB_0RD1LA_0LA1RD : sconf := mkC StB (mkS [S0;S0;S0] [S0;S0] 1 0 [S1]) S0 (mkS [] [] 0 0 []).
(** j = 2*i + 2 *)
Definition O0_1RB1LC_0LC0RB_0RD1LA_0LA1RD0 : sconf := mkC StB (mkS [S1;S1;S1] [S1;S1] 1 0 [S0]) S0 (mkS [] [] 0 0 []).
Definition O0_1RB1LC_0LC0RB_0RD1LA_0LA1RD1 : sconf := mkC StB (mkS [S0;S0;S0] [S0;S0] 1 0 [S1]) S0 (mkS [] [] 0 0 []).
Definition cho0_1RB1LC_0LC0RB_0RD1LA_0LA1RD : list lstep := [SWin 3; SCycL 2 0; SWin 2; SCycR 2; SWin 3].

Lemma run_o0_1RB1LC_0LC0RB_0RD1LA_0LA1RD : srun tm true true cho0_1RB1LC_0LC0RB_0RD1LA_0LA1RD O0_1RB1LC_0LC0RB_0RD1LA_0LA1RD0 = Some (O0_1RB1LC_0LC0RB_0RD1LA_0LA1RD1, 4, 8).
Proof. vm_compute. reflexivity. Qed.

(** j = 0 (concrete) *)
Definition O1_1RB1LC_0LC0RB_0RD1LA_0LA1RD0 : sconf := mkC StB (mkS [S1;S0] [] 0 0 []) S0 (mkS [] [] 0 0 []).
Definition O1_1RB1LC_0LC0RB_0RD1LA_0LA1RD1 : sconf := mkC StB (mkS [S0;S1] [] 0 0 []) S0 (mkS [] [] 0 0 []).
Definition cho1_1RB1LC_0LC0RB_0RD1LA_0LA1RD : list lstep := [SWin 4].

Lemma run_o1_1RB1LC_0LC0RB_0RD1LA_0LA1RD : srun tm true true cho1_1RB1LC_0LC0RB_0RD1LA_0LA1RD O1_1RB1LC_0LC0RB_0RD1LA_0LA1RD0 = Some (O1_1RB1LC_0LC0RB_0RD1LA_0LA1RD1, 0, 4).
Proof. vm_compute. reflexivity. Qed.

(** j = 2*i + 3 *)
Definition O2_1RB1LC_0LC0RB_0RD1LA_0LA1RD0 : sconf := mkC StB (mkS [S1;S1;S1;S1] [S1;S1] 1 0 [S0]) S0 (mkS [] [] 0 0 []).
Definition O2_1RB1LC_0LC0RB_0RD1LA_0LA1RD1 : sconf := mkC StB (mkS [S0;S0;S0;S0] [S0;S0] 1 0 [S1]) S0 (mkS [] [] 0 0 []).
Definition cho2_1RB1LC_0LC0RB_0RD1LA_0LA1RD : list lstep := [SWin 4; SCycL 2 0; SWin 2; SCycR 2; SWin 8; SCycL 2 0; SWin 2; SCycR 2; SWin 4].

Lemma run_o2_1RB1LC_0LC0RB_0RD1LA_0LA1RD : srun tm true true cho2_1RB1LC_0LC0RB_0RD1LA_0LA1RD O2_1RB1LC_0LC0RB_0RD1LA_0LA1RD0 = Some (O2_1RB1LC_0LC0RB_0RD1LA_0LA1RD1, 8, 20).
Proof. vm_compute. reflexivity. Qed.

(** j = 1 (concrete) *)
Definition O3_1RB1LC_0LC0RB_0RD1LA_0LA1RD0 : sconf := mkC StB (mkS [S1;S1;S0] [] 0 0 []) S0 (mkS [] [] 0 0 []).
Definition O3_1RB1LC_0LC0RB_0RD1LA_0LA1RD1 : sconf := mkC StB (mkS [S0;S0;S1] [] 0 0 []) S0 (mkS [] [] 0 0 []).
Definition cho3_1RB1LC_0LC0RB_0RD1LA_0LA1RD : list lstep := [SWin 12].

Lemma run_o3_1RB1LC_0LC0RB_0RD1LA_0LA1RD : srun tm true true cho3_1RB1LC_0LC0RB_0RD1LA_0LA1RD O3_1RB1LC_0LC0RB_0RD1LA_0LA1RD0 = Some (O3_1RB1LC_0LC0RB_0RD1LA_0LA1RD1, 0, 12).
Proof. vm_compute. reflexivity. Qed.

(** ** Anchor glue -- the only per-machine mathematics *)

(** [rep] at [j = m*i + (c1 + c2)]: the residue cases' only algebra. *)
Lemma repeq_1RB1LC_0LC0RB_0RD1LA_0LA1RD : forall (u : list Sym) n m, n = m -> rep u n = rep u m.
Proof. intros u n m ->. reflexivity. Qed.

Lemma repmul_1RB1LC_0LC0RB_0RD1LA_0LA1RD : forall (u : list Sym) m i, rep u (m * i) = rep (rep u m) i.
Proof.
  intros u m i. induction i as [|i IH]; [rewrite Nat.mul_0_r; reflexivity|].
  replace (m * S i) with (m + m * i) by lia. rewrite rep_add, IH. reflexivity.
Qed.

Lemma repm_1RB1LC_0LC0RB_0RD1LA_0LA1RD : forall (u : list Sym) m i c1 c2,
  rep u (m * i + (c1 + c2)) = rep u c1 ++ rep (rep u m) i ++ rep u c2.
Proof.
  intros u m i c1 c2.
  replace (m * i + (c1 + c2)) with (c1 + (m * i + c2)) by lia.
  rewrite !rep_add, repmul_1RB1LC_0LC0RB_0RD1LA_0LA1RD. reflexivity.
Qed.

Lemma gpar0_1RB1LC_0LC0RB_0RD1LA_0LA1RD : forall p j q0 i, cview p = (j, Some q0) ->
  j = 2 * i + 2 ->
  Cc p = cden (Kp q0 ++ [S0]) [] i P0_1RB1LC_0LC0RB_0RD1LA_0LA1RD0 /\ cden (Kp q0 ++ [S0]) [] i P0_1RB1LC_0LC0RB_0RD1LA_0LA1RD1 = Cc (Pos.succ p).
Proof.
  intros p j q0 i E Hj. destruct (KpCounter.cview_some_K p j q0 E) as (H1 & H2).
  rewrite (repeq_1RB1LC_0LC0RB_0RD1LA_0LA1RD [S1] _ (2 * i + (0 + 2))) in H1 by lia.
  rewrite (repeq_1RB1LC_0LC0RB_0RD1LA_0LA1RD [S0] _ (2 * i + (0 + 2))) in H2 by lia.
  rewrite repm_1RB1LC_0LC0RB_0RD1LA_0LA1RD in H1, H2.
  unfold Cc_1RB1LC_0LC0RB_0RD1LA_0LA1RD, cden, P0_1RB1LC_0LC0RB_0RD1LA_0LA1RD0, P0_1RB1LC_0LC0RB_0RD1LA_0LA1RD1; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia.
  split; [rewrite H1 | rewrite H2]; cbn [rep app Nat.mul Nat.add]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity.
Qed.

Lemma gpar1_1RB1LC_0LC0RB_0RD1LA_0LA1RD : forall p q0, cview p = (0, Some q0) ->
  Cc p = cden (Kp q0 ++ [S0]) [] 0 P1_1RB1LC_0LC0RB_0RD1LA_0LA1RD0 /\ cden (Kp q0 ++ [S0]) [] 0 P1_1RB1LC_0LC0RB_0RD1LA_0LA1RD1 = Cc (Pos.succ p).
Proof.
  intros p q0 E. destruct (KpCounter.cview_some_K p 0 q0 E) as (H1 & H2).
  unfold Cc_1RB1LC_0LC0RB_0RD1LA_0LA1RD, cden, P1_1RB1LC_0LC0RB_0RD1LA_0LA1RD0, P1_1RB1LC_0LC0RB_0RD1LA_0LA1RD1; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  split; [rewrite H1 | rewrite H2]; cbn [rep app Nat.mul Nat.add]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity.
Qed.

Lemma gpar2_1RB1LC_0LC0RB_0RD1LA_0LA1RD : forall p j q0 i, cview p = (j, Some q0) ->
  j = 2 * i + 1 ->
  Cc p = cden (Kp q0 ++ [S0]) [] i P2_1RB1LC_0LC0RB_0RD1LA_0LA1RD0 /\ cden (Kp q0 ++ [S0]) [] i P2_1RB1LC_0LC0RB_0RD1LA_0LA1RD1 = Cc (Pos.succ p).
Proof.
  intros p j q0 i E Hj. destruct (KpCounter.cview_some_K p j q0 E) as (H1 & H2).
  rewrite (repeq_1RB1LC_0LC0RB_0RD1LA_0LA1RD [S1] _ (2 * i + (0 + 1))) in H1 by lia.
  rewrite (repeq_1RB1LC_0LC0RB_0RD1LA_0LA1RD [S0] _ (2 * i + (0 + 1))) in H2 by lia.
  rewrite repm_1RB1LC_0LC0RB_0RD1LA_0LA1RD in H1, H2.
  unfold Cc_1RB1LC_0LC0RB_0RD1LA_0LA1RD, cden, P2_1RB1LC_0LC0RB_0RD1LA_0LA1RD0, P2_1RB1LC_0LC0RB_0RD1LA_0LA1RD1; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia.
  split; [rewrite H1 | rewrite H2]; cbn [rep app Nat.mul Nat.add]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity.
Qed.

Lemma lapi_1RB1LC_0LC0RB_0RD1LA_0LA1RD : forall p j q0, cview p = (j, Some q0) ->
  exists n, 0 < n /\ csteps tm n (Cc p) = Some (Cc (Pos.succ p)).
Proof.
  intros p j q0 E.
  pose proof (Nat.div_mod_eq j 2) as Hd.
  pose proof (Nat.mod_upper_bound j 2 ltac:(discriminate)) as Hm.
  set (i := j / 2) in *. set (r := j mod 2) in *. clearbody i r.
  destruct r as [|[|r]]; [idtac | idtac | exfalso; lia].
  - destruct i as [|i].
    + assert (Ej : j = 0) by lia. subst j.
      destruct (gpar1_1RB1LC_0LC0RB_0RD1LA_0LA1RD p q0 E) as (HA & HB).
      exists (0 * 0 + 4). split; [lia|]. rewrite HA.
      rewrite (srun_sound tm false true chp1_1RB1LC_0LC0RB_0RD1LA_0LA1RD P1_1RB1LC_0LC0RB_0RD1LA_0LA1RD0 P1_1RB1LC_0LC0RB_0RD1LA_0LA1RD1 0 4
                 run_p1_1RB1LC_0LC0RB_0RD1LA_0LA1RD (Kp q0 ++ [S0]) [] 0 ltac:(discriminate) ltac:(reflexivity)).
      f_equal. exact HB.
    + destruct (gpar0_1RB1LC_0LC0RB_0RD1LA_0LA1RD p j q0 i E ltac:(lia)) as (HA & HB).
      exists (8 * i + 12). split; [lia|]. rewrite HA.
      rewrite (srun_sound tm false true chp0_1RB1LC_0LC0RB_0RD1LA_0LA1RD P0_1RB1LC_0LC0RB_0RD1LA_0LA1RD0 P0_1RB1LC_0LC0RB_0RD1LA_0LA1RD1 8 12
                 run_p0_1RB1LC_0LC0RB_0RD1LA_0LA1RD (Kp q0 ++ [S0]) [] i ltac:(discriminate) ltac:(reflexivity)).
      f_equal. exact HB.
  - destruct (gpar2_1RB1LC_0LC0RB_0RD1LA_0LA1RD p j q0 i E ltac:(lia)) as (HA & HB).
    exists (4 * i + 4). split; [lia|]. rewrite HA.
    rewrite (srun_sound tm false true chp2_1RB1LC_0LC0RB_0RD1LA_0LA1RD P2_1RB1LC_0LC0RB_0RD1LA_0LA1RD0 P2_1RB1LC_0LC0RB_0RD1LA_0LA1RD1 4 4
               run_p2_1RB1LC_0LC0RB_0RD1LA_0LA1RD (Kp q0 ++ [S0]) [] i ltac:(discriminate) ltac:(reflexivity)).
    f_equal. exact HB.
Qed.

Lemma lbl_1RB1LC_0LC0RB_0RD1LA_0LA1RD : forall q l h r, lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.

Lemma gopar0_1RB1LC_0LC0RB_0RD1LA_0LA1RD : forall p j i, cview p = (S j, None) ->
  j = 2 * i + 2 ->
  Cc p = cden [] [] i O0_1RB1LC_0LC0RB_0RD1LA_0LA1RD0 /\
  lift (cden [] [] i O0_1RB1LC_0LC0RB_0RD1LA_0LA1RD1) = lift (Cc (Pos.succ p)).
Proof.
  intros p j i E Hj. destruct (KpCounter.cview_none_K p j E) as (H1 & H2).
  rewrite (repeq_1RB1LC_0LC0RB_0RD1LA_0LA1RD [S1] _ (2 * i + (3 + 0))) in H1 by lia.
  rewrite (repeq_1RB1LC_0LC0RB_0RD1LA_0LA1RD [S0] _ (2 * i + (3 + 0))) in H2 by lia.
  rewrite repm_1RB1LC_0LC0RB_0RD1LA_0LA1RD in H1, H2.
  split.
  - unfold Cc_1RB1LC_0LC0RB_0RD1LA_0LA1RD, cden, O0_1RB1LC_0LC0RB_0RD1LA_0LA1RD0; cbn [c_st c_l c_h c_r].
    unfold sden; cbn [s_pre s_u s_a s_b s_post].
    replace (1 * i + 0) with i by lia.
    rewrite H1; cbn [rep app Nat.mul Nat.add]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity.
  - assert (HD : cden [] [] i O0_1RB1LC_0LC0RB_0RD1LA_0LA1RD1 = (StB, ([S0;S0;S0] ++ rep [S0;S0] i ++ [S1], S0, []))).
    { unfold cden, O0_1RB1LC_0LC0RB_0RD1LA_0LA1RD1, sden; cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
      replace (1 * i + 0) with i by lia. cbn [rep app Nat.mul Nat.add]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity. }
    assert (HC : Cc (Pos.succ p) = (StB, (([S0;S0;S0] ++ rep [S0;S0] i ++ [S1]) ++ [S0], S0, []))).
    { unfold Cc_1RB1LC_0LC0RB_0RD1LA_0LA1RD. rewrite H2. cbn [rep app Nat.mul Nat.add]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity. }
    rewrite HD, HC. rewrite ?lift_app_blank_l, ?lift_app_blank. reflexivity.
Qed.

Lemma gopar1_1RB1LC_0LC0RB_0RD1LA_0LA1RD : forall p, cview p = (S 0, None) ->
  Cc p = cden [] [] 0 O1_1RB1LC_0LC0RB_0RD1LA_0LA1RD0 /\
  lift (cden [] [] 0 O1_1RB1LC_0LC0RB_0RD1LA_0LA1RD1) = lift (Cc (Pos.succ p)).
Proof.
  intros p E. destruct (KpCounter.cview_none_K p 0 E) as (H1 & H2).
  split.
  - unfold Cc_1RB1LC_0LC0RB_0RD1LA_0LA1RD, cden, O1_1RB1LC_0LC0RB_0RD1LA_0LA1RD0; cbn [c_st c_l c_h c_r].
    unfold sden; cbn [s_pre s_u s_a s_b s_post].
    rewrite H1; cbn [rep app Nat.mul Nat.add]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity.
  - assert (HD : cden [] [] 0 O1_1RB1LC_0LC0RB_0RD1LA_0LA1RD1 = (StB, ([S0;S1], S0, []))).
    { unfold cden, O1_1RB1LC_0LC0RB_0RD1LA_0LA1RD1, sden; cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
      cbn [rep app Nat.mul Nat.add]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity. }
    assert (HC : Cc (Pos.succ p) = (StB, (([S0;S1]) ++ [S0], S0, []))).
    { unfold Cc_1RB1LC_0LC0RB_0RD1LA_0LA1RD. rewrite H2. cbn [rep app Nat.mul Nat.add]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity. }
    rewrite HD, HC. rewrite ?lift_app_blank_l, ?lift_app_blank. reflexivity.
Qed.

Lemma gopar2_1RB1LC_0LC0RB_0RD1LA_0LA1RD : forall p j i, cview p = (S j, None) ->
  j = 2 * i + 3 ->
  Cc p = cden [] [] i O2_1RB1LC_0LC0RB_0RD1LA_0LA1RD0 /\
  lift (cden [] [] i O2_1RB1LC_0LC0RB_0RD1LA_0LA1RD1) = lift (Cc (Pos.succ p)).
Proof.
  intros p j i E Hj. destruct (KpCounter.cview_none_K p j E) as (H1 & H2).
  rewrite (repeq_1RB1LC_0LC0RB_0RD1LA_0LA1RD [S1] _ (2 * i + (4 + 0))) in H1 by lia.
  rewrite (repeq_1RB1LC_0LC0RB_0RD1LA_0LA1RD [S0] _ (2 * i + (4 + 0))) in H2 by lia.
  rewrite repm_1RB1LC_0LC0RB_0RD1LA_0LA1RD in H1, H2.
  split.
  - unfold Cc_1RB1LC_0LC0RB_0RD1LA_0LA1RD, cden, O2_1RB1LC_0LC0RB_0RD1LA_0LA1RD0; cbn [c_st c_l c_h c_r].
    unfold sden; cbn [s_pre s_u s_a s_b s_post].
    replace (1 * i + 0) with i by lia.
    rewrite H1; cbn [rep app Nat.mul Nat.add]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity.
  - assert (HD : cden [] [] i O2_1RB1LC_0LC0RB_0RD1LA_0LA1RD1 = (StB, ([S0;S0;S0;S0] ++ rep [S0;S0] i ++ [S1], S0, []))).
    { unfold cden, O2_1RB1LC_0LC0RB_0RD1LA_0LA1RD1, sden; cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
      replace (1 * i + 0) with i by lia. cbn [rep app Nat.mul Nat.add]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity. }
    assert (HC : Cc (Pos.succ p) = (StB, (([S0;S0;S0;S0] ++ rep [S0;S0] i ++ [S1]) ++ [S0], S0, []))).
    { unfold Cc_1RB1LC_0LC0RB_0RD1LA_0LA1RD. rewrite H2. cbn [rep app Nat.mul Nat.add]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity. }
    rewrite HD, HC. rewrite ?lift_app_blank_l, ?lift_app_blank. reflexivity.
Qed.

Lemma gopar3_1RB1LC_0LC0RB_0RD1LA_0LA1RD : forall p, cview p = (S 1, None) ->
  Cc p = cden [] [] 0 O3_1RB1LC_0LC0RB_0RD1LA_0LA1RD0 /\
  lift (cden [] [] 0 O3_1RB1LC_0LC0RB_0RD1LA_0LA1RD1) = lift (Cc (Pos.succ p)).
Proof.
  intros p E. destruct (KpCounter.cview_none_K p 1 E) as (H1 & H2).
  split.
  - unfold Cc_1RB1LC_0LC0RB_0RD1LA_0LA1RD, cden, O3_1RB1LC_0LC0RB_0RD1LA_0LA1RD0; cbn [c_st c_l c_h c_r].
    unfold sden; cbn [s_pre s_u s_a s_b s_post].
    rewrite H1; cbn [rep app Nat.mul Nat.add]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity.
  - assert (HD : cden [] [] 0 O3_1RB1LC_0LC0RB_0RD1LA_0LA1RD1 = (StB, ([S0;S0;S1], S0, []))).
    { unfold cden, O3_1RB1LC_0LC0RB_0RD1LA_0LA1RD1, sden; cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
      cbn [rep app Nat.mul Nat.add]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity. }
    assert (HC : Cc (Pos.succ p) = (StB, (([S0;S0;S1]) ++ [S0], S0, []))).
    { unfold Cc_1RB1LC_0LC0RB_0RD1LA_0LA1RD. rewrite H2. cbn [rep app Nat.mul Nat.add]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity. }
    rewrite HD, HC. rewrite ?lift_app_blank_l, ?lift_app_blank. reflexivity.
Qed.

Lemma lapo_1RB1LC_0LC0RB_0RD1LA_0LA1RD : forall p j, cview p = (S j, None) ->
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
      destruct (gopar1_1RB1LC_0LC0RB_0RD1LA_0LA1RD p E) as (HA & HB).
      exists (0 * 0 + 4), (cden [] [] 0 O1_1RB1LC_0LC0RB_0RD1LA_0LA1RD1).
      split; [| split; [exact HB | lia]].
      rewrite HA. exact (srun_sound tm true true cho1_1RB1LC_0LC0RB_0RD1LA_0LA1RD O1_1RB1LC_0LC0RB_0RD1LA_0LA1RD0 O1_1RB1LC_0LC0RB_0RD1LA_0LA1RD1 0 4
                 run_o1_1RB1LC_0LC0RB_0RD1LA_0LA1RD [] [] 0 ltac:(reflexivity) ltac:(reflexivity)).
    + destruct (gopar0_1RB1LC_0LC0RB_0RD1LA_0LA1RD p j i E ltac:(lia)) as (HA & HB).
      exists (4 * i + 8), (cden [] [] i O0_1RB1LC_0LC0RB_0RD1LA_0LA1RD1).
      split; [| split; [exact HB | lia]].
      rewrite HA. exact (srun_sound tm true true cho0_1RB1LC_0LC0RB_0RD1LA_0LA1RD O0_1RB1LC_0LC0RB_0RD1LA_0LA1RD0 O0_1RB1LC_0LC0RB_0RD1LA_0LA1RD1 4 8
                 run_o0_1RB1LC_0LC0RB_0RD1LA_0LA1RD [] [] i ltac:(reflexivity) ltac:(reflexivity)).
  - destruct i as [|i].
    + assert (Ej : j = 1) by lia. subst j.
      destruct (gopar3_1RB1LC_0LC0RB_0RD1LA_0LA1RD p E) as (HA & HB).
      exists (0 * 0 + 12), (cden [] [] 0 O3_1RB1LC_0LC0RB_0RD1LA_0LA1RD1).
      split; [| split; [exact HB | lia]].
      rewrite HA. exact (srun_sound tm true true cho3_1RB1LC_0LC0RB_0RD1LA_0LA1RD O3_1RB1LC_0LC0RB_0RD1LA_0LA1RD0 O3_1RB1LC_0LC0RB_0RD1LA_0LA1RD1 0 12
                 run_o3_1RB1LC_0LC0RB_0RD1LA_0LA1RD [] [] 0 ltac:(reflexivity) ltac:(reflexivity)).
    + destruct (gopar2_1RB1LC_0LC0RB_0RD1LA_0LA1RD p j i E ltac:(lia)) as (HA & HB).
      exists (8 * i + 20), (cden [] [] i O2_1RB1LC_0LC0RB_0RD1LA_0LA1RD1).
      split; [| split; [exact HB | lia]].
      rewrite HA. exact (srun_sound tm true true cho2_1RB1LC_0LC0RB_0RD1LA_0LA1RD O2_1RB1LC_0LC0RB_0RD1LA_0LA1RD0 O2_1RB1LC_0LC0RB_0RD1LA_0LA1RD1 8 20
                 run_o2_1RB1LC_0LC0RB_0RD1LA_0LA1RD [] [] i ltac:(reflexivity) ltac:(reflexivity)).
Qed.

(** ** The lap *)

Lemma lap_1RB1LC_0LC0RB_0RD1LA_0LA1RD : forall p, exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:E. destruct oq as [q0|].
  - destruct (lapi_1RB1LC_0LC0RB_0RD1LA_0LA1RD p j q0 E) as (n & Hn & Hrun).
    exists n, (Cc (Pos.succ p)).
    split; [exact Hrun | split; [reflexivity | exact Hn]].
  - destruct (cview_pos p j E) as (j' & ->).
    exact (lapo_1RB1LC_0LC0RB_0RD1LA_0LA1RD p j' E).
Qed.

(** ** Bootstrap *)

Lemma boot_1RB1LC_0LC0RB_0RD1LA_0LA1RD : exists t0, stepn tm t0 InitES = Some (lift (Cc 1)).
Proof.
  exists 1.
  assert (H : match csteps tm 1 c0 with
              | Some c => ceqb c (Cc 1) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 1 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** ** Visits

    Every state fires inside the OVERFLOW lap, so one prefix chain per state
    plus [LapCertGlue.vis_via_ovf] (run interior laps until the counter
    overflows -- they close exactly) covers every anchor. *)

Lemma fireo_1RB1LC_0LC0RB_0RD1LA_0LA1RD : forall (l0 l1 l2 l3 : list lstep) (t : Instr),
  srun_instr tm true true l0 O0_1RB1LC_0LC0RB_0RD1LA_0LA1RD0 = Some t ->
  srun_instr tm true true l1 O1_1RB1LC_0LC0RB_0RD1LA_0LA1RD0 = Some t ->
  srun_instr tm true true l2 O2_1RB1LC_0LC0RB_0RD1LA_0LA1RD0 = Some t ->
  srun_instr tm true true l3 O3_1RB1LC_0LC0RB_0RD1LA_0LA1RD0 = Some t ->
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
      destruct (gopar1_1RB1LC_0LC0RB_0RD1LA_0LA1RD p E) as (HA & _).
      exact (fire_of_run_instr tm Cc true true l1 O1_1RB1LC_0LC0RB_0RD1LA_0LA1RD0 p 0 [] [] t
               H1 ltac:(reflexivity) ltac:(reflexivity) HA).
    + destruct (gopar0_1RB1LC_0LC0RB_0RD1LA_0LA1RD p j i E ltac:(lia)) as (HA & _).
      exact (fire_of_run_instr tm Cc true true l0 O0_1RB1LC_0LC0RB_0RD1LA_0LA1RD0 p i [] [] t
               H0 ltac:(reflexivity) ltac:(reflexivity) HA).
  - destruct i as [|i].
    + assert (Ej : j = 1) by lia. subst j.
      destruct (gopar3_1RB1LC_0LC0RB_0RD1LA_0LA1RD p E) as (HA & _).
      exact (fire_of_run_instr tm Cc true true l3 O3_1RB1LC_0LC0RB_0RD1LA_0LA1RD0 p 0 [] [] t
               H3 ltac:(reflexivity) ltac:(reflexivity) HA).
    + destruct (gopar2_1RB1LC_0LC0RB_0RD1LA_0LA1RD p j i E ltac:(lia)) as (HA & _).
      exact (fire_of_run_instr tm Cc true true l2 O2_1RB1LC_0LC0RB_0RD1LA_0LA1RD0 p i [] [] t
               H2 ltac:(reflexivity) ltac:(reflexivity) HA).
Qed.

(** ** Fires: every UNPINNED instruction fires from every anchor
    (inside the overflow lap; [LapGlueTr.fire_via_ovf] runs the
    interior laps until the counter overflows). *)

Lemma fire_1RB1LC_0LC0RB_0RD1LA_0LA1RD : forall t, ~ In t pins_1RB1LC_0LC0RB_0RD1LA_0LA1RD ->
  forall p, exists k c, csteps tm k (Cc p) = Some c /\ cinstr c = t.
Proof.
  intros t Hnp p.
  assert (Hi : forall p0 j q0, cview p0 = (j, Some q0) ->
            exists n, 0 < n /\ csteps tm n (Cc p0) = Some (Cc (Pos.succ p0)))
    by exact lapi_1RB1LC_0LC0RB_0RD1LA_0LA1RD.
  destruct t as [q b]; destruct q, b.
  - (* A0 *)
    apply (fire_via_ovf tm Cc Hi (StA, S0)), (fireo_1RB1LC_0LC0RB_0RD1LA_0LA1RD
      ([SWin 3; SCycL 2 0; SWin 1])
      ([SWin 2])
      ([SWin 4; SCycL 2 0; SWin 2; SCycR 2; SWin 8; SCycL 2 0; SWin 1])
      ([SWin 9])); vm_compute; reflexivity.
  - (* A1 *)
    apply (fire_via_ovf tm Cc Hi (StA, S1)), (fireo_1RB1LC_0LC0RB_0RD1LA_0LA1RD
      ([SWin 2])
      ([SWin 4; SWin 6])
      ([SWin 2])
      ([SWin 2])); vm_compute; reflexivity.
  - (* B0 *)
    apply (fire_via_ovf tm Cc Hi (StB, S0)), (fireo_1RB1LC_0LC0RB_0RD1LA_0LA1RD
      ([])
      ([])
      ([])
      ([])); vm_compute; reflexivity.
  - (* B1 *)
    apply (fire_via_ovf tm Cc Hi (StB, S1)), (fireo_1RB1LC_0LC0RB_0RD1LA_0LA1RD
      ([SWin 3; SCycL 2 0; SWin 2])
      ([SWin 3])
      ([SWin 4; SCycL 2 0; SWin 2; SCycR 2; SWin 8; SCycL 2 0; SWin 2])
      ([SWin 10])); vm_compute; reflexivity.
  - (* C0 *)
    apply (fire_via_ovf tm Cc Hi (StC, S0)), (fireo_1RB1LC_0LC0RB_0RD1LA_0LA1RD
      ([SWin 3; SCycL 2 0; SWin 2; SCycR 2; SWin 3; SWin 1])
      ([SWin 4; SWin 1])
      ([SWin 4; SCycL 2 0; SWin 1])
      ([SWin 3])); vm_compute; reflexivity.
  - (* C1 *)
    apply (fire_via_ovf tm Cc Hi (StC, S1)), (fireo_1RB1LC_0LC0RB_0RD1LA_0LA1RD
      ([SWin 1])
      ([SWin 1])
      ([SWin 1])
      ([SWin 1])); vm_compute; reflexivity.
  - (* D0 *)
    apply (fire_via_ovf tm Cc Hi (StD, S0)), (fireo_1RB1LC_0LC0RB_0RD1LA_0LA1RD
      ([SWin 3; SCycL 2 0; SWin 2; SCycR 2; SWin 3; SWin 2])
      ([SWin 4; SWin 2])
      ([SWin 4; SCycL 2 0; SWin 2; SCycR 2; SWin 4])
      ([SWin 6])); vm_compute; reflexivity.
  - (* D1 *)
    apply (fire_via_ovf tm Cc Hi (StD, S1)), (fireo_1RB1LC_0LC0RB_0RD1LA_0LA1RD
      ([SWin 3; SCycL 2 0; SWin 2; SCycR 2; SWin 3; SWin 16])
      ([SWin 4; SWinL 8])
      ([SWin 4; SCycL 2 0; SWin 2])
      ([SWin 4])); vm_compute; reflexivity.
Qed.

Theorem nqhtr_1RB1LC_0LC0RB_0RD1LA_0LA1RD : NeverQuasiHaltsTr tm_1RB1LC_0LC0RB_0RD1LA_0LA1RD.
Proof.
  apply (glue_neverqhtr tm_1RB1LC_0LC0RB_0RD1LA_0LA1RD pins_1RB1LC_0LC0RB_0RD1LA_0LA1RD Cc 1).
  - exact boot_1RB1LC_0LC0RB_0RD1LA_0LA1RD.
  - intros p _. apply lap_1RB1LC_0LC0RB_0RD1LA_0LA1RD.
  - intros t Ht p _. apply fire_1RB1LC_0LC0RB_0RD1LA_0LA1RD. exact Ht.
Qed.

Theorem nonhalt_1RB1LC_0LC0RB_0RD1LA_0LA1RD : NonHalt tm_1RB1LC_0LC0RB_0RD1LA_0LA1RD.
Proof. apply never_qh_tr_nonhalt, nqhtr_1RB1LC_0LC0RB_0RD1LA_0LA1RD. Qed.
