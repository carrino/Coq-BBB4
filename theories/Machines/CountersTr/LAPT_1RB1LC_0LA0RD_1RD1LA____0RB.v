(** * LAPT_1RB1LC_0LA0RD_1RD1LA____0RB: TRANSITION-LEVEL board for machine 1RB1LC_0LA0RD_1RD1LA_---0RB, boarded by CERTIFICATE.

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

Definition mk_1RB1LC_0LA0RD_1RD1LA____0RB (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_1RB1LC_0LA0RD_1RD1LA____0RB.

(** 1RB1LC_0LA0RD_1RD1LA_---0RB *)
Definition tm_1RB1LC_0LA0RD_1RD1LA____0RB : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S1 DL StC
  | StB, S0 => mk S0 DL StA | StB, S1 => mk S0 DR StD
  | StC, S0 => mk S1 DR StD | StC, S1 => mk S1 DL StA
  | StD, S0 => None | StD, S1 => mk S0 DR StB end.
(** the instructions the certificate claims NEVER fire; the lap
    argument runs on the machine WRAPPED at them
    ([WrapTr.tm_wrap_trs]), so a pinned instruction firing would
    halt it and every [srun] below would fail. *)
Definition pins_1RB1LC_0LA0RD_1RD1LA____0RB : list Instr := [(StD, S0)].
Definition tmw_1RB1LC_0LA0RD_1RD1LA____0RB : TM := tm_wrap_trs tm_1RB1LC_0LA0RD_1RD1LA____0RB pins_1RB1LC_0LA0RD_1RD1LA____0RB.
Local Notation tm := tmw_1RB1LC_0LA0RD_1RD1LA____0RB.

Definition Cc_1RB1LC_0LA0RD_1RD1LA____0RB (p : positive) : cconf := (StB, (Kp p ++ [S0], S0, [])).
Local Notation Cc := Cc_1RB1LC_0LA0RD_1RD1LA____0RB.

(** ** The certificate *)

(** j = 2*i + 2 *)
Definition P0_1RB1LC_0LA0RD_1RD1LA____0RB0 : sconf := mkC StB (mkS [] [S1;S1] 1 0 [S1;S1;S0]) S0 (mkS [] [] 0 0 []).
Definition P0_1RB1LC_0LA0RD_1RD1LA____0RB1 : sconf := mkC StB (mkS [] [S0;S0] 1 0 [S0;S0;S1]) S0 (mkS [] [] 0 0 []).
Definition chp0_1RB1LC_0LA0RD_1RD1LA____0RB : list lstep := [SRotL 1; SWin 1; SCycL 2 0; SWin 4; SCycR 2; SWin 1; SUnrotL 1].

Lemma run_p0_1RB1LC_0LA0RD_1RD1LA____0RB : srun tm false true chp0_1RB1LC_0LA0RD_1RD1LA____0RB P0_1RB1LC_0LA0RD_1RD1LA____0RB0 = Some (P0_1RB1LC_0LA0RD_1RD1LA____0RB1, 4, 6).
Proof. vm_compute. reflexivity. Qed.

(** j = 0 (concrete) *)
Definition P1_1RB1LC_0LA0RD_1RD1LA____0RB0 : sconf := mkC StB (mkS [S0] [] 0 0 []) S0 (mkS [] [] 0 0 []).
Definition P1_1RB1LC_0LA0RD_1RD1LA____0RB1 : sconf := mkC StB (mkS [S1] [] 0 0 []) S0 (mkS [] [] 0 0 []).
Definition chp1_1RB1LC_0LA0RD_1RD1LA____0RB : list lstep := [SWin 2].

Lemma run_p1_1RB1LC_0LA0RD_1RD1LA____0RB : srun tm false true chp1_1RB1LC_0LA0RD_1RD1LA____0RB P1_1RB1LC_0LA0RD_1RD1LA____0RB0 = Some (P1_1RB1LC_0LA0RD_1RD1LA____0RB1, 0, 2).
Proof. vm_compute. reflexivity. Qed.

(** j = 2*i + 1 *)
Definition P2_1RB1LC_0LA0RD_1RD1LA____0RB0 : sconf := mkC StB (mkS [] [S1;S1] 1 0 [S1;S0]) S0 (mkS [] [] 0 0 []).
Definition P2_1RB1LC_0LA0RD_1RD1LA____0RB1 : sconf := mkC StB (mkS [] [S0;S0] 1 0 [S0;S1]) S0 (mkS [] [] 0 0 []).
Definition chp2_1RB1LC_0LA0RD_1RD1LA____0RB : list lstep := [SRotL 1; SWin 1; SCycL 2 0; SWin 2; SCycR 2; SWin 1; SUnrotL 1].

Lemma run_p2_1RB1LC_0LA0RD_1RD1LA____0RB : srun tm false true chp2_1RB1LC_0LA0RD_1RD1LA____0RB P2_1RB1LC_0LA0RD_1RD1LA____0RB0 = Some (P2_1RB1LC_0LA0RD_1RD1LA____0RB1, 4, 4).
Proof. vm_compute. reflexivity. Qed.

Definition B0_1RB1LC_0LA0RD_1RD1LA____0RB : sconf := mkC StB (mkS [S1;S1;S1] [S1;S1] 1 0 [S0]) S0 (mkS [] [] 0 0 []).
Definition B1_1RB1LC_0LA0RD_1RD1LA____0RB : sconf := mkC StB (mkS [S0;S0;S0] [S0;S0] 1 0 [S1]) S0 (mkS [] [] 0 0 []).
(** j = 2*i + 2 *)
Definition O0_1RB1LC_0LA0RD_1RD1LA____0RB0 : sconf := mkC StB (mkS [S1;S1;S1] [S1;S1] 1 0 [S0]) S0 (mkS [] [] 0 0 []).
Definition O0_1RB1LC_0LA0RD_1RD1LA____0RB1 : sconf := mkC StB (mkS [S0;S0;S0] [S0;S0] 1 0 [S1]) S0 (mkS [] [] 0 0 []).
Definition cho0_1RB1LC_0LA0RD_1RD1LA____0RB : list lstep := [SWin 3; SCycL 2 0; SWin 2; SCycR 2; SWin 3].

Lemma run_o0_1RB1LC_0LA0RD_1RD1LA____0RB : srun tm true true cho0_1RB1LC_0LA0RD_1RD1LA____0RB O0_1RB1LC_0LA0RD_1RD1LA____0RB0 = Some (O0_1RB1LC_0LA0RD_1RD1LA____0RB1, 4, 8).
Proof. vm_compute. reflexivity. Qed.

(** j = 0 (concrete) *)
Definition O1_1RB1LC_0LA0RD_1RD1LA____0RB0 : sconf := mkC StB (mkS [S1;S0] [] 0 0 []) S0 (mkS [] [] 0 0 []).
Definition O1_1RB1LC_0LA0RD_1RD1LA____0RB1 : sconf := mkC StB (mkS [S0;S1] [] 0 0 []) S0 (mkS [] [] 0 0 []).
Definition cho1_1RB1LC_0LA0RD_1RD1LA____0RB : list lstep := [SWin 4].

Lemma run_o1_1RB1LC_0LA0RD_1RD1LA____0RB : srun tm true true cho1_1RB1LC_0LA0RD_1RD1LA____0RB O1_1RB1LC_0LA0RD_1RD1LA____0RB0 = Some (O1_1RB1LC_0LA0RD_1RD1LA____0RB1, 0, 4).
Proof. vm_compute. reflexivity. Qed.

(** j = 2*i + 3 *)
Definition O2_1RB1LC_0LA0RD_1RD1LA____0RB0 : sconf := mkC StB (mkS [S1;S1;S1;S1] [S1;S1] 1 0 [S0]) S0 (mkS [] [] 0 0 []).
Definition O2_1RB1LC_0LA0RD_1RD1LA____0RB1 : sconf := mkC StB (mkS [S0;S0;S0;S0] [S0;S0] 1 0 [S1]) S0 (mkS [] [] 0 0 []).
Definition cho2_1RB1LC_0LA0RD_1RD1LA____0RB : list lstep := [SWin 4; SCycL 2 0; SWin 2; SCycR 2; SWin 4].

Lemma run_o2_1RB1LC_0LA0RD_1RD1LA____0RB : srun tm true true cho2_1RB1LC_0LA0RD_1RD1LA____0RB O2_1RB1LC_0LA0RD_1RD1LA____0RB0 = Some (O2_1RB1LC_0LA0RD_1RD1LA____0RB1, 4, 10).
Proof. vm_compute. reflexivity. Qed.

(** j = 1 (concrete) *)
Definition O3_1RB1LC_0LA0RD_1RD1LA____0RB0 : sconf := mkC StB (mkS [S1;S1;S0] [] 0 0 []) S0 (mkS [] [] 0 0 []).
Definition O3_1RB1LC_0LA0RD_1RD1LA____0RB1 : sconf := mkC StB (mkS [S0;S0;S1] [] 0 0 []) S0 (mkS [] [] 0 0 []).
Definition cho3_1RB1LC_0LA0RD_1RD1LA____0RB : list lstep := [SWin 6].

Lemma run_o3_1RB1LC_0LA0RD_1RD1LA____0RB : srun tm true true cho3_1RB1LC_0LA0RD_1RD1LA____0RB O3_1RB1LC_0LA0RD_1RD1LA____0RB0 = Some (O3_1RB1LC_0LA0RD_1RD1LA____0RB1, 0, 6).
Proof. vm_compute. reflexivity. Qed.

(** ** Anchor glue -- the only per-machine mathematics *)

(** [rep] at [j = m*i + (c1 + c2)]: the residue cases' only algebra. *)
Lemma repeq_1RB1LC_0LA0RD_1RD1LA____0RB : forall (u : list Sym) n m, n = m -> rep u n = rep u m.
Proof. intros u n m ->. reflexivity. Qed.

Lemma repmul_1RB1LC_0LA0RD_1RD1LA____0RB : forall (u : list Sym) m i, rep u (m * i) = rep (rep u m) i.
Proof.
  intros u m i. induction i as [|i IH]; [rewrite Nat.mul_0_r; reflexivity|].
  replace (m * S i) with (m + m * i) by lia. rewrite rep_add, IH. reflexivity.
Qed.

Lemma repm_1RB1LC_0LA0RD_1RD1LA____0RB : forall (u : list Sym) m i c1 c2,
  rep u (m * i + (c1 + c2)) = rep u c1 ++ rep (rep u m) i ++ rep u c2.
Proof.
  intros u m i c1 c2.
  replace (m * i + (c1 + c2)) with (c1 + (m * i + c2)) by lia.
  rewrite !rep_add, repmul_1RB1LC_0LA0RD_1RD1LA____0RB. reflexivity.
Qed.

Lemma gpar0_1RB1LC_0LA0RD_1RD1LA____0RB : forall p j q0 i, cview p = (j, Some q0) ->
  j = 2 * i + 2 ->
  Cc p = cden (Kp q0 ++ [S0]) [] i P0_1RB1LC_0LA0RD_1RD1LA____0RB0 /\ cden (Kp q0 ++ [S0]) [] i P0_1RB1LC_0LA0RD_1RD1LA____0RB1 = Cc (Pos.succ p).
Proof.
  intros p j q0 i E Hj. destruct (KpCounter.cview_some_K p j q0 E) as (H1 & H2).
  rewrite (repeq_1RB1LC_0LA0RD_1RD1LA____0RB [S1] _ (2 * i + (0 + 2))) in H1 by lia.
  rewrite (repeq_1RB1LC_0LA0RD_1RD1LA____0RB [S0] _ (2 * i + (0 + 2))) in H2 by lia.
  rewrite repm_1RB1LC_0LA0RD_1RD1LA____0RB in H1, H2.
  unfold Cc_1RB1LC_0LA0RD_1RD1LA____0RB, cden, P0_1RB1LC_0LA0RD_1RD1LA____0RB0, P0_1RB1LC_0LA0RD_1RD1LA____0RB1; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia.
  split; [rewrite H1 | rewrite H2]; cbn [rep app Nat.mul Nat.add]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity.
Qed.

Lemma gpar1_1RB1LC_0LA0RD_1RD1LA____0RB : forall p q0, cview p = (0, Some q0) ->
  Cc p = cden (Kp q0 ++ [S0]) [] 0 P1_1RB1LC_0LA0RD_1RD1LA____0RB0 /\ cden (Kp q0 ++ [S0]) [] 0 P1_1RB1LC_0LA0RD_1RD1LA____0RB1 = Cc (Pos.succ p).
Proof.
  intros p q0 E. destruct (KpCounter.cview_some_K p 0 q0 E) as (H1 & H2).
  unfold Cc_1RB1LC_0LA0RD_1RD1LA____0RB, cden, P1_1RB1LC_0LA0RD_1RD1LA____0RB0, P1_1RB1LC_0LA0RD_1RD1LA____0RB1; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  split; [rewrite H1 | rewrite H2]; cbn [rep app Nat.mul Nat.add]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity.
Qed.

Lemma gpar2_1RB1LC_0LA0RD_1RD1LA____0RB : forall p j q0 i, cview p = (j, Some q0) ->
  j = 2 * i + 1 ->
  Cc p = cden (Kp q0 ++ [S0]) [] i P2_1RB1LC_0LA0RD_1RD1LA____0RB0 /\ cden (Kp q0 ++ [S0]) [] i P2_1RB1LC_0LA0RD_1RD1LA____0RB1 = Cc (Pos.succ p).
Proof.
  intros p j q0 i E Hj. destruct (KpCounter.cview_some_K p j q0 E) as (H1 & H2).
  rewrite (repeq_1RB1LC_0LA0RD_1RD1LA____0RB [S1] _ (2 * i + (0 + 1))) in H1 by lia.
  rewrite (repeq_1RB1LC_0LA0RD_1RD1LA____0RB [S0] _ (2 * i + (0 + 1))) in H2 by lia.
  rewrite repm_1RB1LC_0LA0RD_1RD1LA____0RB in H1, H2.
  unfold Cc_1RB1LC_0LA0RD_1RD1LA____0RB, cden, P2_1RB1LC_0LA0RD_1RD1LA____0RB0, P2_1RB1LC_0LA0RD_1RD1LA____0RB1; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia.
  split; [rewrite H1 | rewrite H2]; cbn [rep app Nat.mul Nat.add]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity.
Qed.

Lemma lapi_1RB1LC_0LA0RD_1RD1LA____0RB : forall p j q0, cview p = (j, Some q0) ->
  exists n, 0 < n /\ csteps tm n (Cc p) = Some (Cc (Pos.succ p)).
Proof.
  intros p j q0 E.
  pose proof (Nat.div_mod_eq j 2) as Hd.
  pose proof (Nat.mod_upper_bound j 2 ltac:(discriminate)) as Hm.
  set (i := j / 2) in *. set (r := j mod 2) in *. clearbody i r.
  destruct r as [|[|r]]; [idtac | idtac | exfalso; lia].
  - destruct i as [|i].
    + assert (Ej : j = 0) by lia. subst j.
      destruct (gpar1_1RB1LC_0LA0RD_1RD1LA____0RB p q0 E) as (HA & HB).
      exists (0 * 0 + 2). split; [lia|]. rewrite HA.
      rewrite (srun_sound tm false true chp1_1RB1LC_0LA0RD_1RD1LA____0RB P1_1RB1LC_0LA0RD_1RD1LA____0RB0 P1_1RB1LC_0LA0RD_1RD1LA____0RB1 0 2
                 run_p1_1RB1LC_0LA0RD_1RD1LA____0RB (Kp q0 ++ [S0]) [] 0 ltac:(discriminate) ltac:(reflexivity)).
      f_equal. exact HB.
    + destruct (gpar0_1RB1LC_0LA0RD_1RD1LA____0RB p j q0 i E ltac:(lia)) as (HA & HB).
      exists (4 * i + 6). split; [lia|]. rewrite HA.
      rewrite (srun_sound tm false true chp0_1RB1LC_0LA0RD_1RD1LA____0RB P0_1RB1LC_0LA0RD_1RD1LA____0RB0 P0_1RB1LC_0LA0RD_1RD1LA____0RB1 4 6
                 run_p0_1RB1LC_0LA0RD_1RD1LA____0RB (Kp q0 ++ [S0]) [] i ltac:(discriminate) ltac:(reflexivity)).
      f_equal. exact HB.
  - destruct (gpar2_1RB1LC_0LA0RD_1RD1LA____0RB p j q0 i E ltac:(lia)) as (HA & HB).
    exists (4 * i + 4). split; [lia|]. rewrite HA.
    rewrite (srun_sound tm false true chp2_1RB1LC_0LA0RD_1RD1LA____0RB P2_1RB1LC_0LA0RD_1RD1LA____0RB0 P2_1RB1LC_0LA0RD_1RD1LA____0RB1 4 4
               run_p2_1RB1LC_0LA0RD_1RD1LA____0RB (Kp q0 ++ [S0]) [] i ltac:(discriminate) ltac:(reflexivity)).
    f_equal. exact HB.
Qed.

Lemma lbl_1RB1LC_0LA0RD_1RD1LA____0RB : forall q l h r, lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.

Lemma gopar0_1RB1LC_0LA0RD_1RD1LA____0RB : forall p j i, cview p = (S j, None) ->
  j = 2 * i + 2 ->
  Cc p = cden [] [] i O0_1RB1LC_0LA0RD_1RD1LA____0RB0 /\
  lift (cden [] [] i O0_1RB1LC_0LA0RD_1RD1LA____0RB1) = lift (Cc (Pos.succ p)).
Proof.
  intros p j i E Hj. destruct (KpCounter.cview_none_K p j E) as (H1 & H2).
  rewrite (repeq_1RB1LC_0LA0RD_1RD1LA____0RB [S1] _ (2 * i + (3 + 0))) in H1 by lia.
  rewrite (repeq_1RB1LC_0LA0RD_1RD1LA____0RB [S0] _ (2 * i + (3 + 0))) in H2 by lia.
  rewrite repm_1RB1LC_0LA0RD_1RD1LA____0RB in H1, H2.
  split.
  - unfold Cc_1RB1LC_0LA0RD_1RD1LA____0RB, cden, O0_1RB1LC_0LA0RD_1RD1LA____0RB0; cbn [c_st c_l c_h c_r].
    unfold sden; cbn [s_pre s_u s_a s_b s_post].
    replace (1 * i + 0) with i by lia.
    rewrite H1; cbn [rep app Nat.mul Nat.add]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity.
  - assert (HD : cden [] [] i O0_1RB1LC_0LA0RD_1RD1LA____0RB1 = (StB, ([S0;S0;S0] ++ rep [S0;S0] i ++ [S1], S0, []))).
    { unfold cden, O0_1RB1LC_0LA0RD_1RD1LA____0RB1, sden; cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
      replace (1 * i + 0) with i by lia. cbn [rep app Nat.mul Nat.add]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity. }
    assert (HC : Cc (Pos.succ p) = (StB, (([S0;S0;S0] ++ rep [S0;S0] i ++ [S1]) ++ [S0], S0, []))).
    { unfold Cc_1RB1LC_0LA0RD_1RD1LA____0RB. rewrite H2. cbn [rep app Nat.mul Nat.add]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity. }
    rewrite HD, HC. rewrite ?lift_app_blank_l, ?lift_app_blank. reflexivity.
Qed.

Lemma gopar1_1RB1LC_0LA0RD_1RD1LA____0RB : forall p, cview p = (S 0, None) ->
  Cc p = cden [] [] 0 O1_1RB1LC_0LA0RD_1RD1LA____0RB0 /\
  lift (cden [] [] 0 O1_1RB1LC_0LA0RD_1RD1LA____0RB1) = lift (Cc (Pos.succ p)).
Proof.
  intros p E. destruct (KpCounter.cview_none_K p 0 E) as (H1 & H2).
  split.
  - unfold Cc_1RB1LC_0LA0RD_1RD1LA____0RB, cden, O1_1RB1LC_0LA0RD_1RD1LA____0RB0; cbn [c_st c_l c_h c_r].
    unfold sden; cbn [s_pre s_u s_a s_b s_post].
    rewrite H1; cbn [rep app Nat.mul Nat.add]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity.
  - assert (HD : cden [] [] 0 O1_1RB1LC_0LA0RD_1RD1LA____0RB1 = (StB, ([S0;S1], S0, []))).
    { unfold cden, O1_1RB1LC_0LA0RD_1RD1LA____0RB1, sden; cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
      cbn [rep app Nat.mul Nat.add]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity. }
    assert (HC : Cc (Pos.succ p) = (StB, (([S0;S1]) ++ [S0], S0, []))).
    { unfold Cc_1RB1LC_0LA0RD_1RD1LA____0RB. rewrite H2. cbn [rep app Nat.mul Nat.add]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity. }
    rewrite HD, HC. rewrite ?lift_app_blank_l, ?lift_app_blank. reflexivity.
Qed.

Lemma gopar2_1RB1LC_0LA0RD_1RD1LA____0RB : forall p j i, cview p = (S j, None) ->
  j = 2 * i + 3 ->
  Cc p = cden [] [] i O2_1RB1LC_0LA0RD_1RD1LA____0RB0 /\
  lift (cden [] [] i O2_1RB1LC_0LA0RD_1RD1LA____0RB1) = lift (Cc (Pos.succ p)).
Proof.
  intros p j i E Hj. destruct (KpCounter.cview_none_K p j E) as (H1 & H2).
  rewrite (repeq_1RB1LC_0LA0RD_1RD1LA____0RB [S1] _ (2 * i + (4 + 0))) in H1 by lia.
  rewrite (repeq_1RB1LC_0LA0RD_1RD1LA____0RB [S0] _ (2 * i + (4 + 0))) in H2 by lia.
  rewrite repm_1RB1LC_0LA0RD_1RD1LA____0RB in H1, H2.
  split.
  - unfold Cc_1RB1LC_0LA0RD_1RD1LA____0RB, cden, O2_1RB1LC_0LA0RD_1RD1LA____0RB0; cbn [c_st c_l c_h c_r].
    unfold sden; cbn [s_pre s_u s_a s_b s_post].
    replace (1 * i + 0) with i by lia.
    rewrite H1; cbn [rep app Nat.mul Nat.add]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity.
  - assert (HD : cden [] [] i O2_1RB1LC_0LA0RD_1RD1LA____0RB1 = (StB, ([S0;S0;S0;S0] ++ rep [S0;S0] i ++ [S1], S0, []))).
    { unfold cden, O2_1RB1LC_0LA0RD_1RD1LA____0RB1, sden; cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
      replace (1 * i + 0) with i by lia. cbn [rep app Nat.mul Nat.add]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity. }
    assert (HC : Cc (Pos.succ p) = (StB, (([S0;S0;S0;S0] ++ rep [S0;S0] i ++ [S1]) ++ [S0], S0, []))).
    { unfold Cc_1RB1LC_0LA0RD_1RD1LA____0RB. rewrite H2. cbn [rep app Nat.mul Nat.add]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity. }
    rewrite HD, HC. rewrite ?lift_app_blank_l, ?lift_app_blank. reflexivity.
Qed.

Lemma gopar3_1RB1LC_0LA0RD_1RD1LA____0RB : forall p, cview p = (S 1, None) ->
  Cc p = cden [] [] 0 O3_1RB1LC_0LA0RD_1RD1LA____0RB0 /\
  lift (cden [] [] 0 O3_1RB1LC_0LA0RD_1RD1LA____0RB1) = lift (Cc (Pos.succ p)).
Proof.
  intros p E. destruct (KpCounter.cview_none_K p 1 E) as (H1 & H2).
  split.
  - unfold Cc_1RB1LC_0LA0RD_1RD1LA____0RB, cden, O3_1RB1LC_0LA0RD_1RD1LA____0RB0; cbn [c_st c_l c_h c_r].
    unfold sden; cbn [s_pre s_u s_a s_b s_post].
    rewrite H1; cbn [rep app Nat.mul Nat.add]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity.
  - assert (HD : cden [] [] 0 O3_1RB1LC_0LA0RD_1RD1LA____0RB1 = (StB, ([S0;S0;S1], S0, []))).
    { unfold cden, O3_1RB1LC_0LA0RD_1RD1LA____0RB1, sden; cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
      cbn [rep app Nat.mul Nat.add]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity. }
    assert (HC : Cc (Pos.succ p) = (StB, (([S0;S0;S1]) ++ [S0], S0, []))).
    { unfold Cc_1RB1LC_0LA0RD_1RD1LA____0RB. rewrite H2. cbn [rep app Nat.mul Nat.add]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity. }
    rewrite HD, HC. rewrite ?lift_app_blank_l, ?lift_app_blank. reflexivity.
Qed.

Lemma lapo_1RB1LC_0LA0RD_1RD1LA____0RB : forall p j, cview p = (S j, None) ->
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
      destruct (gopar1_1RB1LC_0LA0RD_1RD1LA____0RB p E) as (HA & HB).
      exists (0 * 0 + 4), (cden [] [] 0 O1_1RB1LC_0LA0RD_1RD1LA____0RB1).
      split; [| split; [exact HB | lia]].
      rewrite HA. exact (srun_sound tm true true cho1_1RB1LC_0LA0RD_1RD1LA____0RB O1_1RB1LC_0LA0RD_1RD1LA____0RB0 O1_1RB1LC_0LA0RD_1RD1LA____0RB1 0 4
                 run_o1_1RB1LC_0LA0RD_1RD1LA____0RB [] [] 0 ltac:(reflexivity) ltac:(reflexivity)).
    + destruct (gopar0_1RB1LC_0LA0RD_1RD1LA____0RB p j i E ltac:(lia)) as (HA & HB).
      exists (4 * i + 8), (cden [] [] i O0_1RB1LC_0LA0RD_1RD1LA____0RB1).
      split; [| split; [exact HB | lia]].
      rewrite HA. exact (srun_sound tm true true cho0_1RB1LC_0LA0RD_1RD1LA____0RB O0_1RB1LC_0LA0RD_1RD1LA____0RB0 O0_1RB1LC_0LA0RD_1RD1LA____0RB1 4 8
                 run_o0_1RB1LC_0LA0RD_1RD1LA____0RB [] [] i ltac:(reflexivity) ltac:(reflexivity)).
  - destruct i as [|i].
    + assert (Ej : j = 1) by lia. subst j.
      destruct (gopar3_1RB1LC_0LA0RD_1RD1LA____0RB p E) as (HA & HB).
      exists (0 * 0 + 6), (cden [] [] 0 O3_1RB1LC_0LA0RD_1RD1LA____0RB1).
      split; [| split; [exact HB | lia]].
      rewrite HA. exact (srun_sound tm true true cho3_1RB1LC_0LA0RD_1RD1LA____0RB O3_1RB1LC_0LA0RD_1RD1LA____0RB0 O3_1RB1LC_0LA0RD_1RD1LA____0RB1 0 6
                 run_o3_1RB1LC_0LA0RD_1RD1LA____0RB [] [] 0 ltac:(reflexivity) ltac:(reflexivity)).
    + destruct (gopar2_1RB1LC_0LA0RD_1RD1LA____0RB p j i E ltac:(lia)) as (HA & HB).
      exists (4 * i + 10), (cden [] [] i O2_1RB1LC_0LA0RD_1RD1LA____0RB1).
      split; [| split; [exact HB | lia]].
      rewrite HA. exact (srun_sound tm true true cho2_1RB1LC_0LA0RD_1RD1LA____0RB O2_1RB1LC_0LA0RD_1RD1LA____0RB0 O2_1RB1LC_0LA0RD_1RD1LA____0RB1 4 10
                 run_o2_1RB1LC_0LA0RD_1RD1LA____0RB [] [] i ltac:(reflexivity) ltac:(reflexivity)).
Qed.

(** ** The lap *)

Lemma lap_1RB1LC_0LA0RD_1RD1LA____0RB : forall p, exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:E. destruct oq as [q0|].
  - destruct (lapi_1RB1LC_0LA0RD_1RD1LA____0RB p j q0 E) as (n & Hn & Hrun).
    exists n, (Cc (Pos.succ p)).
    split; [exact Hrun | split; [reflexivity | exact Hn]].
  - destruct (cview_pos p j E) as (j' & ->).
    exact (lapo_1RB1LC_0LA0RD_1RD1LA____0RB p j' E).
Qed.

(** ** Bootstrap *)

Lemma boot_1RB1LC_0LA0RD_1RD1LA____0RB : exists t0, stepn tm t0 InitES = Some (lift (Cc 1)).
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

Lemma fireo_1RB1LC_0LA0RD_1RD1LA____0RB : forall (l0 l1 l2 l3 : list lstep) (t : Instr),
  srun_instr tm true true l0 O0_1RB1LC_0LA0RD_1RD1LA____0RB0 = Some t ->
  srun_instr tm true true l1 O1_1RB1LC_0LA0RD_1RD1LA____0RB0 = Some t ->
  srun_instr tm true true l2 O2_1RB1LC_0LA0RD_1RD1LA____0RB0 = Some t ->
  srun_instr tm true true l3 O3_1RB1LC_0LA0RD_1RD1LA____0RB0 = Some t ->
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
      destruct (gopar1_1RB1LC_0LA0RD_1RD1LA____0RB p E) as (HA & _).
      exact (fire_of_run_instr tm Cc true true l1 O1_1RB1LC_0LA0RD_1RD1LA____0RB0 p 0 [] [] t
               H1 ltac:(reflexivity) ltac:(reflexivity) HA).
    + destruct (gopar0_1RB1LC_0LA0RD_1RD1LA____0RB p j i E ltac:(lia)) as (HA & _).
      exact (fire_of_run_instr tm Cc true true l0 O0_1RB1LC_0LA0RD_1RD1LA____0RB0 p i [] [] t
               H0 ltac:(reflexivity) ltac:(reflexivity) HA).
  - destruct i as [|i].
    + assert (Ej : j = 1) by lia. subst j.
      destruct (gopar3_1RB1LC_0LA0RD_1RD1LA____0RB p E) as (HA & _).
      exact (fire_of_run_instr tm Cc true true l3 O3_1RB1LC_0LA0RD_1RD1LA____0RB0 p 0 [] [] t
               H3 ltac:(reflexivity) ltac:(reflexivity) HA).
    + destruct (gopar2_1RB1LC_0LA0RD_1RD1LA____0RB p j i E ltac:(lia)) as (HA & _).
      exact (fire_of_run_instr tm Cc true true l2 O2_1RB1LC_0LA0RD_1RD1LA____0RB0 p i [] [] t
               H2 ltac:(reflexivity) ltac:(reflexivity) HA).
Qed.

(** ** Fires: every UNPINNED instruction fires from every anchor
    (inside the overflow lap; [LapGlueTr.fire_via_ovf] runs the
    interior laps until the counter overflows). *)

Lemma fire_1RB1LC_0LA0RD_1RD1LA____0RB : forall t, ~ In t pins_1RB1LC_0LA0RD_1RD1LA____0RB ->
  forall p, exists k c, csteps tm k (Cc p) = Some c /\ cinstr c = t.
Proof.
  intros t Hnp p.
  assert (Hi : forall p0 j q0, cview p0 = (j, Some q0) ->
            exists n, 0 < n /\ csteps tm n (Cc p0) = Some (Cc (Pos.succ p0)))
    by exact lapi_1RB1LC_0LA0RD_1RD1LA____0RB.
  destruct t as [q b]; destruct q, b.
  - (* A0 *)
    apply (fire_via_ovf tm Cc Hi (StA, S0)), (fireo_1RB1LC_0LA0RD_1RD1LA____0RB
      ([SWin 3; SCycL 2 0; SWin 2; SCycR 2; SWin 3; SWin 1])
      ([SWin 4; SWin 1])
      ([SWin 4; SCycL 2 0; SWin 1])
      ([SWin 3])); vm_compute; reflexivity.
  - (* A1 *)
    apply (fire_via_ovf tm Cc Hi (StA, S1)), (fireo_1RB1LC_0LA0RD_1RD1LA____0RB
      ([SWin 1])
      ([SWin 1])
      ([SWin 1])
      ([SWin 1])); vm_compute; reflexivity.
  - (* B0 *)
    apply (fire_via_ovf tm Cc Hi (StB, S0)), (fireo_1RB1LC_0LA0RD_1RD1LA____0RB
      ([])
      ([])
      ([])
      ([])); vm_compute; reflexivity.
  - (* B1 *)
    apply (fire_via_ovf tm Cc Hi (StB, S1)), (fireo_1RB1LC_0LA0RD_1RD1LA____0RB
      ([SWin 3; SCycL 2 0; SWin 2; SCycR 2; SWin 1])
      ([SWin 4; SWinL 6])
      ([SWin 4; SCycL 2 0; SWin 2])
      ([SWin 4])); vm_compute; reflexivity.
  - (* C0 *)
    apply (fire_via_ovf tm Cc Hi (StC, S0)), (fireo_1RB1LC_0LA0RD_1RD1LA____0RB
      ([SWin 3; SCycL 2 0; SWin 1])
      ([SWin 2])
      ([SWin 4; SCycL 2 0; SWin 2; SCycR 2; SWin 4; SWin 4])
      ([SWin 6; SWin 4])); vm_compute; reflexivity.
  - (* C1 *)
    apply (fire_via_ovf tm Cc Hi (StC, S1)), (fireo_1RB1LC_0LA0RD_1RD1LA____0RB
      ([SWin 2])
      ([SWin 4; SWin 4])
      ([SWin 2])
      ([SWin 2])); vm_compute; reflexivity.
  - (* D0: pinned *)
    exfalso. apply Hnp. apply tr_inb_spec. reflexivity.
  - (* D1 *)
    apply (fire_via_ovf tm Cc Hi (StD, S1)), (fireo_1RB1LC_0LA0RD_1RD1LA____0RB
      ([SWin 3; SCycL 2 0; SWin 2])
      ([SWin 3])
      ([SWin 4; SCycL 2 0; SWin 2; SCycR 2; SWin 1])
      ([SWin 5])); vm_compute; reflexivity.
Qed.

Theorem nqhtr_1RB1LC_0LA0RD_1RD1LA____0RB : NeverQuasiHaltsTr tm_1RB1LC_0LA0RD_1RD1LA____0RB.
Proof.
  apply (glue_neverqhtr tm_1RB1LC_0LA0RD_1RD1LA____0RB pins_1RB1LC_0LA0RD_1RD1LA____0RB Cc 1).
  - exact boot_1RB1LC_0LA0RD_1RD1LA____0RB.
  - intros p _. apply lap_1RB1LC_0LA0RD_1RD1LA____0RB.
  - intros t Ht p _. apply fire_1RB1LC_0LA0RD_1RD1LA____0RB. exact Ht.
Qed.

Theorem nonhalt_1RB1LC_0LA0RD_1RD1LA____0RB : NonHalt tm_1RB1LC_0LA0RD_1RD1LA____0RB.
Proof. apply never_qh_tr_nonhalt, nqhtr_1RB1LC_0LA0RD_1RD1LA____0RB. Qed.
