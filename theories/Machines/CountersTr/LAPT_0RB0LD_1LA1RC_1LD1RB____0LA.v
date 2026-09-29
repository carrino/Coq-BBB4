(** * LAPT_0RB0LD_1LA1RC_1LD1RB____0LA: TRANSITION-LEVEL board for machine 0RB0LD_1LA1RC_1LD1RB_---0LA, boarded by CERTIFICATE.

    Auto-emitted by tools/counters/emit_lapcert.py (UNTRUSTED emitter; the Coq
    kernel re-runs the checker on every line below).  Left-growth binary
    counter under the Kp digit alphabet (KpCounter.v), anchored at

      Cc p = (StA, (Kp p ++ [S0], S0, []))

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

Definition mk_0RB0LD_1LA1RC_1LD1RB____0LA (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_0RB0LD_1LA1RC_1LD1RB____0LA.

(** 0RB0LD_1LA1RC_1LD1RB_---0LA *)
(** 0RB0LD_1LA1RC_1LD1RB_---0LA -- the real machine (its counter grows RIGHT). *)
Definition tm_0RB0LD_1LA1RC_1LD1RB____0LA : TM := fun q s => match q, s with
  | StA, S0 => mk S0 DR StB | StA, S1 => mk S0 DL StD
  | StB, S0 => mk S1 DL StA | StB, S1 => mk S1 DR StC
  | StC, S0 => mk S1 DL StD | StC, S1 => mk S1 DR StB
  | StD, S0 => None | StD, S1 => mk S0 DL StA end.

(** Its mirror 0LB0RD_1RA1LC_1RD1LB_---0RA: the same counter grown leftward.  Every
    lemma below runs on the MIRRORED table;
    [Mirror.mirror_never_qh] transfers the conclusion back. *)
Definition tmm_0RB0LD_1LA1RC_1LD1RB____0LA : TM := fun q s => match q, s with
  | StA, S0 => mk S0 DL StB | StA, S1 => mk S0 DR StD
  | StB, S0 => mk S1 DR StA | StB, S1 => mk S1 DL StC
  | StC, S0 => mk S1 DR StD | StC, S1 => mk S1 DL StB
  | StD, S0 => None | StD, S1 => mk S0 DR StA end.
(** the instructions the certificate claims NEVER fire; the lap
    argument runs on the machine WRAPPED at them
    ([WrapTr.tm_wrap_trs]), so a pinned instruction firing would
    halt it and every [srun] below would fail. *)
Definition pins_0RB0LD_1LA1RC_1LD1RB____0LA : list Instr := [(StD, S0)].
Definition tmw_0RB0LD_1LA1RC_1LD1RB____0LA : TM := tm_wrap_trs tmm_0RB0LD_1LA1RC_1LD1RB____0LA pins_0RB0LD_1LA1RC_1LD1RB____0LA.
Local Notation tm := tmw_0RB0LD_1LA1RC_1LD1RB____0LA.

Lemma mirror_ok_0RB0LD_1LA1RC_1LD1RB____0LA : mirror_tm tm_0RB0LD_1LA1RC_1LD1RB____0LA = tmm_0RB0LD_1LA1RC_1LD1RB____0LA.
Proof.
  apply functional_extensionality; intro q;
    apply functional_extensionality; intro b; destruct q, b; reflexivity.
Qed.

Definition Cc_0RB0LD_1LA1RC_1LD1RB____0LA (p : positive) : cconf := (StA, (Kp p ++ [S0], S0, [])).
Local Notation Cc := Cc_0RB0LD_1LA1RC_1LD1RB____0LA.

(** ** The certificate *)

(** j = 2*i + 2 *)
Definition P0_0RB0LD_1LA1RC_1LD1RB____0LA0 : sconf := mkC StA (mkS [] [S1;S1] 1 0 [S1;S1;S0]) S0 (mkS [] [] 0 0 []).
Definition P0_0RB0LD_1LA1RC_1LD1RB____0LA1 : sconf := mkC StA (mkS [] [S0;S0] 1 0 [S0;S0;S1]) S0 (mkS [] [] 0 0 []).
Definition chp0_0RB0LD_1LA1RC_1LD1RB____0LA : list lstep := [SRotL 1; SWin 1; SCycL 2 0; SWin 4; SCycR 2; SWin 1; SUnrotL 1].

Lemma run_p0_0RB0LD_1LA1RC_1LD1RB____0LA : srun tm false true chp0_0RB0LD_1LA1RC_1LD1RB____0LA P0_0RB0LD_1LA1RC_1LD1RB____0LA0 = Some (P0_0RB0LD_1LA1RC_1LD1RB____0LA1, 4, 6).
Proof. vm_compute. reflexivity. Qed.

(** j = 0 (concrete) *)
Definition P1_0RB0LD_1LA1RC_1LD1RB____0LA0 : sconf := mkC StA (mkS [S0] [] 0 0 []) S0 (mkS [] [] 0 0 []).
Definition P1_0RB0LD_1LA1RC_1LD1RB____0LA1 : sconf := mkC StA (mkS [S1] [] 0 0 []) S0 (mkS [] [] 0 0 []).
Definition chp1_0RB0LD_1LA1RC_1LD1RB____0LA : list lstep := [SWin 2].

Lemma run_p1_0RB0LD_1LA1RC_1LD1RB____0LA : srun tm false true chp1_0RB0LD_1LA1RC_1LD1RB____0LA P1_0RB0LD_1LA1RC_1LD1RB____0LA0 = Some (P1_0RB0LD_1LA1RC_1LD1RB____0LA1, 0, 2).
Proof. vm_compute. reflexivity. Qed.

(** j = 2*i + 1 *)
Definition P2_0RB0LD_1LA1RC_1LD1RB____0LA0 : sconf := mkC StA (mkS [] [S1;S1] 1 0 [S1;S0]) S0 (mkS [] [] 0 0 []).
Definition P2_0RB0LD_1LA1RC_1LD1RB____0LA1 : sconf := mkC StA (mkS [] [S0;S0] 1 0 [S0;S1]) S0 (mkS [] [] 0 0 []).
Definition chp2_0RB0LD_1LA1RC_1LD1RB____0LA : list lstep := [SRotL 1; SWin 1; SCycL 2 0; SWin 2; SCycR 2; SWin 1; SUnrotL 1].

Lemma run_p2_0RB0LD_1LA1RC_1LD1RB____0LA : srun tm false true chp2_0RB0LD_1LA1RC_1LD1RB____0LA P2_0RB0LD_1LA1RC_1LD1RB____0LA0 = Some (P2_0RB0LD_1LA1RC_1LD1RB____0LA1, 4, 4).
Proof. vm_compute. reflexivity. Qed.

Definition B0_0RB0LD_1LA1RC_1LD1RB____0LA : sconf := mkC StA (mkS [S1;S1;S1] [S1;S1] 1 0 [S0]) S0 (mkS [] [] 0 0 []).
Definition B1_0RB0LD_1LA1RC_1LD1RB____0LA : sconf := mkC StA (mkS [S0;S0;S0] [S0;S0] 1 0 [S1]) S0 (mkS [] [] 0 0 []).
(** j = 2*i + 2 *)
Definition O0_0RB0LD_1LA1RC_1LD1RB____0LA0 : sconf := mkC StA (mkS [S1;S1;S1] [S1;S1] 1 0 [S0]) S0 (mkS [] [] 0 0 []).
Definition O0_0RB0LD_1LA1RC_1LD1RB____0LA1 : sconf := mkC StA (mkS [S0;S0;S0] [S0;S0] 1 0 [S1]) S0 (mkS [] [] 0 0 []).
Definition cho0_0RB0LD_1LA1RC_1LD1RB____0LA : list lstep := [SWin 3; SCycL 2 0; SWin 2; SCycR 2; SWin 3].

Lemma run_o0_0RB0LD_1LA1RC_1LD1RB____0LA : srun tm true true cho0_0RB0LD_1LA1RC_1LD1RB____0LA O0_0RB0LD_1LA1RC_1LD1RB____0LA0 = Some (O0_0RB0LD_1LA1RC_1LD1RB____0LA1, 4, 8).
Proof. vm_compute. reflexivity. Qed.

(** j = 0 (concrete) *)
Definition O1_0RB0LD_1LA1RC_1LD1RB____0LA0 : sconf := mkC StA (mkS [S1;S0] [] 0 0 []) S0 (mkS [] [] 0 0 []).
Definition O1_0RB0LD_1LA1RC_1LD1RB____0LA1 : sconf := mkC StA (mkS [S0;S1] [] 0 0 []) S0 (mkS [] [] 0 0 []).
Definition cho1_0RB0LD_1LA1RC_1LD1RB____0LA : list lstep := [SWin 4].

Lemma run_o1_0RB0LD_1LA1RC_1LD1RB____0LA : srun tm true true cho1_0RB0LD_1LA1RC_1LD1RB____0LA O1_0RB0LD_1LA1RC_1LD1RB____0LA0 = Some (O1_0RB0LD_1LA1RC_1LD1RB____0LA1, 0, 4).
Proof. vm_compute. reflexivity. Qed.

(** j = 2*i + 3 *)
Definition O2_0RB0LD_1LA1RC_1LD1RB____0LA0 : sconf := mkC StA (mkS [S1;S1;S1;S1] [S1;S1] 1 0 [S0]) S0 (mkS [] [] 0 0 []).
Definition O2_0RB0LD_1LA1RC_1LD1RB____0LA1 : sconf := mkC StA (mkS [S0;S0;S0;S0] [S0;S0] 1 0 [S1]) S0 (mkS [] [] 0 0 []).
Definition cho2_0RB0LD_1LA1RC_1LD1RB____0LA : list lstep := [SWin 4; SCycL 2 0; SWin 2; SCycR 2; SWin 4].

Lemma run_o2_0RB0LD_1LA1RC_1LD1RB____0LA : srun tm true true cho2_0RB0LD_1LA1RC_1LD1RB____0LA O2_0RB0LD_1LA1RC_1LD1RB____0LA0 = Some (O2_0RB0LD_1LA1RC_1LD1RB____0LA1, 4, 10).
Proof. vm_compute. reflexivity. Qed.

(** j = 1 (concrete) *)
Definition O3_0RB0LD_1LA1RC_1LD1RB____0LA0 : sconf := mkC StA (mkS [S1;S1;S0] [] 0 0 []) S0 (mkS [] [] 0 0 []).
Definition O3_0RB0LD_1LA1RC_1LD1RB____0LA1 : sconf := mkC StA (mkS [S0;S0;S1] [] 0 0 []) S0 (mkS [] [] 0 0 []).
Definition cho3_0RB0LD_1LA1RC_1LD1RB____0LA : list lstep := [SWin 6].

Lemma run_o3_0RB0LD_1LA1RC_1LD1RB____0LA : srun tm true true cho3_0RB0LD_1LA1RC_1LD1RB____0LA O3_0RB0LD_1LA1RC_1LD1RB____0LA0 = Some (O3_0RB0LD_1LA1RC_1LD1RB____0LA1, 0, 6).
Proof. vm_compute. reflexivity. Qed.

(** ** Anchor glue -- the only per-machine mathematics *)

(** [rep] at [j = m*i + (c1 + c2)]: the residue cases' only algebra. *)
Lemma repeq_0RB0LD_1LA1RC_1LD1RB____0LA : forall (u : list Sym) n m, n = m -> rep u n = rep u m.
Proof. intros u n m ->. reflexivity. Qed.

Lemma repmul_0RB0LD_1LA1RC_1LD1RB____0LA : forall (u : list Sym) m i, rep u (m * i) = rep (rep u m) i.
Proof.
  intros u m i. induction i as [|i IH]; [rewrite Nat.mul_0_r; reflexivity|].
  replace (m * S i) with (m + m * i) by lia. rewrite rep_add, IH. reflexivity.
Qed.

Lemma repm_0RB0LD_1LA1RC_1LD1RB____0LA : forall (u : list Sym) m i c1 c2,
  rep u (m * i + (c1 + c2)) = rep u c1 ++ rep (rep u m) i ++ rep u c2.
Proof.
  intros u m i c1 c2.
  replace (m * i + (c1 + c2)) with (c1 + (m * i + c2)) by lia.
  rewrite !rep_add, repmul_0RB0LD_1LA1RC_1LD1RB____0LA. reflexivity.
Qed.

Lemma gpar0_0RB0LD_1LA1RC_1LD1RB____0LA : forall p j q0 i, cview p = (j, Some q0) ->
  j = 2 * i + 2 ->
  Cc p = cden (Kp q0 ++ [S0]) [] i P0_0RB0LD_1LA1RC_1LD1RB____0LA0 /\ cden (Kp q0 ++ [S0]) [] i P0_0RB0LD_1LA1RC_1LD1RB____0LA1 = Cc (Pos.succ p).
Proof.
  intros p j q0 i E Hj. destruct (KpCounter.cview_some_K p j q0 E) as (H1 & H2).
  rewrite (repeq_0RB0LD_1LA1RC_1LD1RB____0LA [S1] _ (2 * i + (0 + 2))) in H1 by lia.
  rewrite (repeq_0RB0LD_1LA1RC_1LD1RB____0LA [S0] _ (2 * i + (0 + 2))) in H2 by lia.
  rewrite repm_0RB0LD_1LA1RC_1LD1RB____0LA in H1, H2.
  unfold Cc_0RB0LD_1LA1RC_1LD1RB____0LA, cden, P0_0RB0LD_1LA1RC_1LD1RB____0LA0, P0_0RB0LD_1LA1RC_1LD1RB____0LA1; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia.
  split; [rewrite H1 | rewrite H2]; cbn [rep app Nat.mul Nat.add]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity.
Qed.

Lemma gpar1_0RB0LD_1LA1RC_1LD1RB____0LA : forall p q0, cview p = (0, Some q0) ->
  Cc p = cden (Kp q0 ++ [S0]) [] 0 P1_0RB0LD_1LA1RC_1LD1RB____0LA0 /\ cden (Kp q0 ++ [S0]) [] 0 P1_0RB0LD_1LA1RC_1LD1RB____0LA1 = Cc (Pos.succ p).
Proof.
  intros p q0 E. destruct (KpCounter.cview_some_K p 0 q0 E) as (H1 & H2).
  unfold Cc_0RB0LD_1LA1RC_1LD1RB____0LA, cden, P1_0RB0LD_1LA1RC_1LD1RB____0LA0, P1_0RB0LD_1LA1RC_1LD1RB____0LA1; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  split; [rewrite H1 | rewrite H2]; cbn [rep app Nat.mul Nat.add]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity.
Qed.

Lemma gpar2_0RB0LD_1LA1RC_1LD1RB____0LA : forall p j q0 i, cview p = (j, Some q0) ->
  j = 2 * i + 1 ->
  Cc p = cden (Kp q0 ++ [S0]) [] i P2_0RB0LD_1LA1RC_1LD1RB____0LA0 /\ cden (Kp q0 ++ [S0]) [] i P2_0RB0LD_1LA1RC_1LD1RB____0LA1 = Cc (Pos.succ p).
Proof.
  intros p j q0 i E Hj. destruct (KpCounter.cview_some_K p j q0 E) as (H1 & H2).
  rewrite (repeq_0RB0LD_1LA1RC_1LD1RB____0LA [S1] _ (2 * i + (0 + 1))) in H1 by lia.
  rewrite (repeq_0RB0LD_1LA1RC_1LD1RB____0LA [S0] _ (2 * i + (0 + 1))) in H2 by lia.
  rewrite repm_0RB0LD_1LA1RC_1LD1RB____0LA in H1, H2.
  unfold Cc_0RB0LD_1LA1RC_1LD1RB____0LA, cden, P2_0RB0LD_1LA1RC_1LD1RB____0LA0, P2_0RB0LD_1LA1RC_1LD1RB____0LA1; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia.
  split; [rewrite H1 | rewrite H2]; cbn [rep app Nat.mul Nat.add]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity.
Qed.

Lemma lapi_0RB0LD_1LA1RC_1LD1RB____0LA : forall p j q0, cview p = (j, Some q0) ->
  exists n, 0 < n /\ csteps tm n (Cc p) = Some (Cc (Pos.succ p)).
Proof.
  intros p j q0 E.
  pose proof (Nat.div_mod_eq j 2) as Hd.
  pose proof (Nat.mod_upper_bound j 2 ltac:(discriminate)) as Hm.
  set (i := j / 2) in *. set (r := j mod 2) in *. clearbody i r.
  destruct r as [|[|r]]; [idtac | idtac | exfalso; lia].
  - destruct i as [|i].
    + assert (Ej : j = 0) by lia. subst j.
      destruct (gpar1_0RB0LD_1LA1RC_1LD1RB____0LA p q0 E) as (HA & HB).
      exists (0 * 0 + 2). split; [lia|]. rewrite HA.
      rewrite (srun_sound tm false true chp1_0RB0LD_1LA1RC_1LD1RB____0LA P1_0RB0LD_1LA1RC_1LD1RB____0LA0 P1_0RB0LD_1LA1RC_1LD1RB____0LA1 0 2
                 run_p1_0RB0LD_1LA1RC_1LD1RB____0LA (Kp q0 ++ [S0]) [] 0 ltac:(discriminate) ltac:(reflexivity)).
      f_equal. exact HB.
    + destruct (gpar0_0RB0LD_1LA1RC_1LD1RB____0LA p j q0 i E ltac:(lia)) as (HA & HB).
      exists (4 * i + 6). split; [lia|]. rewrite HA.
      rewrite (srun_sound tm false true chp0_0RB0LD_1LA1RC_1LD1RB____0LA P0_0RB0LD_1LA1RC_1LD1RB____0LA0 P0_0RB0LD_1LA1RC_1LD1RB____0LA1 4 6
                 run_p0_0RB0LD_1LA1RC_1LD1RB____0LA (Kp q0 ++ [S0]) [] i ltac:(discriminate) ltac:(reflexivity)).
      f_equal. exact HB.
  - destruct (gpar2_0RB0LD_1LA1RC_1LD1RB____0LA p j q0 i E ltac:(lia)) as (HA & HB).
    exists (4 * i + 4). split; [lia|]. rewrite HA.
    rewrite (srun_sound tm false true chp2_0RB0LD_1LA1RC_1LD1RB____0LA P2_0RB0LD_1LA1RC_1LD1RB____0LA0 P2_0RB0LD_1LA1RC_1LD1RB____0LA1 4 4
               run_p2_0RB0LD_1LA1RC_1LD1RB____0LA (Kp q0 ++ [S0]) [] i ltac:(discriminate) ltac:(reflexivity)).
    f_equal. exact HB.
Qed.

Lemma lbl_0RB0LD_1LA1RC_1LD1RB____0LA : forall q l h r, lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.

Lemma gopar0_0RB0LD_1LA1RC_1LD1RB____0LA : forall p j i, cview p = (S j, None) ->
  j = 2 * i + 2 ->
  Cc p = cden [] [] i O0_0RB0LD_1LA1RC_1LD1RB____0LA0 /\
  lift (cden [] [] i O0_0RB0LD_1LA1RC_1LD1RB____0LA1) = lift (Cc (Pos.succ p)).
Proof.
  intros p j i E Hj. destruct (KpCounter.cview_none_K p j E) as (H1 & H2).
  rewrite (repeq_0RB0LD_1LA1RC_1LD1RB____0LA [S1] _ (2 * i + (3 + 0))) in H1 by lia.
  rewrite (repeq_0RB0LD_1LA1RC_1LD1RB____0LA [S0] _ (2 * i + (3 + 0))) in H2 by lia.
  rewrite repm_0RB0LD_1LA1RC_1LD1RB____0LA in H1, H2.
  split.
  - unfold Cc_0RB0LD_1LA1RC_1LD1RB____0LA, cden, O0_0RB0LD_1LA1RC_1LD1RB____0LA0; cbn [c_st c_l c_h c_r].
    unfold sden; cbn [s_pre s_u s_a s_b s_post].
    replace (1 * i + 0) with i by lia.
    rewrite H1; cbn [rep app Nat.mul Nat.add]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity.
  - assert (HD : cden [] [] i O0_0RB0LD_1LA1RC_1LD1RB____0LA1 = (StA, ([S0;S0;S0] ++ rep [S0;S0] i ++ [S1], S0, []))).
    { unfold cden, O0_0RB0LD_1LA1RC_1LD1RB____0LA1, sden; cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
      replace (1 * i + 0) with i by lia. cbn [rep app Nat.mul Nat.add]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity. }
    assert (HC : Cc (Pos.succ p) = (StA, (([S0;S0;S0] ++ rep [S0;S0] i ++ [S1]) ++ [S0], S0, []))).
    { unfold Cc_0RB0LD_1LA1RC_1LD1RB____0LA. rewrite H2. cbn [rep app Nat.mul Nat.add]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity. }
    rewrite HD, HC. rewrite ?lift_app_blank_l, ?lift_app_blank. reflexivity.
Qed.

Lemma gopar1_0RB0LD_1LA1RC_1LD1RB____0LA : forall p, cview p = (S 0, None) ->
  Cc p = cden [] [] 0 O1_0RB0LD_1LA1RC_1LD1RB____0LA0 /\
  lift (cden [] [] 0 O1_0RB0LD_1LA1RC_1LD1RB____0LA1) = lift (Cc (Pos.succ p)).
Proof.
  intros p E. destruct (KpCounter.cview_none_K p 0 E) as (H1 & H2).
  split.
  - unfold Cc_0RB0LD_1LA1RC_1LD1RB____0LA, cden, O1_0RB0LD_1LA1RC_1LD1RB____0LA0; cbn [c_st c_l c_h c_r].
    unfold sden; cbn [s_pre s_u s_a s_b s_post].
    rewrite H1; cbn [rep app Nat.mul Nat.add]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity.
  - assert (HD : cden [] [] 0 O1_0RB0LD_1LA1RC_1LD1RB____0LA1 = (StA, ([S0;S1], S0, []))).
    { unfold cden, O1_0RB0LD_1LA1RC_1LD1RB____0LA1, sden; cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
      cbn [rep app Nat.mul Nat.add]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity. }
    assert (HC : Cc (Pos.succ p) = (StA, (([S0;S1]) ++ [S0], S0, []))).
    { unfold Cc_0RB0LD_1LA1RC_1LD1RB____0LA. rewrite H2. cbn [rep app Nat.mul Nat.add]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity. }
    rewrite HD, HC. rewrite ?lift_app_blank_l, ?lift_app_blank. reflexivity.
Qed.

Lemma gopar2_0RB0LD_1LA1RC_1LD1RB____0LA : forall p j i, cview p = (S j, None) ->
  j = 2 * i + 3 ->
  Cc p = cden [] [] i O2_0RB0LD_1LA1RC_1LD1RB____0LA0 /\
  lift (cden [] [] i O2_0RB0LD_1LA1RC_1LD1RB____0LA1) = lift (Cc (Pos.succ p)).
Proof.
  intros p j i E Hj. destruct (KpCounter.cview_none_K p j E) as (H1 & H2).
  rewrite (repeq_0RB0LD_1LA1RC_1LD1RB____0LA [S1] _ (2 * i + (4 + 0))) in H1 by lia.
  rewrite (repeq_0RB0LD_1LA1RC_1LD1RB____0LA [S0] _ (2 * i + (4 + 0))) in H2 by lia.
  rewrite repm_0RB0LD_1LA1RC_1LD1RB____0LA in H1, H2.
  split.
  - unfold Cc_0RB0LD_1LA1RC_1LD1RB____0LA, cden, O2_0RB0LD_1LA1RC_1LD1RB____0LA0; cbn [c_st c_l c_h c_r].
    unfold sden; cbn [s_pre s_u s_a s_b s_post].
    replace (1 * i + 0) with i by lia.
    rewrite H1; cbn [rep app Nat.mul Nat.add]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity.
  - assert (HD : cden [] [] i O2_0RB0LD_1LA1RC_1LD1RB____0LA1 = (StA, ([S0;S0;S0;S0] ++ rep [S0;S0] i ++ [S1], S0, []))).
    { unfold cden, O2_0RB0LD_1LA1RC_1LD1RB____0LA1, sden; cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
      replace (1 * i + 0) with i by lia. cbn [rep app Nat.mul Nat.add]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity. }
    assert (HC : Cc (Pos.succ p) = (StA, (([S0;S0;S0;S0] ++ rep [S0;S0] i ++ [S1]) ++ [S0], S0, []))).
    { unfold Cc_0RB0LD_1LA1RC_1LD1RB____0LA. rewrite H2. cbn [rep app Nat.mul Nat.add]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity. }
    rewrite HD, HC. rewrite ?lift_app_blank_l, ?lift_app_blank. reflexivity.
Qed.

Lemma gopar3_0RB0LD_1LA1RC_1LD1RB____0LA : forall p, cview p = (S 1, None) ->
  Cc p = cden [] [] 0 O3_0RB0LD_1LA1RC_1LD1RB____0LA0 /\
  lift (cden [] [] 0 O3_0RB0LD_1LA1RC_1LD1RB____0LA1) = lift (Cc (Pos.succ p)).
Proof.
  intros p E. destruct (KpCounter.cview_none_K p 1 E) as (H1 & H2).
  split.
  - unfold Cc_0RB0LD_1LA1RC_1LD1RB____0LA, cden, O3_0RB0LD_1LA1RC_1LD1RB____0LA0; cbn [c_st c_l c_h c_r].
    unfold sden; cbn [s_pre s_u s_a s_b s_post].
    rewrite H1; cbn [rep app Nat.mul Nat.add]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity.
  - assert (HD : cden [] [] 0 O3_0RB0LD_1LA1RC_1LD1RB____0LA1 = (StA, ([S0;S0;S1], S0, []))).
    { unfold cden, O3_0RB0LD_1LA1RC_1LD1RB____0LA1, sden; cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
      cbn [rep app Nat.mul Nat.add]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity. }
    assert (HC : Cc (Pos.succ p) = (StA, (([S0;S0;S1]) ++ [S0], S0, []))).
    { unfold Cc_0RB0LD_1LA1RC_1LD1RB____0LA. rewrite H2. cbn [rep app Nat.mul Nat.add]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity. }
    rewrite HD, HC. rewrite ?lift_app_blank_l, ?lift_app_blank. reflexivity.
Qed.

Lemma lapo_0RB0LD_1LA1RC_1LD1RB____0LA : forall p j, cview p = (S j, None) ->
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
      destruct (gopar1_0RB0LD_1LA1RC_1LD1RB____0LA p E) as (HA & HB).
      exists (0 * 0 + 4), (cden [] [] 0 O1_0RB0LD_1LA1RC_1LD1RB____0LA1).
      split; [| split; [exact HB | lia]].
      rewrite HA. exact (srun_sound tm true true cho1_0RB0LD_1LA1RC_1LD1RB____0LA O1_0RB0LD_1LA1RC_1LD1RB____0LA0 O1_0RB0LD_1LA1RC_1LD1RB____0LA1 0 4
                 run_o1_0RB0LD_1LA1RC_1LD1RB____0LA [] [] 0 ltac:(reflexivity) ltac:(reflexivity)).
    + destruct (gopar0_0RB0LD_1LA1RC_1LD1RB____0LA p j i E ltac:(lia)) as (HA & HB).
      exists (4 * i + 8), (cden [] [] i O0_0RB0LD_1LA1RC_1LD1RB____0LA1).
      split; [| split; [exact HB | lia]].
      rewrite HA. exact (srun_sound tm true true cho0_0RB0LD_1LA1RC_1LD1RB____0LA O0_0RB0LD_1LA1RC_1LD1RB____0LA0 O0_0RB0LD_1LA1RC_1LD1RB____0LA1 4 8
                 run_o0_0RB0LD_1LA1RC_1LD1RB____0LA [] [] i ltac:(reflexivity) ltac:(reflexivity)).
  - destruct i as [|i].
    + assert (Ej : j = 1) by lia. subst j.
      destruct (gopar3_0RB0LD_1LA1RC_1LD1RB____0LA p E) as (HA & HB).
      exists (0 * 0 + 6), (cden [] [] 0 O3_0RB0LD_1LA1RC_1LD1RB____0LA1).
      split; [| split; [exact HB | lia]].
      rewrite HA. exact (srun_sound tm true true cho3_0RB0LD_1LA1RC_1LD1RB____0LA O3_0RB0LD_1LA1RC_1LD1RB____0LA0 O3_0RB0LD_1LA1RC_1LD1RB____0LA1 0 6
                 run_o3_0RB0LD_1LA1RC_1LD1RB____0LA [] [] 0 ltac:(reflexivity) ltac:(reflexivity)).
    + destruct (gopar2_0RB0LD_1LA1RC_1LD1RB____0LA p j i E ltac:(lia)) as (HA & HB).
      exists (4 * i + 10), (cden [] [] i O2_0RB0LD_1LA1RC_1LD1RB____0LA1).
      split; [| split; [exact HB | lia]].
      rewrite HA. exact (srun_sound tm true true cho2_0RB0LD_1LA1RC_1LD1RB____0LA O2_0RB0LD_1LA1RC_1LD1RB____0LA0 O2_0RB0LD_1LA1RC_1LD1RB____0LA1 4 10
                 run_o2_0RB0LD_1LA1RC_1LD1RB____0LA [] [] i ltac:(reflexivity) ltac:(reflexivity)).
Qed.

(** ** The lap *)

Lemma lap_0RB0LD_1LA1RC_1LD1RB____0LA : forall p, exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:E. destruct oq as [q0|].
  - destruct (lapi_0RB0LD_1LA1RC_1LD1RB____0LA p j q0 E) as (n & Hn & Hrun).
    exists n, (Cc (Pos.succ p)).
    split; [exact Hrun | split; [reflexivity | exact Hn]].
  - destruct (cview_pos p j E) as (j' & ->).
    exact (lapo_0RB0LD_1LA1RC_1LD1RB____0LA p j' E).
Qed.

(** ** Bootstrap *)

Lemma boot_0RB0LD_1LA1RC_1LD1RB____0LA : exists t0, stepn tm t0 InitES = Some (lift (Cc 1)).
Proof.
  exists 2.
  assert (H : match csteps tm 2 c0 with
              | Some c => ceqb c (Cc 1) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 2 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** ** Visits

    Every state fires inside the OVERFLOW lap, so one prefix chain per state
    plus [LapCertGlue.vis_via_ovf] (run interior laps until the counter
    overflows -- they close exactly) covers every anchor. *)

Lemma fireo_0RB0LD_1LA1RC_1LD1RB____0LA : forall (l0 l1 l2 l3 : list lstep) (t : Instr),
  srun_instr tm true true l0 O0_0RB0LD_1LA1RC_1LD1RB____0LA0 = Some t ->
  srun_instr tm true true l1 O1_0RB0LD_1LA1RC_1LD1RB____0LA0 = Some t ->
  srun_instr tm true true l2 O2_0RB0LD_1LA1RC_1LD1RB____0LA0 = Some t ->
  srun_instr tm true true l3 O3_0RB0LD_1LA1RC_1LD1RB____0LA0 = Some t ->
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
      destruct (gopar1_0RB0LD_1LA1RC_1LD1RB____0LA p E) as (HA & _).
      exact (fire_of_run_instr tm Cc true true l1 O1_0RB0LD_1LA1RC_1LD1RB____0LA0 p 0 [] [] t
               H1 ltac:(reflexivity) ltac:(reflexivity) HA).
    + destruct (gopar0_0RB0LD_1LA1RC_1LD1RB____0LA p j i E ltac:(lia)) as (HA & _).
      exact (fire_of_run_instr tm Cc true true l0 O0_0RB0LD_1LA1RC_1LD1RB____0LA0 p i [] [] t
               H0 ltac:(reflexivity) ltac:(reflexivity) HA).
  - destruct i as [|i].
    + assert (Ej : j = 1) by lia. subst j.
      destruct (gopar3_0RB0LD_1LA1RC_1LD1RB____0LA p E) as (HA & _).
      exact (fire_of_run_instr tm Cc true true l3 O3_0RB0LD_1LA1RC_1LD1RB____0LA0 p 0 [] [] t
               H3 ltac:(reflexivity) ltac:(reflexivity) HA).
    + destruct (gopar2_0RB0LD_1LA1RC_1LD1RB____0LA p j i E ltac:(lia)) as (HA & _).
      exact (fire_of_run_instr tm Cc true true l2 O2_0RB0LD_1LA1RC_1LD1RB____0LA0 p i [] [] t
               H2 ltac:(reflexivity) ltac:(reflexivity) HA).
Qed.

(** ** Fires: every UNPINNED instruction fires from every anchor
    (inside the overflow lap; [LapGlueTr.fire_via_ovf] runs the
    interior laps until the counter overflows). *)

Lemma fire_0RB0LD_1LA1RC_1LD1RB____0LA : forall t, ~ In t pins_0RB0LD_1LA1RC_1LD1RB____0LA ->
  forall p, exists k c, csteps tm k (Cc p) = Some c /\ cinstr c = t.
Proof.
  intros t Hnp p.
  assert (Hi : forall p0 j q0, cview p0 = (j, Some q0) ->
            exists n, 0 < n /\ csteps tm n (Cc p0) = Some (Cc (Pos.succ p0)))
    by exact lapi_0RB0LD_1LA1RC_1LD1RB____0LA.
  destruct t as [q b]; destruct q, b.
  - (* A0 *)
    apply (fire_via_ovf tm Cc Hi (StA, S0)), (fireo_0RB0LD_1LA1RC_1LD1RB____0LA
      ([])
      ([])
      ([])
      ([])); vm_compute; reflexivity.
  - (* A1 *)
    apply (fire_via_ovf tm Cc Hi (StA, S1)), (fireo_0RB0LD_1LA1RC_1LD1RB____0LA
      ([SWin 3; SCycL 2 0; SWin 2; SCycR 2; SWin 1])
      ([SWin 4; SWinL 6])
      ([SWin 4; SCycL 2 0; SWin 2])
      ([SWin 4])); vm_compute; reflexivity.
  - (* B0 *)
    apply (fire_via_ovf tm Cc Hi (StB, S0)), (fireo_0RB0LD_1LA1RC_1LD1RB____0LA
      ([SWin 3; SCycL 2 0; SWin 2; SCycR 2; SWin 3; SWin 1])
      ([SWin 4; SWin 1])
      ([SWin 4; SCycL 2 0; SWin 1])
      ([SWin 3])); vm_compute; reflexivity.
  - (* B1 *)
    apply (fire_via_ovf tm Cc Hi (StB, S1)), (fireo_0RB0LD_1LA1RC_1LD1RB____0LA
      ([SWin 1])
      ([SWin 1])
      ([SWin 1])
      ([SWin 1])); vm_compute; reflexivity.
  - (* C0 *)
    apply (fire_via_ovf tm Cc Hi (StC, S0)), (fireo_0RB0LD_1LA1RC_1LD1RB____0LA
      ([SWin 3; SCycL 2 0; SWin 1])
      ([SWin 2])
      ([SWin 4; SCycL 2 0; SWin 2; SCycR 2; SWin 4; SWin 4])
      ([SWin 6; SWin 4])); vm_compute; reflexivity.
  - (* C1 *)
    apply (fire_via_ovf tm Cc Hi (StC, S1)), (fireo_0RB0LD_1LA1RC_1LD1RB____0LA
      ([SWin 2])
      ([SWin 4; SWin 4])
      ([SWin 2])
      ([SWin 2])); vm_compute; reflexivity.
  - (* D0: pinned *)
    exfalso. apply Hnp. apply tr_inb_spec. reflexivity.
  - (* D1 *)
    apply (fire_via_ovf tm Cc Hi (StD, S1)), (fireo_0RB0LD_1LA1RC_1LD1RB____0LA
      ([SWin 3; SCycL 2 0; SWin 2])
      ([SWin 3])
      ([SWin 4; SCycL 2 0; SWin 2; SCycR 2; SWin 1])
      ([SWin 5])); vm_compute; reflexivity.
Qed.

Theorem nqhtrm_0RB0LD_1LA1RC_1LD1RB____0LA : NeverQuasiHaltsTr tmm_0RB0LD_1LA1RC_1LD1RB____0LA.
Proof.
  apply (glue_neverqhtr tmm_0RB0LD_1LA1RC_1LD1RB____0LA pins_0RB0LD_1LA1RC_1LD1RB____0LA Cc 1).
  - exact boot_0RB0LD_1LA1RC_1LD1RB____0LA.
  - intros p _. apply lap_0RB0LD_1LA1RC_1LD1RB____0LA.
  - intros t Ht p _. apply fire_0RB0LD_1LA1RC_1LD1RB____0LA. exact Ht.
Qed.

Theorem nqhtr_0RB0LD_1LA1RC_1LD1RB____0LA : NeverQuasiHaltsTr tm_0RB0LD_1LA1RC_1LD1RB____0LA.
Proof. apply (neverqhtr_mirror tm_0RB0LD_1LA1RC_1LD1RB____0LA). rewrite mirror_ok_0RB0LD_1LA1RC_1LD1RB____0LA. exact nqhtrm_0RB0LD_1LA1RC_1LD1RB____0LA. Qed.

Theorem nonhalt_0RB0LD_1LA1RC_1LD1RB____0LA : NonHalt tm_0RB0LD_1LA1RC_1LD1RB____0LA.
Proof. apply never_qh_tr_nonhalt, nqhtr_0RB0LD_1LA1RC_1LD1RB____0LA. Qed.
