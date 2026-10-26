(** * LAPQ_1RB1LA1RB_1LB2RB2LA: TRANSITION-LEVEL QUASIHALTING-side board for machine 1RB1LA1RB_1LB2RB2LA, boarded by CERTIFICATE.

    Auto-emitted by tools/counters/emit_lapcert.py (UNTRUSTED emitter; the Coq
    kernel re-runs the checker on every line below).  Left-growth binary
    counter under the Ap_Alph_2_1_1 digit alphabet (Alph_2_1_1.v), anchored at

      Cc p = (StB, (Ap_Alph_2_1_1 p ++ [S0], S1, [S2;S1]))

    The lap is DATA, not a proof script: each branch is a list of steps for
    [Checkers/LapDecider.v], run by the kernel through [vm_compute] and
    discharged by the single theorem [srun_sound].

      interior  (cview p = (j, Some q0)):  2*j+6 steps
      overflow  (cview p = (S j, None)):   2*j+8 steps

    The interior branch closes EXACTLY (which is what feeds
    [LapCertGlue.reach_ovf]); the overflow branch closes one blank short of
    the anchor tail, hence up to [lift].

    Differentially validated against the raw simulator on BOTH branches --
    step counts AND exact configurations -- for 198 anchors.
    Axiom footprint: [functional_extensionality_dep] (via [CTape.lift]). *)
From Coq Require Import Arith Lia Bool List PArith Wellfounded.
From SmallBB Require Import Statement CTape.
From SmallBB.Counters Require Import WTape LapGlue
                                  MonoCounter JpCounter Alph_2_1_1 LapCertGlue.
From SmallBB.Checkers Require Import LapDecider.
From SmallBB Require Import StatementTr.
From SmallBB.Checkers Require Import WrapTr.
From SmallBB.Checkers.IRules Require Import AnchorVisitsTr.
From SmallBB.Counters Require Import LapGlueTr.
From SmallBB Require Import ClosureTr Bounds.
From SmallBB.Counters Require Import LapGlueQHTr.
Import ListNotations.

Definition mk_1RB1LA1RB_1LB2RB2LA (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_1RB1LA1RB_1LB2RB2LA.

(** 1RB1LA1RB_1LB2RB2LA *)
Definition tm_1RB1LA1RB_1LB2RB2LA : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DR StB
  | StA, S1 => mk S1 DL StA
  | StA, S2 => mk S1 DR StB
  | StB, S0 => mk S1 DL StB
  | StB, S1 => mk S2 DR StB
  | StB, S2 => mk S2 DL StA
  | StC, S0 => None
  | StC, S1 => None
  | StC, S2 => None end.
(** the instructions the certificate claims NEVER fire; the lap
    argument runs on the machine WRAPPED at them
    ([WrapTr.tm_wrap_trs]), so a pinned instruction firing would
    halt it and every [srun] below would fail. *)
Definition pins_1RB1LA1RB_1LB2RB2LA : list Instr := [(StC, S0); (StC, S1); (StC, S2); (StB, S0)].
Definition tmw_1RB1LA1RB_1LB2RB2LA : TM := tm_wrap_trs tm_1RB1LA1RB_1LB2RB2LA pins_1RB1LA1RB_1LB2RB2LA.
Local Notation tm := tmw_1RB1LA1RB_1LB2RB2LA.

Definition Cc_1RB1LA1RB_1LB2RB2LA (p : positive) : cconf := (StB, (Ap_Alph_2_1_1 p ++ [S0], S1, [S2;S1])).
Local Notation Cc := Cc_1RB1LA1RB_1LB2RB2LA.

(** ** The certificate *)

Definition A0_1RB1LA1RB_1LB2RB2LA : sconf := mkC StB (mkS [] [S1] 1 0 [S2]) S1 (mkS [S2;S1] [] 0 0 []).
Definition A1_1RB1LA1RB_1LB2RB2LA : sconf := mkC StB (mkS [] [S2] 1 0 [S1]) S1 (mkS [S2;S1] [] 0 0 []).
Definition chi_1RB1LA1RB_1LB2RB2LA : list lstep := [SWin 4; SCycL 1 0; SWin 2; SCycR 1].

Lemma run_int_1RB1LA1RB_1LB2RB2LA : srun tm false true chi_1RB1LA1RB_1LB2RB2LA A0_1RB1LA1RB_1LB2RB2LA = Some (A1_1RB1LA1RB_1LB2RB2LA, 2, 6).
Proof. vm_compute. reflexivity. Qed.

Definition B0_1RB1LA1RB_1LB2RB2LA : sconf := mkC StB (mkS [] [S1] 1 0 [S1;S0]) S1 (mkS [S2;S1] [] 0 0 []).
Definition B1_1RB1LA1RB_1LB2RB2LA : sconf := mkC StB (mkS [] [S2] 1 1 [S1]) S1 (mkS [S2;S1] [] 0 0 []).
Definition cho_1RB1LA1RB_1LB2RB2LA : list lstep := [SWin 4; SCycL 1 0; SWin 4; SCycR 1; SRotL 1; SFoldL 1].

Lemma run_ovf_1RB1LA1RB_1LB2RB2LA : srun tm true true cho_1RB1LA1RB_1LB2RB2LA B0_1RB1LA1RB_1LB2RB2LA = Some (B1_1RB1LA1RB_1LB2RB2LA, 2, 8).
Proof. vm_compute. reflexivity. Qed.

(** ** Anchor glue -- the only per-machine mathematics *)

Lemma gsi_1RB1LA1RB_1LB2RB2LA : forall p j q0, cview p = (j, Some q0) ->
  Cc p = cden (Ap_Alph_2_1_1 q0 ++ [S0]) [] j A0_1RB1LA1RB_1LB2RB2LA.
Proof.
  intros p j q0 E. destruct (Alph_2_1_1.cview_some_Alph_2_1_1 p j q0 E) as (H1 & _).
  unfold Cc_1RB1LA1RB_1LB2RB2LA, cden, A0_1RB1LA1RB_1LB2RB2LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  rewrite H1. first [ rewrite <- (app_assoc (rep [S1] j)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma gei_1RB1LA1RB_1LB2RB2LA : forall p j q0, cview p = (j, Some q0) ->
  cden (Ap_Alph_2_1_1 q0 ++ [S0]) [] j A1_1RB1LA1RB_1LB2RB2LA = Cc (Pos.succ p).
Proof.
  intros p j q0 E. destruct (Alph_2_1_1.cview_some_Alph_2_1_1 p j q0 E) as (_ & H2).
  unfold Cc_1RB1LA1RB_1LB2RB2LA, cden, A1_1RB1LA1RB_1LB2RB2LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  rewrite H2. first [ rewrite <- (app_assoc (rep [S2] j)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapi_1RB1LA1RB_1LB2RB2LA : forall p j q0, cview p = (j, Some q0) ->
  exists n, 0 < n /\ csteps tm n (Cc p) = Some (Cc (Pos.succ p)).
Proof.
  intros p j q0 E. exists (2 * j + 6). split; [lia|].
  rewrite (gsi_1RB1LA1RB_1LB2RB2LA p j q0 E).
  rewrite (srun_sound tm false true chi_1RB1LA1RB_1LB2RB2LA A0_1RB1LA1RB_1LB2RB2LA A1_1RB1LA1RB_1LB2RB2LA 2 6
             run_int_1RB1LA1RB_1LB2RB2LA (Ap_Alph_2_1_1 q0 ++ [S0]) [] j
             ltac:(discriminate) ltac:(reflexivity)).
  f_equal. exact (gei_1RB1LA1RB_1LB2RB2LA p j q0 E).
Qed.

Lemma gso_1RB1LA1RB_1LB2RB2LA : forall p j, cview p = (S j, None) ->
  Cc p = cden [] [] j B0_1RB1LA1RB_1LB2RB2LA.
Proof.
  intros p j E. destruct (Alph_2_1_1.cview_none_Alph_2_1_1 p j E) as (H1 & _).
  unfold Cc_1RB1LA1RB_1LB2RB2LA, cden, B0_1RB1LA1RB_1LB2RB2LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with (j) by lia.
  rewrite H1; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lbl_1RB1LA1RB_1LB2RB2LA : forall q l h r, lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.

Lemma geo_1RB1LA1RB_1LB2RB2LA : forall p j, cview p = (S j, None) ->
  lift (cden [] [] j B1_1RB1LA1RB_1LB2RB2LA) = lift (Cc (Pos.succ p)).
Proof.
  intros p j E. destruct (Alph_2_1_1.cview_none_Alph_2_1_1 p j E) as (_ & H2).
  assert (HD : cden [] [] j B1_1RB1LA1RB_1LB2RB2LA
             = (StB, (rep [S2] (S j) ++ [S1], S1, [S2;S1]))).
  { unfold cden, B1_1RB1LA1RB_1LB2RB2LA, sden, sflat;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 1) with (S j) by lia.
    replace (0 * j + 0) with 0 by lia.
    cbn [rep app]. first [ reflexivity
      | rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  assert (HC : Cc (Pos.succ p) = (StB, ((rep [S2] (S j) ++ [S1]) ++ [S0], S1, [S2;S1]))).
  { unfold Cc_1RB1LA1RB_1LB2RB2LA. rewrite H2.
    first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  rewrite HD, HC. rewrite !lbl_1RB1LA1RB_1LB2RB2LA. reflexivity.
Qed.

(** ** The lap *)

Lemma lap_1RB1LA1RB_1LB2RB2LA : forall p, exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:E. destruct oq as [q0|].
  - destruct (lapi_1RB1LA1RB_1LB2RB2LA p j q0 E) as (n & Hn & Hrun).
    exists n, (Cc (Pos.succ p)).
    split; [exact Hrun | split; [reflexivity | exact Hn]].
  - destruct (cview_pos p j E) as (j' & ->).
    apply (lap_of_run tm Cc true true cho_1RB1LA1RB_1LB2RB2LA B0_1RB1LA1RB_1LB2RB2LA B1_1RB1LA1RB_1LB2RB2LA 2 8 p j' [] []).
    + exact run_ovf_1RB1LA1RB_1LB2RB2LA.
    + reflexivity.
    + reflexivity.
    + exact (gso_1RB1LA1RB_1LB2RB2LA p j' E).
    + exact (geo_1RB1LA1RB_1LB2RB2LA p j' E).
    + lia.
Qed.

(** ** Bootstrap *)

Lemma bootq_1RB1LA1RB_1LB2RB2LA : stepn tm_1RB1LA1RB_1LB2RB2LA 10 InitES = Some (lift (Cc 1)).
Proof.
  assert (H : match csteps tm_1RB1LA1RB_1LB2RB2LA 10 c0 with
              | Some c => ceqb c (Cc 1) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm_1RB1LA1RB_1LB2RB2LA 10 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** the quasihalt witness: a pinned instruction fired in the prefix *)
Lemma wit_1RB1LA1RB_1LB2RB2LA : existsb (fun tg => cfires tm_1RB1LA1RB_1LB2RB2LA c0 10 tg) pins_1RB1LA1RB_1LB2RB2LA = true.
Proof. vm_compute. reflexivity. Qed.

(** ** Visits

    Every state fires inside the OVERFLOW lap, so one prefix chain per state
    plus [LapCertGlue.vis_via_ovf] (run interior laps until the counter
    overflows -- they close exactly) covers every anchor. *)

Lemma fireo_1RB1LA1RB_1LB2RB2LA : forall (l : list lstep) (t : Instr),
  srun_instr tm true true l B0_1RB1LA1RB_1LB2RB2LA = Some t ->
  forall p j, cview p = (S j, None) ->
  exists k c, csteps tm k (Cc p) = Some c /\ cinstr c = t.
Proof.
  intros l t Hst p j E.
  apply (fire_of_run_instr tm Cc true true l B0_1RB1LA1RB_1LB2RB2LA p j [] []);
    [exact Hst | reflexivity | reflexivity | exact (gso_1RB1LA1RB_1LB2RB2LA p j E)].
Qed.


(** ** Fires: every UNPINNED instruction fires from every anchor
    (inside the overflow lap; [LapGlueTr.fire_via_ovf] runs the
    interior laps until the counter overflows). *)

Lemma fire_1RB1LA1RB_1LB2RB2LA : forall t, ~ In t pins_1RB1LA1RB_1LB2RB2LA ->
  forall p, exists k c, csteps tm k (Cc p) = Some c /\ cinstr c = t.
Proof.
  intros t Hnp p.
  assert (Hi : forall p0 j q0, cview p0 = (j, Some q0) ->
            exists n, 0 < n /\ csteps tm n (Cc p0) = Some (Cc (Pos.succ p0)))
    by exact lapi_1RB1LA1RB_1LB2RB2LA.
  destruct t as [q b]; destruct q, b.
  - (* A0 *)
    apply (fire_via_ovf tm Cc Hi (StA, S0)), fireo_1RB1LA1RB_1LB2RB2LA
      with (l := [SWin 4; SCycL 1 0; SWin 2]).
    vm_compute; reflexivity.
  - (* A1 *)
    apply (fire_via_ovf tm Cc Hi (StA, S1)), fireo_1RB1LA1RB_1LB2RB2LA
      with (l := [SWin 4]).
    vm_compute; reflexivity.
  - (* A2 *)
    apply (fire_via_ovf tm Cc Hi (StA, S2)), fireo_1RB1LA1RB_1LB2RB2LA
      with (l := [SWin 2]).
    vm_compute; reflexivity.
  - (* B0: pinned *)
    exfalso. apply Hnp. apply tr_inb_spec. reflexivity.
  - (* B1 *)
    apply (fire_via_ovf tm Cc Hi (StB, S1)), fireo_1RB1LA1RB_1LB2RB2LA
      with (l := []).
    vm_compute; reflexivity.
  - (* B2 *)
    apply (fire_via_ovf tm Cc Hi (StB, S2)), fireo_1RB1LA1RB_1LB2RB2LA
      with (l := [SWin 1]).
    vm_compute; reflexivity.
  - (* C0: pinned *)
    exfalso. apply Hnp. apply tr_inb_spec. reflexivity.
  - (* C1: pinned *)
    exfalso. apply Hnp. apply tr_inb_spec. reflexivity.
  - (* C2: pinned *)
    exfalso. apply Hnp. apply tr_inb_spec. reflexivity.
Qed.

Theorem qhtr_1RB1LA1RB_1LB2RB2LA:NonHalt tm_1RB1LA1RB_1LB2RB2LA /\ QHBoundTr 67 tm_1RB1LA1RB_1LB2RB2LA.
Proof.
 destruct(glue_qhboundtr tm_1RB1LA1RB_1LB2RB2LA pins_1RB1LA1RB_1LB2RB2LA Cc 1 10
 bootq_1RB1LA1RB_1LB2RB2LA (fun p _=>lap_1RB1LA1RB_1LB2RB2LA p)
 (fun t Ht p _=>fire_1RB1LA1RB_1LB2RB2LA t Ht p) wit_1RB1LA1RB_1LB2RB2LA)as[HN[HB _]].
 split;[exact HN|]. intros tg s H;specialize(HB tg s H);lia.
Qed.
