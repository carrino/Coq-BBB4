(** * LAPQ_2RB2RB2LA_2LB1LA1RB: TRANSITION-LEVEL QUASIHALTING-side board for machine 2RB2RB2LA_2LB1LA1RB, boarded by CERTIFICATE.

    Auto-emitted by tools/counters/emit_lapcert.py (UNTRUSTED emitter; the Coq
    kernel re-runs the checker on every line below).  Left-growth binary
    counter under the Ap_Alph_1_2_2 digit alphabet (Alph_1_2_2.v), anchored at

      Cc p = (StB, (Ap_Alph_1_2_2 p ++ [S0], S2, [S1;S2]))

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
                                  MonoCounter JpCounter Alph_1_2_2 LapCertGlue.
From SmallBB.Checkers Require Import LapDecider.
From SmallBB Require Import StatementTr.
From SmallBB.Checkers Require Import WrapTr.
From SmallBB.Checkers.IRules Require Import AnchorVisitsTr.
From SmallBB.Counters Require Import LapGlueTr.
From SmallBB Require Import ClosureTr Bounds.
From SmallBB.Counters Require Import LapGlueQHTr.
Import ListNotations.

Definition mk_2RB2RB2LA_2LB1LA1RB (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_2RB2RB2LA_2LB1LA1RB.

(** 2RB2RB2LA_2LB1LA1RB *)
Definition tm_2RB2RB2LA_2LB1LA1RB : TM := fun q s => match q, s with
  | StA, S0 => mk S2 DR StB
  | StA, S1 => mk S2 DR StB
  | StA, S2 => mk S2 DL StA
  | StB, S0 => mk S2 DL StB
  | StB, S1 => mk S1 DL StA
  | StB, S2 => mk S1 DR StB
  | StC, S0 => None
  | StC, S1 => None
  | StC, S2 => None end.
(** the instructions the certificate claims NEVER fire; the lap
    argument runs on the machine WRAPPED at them
    ([WrapTr.tm_wrap_trs]), so a pinned instruction firing would
    halt it and every [srun] below would fail. *)
Definition pins_2RB2RB2LA_2LB1LA1RB : list Instr := [(StC, S0); (StC, S1); (StC, S2); (StB, S0)].
Definition tmw_2RB2RB2LA_2LB1LA1RB : TM := tm_wrap_trs tm_2RB2RB2LA_2LB1LA1RB pins_2RB2RB2LA_2LB1LA1RB.
Local Notation tm := tmw_2RB2RB2LA_2LB1LA1RB.

Definition Cc_2RB2RB2LA_2LB1LA1RB (p : positive) : cconf := (StB, (Ap_Alph_1_2_2 p ++ [S0], S2, [S1;S2])).
Local Notation Cc := Cc_2RB2RB2LA_2LB1LA1RB.

(** ** The certificate *)

Definition A0_2RB2RB2LA_2LB1LA1RB : sconf := mkC StB (mkS [] [S2] 1 0 [S1]) S2 (mkS [S1;S2] [] 0 0 []).
Definition A1_2RB2RB2LA_2LB1LA1RB : sconf := mkC StB (mkS [] [S1] 1 0 [S2]) S2 (mkS [S1;S2] [] 0 0 []).
Definition chi_2RB2RB2LA_2LB1LA1RB : list lstep := [SWin 4; SCycL 1 0; SWin 2; SCycR 1].

Lemma run_int_2RB2RB2LA_2LB1LA1RB : srun tm false true chi_2RB2RB2LA_2LB1LA1RB A0_2RB2RB2LA_2LB1LA1RB = Some (A1_2RB2RB2LA_2LB1LA1RB, 2, 6).
Proof. vm_compute. reflexivity. Qed.

Definition B0_2RB2RB2LA_2LB1LA1RB : sconf := mkC StB (mkS [] [S2] 1 0 [S2;S0]) S2 (mkS [S1;S2] [] 0 0 []).
Definition B1_2RB2RB2LA_2LB1LA1RB : sconf := mkC StB (mkS [] [S1] 1 1 [S2]) S2 (mkS [S1;S2] [] 0 0 []).
Definition cho_2RB2RB2LA_2LB1LA1RB : list lstep := [SWin 4; SCycL 1 0; SWin 4; SCycR 1; SRotL 1; SFoldL 1].

Lemma run_ovf_2RB2RB2LA_2LB1LA1RB : srun tm true true cho_2RB2RB2LA_2LB1LA1RB B0_2RB2RB2LA_2LB1LA1RB = Some (B1_2RB2RB2LA_2LB1LA1RB, 2, 8).
Proof. vm_compute. reflexivity. Qed.

(** ** Anchor glue -- the only per-machine mathematics *)

Lemma gsi_2RB2RB2LA_2LB1LA1RB : forall p j q0, cview p = (j, Some q0) ->
  Cc p = cden (Ap_Alph_1_2_2 q0 ++ [S0]) [] j A0_2RB2RB2LA_2LB1LA1RB.
Proof.
  intros p j q0 E. destruct (Alph_1_2_2.cview_some_Alph_1_2_2 p j q0 E) as (H1 & _).
  unfold Cc_2RB2RB2LA_2LB1LA1RB, cden, A0_2RB2RB2LA_2LB1LA1RB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  rewrite H1. first [ rewrite <- (app_assoc (rep [S2] j)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma gei_2RB2RB2LA_2LB1LA1RB : forall p j q0, cview p = (j, Some q0) ->
  cden (Ap_Alph_1_2_2 q0 ++ [S0]) [] j A1_2RB2RB2LA_2LB1LA1RB = Cc (Pos.succ p).
Proof.
  intros p j q0 E. destruct (Alph_1_2_2.cview_some_Alph_1_2_2 p j q0 E) as (_ & H2).
  unfold Cc_2RB2RB2LA_2LB1LA1RB, cden, A1_2RB2RB2LA_2LB1LA1RB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  rewrite H2. first [ rewrite <- (app_assoc (rep [S1] j)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapi_2RB2RB2LA_2LB1LA1RB : forall p j q0, cview p = (j, Some q0) ->
  exists n, 0 < n /\ csteps tm n (Cc p) = Some (Cc (Pos.succ p)).
Proof.
  intros p j q0 E. exists (2 * j + 6). split; [lia|].
  rewrite (gsi_2RB2RB2LA_2LB1LA1RB p j q0 E).
  rewrite (srun_sound tm false true chi_2RB2RB2LA_2LB1LA1RB A0_2RB2RB2LA_2LB1LA1RB A1_2RB2RB2LA_2LB1LA1RB 2 6
             run_int_2RB2RB2LA_2LB1LA1RB (Ap_Alph_1_2_2 q0 ++ [S0]) [] j
             ltac:(discriminate) ltac:(reflexivity)).
  f_equal. exact (gei_2RB2RB2LA_2LB1LA1RB p j q0 E).
Qed.

Lemma gso_2RB2RB2LA_2LB1LA1RB : forall p j, cview p = (S j, None) ->
  Cc p = cden [] [] j B0_2RB2RB2LA_2LB1LA1RB.
Proof.
  intros p j E. destruct (Alph_1_2_2.cview_none_Alph_1_2_2 p j E) as (H1 & _).
  unfold Cc_2RB2RB2LA_2LB1LA1RB, cden, B0_2RB2RB2LA_2LB1LA1RB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with (j) by lia.
  rewrite H1; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lbl_2RB2RB2LA_2LB1LA1RB : forall q l h r, lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.

Lemma geo_2RB2RB2LA_2LB1LA1RB : forall p j, cview p = (S j, None) ->
  lift (cden [] [] j B1_2RB2RB2LA_2LB1LA1RB) = lift (Cc (Pos.succ p)).
Proof.
  intros p j E. destruct (Alph_1_2_2.cview_none_Alph_1_2_2 p j E) as (_ & H2).
  assert (HD : cden [] [] j B1_2RB2RB2LA_2LB1LA1RB
             = (StB, (rep [S1] (S j) ++ [S2], S2, [S1;S2]))).
  { unfold cden, B1_2RB2RB2LA_2LB1LA1RB, sden, sflat;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 1) with (S j) by lia.
    replace (0 * j + 0) with 0 by lia.
    cbn [rep app]. first [ reflexivity
      | rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  assert (HC : Cc (Pos.succ p) = (StB, ((rep [S1] (S j) ++ [S2]) ++ [S0], S2, [S1;S2]))).
  { unfold Cc_2RB2RB2LA_2LB1LA1RB. rewrite H2.
    first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  rewrite HD, HC. rewrite !lbl_2RB2RB2LA_2LB1LA1RB. reflexivity.
Qed.

(** ** The lap *)

Lemma lap_2RB2RB2LA_2LB1LA1RB : forall p, exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:E. destruct oq as [q0|].
  - destruct (lapi_2RB2RB2LA_2LB1LA1RB p j q0 E) as (n & Hn & Hrun).
    exists n, (Cc (Pos.succ p)).
    split; [exact Hrun | split; [reflexivity | exact Hn]].
  - destruct (cview_pos p j E) as (j' & ->).
    apply (lap_of_run tm Cc true true cho_2RB2RB2LA_2LB1LA1RB B0_2RB2RB2LA_2LB1LA1RB B1_2RB2RB2LA_2LB1LA1RB 2 8 p j' [] []).
    + exact run_ovf_2RB2RB2LA_2LB1LA1RB.
    + reflexivity.
    + reflexivity.
    + exact (gso_2RB2RB2LA_2LB1LA1RB p j' E).
    + exact (geo_2RB2RB2LA_2LB1LA1RB p j' E).
    + lia.
Qed.

(** ** Bootstrap *)

Lemma bootq_2RB2RB2LA_2LB1LA1RB : stepn tm_2RB2RB2LA_2LB1LA1RB 10 InitES = Some (lift (Cc 1)).
Proof.
  assert (H : match csteps tm_2RB2RB2LA_2LB1LA1RB 10 c0 with
              | Some c => ceqb c (Cc 1) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm_2RB2RB2LA_2LB1LA1RB 10 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** the quasihalt witness: a pinned instruction fired in the prefix *)
Lemma wit_2RB2RB2LA_2LB1LA1RB : existsb (fun tg => cfires tm_2RB2RB2LA_2LB1LA1RB c0 10 tg) pins_2RB2RB2LA_2LB1LA1RB = true.
Proof. vm_compute. reflexivity. Qed.

(** ** Visits

    Every state fires inside the OVERFLOW lap, so one prefix chain per state
    plus [LapCertGlue.vis_via_ovf] (run interior laps until the counter
    overflows -- they close exactly) covers every anchor. *)

Lemma fireo_2RB2RB2LA_2LB1LA1RB : forall (l : list lstep) (t : Instr),
  srun_instr tm true true l B0_2RB2RB2LA_2LB1LA1RB = Some t ->
  forall p j, cview p = (S j, None) ->
  exists k c, csteps tm k (Cc p) = Some c /\ cinstr c = t.
Proof.
  intros l t Hst p j E.
  apply (fire_of_run_instr tm Cc true true l B0_2RB2RB2LA_2LB1LA1RB p j [] []);
    [exact Hst | reflexivity | reflexivity | exact (gso_2RB2RB2LA_2LB1LA1RB p j E)].
Qed.


(** ** Fires: every UNPINNED instruction fires from every anchor
    (inside the overflow lap; [LapGlueTr.fire_via_ovf] runs the
    interior laps until the counter overflows). *)

Lemma fire_2RB2RB2LA_2LB1LA1RB : forall t, ~ In t pins_2RB2RB2LA_2LB1LA1RB ->
  forall p, exists k c, csteps tm k (Cc p) = Some c /\ cinstr c = t.
Proof.
  intros t Hnp p.
  assert (Hi : forall p0 j q0, cview p0 = (j, Some q0) ->
            exists n, 0 < n /\ csteps tm n (Cc p0) = Some (Cc (Pos.succ p0)))
    by exact lapi_2RB2RB2LA_2LB1LA1RB.
  destruct t as [q b]; destruct q, b.
  - (* A0 *)
    apply (fire_via_ovf tm Cc Hi (StA, S0)), fireo_2RB2RB2LA_2LB1LA1RB
      with (l := [SWin 4; SCycL 1 0; SWin 2]).
    vm_compute; reflexivity.
  - (* A1 *)
    apply (fire_via_ovf tm Cc Hi (StA, S1)), fireo_2RB2RB2LA_2LB1LA1RB
      with (l := [SWin 2]).
    vm_compute; reflexivity.
  - (* A2 *)
    apply (fire_via_ovf tm Cc Hi (StA, S2)), fireo_2RB2RB2LA_2LB1LA1RB
      with (l := [SWin 4]).
    vm_compute; reflexivity.
  - (* B0: pinned *)
    exfalso. apply Hnp. apply tr_inb_spec. reflexivity.
  - (* B1 *)
    apply (fire_via_ovf tm Cc Hi (StB, S1)), fireo_2RB2RB2LA_2LB1LA1RB
      with (l := [SWin 1]).
    vm_compute; reflexivity.
  - (* B2 *)
    apply (fire_via_ovf tm Cc Hi (StB, S2)), fireo_2RB2RB2LA_2LB1LA1RB
      with (l := []).
    vm_compute; reflexivity.
  - (* C0: pinned *)
    exfalso. apply Hnp. apply tr_inb_spec. reflexivity.
  - (* C1: pinned *)
    exfalso. apply Hnp. apply tr_inb_spec. reflexivity.
  - (* C2: pinned *)
    exfalso. apply Hnp. apply tr_inb_spec. reflexivity.
Qed.

Theorem qhtr_2RB2RB2LA_2LB1LA1RB:NonHalt tm_2RB2RB2LA_2LB1LA1RB /\ QHBoundTr 67 tm_2RB2RB2LA_2LB1LA1RB.
Proof.
 destruct(glue_qhboundtr tm_2RB2RB2LA_2LB1LA1RB pins_2RB2RB2LA_2LB1LA1RB Cc 1 10
 bootq_2RB2RB2LA_2LB1LA1RB (fun p _=>lap_2RB2RB2LA_2LB1LA1RB p)
 (fun t Ht p _=>fire_2RB2RB2LA_2LB1LA1RB t Ht p) wit_2RB2RB2LA_2LB1LA1RB)as[HN[HB _]].
 split;[exact HN|]. intros tg s H;specialize(HB tg s H);lia.
Qed.
