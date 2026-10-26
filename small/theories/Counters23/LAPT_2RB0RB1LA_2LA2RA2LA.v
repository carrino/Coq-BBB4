(** * LAPT_2RB0RB1LA_2LA2RA2LA: TRANSITION-LEVEL board for machine 2RB0RB1LA_2LA2RA2LA, boarded by CERTIFICATE.

    Auto-emitted by tools/counters/emit_lapcert.py (UNTRUSTED emitter; the Coq
    kernel re-runs the checker on every line below).  Left-growth binary
    counter under the Ap_Alph_20_22_2 digit alphabet (Alph_20_22_2.v), anchored at

      Cc p = (StA, (Ap_Alph_20_22_2 p ++ [S2;S2;S2;S0], S1, [S2]))

    The lap is DATA, not a proof script: each branch is a list of steps for
    [Checkers/LapDecider.v], run by the kernel through [vm_compute] and
    discharged by the single theorem [srun_sound].

      interior  (cview p = (j, Some q0)):  4*j+8 steps
      overflow  (cview p = (S j, None)):   boot 4*j+37, then the inner counter's own laps to the
                                           all-ones fill, then exit 4*j+14

    The interior branch closes EXACTLY (which is what feeds
    [LapCertGlue.reach_ovf]); the overflow branch closes one blank short of
    the anchor tail, hence up to [lift].

    Differentially validated against the raw simulator on BOTH branches --
    step counts AND exact configurations -- for 192 interior anchors (interior); offset c=2: 7 overflow phases, j = 1..7 (487 inner laps), plus the concrete j=0 lap (nested overflow).
    Axiom footprint: [functional_extensionality_dep] (via [CTape.lift]). *)
From Coq Require Import Arith Lia Bool List PArith Wellfounded.
From SmallBB Require Import Statement CTape.
From SmallBB.Counters Require Import WTape LapGlue
                                  MonoCounter JpCounter Alph_20_22_2 LapCertGlue LapCertGlueLift IXPGadgets NestedLap NestedLapLift.
From SmallBB.Checkers Require Import LapDecider.
From SmallBB Require Import StatementTr.
From SmallBB.Checkers Require Import WrapTr.
From SmallBB.Checkers.IRules Require Import AnchorVisitsTr.
From SmallBB.Counters Require Import LapGlueTr.
Import ListNotations.

Definition mk_2RB0RB1LA_2LA2RA2LA (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_2RB0RB1LA_2LA2RA2LA.

(** 2RB0RB1LA_2LA2RA2LA *)
Definition tm_2RB0RB1LA_2LA2RA2LA : TM := fun q s => match q, s with
  | StA, S0 => mk S2 DR StB
  | StA, S1 => mk S0 DR StB
  | StA, S2 => mk S1 DL StA
  | StB, S0 => mk S2 DL StA
  | StB, S1 => mk S2 DR StA
  | StB, S2 => mk S2 DL StA
  | StC, S0 => None
  | StC, S1 => None
  | StC, S2 => None end.
(** the instructions the certificate claims NEVER fire; the lap
    argument runs on the machine WRAPPED at them
    ([WrapTr.tm_wrap_trs]), so a pinned instruction firing would
    halt it and every [srun] below would fail. *)
Definition pins_2RB0RB1LA_2LA2RA2LA : list Instr := [(StC, S0); (StC, S1); (StC, S2)].
Definition tmw_2RB0RB1LA_2LA2RA2LA : TM := tm_wrap_trs tm_2RB0RB1LA_2LA2RA2LA pins_2RB0RB1LA_2LA2RA2LA.
Local Notation tm := tmw_2RB0RB1LA_2LA2RA2LA.

Definition Cc_2RB0RB1LA_2LA2RA2LA (p : positive) : cconf := (StA, (Ap_Alph_20_22_2 p ++ [S2;S2;S2;S0], S1, [S2])).
Local Notation Cc := Cc_2RB0RB1LA_2LA2RA2LA.

(** ** The certificate *)

Definition A0_2RB0RB1LA_2LA2RA2LA : sconf := mkC StA (mkS [] [S2;S2] 1 0 [S2;S0]) S1 (mkS [S2] [] 0 0 []).
Definition A1_2RB0RB1LA_2LA2RA2LA : sconf := mkC StA (mkS [] [S2;S0] 1 0 [S2;S2]) S1 (mkS [S2] [] 0 0 []).
Definition chi_2RB0RB1LA_2LA2RA2LA : list lstep := [SWin 4; SCycL 2 0; SWin 4; SCycR 2].

Lemma run_int_2RB0RB1LA_2LA2RA2LA : srun tm false true chi_2RB0RB1LA_2LA2RA2LA A0_2RB0RB1LA_2LA2RA2LA = Some (A1_2RB0RB1LA_2LA2RA2LA, 4, 8).
Proof. vm_compute. reflexivity. Qed.

Definition B0_2RB0RB1LA_2LA2RA2LA : sconf := mkC StA (mkS [] [S2;S2] 1 1 [S2;S2;S2;S2;S0]) S1 (mkS [S2] [] 0 0 []).
Definition B1_2RB0RB1LA_2LA2RA2LA : sconf := mkC StA (mkS [] [S2;S0] 1 2 [S2;S2;S2;S2]) S1 (mkS [S2] [] 0 0 []).
(** ** The INNER anchor family -- Ap_Alph_20_22_2 at StA *)
Definition Cin_2RB0RB1LA_2LA2RA2LA (v : positive) : cconf := (StA, (Ap_Alph_20_22_2 v ++ [S0;S2;S2], S0, [S2])).
Local Notation Cin := Cin_2RB0RB1LA_2LA2RA2LA.

(** [E (2^n) = A^n C]: the value this family's count starts at. *)
Lemma epow2_2RB0RB1LA_2LA2RA2LA : forall n, Ap_Alph_20_22_2 (pow2 n) = rep [S2;S0] n ++ [S2].
Proof. induction n; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.

(** Its own INTERIOR lap -- ordinary and affine.  Iterating it to the fill is
    where a [Theta(2^j)] lives, and [inner_to_fill_lift] keeps it inside an
    existential. *)
Definition AI0_2RB0RB1LA_2LA2RA2LA : sconf := mkC StA (mkS [] [S2;S2] 1 0 [S2;S0]) S0 (mkS [S2] [] 0 0 []).
Definition AI1_2RB0RB1LA_2LA2RA2LA : sconf := mkC StA (mkS [] [S2;S0] 1 0 [S2;S2]) S0 (mkS [S2] [] 0 0 []).
Definition chn_2RB0RB1LA_2LA2RA2LA : list lstep := [SWin 2; SCycL 2 0; SWin 4; SCycR 2; SWin 2].

Lemma run_inner_2RB0RB1LA_2LA2RA2LA : srun tm false true chn_2RB0RB1LA_2LA2RA2LA AI0_2RB0RB1LA_2LA2RA2LA = Some (AI1_2RB0RB1LA_2LA2RA2LA, 4, 8).
Proof. vm_compute. reflexivity. Qed.

(** The OFFSET start: [E (2^(n+2)+2)] is fixed digit blocks, then the rep.
    Its block count is one short of the outer index, which is why [lapo_]
    below REINDEXES at [j = S j']. *)
Lemma epre_2RB0RB1LA_2LA2RA2LA : forall n, Ap_Alph_20_22_2 (xO (xI (pow2 n))) = [S2;S0;S2;S2] ++ rep [S2;S0] n ++ [S2].
Proof.
  intro n. cbn [Ap_Alph_20_22_2]. rewrite epow2_2RB0RB1LA_2LA2RA2LA.
  cbn [app]. rewrite <- ?app_assoc. cbn [app]. reflexivity.
Qed.

(** *** boot: the outer overflow anchor -> the first inner anchor at [pow2 j] *)
Definition BB1_2RB0RB1LA_2LA2RA2LA : sconf := mkC StA (mkS [S2;S0;S2;S2] [S2;S0] 1 1 [S2;S2]) S0 (mkS [S2] [] 0 0 []).
Definition chb_2RB0RB1LA_2LA2RA2LA : list lstep := [SWin 4; SCycL 2 0; SWin 10; SCycR 2; SWin 2; SRotL 1; SWin 3; SWinR 6; SRotL 1; SWin 1; SRotL 1; SWin 7].

Lemma run_boot_2RB0RB1LA_2LA2RA2LA : srun tm true true chb_2RB0RB1LA_2LA2RA2LA B0_2RB0RB1LA_2LA2RA2LA = Some (BB1_2RB0RB1LA_2LA2RA2LA, 4, 37).
Proof. vm_compute. reflexivity. Qed.

(** *** exit: the last inner all-ones fill -> the outer successor *)
Definition BE0_2RB0RB1LA_2LA2RA2LA : sconf := mkC StA (mkS [] [S2;S2] 1 2 [S2;S0;S2;S2]) S0 (mkS [S2] [] 0 0 []).
Definition che_2RB0RB1LA_2LA2RA2LA : list lstep := [SWin 2; SCycL 2 0; SWin 4; SCycR 2].

Lemma run_exit_2RB0RB1LA_2LA2RA2LA : srun tm true true che_2RB0RB1LA_2LA2RA2LA BE0_2RB0RB1LA_2LA2RA2LA = Some (B1_2RB0RB1LA_2LA2RA2LA, 4, 14).
Proof. vm_compute. reflexivity. Qed.

(** ** Anchor glue -- the only per-machine mathematics *)

Lemma gsi_2RB0RB1LA_2LA2RA2LA : forall p j q0, cview p = (j, Some q0) ->
  Cc p = cden (Ap_Alph_20_22_2 q0 ++ [S2;S2;S2;S0]) [] j A0_2RB0RB1LA_2LA2RA2LA.
Proof.
  intros p j q0 E. destruct (Alph_20_22_2.cview_some_Alph_20_22_2 p j q0 E) as (H1 & _).
  unfold Cc_2RB0RB1LA_2LA2RA2LA, cden, A0_2RB0RB1LA_2LA2RA2LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  rewrite H1. first [ rewrite <- (app_assoc (rep [S2;S2] j)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma gei_2RB0RB1LA_2LA2RA2LA : forall p j q0, cview p = (j, Some q0) ->
  cden (Ap_Alph_20_22_2 q0 ++ [S2;S2;S2;S0]) [] j A1_2RB0RB1LA_2LA2RA2LA = Cc (Pos.succ p).
Proof.
  intros p j q0 E. destruct (Alph_20_22_2.cview_some_Alph_20_22_2 p j q0 E) as (_ & H2).
  unfold Cc_2RB0RB1LA_2LA2RA2LA, cden, A1_2RB0RB1LA_2LA2RA2LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  rewrite H2. first [ rewrite <- (app_assoc (rep [S2;S0] j)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapi_2RB0RB1LA_2LA2RA2LA : forall p j q0, cview p = (j, Some q0) ->
  exists n, 0 < n /\ csteps tm n (Cc p) = Some (Cc (Pos.succ p)).
Proof.
  intros p j q0 E. exists (4 * j + 8). split; [lia|].
  rewrite (gsi_2RB0RB1LA_2LA2RA2LA p j q0 E).
  rewrite (srun_sound tm false true chi_2RB0RB1LA_2LA2RA2LA A0_2RB0RB1LA_2LA2RA2LA A1_2RB0RB1LA_2LA2RA2LA 4 8
             run_int_2RB0RB1LA_2LA2RA2LA (Ap_Alph_20_22_2 q0 ++ [S2;S2;S2;S0]) [] j
             ltac:(discriminate) ltac:(reflexivity)).
  f_equal. exact (gei_2RB0RB1LA_2LA2RA2LA p j q0 E).
Qed.

Lemma gso_2RB0RB1LA_2LA2RA2LA : forall p j, cview p = (S (S j), None) ->
  Cc p = cden [] [] j B0_2RB0RB1LA_2LA2RA2LA.
Proof.
  intros p j E. destruct (Alph_20_22_2.cview_none_Alph_20_22_2 p (S j) E) as (H1 & _).
  unfold Cc_2RB0RB1LA_2LA2RA2LA, cden, B0_2RB0RB1LA_2LA2RA2LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 1) with ((S j)) by lia.
  rewrite H1; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lbl_2RB0RB1LA_2LA2RA2LA : forall q l h r, lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.

Lemma geo_2RB0RB1LA_2LA2RA2LA : forall p j, cview p = (S (S j), None) ->
  lift (cden [] [] j B1_2RB0RB1LA_2LA2RA2LA) = lift (Cc (Pos.succ p)).
Proof.
  intros p j E. destruct (Alph_20_22_2.cview_none_Alph_20_22_2 p (S j) E) as (_ & H2).
  assert (HD : cden [] [] j B1_2RB0RB1LA_2LA2RA2LA
             = (StA, (rep [S2;S0] (S (S j)) ++ [S2;S2;S2;S2], S1, [S2]))).
  { unfold cden, B1_2RB0RB1LA_2LA2RA2LA, sden, sflat;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 2) with (S (S j)) by lia.
    replace (0 * j + 0) with 0 by lia.
    cbn [rep app]. first [ reflexivity
      | rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  assert (HC : Cc (Pos.succ p) = (StA, ((rep [S2;S0] (S (S j)) ++ [S2;S2;S2;S2]) ++ [S0], S1, [S2]))).
  { unfold Cc_2RB0RB1LA_2LA2RA2LA. rewrite H2.
    first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  rewrite HD, HC. rewrite !lbl_2RB0RB1LA_2LA2RA2LA. reflexivity.
Qed.

Lemma gsn_2RB0RB1LA_2LA2RA2LA : forall v i q0, cview v = (i, Some q0) ->
  Cin v = cden (Ap_Alph_20_22_2 q0 ++ [S0;S2;S2]) [] i AI0_2RB0RB1LA_2LA2RA2LA.
Proof.
  intros v i q0 E. destruct (Alph_20_22_2.cview_some_Alph_20_22_2 v i q0 E) as (H1 & _).
  unfold Cin_2RB0RB1LA_2LA2RA2LA, cden, AI0_2RB0RB1LA_2LA2RA2LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia.
  rewrite H1. first [ rewrite <- (app_assoc (rep [S2;S2] i)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma gen_2RB0RB1LA_2LA2RA2LA : forall v i q0, cview v = (i, Some q0) ->
  lift (cden (Ap_Alph_20_22_2 q0 ++ [S0;S2;S2]) [] i AI1_2RB0RB1LA_2LA2RA2LA) = lift (Cin (Pos.succ v)).
Proof.
  intros v i q0 E. destruct (Alph_20_22_2.cview_some_Alph_20_22_2 v i q0 E) as (_ & H2).
  unfold Cin_2RB0RB1LA_2LA2RA2LA, cden, AI1_2RB0RB1LA_2LA2RA2LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia.
  replace (0 * i + 0) with 0 by lia.
  cbn [rep app]. rewrite ?app_nil_r.
  rewrite H2. first [ rewrite <- (app_assoc (rep [S2;S0] i)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapin_2RB0RB1LA_2LA2RA2LA : forall v i q0, cview v = (i, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cin v) = Some c'
               /\ lift c' = lift (Cin (Pos.succ v)).
Proof.
  intros v i q0 E.
  exists (4 * i + 8), (cden (Ap_Alph_20_22_2 q0 ++ [S0;S2;S2]) [] i AI1_2RB0RB1LA_2LA2RA2LA).
  split; [lia|]. split; [| exact (gen_2RB0RB1LA_2LA2RA2LA v i q0 E)].
  rewrite (gsn_2RB0RB1LA_2LA2RA2LA v i q0 E).
  exact (srun_sound tm false true chn_2RB0RB1LA_2LA2RA2LA AI0_2RB0RB1LA_2LA2RA2LA AI1_2RB0RB1LA_2LA2RA2LA 4 8
           run_inner_2RB0RB1LA_2LA2RA2LA (Ap_Alph_20_22_2 q0 ++ [S0;S2;S2]) [] i
           ltac:(discriminate) ltac:(reflexivity)).
Qed.

(** The boot lands on the OFFSET inner anchor up to 0/0 trailing
    blanks. *)
Lemma gbo_2RB0RB1LA_2LA2RA2LA : forall j, lift (cden [] [] j BB1_2RB0RB1LA_2LA2RA2LA) = lift (Cin (xO (xI (pow2 j)))).
Proof.
  intro j.
  assert (HD : cden [] [] j BB1_2RB0RB1LA_2LA2RA2LA = (StA, ([S2;S0;S2;S2] ++ rep [S2;S0] j ++ [S2;S0;S2;S2], S0, [S2]))).
  { unfold cden, BB1_2RB0RB1LA_2LA2RA2LA, sden;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 1) with (j + 1) by lia.
    rewrite rep_add. cbn [rep app]. rewrite ?app_nil_r.
    rewrite <- ?app_assoc. cbn [app]. rewrite ?app_nil_r.
    reflexivity. }
  assert (HC : Cin (xO (xI (pow2 j))) = (StA, ([S2;S0;S2;S2] ++ rep [S2;S0] j ++ [S2;S0;S2;S2], S0, [S2]))).
  { unfold Cin_2RB0RB1LA_2LA2RA2LA. rewrite epre_2RB0RB1LA_2LA2RA2LA.
    first [ rewrite <- ?app_assoc; reflexivity
          | cbn [app]; rewrite <- ?app_assoc; cbn [app];
            rewrite ?app_nil_r; reflexivity ]. }
  (* The offset boot can land one written blank past the anchor on EITHER
     side, and [lift] sees neither.  Strip it FIRST: [cbn [app]] flattens
     `w ++ [S0]` into one literal and destroys the shape
     [WTape.lift_app_blank_l] matches on. *)
  rewrite HD, HC. rewrite ?lift_app_blank_l.
  cbn [app]. rewrite <- ?app_assoc. cbn [app].
  rewrite ?lbl_2RB0RB1LA_2LA2RA2LA. rewrite ?lift_app_blank. reflexivity.
Qed.

(** The offset family's all-ones fill is the ordinary one two octaves up:
    [fill (xO (xI (pow2 j))) = fill (pow2 (S (S j)))] by computation, so
    [cview_fill_pow2] still names the exit chain's start word. *)
Lemma gxi_2RB0RB1LA_2LA2RA2LA : forall j, Cin (fill (xO (xI (pow2 j)))) = cden [] [] j BE0_2RB0RB1LA_2LA2RA2LA.
Proof.
  intro j.
  assert (Hf : fill (xO (xI (pow2 j))) = fill (pow2 (S (S j))))
    by (cbn [pow2 fill]; reflexivity).
  rewrite Hf.
  destruct (Alph_20_22_2.cview_none_Alph_20_22_2 (fill (pow2 (S (S j)))) (S (S j))
              (cview_fill_pow2 (S (S j)))) as (H1 & _).
  unfold Cin_2RB0RB1LA_2LA2RA2LA, cden, BE0_2RB0RB1LA_2LA2RA2LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 2) with (S (S j)) by lia.
  replace (0 * j + 0) with 0 by lia.
  rewrite H1; cbn [rep app]. first [ rewrite <- ?app_assoc; cbn [app];
        rewrite ?app_nil_r; reflexivity | reflexivity ].
Qed.

(** The interior lap, restated up to [lift] -- what [vis_via_ovf_lift] and
    [vis_via_fill] consume. *)
Lemma lapil_2RB0RB1LA_2LA2RA2LA : forall p j q0, cview p = (j, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof. intros p j q0 E. destruct (lapi_2RB0RB1LA_2LA2RA2LA p j q0 E) as (n & Hn & Hr).
  exists n, (Cc (Pos.succ p)).
  split; [exact Hn | split; [exact Hr | reflexivity]]. Qed.

(** [cview p = (1, None)] forces [p = 1], where the offset family's count is
    empty: the overflow lap at p = 1 is ONE CONCRETE run, checked the way the
    bootstrap lemma is. *)
Lemma lapo0_2RB0RB1LA_2LA2RA2LA : exists n c', csteps tm n (Cc 1) = Some c'
    /\ lift c' = lift (Cc 2) /\ 0 < n.
Proof.
  exists 31.
  assert (H : match csteps tm 31 (Cc 1) with
              | Some c => ceqb c (Cc 2) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 31 (Cc 1)) as [c|] eqn:E0; [|discriminate].
  exists c. split; [reflexivity|]. split; [apply ceqb_lift; exact H | lia].
Qed.

(** The outer OVERFLOW branch.  The offset family's block count is one short
    of the outer index, so the branch REINDEXES: the generic route runs at
    [j = S j'] and [j = 0] is the concrete lap above. *)
Lemma lapo_2RB0RB1LA_2LA2RA2LA : forall p j, cview p = (S j, None) ->
  exists n c', csteps tm n (Cc p) = Some c'
          /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intros p j E.
  destruct j as [|j'].
  - rewrite (cview_none_shape p 0 E). exact lapo0_2RB0RB1LA_2LA2RA2LA.
  - apply (nested_overflow_lift tm Cc Cin lapin_2RB0RB1LA_2LA2RA2LA p (xO (xI (pow2 j')))).
    + exists (4 * j' + 37), (cden [] [] j' BB1_2RB0RB1LA_2LA2RA2LA).
      split; [lia|]. split; [| exact (gbo_2RB0RB1LA_2LA2RA2LA j')].
      rewrite (gso_2RB0RB1LA_2LA2RA2LA p j' E).
      exact (srun_sound tm true true chb_2RB0RB1LA_2LA2RA2LA B0_2RB0RB1LA_2LA2RA2LA BB1_2RB0RB1LA_2LA2RA2LA 4 37
               run_boot_2RB0RB1LA_2LA2RA2LA [] [] j' ltac:(reflexivity) ltac:(reflexivity)).
    + exists (4 * j' + 14), (cden [] [] j' B1_2RB0RB1LA_2LA2RA2LA).
      split; [| exact (geo_2RB0RB1LA_2LA2RA2LA p j' E)].
      rewrite (gxi_2RB0RB1LA_2LA2RA2LA j').
      exact (srun_sound tm true true che_2RB0RB1LA_2LA2RA2LA BE0_2RB0RB1LA_2LA2RA2LA B1_2RB0RB1LA_2LA2RA2LA 4 14
               run_exit_2RB0RB1LA_2LA2RA2LA [] [] j' ltac:(reflexivity) ltac:(reflexivity)).
Qed.

(** State StA's visit witness at the reindex's p = 1 case -- concrete. *)
Lemma visz_StA_2RB0RB1LA_2LA2RA2LA : exists k c, csteps tm k (Cc 1) = Some c /\ fst c = StA.
Proof. exists 0. eexists. split; [vm_compute; reflexivity | reflexivity]. Qed.

(** State StB's visit witness at the reindex's p = 1 case -- concrete. *)
Lemma visz_StB_2RB0RB1LA_2LA2RA2LA : exists k c, csteps tm k (Cc 1) = Some c /\ fst c = StB.
Proof. exists 1. eexists. split; [vm_compute; reflexivity | reflexivity]. Qed.



(** ** The lap *)

Lemma lap_2RB0RB1LA_2LA2RA2LA : forall p, exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:E. destruct oq as [q0|].
  - destruct (lapi_2RB0RB1LA_2LA2RA2LA p j q0 E) as (n & Hn & Hrun).
    exists n, (Cc (Pos.succ p)).
    split; [exact Hrun | split; [reflexivity | exact Hn]].
  - destruct (cview_pos p j E) as (j' & ->). exact (lapo_2RB0RB1LA_2LA2RA2LA p j' E).
Qed.

(** ** Bootstrap *)

Lemma boot_2RB0RB1LA_2LA2RA2LA : exists t0, stepn tm t0 InitES = Some (lift (Cc 1)).
Proof.
  exists 18.
  assert (H : match csteps tm 18 c0 with
              | Some c => ceqb c (Cc 1) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 18 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** ** Visits

    Every state fires inside the OVERFLOW lap, so one prefix chain per state
    plus [LapCertGlue.vis_via_ovf] (run interior laps until the counter
    overflows -- they close exactly) covers every anchor. *)

Lemma fireo_2RB0RB1LA_2LA2RA2LA : forall (l : list lstep) (t : Instr),
  srun_instr tm true true l B0_2RB0RB1LA_2LA2RA2LA = Some t ->
  forall p j, cview p = (S (S j), None) ->
  exists k c, csteps tm k (Cc p) = Some c /\ cinstr c = t.
Proof.
  intros l t Hst p j E.
  apply (fire_of_run_instr tm Cc true true l B0_2RB0RB1LA_2LA2RA2LA p j [] []);
    [exact Hst | reflexivity | reflexivity | exact (gso_2RB0RB1LA_2LA2RA2LA p j E)].
Qed.


(** Instruction A0 at the reindexed branch's p = 1 case -- concrete. *)
Lemma firez_A0_2RB0RB1LA_2LA2RA2LA : exists k c, csteps tm k (Cc 1) = Some c /\ cinstr c = (StA, S0).
Proof. exists 2. eexists. split; [vm_compute; reflexivity | reflexivity]. Qed.

(** Instruction A1 at the reindexed branch's p = 1 case -- concrete. *)
Lemma firez_A1_2RB0RB1LA_2LA2RA2LA : exists k c, csteps tm k (Cc 1) = Some c /\ cinstr c = (StA, S1).
Proof. exists 0. eexists. split; [vm_compute; reflexivity | reflexivity]. Qed.

(** Instruction A2 at the reindexed branch's p = 1 case -- concrete. *)
Lemma firez_A2_2RB0RB1LA_2LA2RA2LA : exists k c, csteps tm k (Cc 1) = Some c /\ cinstr c = (StA, S2).
Proof. exists 4. eexists. split; [vm_compute; reflexivity | reflexivity]. Qed.

(** Instruction B0 at the reindexed branch's p = 1 case -- concrete. *)
Lemma firez_B0_2RB0RB1LA_2LA2RA2LA : exists k c, csteps tm k (Cc 1) = Some c /\ cinstr c = (StB, S0).
Proof. exists 20. eexists. split; [vm_compute; reflexivity | reflexivity]. Qed.

(** Instruction B1 at the reindexed branch's p = 1 case -- concrete. *)
Lemma firez_B1_2RB0RB1LA_2LA2RA2LA : exists k c, csteps tm k (Cc 1) = Some c /\ cinstr c = (StB, S1).
Proof. exists 10. eexists. split; [vm_compute; reflexivity | reflexivity]. Qed.

(** Instruction B2 at the reindexed branch's p = 1 case -- concrete. *)
Lemma firez_B2_2RB0RB1LA_2LA2RA2LA : exists k c, csteps tm k (Cc 1) = Some c /\ cinstr c = (StB, S2).
Proof. exists 1. eexists. split; [vm_compute; reflexivity | reflexivity]. Qed.

(** ** Fires: every UNPINNED instruction fires from every anchor
    (inside the overflow lap; [LapGlueTr.fire_via_ovf] runs the
    interior laps until the counter overflows). *)

Lemma fire_2RB0RB1LA_2LA2RA2LA : forall t, ~ In t pins_2RB0RB1LA_2LA2RA2LA ->
  forall p, exists k c, csteps tm k (Cc p) = Some c /\ cinstr c = t.
Proof.
  intros t Hnp p.
  assert (Hi : forall p0 j q0, cview p0 = (j, Some q0) ->
            exists n, 0 < n /\ csteps tm n (Cc p0) = Some (Cc (Pos.succ p0)))
    by exact lapi_2RB0RB1LA_2LA2RA2LA.
  destruct t as [q b]; destruct q, b.
  - (* A0 *)
    apply (fire_via_ovf tm Cc Hi (StA, S0)).
    intros p1 j1 E1. destruct j1 as [|j1'].
    + rewrite (cview_none_shape p1 0 E1).
      exact firez_A0_2RB0RB1LA_2LA2RA2LA.
    + exact (fireo_2RB0RB1LA_2LA2RA2LA [SWin 2] (StA, S0) ltac:(vm_compute; reflexivity)
                   p1 j1' E1).
  - (* A1 *)
    apply (fire_via_ovf tm Cc Hi (StA, S1)).
    intros p1 j1 E1. destruct j1 as [|j1'].
    + rewrite (cview_none_shape p1 0 E1).
      exact firez_A1_2RB0RB1LA_2LA2RA2LA.
    + exact (fireo_2RB0RB1LA_2LA2RA2LA [] (StA, S1) ltac:(vm_compute; reflexivity)
                   p1 j1' E1).
  - (* A2 *)
    apply (fire_via_ovf tm Cc Hi (StA, S2)).
    intros p1 j1 E1. destruct j1 as [|j1'].
    + rewrite (cview_none_shape p1 0 E1).
      exact firez_A2_2RB0RB1LA_2LA2RA2LA.
    + exact (fireo_2RB0RB1LA_2LA2RA2LA [SWin 4] (StA, S2) ltac:(vm_compute; reflexivity)
                   p1 j1' E1).
  - (* B0 *)
    apply (fire_via_ovf tm Cc Hi (StB, S0)).
    intros p1 j1 E1. destruct j1 as [|j1'].
    + rewrite (cview_none_shape p1 0 E1).
      exact firez_B0_2RB0RB1LA_2LA2RA2LA.
    + exact (fireo_2RB0RB1LA_2LA2RA2LA [SWin 4; SCycL 2 0; SWin 10; SCycR 2; SWin 2; SRotL 1; SWin 3; SWinR 1] (StB, S0) ltac:(vm_compute; reflexivity)
                   p1 j1' E1).
  - (* B1 *)
    apply (fire_via_ovf tm Cc Hi (StB, S1)).
    intros p1 j1 E1. destruct j1 as [|j1'].
    + rewrite (cview_none_shape p1 0 E1).
      exact firez_B1_2RB0RB1LA_2LA2RA2LA.
    + exact (fireo_2RB0RB1LA_2LA2RA2LA [SWin 4; SCycL 2 0; SWin 6] (StB, S1) ltac:(vm_compute; reflexivity)
                   p1 j1' E1).
  - (* B2 *)
    apply (fire_via_ovf tm Cc Hi (StB, S2)).
    intros p1 j1 E1. destruct j1 as [|j1'].
    + rewrite (cview_none_shape p1 0 E1).
      exact firez_B2_2RB0RB1LA_2LA2RA2LA.
    + exact (fireo_2RB0RB1LA_2LA2RA2LA [SWin 1] (StB, S2) ltac:(vm_compute; reflexivity)
                   p1 j1' E1).
  - (* C0: pinned *)
    exfalso. apply Hnp. apply tr_inb_spec. reflexivity.
  - (* C1: pinned *)
    exfalso. apply Hnp. apply tr_inb_spec. reflexivity.
  - (* C2: pinned *)
    exfalso. apply Hnp. apply tr_inb_spec. reflexivity.
Qed.

Theorem nqhtr_2RB0RB1LA_2LA2RA2LA : NeverQuasiHaltsTr tm_2RB0RB1LA_2LA2RA2LA.
Proof.
  apply (glue_neverqhtr tm_2RB0RB1LA_2LA2RA2LA pins_2RB0RB1LA_2LA2RA2LA Cc 1).
  - exact boot_2RB0RB1LA_2LA2RA2LA.
  - intros p _. apply lap_2RB0RB1LA_2LA2RA2LA.
  - intros t Ht p _. apply fire_2RB0RB1LA_2LA2RA2LA. exact Ht.
Qed.

Theorem nonhalt_2RB0RB1LA_2LA2RA2LA : NonHalt tm_2RB0RB1LA_2LA2RA2LA.
Proof. apply never_qh_tr_nonhalt, nqhtr_2RB0RB1LA_2LA2RA2LA. Qed.
