(** * REG_0RB0LC_1LC1RB_1LD1LA_1RD0RC: machine 0RB0LC_1LC1RB_1LD1LA_1RD0RC, boarded by CERTIFICATE (REGISTER route).

    Auto-emitted by tools/counters/regcert.py (UNTRUSTED emitter; the Coq
    kernel re-runs the checker on every line below).  A binary counter under
    the Ap_Alph_10_11_11 digit alphabet (Alph_10_11_11.v) whose anchor FRAME depends on the
    OCTAVE: the machine keeps a REGISTER mark past the head and moves it once
    per octave, so the family is (register state x counter) and the anchor is
    PIECEWISE (WAVE28 section 3c, the `period-2+virt` class).

      Cc p = if virt p then (StD, E p ++ tail, S0, frmv p)
             else (StA, E p ++ tail, S0, frm p)

    with [RegGlue.podd] the octave parity ([podd p = true] iff the octave is
    odd), [frm]/[frmv] the two frames it selects, and [virt p] the powers of
    two the machine rests at in a DIFFERENT frame from their own octave's --
    the SKIP route's virtual anchor, one dimension up.  The lap branches are
    NOT all chains:

      interior  (virt p = false, cview p = (j, Some q0)):  4*j+4 / 4*j+4 by parity steps, exact,
                the frame carried as the RIGHT OPAQUE TAIL so ONE chain
                covers both octave parities
      overflow  (cview p = (S j, None)), one chain per parity:
                podd p = true: 4*j+7   podd p = false: 4*j+9
      register  (virt p = true), one arm per parity: parity false NESTED, boot 0*k+6 then the inner counter then exit 4*k+13

    The register step is the point: the mark cannot be moved without a pass
    that COUNTS, so a NESTED branch sits inside a piecewise [Cc] and the
    exponent stays inside the [exists n] of
    [Counters/NestedLapLift.inner_to_fill_lift].  [Counters/SkipGlue.v]
    fences the virtual anchors ([reach_ovf_skip] / [vis_via_skip], the
    interior-lap hypothesis GUARDED by "not virtual"),
    [Counters/RegGlue.v] supplies the octave parity, and the closer is
    [LapGlue.glue_neverqh] directly.

    Differentially validated against the raw simulator on EVERY branch --
    step counts AND configurations, every inner lap of every register step --
    for 119 anchors, 2 register steps, 38 inner laps.
    Axiom footprint: [functional_extensionality_dep] (via [CTape.lift]). *)
From Coq Require Import Arith Lia Bool List PArith Wellfounded.
From BBB4 Require Import BBB4_Statement CTape Mirror.
From Coq Require Import FunctionalExtensionality.
From BBB4.Counters Require Import WTape LapGlue MonoCounter JpCounter
                                  Alph_10_11_11 ILCounter LapCertGlue LapCertGlueLift
                                  IXPGadgets NestedLap NestedLapLift
                                  SkipGlue RegGlue.
From BBB4.Census Require Import TNF_QH.
From BBB4.Checkers Require Import LapDecider.
Import ListNotations.

Definition mk_0RB0LC_1LC1RB_1LD1LA_1RD0RC (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_0RB0LC_1LC1RB_1LD1LA_1RD0RC.

(** 0RB0LC_1LC1RB_1LD1LA_1RD0RC *)
(** 0RB0LC_1LC1RB_1LD1LA_1RD0RC -- the real machine (its counter grows RIGHT). *)
Definition tm_0RB0LC_1LC1RB_1LD1LA_1RD0RC : TM := fun q s => match q, s with
  | StA, S0 => mk S0 DR StB | StA, S1 => mk S0 DL StC
  | StB, S0 => mk S1 DL StC | StB, S1 => mk S1 DR StB
  | StC, S0 => mk S1 DL StD | StC, S1 => mk S1 DL StA
  | StD, S0 => mk S1 DR StD | StD, S1 => mk S0 DR StC end.

(** Its mirror 0LB0RC_1RC1LB_1RD1RA_1LD0LC: the same counter grown leftward.  Every
    lemma below runs on the MIRRORED table;
    [Mirror.mirror_never_qh] transfers the conclusion back. *)
Definition tmm_0RB0LC_1LC1RB_1LD1LA_1RD0RC : TM := fun q s => match q, s with
  | StA, S0 => mk S0 DL StB | StA, S1 => mk S0 DR StC
  | StB, S0 => mk S1 DR StC | StB, S1 => mk S1 DL StB
  | StC, S0 => mk S1 DR StD | StC, S1 => mk S1 DR StA
  | StD, S0 => mk S1 DL StD | StD, S1 => mk S0 DL StC end.
Local Notation tm := tmm_0RB0LC_1LC1RB_1LD1LA_1RD0RC.

Lemma mirror_ok_0RB0LC_1LC1RB_1LD1LA_1RD0RC : mirror_tm tm_0RB0LC_1LC1RB_1LD1LA_1RD0RC = tmm_0RB0LC_1LC1RB_1LD1LA_1RD0RC.
Proof.
  apply functional_extensionality; intro q;
    apply functional_extensionality; intro b; destruct q, b; reflexivity.
Qed.

(** The virtual anchors.  [pexp p = Some 0] (that is, [p = 1]) is excluded by
    the [S _] pattern, so [Cc 1] is an ordinary frame anchor and the overflow
    glue holds at it too. *)
Definition virt_0RB0LC_1LC1RB_1LD1LA_1RD0RC (p : positive) : bool :=
  match pexp p with Some (S _) => negb (podd p) | _ => false end.
Local Notation virt := virt_0RB0LC_1LC1RB_1LD1LA_1RD0RC.

Definition frm_0RB0LC_1LC1RB_1LD1LA_1RD0RC (p : positive) : list Sym :=
  if podd p then [] else [S1].
Local Notation frm := frm_0RB0LC_1LC1RB_1LD1LA_1RD0RC.

Definition frmv_0RB0LC_1LC1RB_1LD1LA_1RD0RC (p : positive) : list Sym :=
  if podd p then [] else [].
Local Notation frmv := frmv_0RB0LC_1LC1RB_1LD1LA_1RD0RC.

Definition Cc_0RB0LC_1LC1RB_1LD1LA_1RD0RC (p : positive) : cconf :=
  if virt_0RB0LC_1LC1RB_1LD1LA_1RD0RC p then (StD, (Ap_Alph_10_11_11 p ++ [], S0, frmv_0RB0LC_1LC1RB_1LD1LA_1RD0RC p))
  else (StA, (Ap_Alph_10_11_11 p ++ [], S0, frm_0RB0LC_1LC1RB_1LD1LA_1RD0RC p)).
Local Notation Cc := Cc_0RB0LC_1LC1RB_1LD1LA_1RD0RC.

(** ** The INNER anchor family of the parity-false register step -- the
    counter that step re-runs *)
Definition Cin0_0RB0LC_1LC1RB_1LD1LA_1RD0RC (v : positive) : cconf :=
  (StA, (Ip v ++ [S1], S0, [S1;S1])).
Local Notation Cin0 := Cin0_0RB0LC_1LC1RB_1LD1LA_1RD0RC.


Ltac rshape_0RB0LC_1LC1RB_1LD1LA_1RD0RC :=
  cbn [rep app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r;
  reflexivity.

(** ** The certificate *)

Definition A01_0RB0LC_1LC1RB_1LD1LA_1RD0RC : sconf := mkC StA (mkS [] [S1;S1] 1 0 [S1;S0]) S0 (mkS [] [] 0 0 []).
Definition A11_0RB0LC_1LC1RB_1LD1LA_1RD0RC : sconf := mkC StA (mkS [] [S1;S0] 1 0 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition chi1_0RB0LC_1LC1RB_1LD1LA_1RD0RC : list lstep := [SRotL 1; SWin 1; SCycL 2 0; SWin 2; SCycR 2; SWin 1; SUnrotL 1].

Lemma run_int1_0RB0LC_1LC1RB_1LD1LA_1RD0RC : srun tm false true chi1_0RB0LC_1LC1RB_1LD1LA_1RD0RC A01_0RB0LC_1LC1RB_1LD1LA_1RD0RC = Some (A11_0RB0LC_1LC1RB_1LD1LA_1RD0RC, 4, 4).
Proof. vm_compute. reflexivity. Qed.

Definition A00_0RB0LC_1LC1RB_1LD1LA_1RD0RC : sconf := mkC StA (mkS [] [S1;S1] 1 0 [S1;S0]) S0 (mkS [S1] [] 0 0 []).
Definition A10_0RB0LC_1LC1RB_1LD1LA_1RD0RC : sconf := mkC StA (mkS [] [S1;S0] 1 0 [S1;S1]) S0 (mkS [S1] [] 0 0 []).
Definition chi0_0RB0LC_1LC1RB_1LD1LA_1RD0RC : list lstep := [SRotL 1; SWin 1; SCycL 2 0; SWin 2; SCycR 2; SWin 1; SUnrotL 1].

Lemma run_int0_0RB0LC_1LC1RB_1LD1LA_1RD0RC : srun tm false true chi0_0RB0LC_1LC1RB_1LD1LA_1RD0RC A00_0RB0LC_1LC1RB_1LD1LA_1RD0RC = Some (A10_0RB0LC_1LC1RB_1LD1LA_1RD0RC, 4, 4).
Proof. vm_compute. reflexivity. Qed.

Definition B01_0RB0LC_1LC1RB_1LD1LA_1RD0RC : sconf := mkC StA (mkS [] [S1;S1] 1 0 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition B11_0RB0LC_1LC1RB_1LD1LA_1RD0RC : sconf := mkC StD (mkS [] [S1;S0] 1 1 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition cho1_0RB0LC_1LC1RB_1LD1LA_1RD0RC : list lstep := [SRotL 1; SWin 1; SCycL 2 0; SWin 1; SWinL 3; SCycR 2; SWin 1; SWinR 1; SFoldL 1].

Lemma run_ovf1_0RB0LC_1LC1RB_1LD1LA_1RD0RC : srun tm true true cho1_0RB0LC_1LC1RB_1LD1LA_1RD0RC B01_0RB0LC_1LC1RB_1LD1LA_1RD0RC = Some (B11_0RB0LC_1LC1RB_1LD1LA_1RD0RC, 4, 7).
Proof. vm_compute. reflexivity. Qed.

Definition B00_0RB0LC_1LC1RB_1LD1LA_1RD0RC : sconf := mkC StA (mkS [] [S1;S1] 1 0 [S1;S1]) S0 (mkS [S1] [] 0 0 []).
Definition B10_0RB0LC_1LC1RB_1LD1LA_1RD0RC : sconf := mkC StA (mkS [] [S1;S0] 1 1 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition cho0_0RB0LC_1LC1RB_1LD1LA_1RD0RC : list lstep := [SRotL 1; SWin 1; SCycL 2 0; SWin 1; SWinL 3; SCycR 2; SWin 4; SFoldL 1].

Lemma run_ovf0_0RB0LC_1LC1RB_1LD1LA_1RD0RC : srun tm true true cho0_0RB0LC_1LC1RB_1LD1LA_1RD0RC B00_0RB0LC_1LC1RB_1LD1LA_1RD0RC = Some (B10_0RB0LC_1LC1RB_1LD1LA_1RD0RC, 4, 9).
Proof. vm_compute. reflexivity. Qed.

(** *** the register step at octave parity false: boot (from the PEELED
    virtual anchor -- the first move is onto the counter's own top block),
    the inner counter's laps, exit *)
Definition VS0_0RB0LC_1LC1RB_1LD1LA_1RD0RC : sconf := mkC StD (mkS [S1;S0] [S1;S0] 1 0 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition CS0_0RB0LC_1LC1RB_1LD1LA_1RD0RC : sconf := mkC StA (mkS [] [S1;S0] 1 0 [S1;S1]) S0 (mkS [S1;S1] [] 0 0 []).
Definition chb0_0RB0LC_1LC1RB_1LD1LA_1RD0RC : list lstep := [SWin 4; SRotL 1; SWin 2; SUnrotL 1].

Lemma run_boot0_0RB0LC_1LC1RB_1LD1LA_1RD0RC : srun tm true true chb0_0RB0LC_1LC1RB_1LD1LA_1RD0RC VS0_0RB0LC_1LC1RB_1LD1LA_1RD0RC = Some (CS0_0RB0LC_1LC1RB_1LD1LA_1RD0RC, 0, 6).
Proof. vm_compute. reflexivity. Qed.

Definition AI00_0RB0LC_1LC1RB_1LD1LA_1RD0RC : sconf := mkC StA (mkS [] [S1;S1] 1 0 [S1;S0]) S0 (mkS [S1;S1] [] 0 0 []).
Definition AI10_0RB0LC_1LC1RB_1LD1LA_1RD0RC : sconf := mkC StA (mkS [] [S1;S0] 1 0 [S1;S1]) S0 (mkS [S1;S1] [] 0 0 []).
Definition chn0_0RB0LC_1LC1RB_1LD1LA_1RD0RC : list lstep := [SRotL 1; SWin 1; SCycL 2 0; SWin 2; SCycR 2; SWin 1; SUnrotL 1].

Lemma run_inner0_0RB0LC_1LC1RB_1LD1LA_1RD0RC : srun tm false true chn0_0RB0LC_1LC1RB_1LD1LA_1RD0RC AI00_0RB0LC_1LC1RB_1LD1LA_1RD0RC = Some (AI10_0RB0LC_1LC1RB_1LD1LA_1RD0RC, 4, 4).
Proof. vm_compute. reflexivity. Qed.

Definition CF0_0RB0LC_1LC1RB_1LD1LA_1RD0RC : sconf := mkC StA (mkS [] [S1;S1] 1 0 [S1;S1]) S0 (mkS [S1;S1] [] 0 0 []).
Definition VT0_0RB0LC_1LC1RB_1LD1LA_1RD0RC : sconf := mkC StA (mkS [S1;S1] [S1;S0] 1 0 [S1;S1]) S0 (mkS [S1] [] 0 0 []).
Definition che0_0RB0LC_1LC1RB_1LD1LA_1RD0RC : list lstep := [SRotL 1; SWin 1; SCycL 2 0; SWin 1; SWinL 3; SCycR 2; SWin 8].

Lemma run_exit0_0RB0LC_1LC1RB_1LD1LA_1RD0RC : srun tm true true che0_0RB0LC_1LC1RB_1LD1LA_1RD0RC CF0_0RB0LC_1LC1RB_1LD1LA_1RD0RC = Some (VT0_0RB0LC_1LC1RB_1LD1LA_1RD0RC, 4, 13).
Proof. vm_compute. reflexivity. Qed.


(** ** Anchor glue -- the only per-machine mathematics *)

Lemma epow_0RB0LC_1LC1RB_1LD1LA_1RD0RC : forall n, Ap_Alph_10_11_11 (pow2 n) = rep [S1;S0] n ++ [S1;S1].
Proof. induction n; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.

Lemma iepow0_0RB0LC_1LC1RB_1LD1LA_1RD0RC : forall n, Ip (pow2 n) = rep [S1;S0] n ++ [S1].
Proof. induction n; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.


Lemma hsucc0_0RB0LC_1LC1RB_1LD1LA_1RD0RC : forall p j q0, cview p = (j, Some q0) ->
  virt (Pos.succ p) = false.
Proof.
  intros p j q0 E. unfold virt_0RB0LC_1LC1RB_1LD1LA_1RD0RC.
  rewrite (pexp_succ_int p j q0 E). reflexivity.
Qed.

Lemma hsuccv_0RB0LC_1LC1RB_1LD1LA_1RD0RC : forall p k, pexp p = Some (S k) -> virt (Pos.succ p) = false.
Proof.
  intros p k Hx. unfold virt_0RB0LC_1LC1RB_1LD1LA_1RD0RC.
  rewrite (pexp_succ_virt p k Hx). reflexivity.
Qed.

Lemma vsome_0RB0LC_1LC1RB_1LD1LA_1RD0RC : forall p, virt p = true -> exists k, pexp p = Some (S k).
Proof.
  intros p Hv. unfold virt_0RB0LC_1LC1RB_1LD1LA_1RD0RC in Hv.
  destruct (pexp p) as [[|m]|]; try discriminate Hv.
  exists m. reflexivity.
Qed.

(** *** the interior branch at octave parity true.  The frame is CONCRETE in
    the chain's own right side: on some machines the head steps onto it. *)
Lemma gsi1_0RB0LC_1LC1RB_1LD1LA_1RD0RC : forall p j q0, cview p = (j, Some q0) -> virt p = false ->
  podd p = true -> Cc p = cden (Ap_Alph_10_11_11 q0 ++ []) [] j A01_0RB0LC_1LC1RB_1LD1LA_1RD0RC.
Proof.
  intros p j q0 E Hv Hb. unfold Cc_0RB0LC_1LC1RB_1LD1LA_1RD0RC. rewrite Hv.
  unfold frm_0RB0LC_1LC1RB_1LD1LA_1RD0RC. rewrite Hb.
  destruct (Alph_10_11_11.cview_some_Alph_10_11_11 p j q0 E) as (H1 & _).
  unfold cden, A01_0RB0LC_1LC1RB_1LD1LA_1RD0RC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia. replace (0 * j + 0) with 0 by lia.
  rewrite H1. rshape_0RB0LC_1LC1RB_1LD1LA_1RD0RC.
Qed.

Lemma gei1_0RB0LC_1LC1RB_1LD1LA_1RD0RC : forall p j q0, cview p = (j, Some q0) -> virt p = false ->
  podd p = true ->
  cden (Ap_Alph_10_11_11 q0 ++ []) [] j A11_0RB0LC_1LC1RB_1LD1LA_1RD0RC = Cc (Pos.succ p).
Proof.
  intros p j q0 E Hv Hb. unfold Cc_0RB0LC_1LC1RB_1LD1LA_1RD0RC.
  rewrite (hsucc0_0RB0LC_1LC1RB_1LD1LA_1RD0RC p j q0 E).
  unfold frm_0RB0LC_1LC1RB_1LD1LA_1RD0RC. rewrite (podd_succ_int p j q0 E), Hb.
  destruct (Alph_10_11_11.cview_some_Alph_10_11_11 p j q0 E) as (_ & H2).
  unfold cden, A11_0RB0LC_1LC1RB_1LD1LA_1RD0RC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia. replace (0 * j + 0) with 0 by lia.
  rewrite H2. rshape_0RB0LC_1LC1RB_1LD1LA_1RD0RC.
Qed.

Lemma lapi1_0RB0LC_1LC1RB_1LD1LA_1RD0RC : forall p j q0, cview p = (j, Some q0) -> virt p = false ->
  podd p = true ->
  exists n, 0 < n /\ csteps tm n (Cc p) = Some (Cc (Pos.succ p)).
Proof.
  intros p j q0 E Hv Hb. exists (4 * j + 4). split; [lia|].
  rewrite (gsi1_0RB0LC_1LC1RB_1LD1LA_1RD0RC p j q0 E Hv Hb).
  rewrite (srun_sound tm false true chi1_0RB0LC_1LC1RB_1LD1LA_1RD0RC A01_0RB0LC_1LC1RB_1LD1LA_1RD0RC A11_0RB0LC_1LC1RB_1LD1LA_1RD0RC 4 4
             run_int1_0RB0LC_1LC1RB_1LD1LA_1RD0RC (Ap_Alph_10_11_11 q0 ++ []) [] j
             ltac:(discriminate) ltac:(reflexivity)).
  f_equal. exact (gei1_0RB0LC_1LC1RB_1LD1LA_1RD0RC p j q0 E Hv Hb).
Qed.

(** *** the interior branch at octave parity false.  The frame is CONCRETE in
    the chain's own right side: on some machines the head steps onto it. *)
Lemma gsi0_0RB0LC_1LC1RB_1LD1LA_1RD0RC : forall p j q0, cview p = (j, Some q0) -> virt p = false ->
  podd p = false -> Cc p = cden (Ap_Alph_10_11_11 q0 ++ []) [] j A00_0RB0LC_1LC1RB_1LD1LA_1RD0RC.
Proof.
  intros p j q0 E Hv Hb. unfold Cc_0RB0LC_1LC1RB_1LD1LA_1RD0RC. rewrite Hv.
  unfold frm_0RB0LC_1LC1RB_1LD1LA_1RD0RC. rewrite Hb.
  destruct (Alph_10_11_11.cview_some_Alph_10_11_11 p j q0 E) as (H1 & _).
  unfold cden, A00_0RB0LC_1LC1RB_1LD1LA_1RD0RC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia. replace (0 * j + 0) with 0 by lia.
  rewrite H1. rshape_0RB0LC_1LC1RB_1LD1LA_1RD0RC.
Qed.

Lemma gei0_0RB0LC_1LC1RB_1LD1LA_1RD0RC : forall p j q0, cview p = (j, Some q0) -> virt p = false ->
  podd p = false ->
  cden (Ap_Alph_10_11_11 q0 ++ []) [] j A10_0RB0LC_1LC1RB_1LD1LA_1RD0RC = Cc (Pos.succ p).
Proof.
  intros p j q0 E Hv Hb. unfold Cc_0RB0LC_1LC1RB_1LD1LA_1RD0RC.
  rewrite (hsucc0_0RB0LC_1LC1RB_1LD1LA_1RD0RC p j q0 E).
  unfold frm_0RB0LC_1LC1RB_1LD1LA_1RD0RC. rewrite (podd_succ_int p j q0 E), Hb.
  destruct (Alph_10_11_11.cview_some_Alph_10_11_11 p j q0 E) as (_ & H2).
  unfold cden, A10_0RB0LC_1LC1RB_1LD1LA_1RD0RC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia. replace (0 * j + 0) with 0 by lia.
  rewrite H2. rshape_0RB0LC_1LC1RB_1LD1LA_1RD0RC.
Qed.

Lemma lapi0_0RB0LC_1LC1RB_1LD1LA_1RD0RC : forall p j q0, cview p = (j, Some q0) -> virt p = false ->
  podd p = false ->
  exists n, 0 < n /\ csteps tm n (Cc p) = Some (Cc (Pos.succ p)).
Proof.
  intros p j q0 E Hv Hb. exists (4 * j + 4). split; [lia|].
  rewrite (gsi0_0RB0LC_1LC1RB_1LD1LA_1RD0RC p j q0 E Hv Hb).
  rewrite (srun_sound tm false true chi0_0RB0LC_1LC1RB_1LD1LA_1RD0RC A00_0RB0LC_1LC1RB_1LD1LA_1RD0RC A10_0RB0LC_1LC1RB_1LD1LA_1RD0RC 4 4
             run_int0_0RB0LC_1LC1RB_1LD1LA_1RD0RC (Ap_Alph_10_11_11 q0 ++ []) [] j
             ltac:(discriminate) ltac:(reflexivity)).
  f_equal. exact (gei0_0RB0LC_1LC1RB_1LD1LA_1RD0RC p j q0 E Hv Hb).
Qed.

Lemma lapi_0RB0LC_1LC1RB_1LD1LA_1RD0RC : forall p j q0, cview p = (j, Some q0) -> virt p = false ->
  exists n, 0 < n /\ csteps tm n (Cc p) = Some (Cc (Pos.succ p)).
Proof.
  intros p j q0 E Hv. destruct (podd p) eqn:Hb.
  - exact (lapi1_0RB0LC_1LC1RB_1LD1LA_1RD0RC p j q0 E Hv Hb).
  - exact (lapi0_0RB0LC_1LC1RB_1LD1LA_1RD0RC p j q0 E Hv Hb).
Qed.


(** *** the overflow branch.  A fill anchor is never virtual: above [1] it is
    not a power of two at all, and [1] fails the [S _] pattern. *)
Lemma vfill_0RB0LC_1LC1RB_1LD1LA_1RD0RC : forall p j, cview p = (S j, None) -> virt p = false.
Proof.
  intros p j E. unfold virt_0RB0LC_1LC1RB_1LD1LA_1RD0RC.
  destruct (pexp p) as [[|k]|] eqn:Epx; [reflexivity | | reflexivity].
  exfalso. exact (pexp_not_fill p j k E Epx).
Qed.

Lemma gso1_0RB0LC_1LC1RB_1LD1LA_1RD0RC : forall p j, cview p = (S j, None) -> podd p = true ->
  Cc p = cden [] [] j B01_0RB0LC_1LC1RB_1LD1LA_1RD0RC.
Proof.
  intros p j E Hb. unfold Cc_0RB0LC_1LC1RB_1LD1LA_1RD0RC. rewrite (vfill_0RB0LC_1LC1RB_1LD1LA_1RD0RC p j E).
  unfold frm_0RB0LC_1LC1RB_1LD1LA_1RD0RC. rewrite Hb.
  destruct (Alph_10_11_11.cview_none_Alph_10_11_11 p j E) as (H1 & _).
  unfold cden, B01_0RB0LC_1LC1RB_1LD1LA_1RD0RC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia. replace (0 * j + 0) with 0 by lia.
  rewrite H1. rshape_0RB0LC_1LC1RB_1LD1LA_1RD0RC.
Qed.

Lemma geo1_0RB0LC_1LC1RB_1LD1LA_1RD0RC : forall p j, cview p = (S j, None) -> podd p = true ->
  cden [] [] j B11_0RB0LC_1LC1RB_1LD1LA_1RD0RC = Cc (Pos.succ p).
Proof.
  intros p j E Hb. unfold Cc_0RB0LC_1LC1RB_1LD1LA_1RD0RC, virt_0RB0LC_1LC1RB_1LD1LA_1RD0RC, frm_0RB0LC_1LC1RB_1LD1LA_1RD0RC, frmv_0RB0LC_1LC1RB_1LD1LA_1RD0RC.
  rewrite (pexp_succ_fill p (S j) E).
  rewrite (podd_succ_fill p j E), Hb. cbn [negb].
  destruct (Alph_10_11_11.cview_none_Alph_10_11_11 p j E) as (_ & H2).
  unfold cden, B11_0RB0LC_1LC1RB_1LD1LA_1RD0RC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 1) with (S j) by lia. replace (0 * j + 0) with 0 by lia.
  rewrite H2. rshape_0RB0LC_1LC1RB_1LD1LA_1RD0RC.
Qed.

Lemma lapo1_0RB0LC_1LC1RB_1LD1LA_1RD0RC : forall p j, cview p = (S j, None) -> podd p = true ->
  exists n, 0 < n /\ csteps tm n (Cc p) = Some (Cc (Pos.succ p)).
Proof.
  intros p j E Hb. exists (4 * j + 7). split; [lia|].
  rewrite (gso1_0RB0LC_1LC1RB_1LD1LA_1RD0RC p j E Hb).
  rewrite (srun_sound tm true true cho1_0RB0LC_1LC1RB_1LD1LA_1RD0RC B01_0RB0LC_1LC1RB_1LD1LA_1RD0RC B11_0RB0LC_1LC1RB_1LD1LA_1RD0RC 4 7
             run_ovf1_0RB0LC_1LC1RB_1LD1LA_1RD0RC [] [] j ltac:(reflexivity) ltac:(reflexivity)).
  f_equal. exact (geo1_0RB0LC_1LC1RB_1LD1LA_1RD0RC p j E Hb).
Qed.

Lemma gso0_0RB0LC_1LC1RB_1LD1LA_1RD0RC : forall p j, cview p = (S j, None) -> podd p = false ->
  Cc p = cden [] [] j B00_0RB0LC_1LC1RB_1LD1LA_1RD0RC.
Proof.
  intros p j E Hb. unfold Cc_0RB0LC_1LC1RB_1LD1LA_1RD0RC. rewrite (vfill_0RB0LC_1LC1RB_1LD1LA_1RD0RC p j E).
  unfold frm_0RB0LC_1LC1RB_1LD1LA_1RD0RC. rewrite Hb.
  destruct (Alph_10_11_11.cview_none_Alph_10_11_11 p j E) as (H1 & _).
  unfold cden, B00_0RB0LC_1LC1RB_1LD1LA_1RD0RC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia. replace (0 * j + 0) with 0 by lia.
  rewrite H1. rshape_0RB0LC_1LC1RB_1LD1LA_1RD0RC.
Qed.

Lemma geo0_0RB0LC_1LC1RB_1LD1LA_1RD0RC : forall p j, cview p = (S j, None) -> podd p = false ->
  cden [] [] j B10_0RB0LC_1LC1RB_1LD1LA_1RD0RC = Cc (Pos.succ p).
Proof.
  intros p j E Hb. unfold Cc_0RB0LC_1LC1RB_1LD1LA_1RD0RC, virt_0RB0LC_1LC1RB_1LD1LA_1RD0RC, frm_0RB0LC_1LC1RB_1LD1LA_1RD0RC, frmv_0RB0LC_1LC1RB_1LD1LA_1RD0RC.
  rewrite (pexp_succ_fill p (S j) E).
  rewrite (podd_succ_fill p j E), Hb. cbn [negb].
  destruct (Alph_10_11_11.cview_none_Alph_10_11_11 p j E) as (_ & H2).
  unfold cden, B10_0RB0LC_1LC1RB_1LD1LA_1RD0RC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 1) with (S j) by lia. replace (0 * j + 0) with 0 by lia.
  rewrite H2. rshape_0RB0LC_1LC1RB_1LD1LA_1RD0RC.
Qed.

Lemma lapo0_0RB0LC_1LC1RB_1LD1LA_1RD0RC : forall p j, cview p = (S j, None) -> podd p = false ->
  exists n, 0 < n /\ csteps tm n (Cc p) = Some (Cc (Pos.succ p)).
Proof.
  intros p j E Hb. exists (4 * j + 9). split; [lia|].
  rewrite (gso0_0RB0LC_1LC1RB_1LD1LA_1RD0RC p j E Hb).
  rewrite (srun_sound tm true true cho0_0RB0LC_1LC1RB_1LD1LA_1RD0RC B00_0RB0LC_1LC1RB_1LD1LA_1RD0RC B10_0RB0LC_1LC1RB_1LD1LA_1RD0RC 4 9
             run_ovf0_0RB0LC_1LC1RB_1LD1LA_1RD0RC [] [] j ltac:(reflexivity) ltac:(reflexivity)).
  f_equal. exact (geo0_0RB0LC_1LC1RB_1LD1LA_1RD0RC p j E Hb).
Qed.

(** ** The register step, one arm per octave parity *)

Lemma gsv0_0RB0LC_1LC1RB_1LD1LA_1RD0RC : forall p k, virt p = true -> pexp p = Some (S k) ->
  podd p = false -> Cc p = cden [] [] k VS0_0RB0LC_1LC1RB_1LD1LA_1RD0RC.
Proof.
  intros p k Hv Hx Hb. unfold Cc_0RB0LC_1LC1RB_1LD1LA_1RD0RC, frmv_0RB0LC_1LC1RB_1LD1LA_1RD0RC. rewrite Hv, Hb.
  rewrite (pexp_some p (S k) Hx), epow_0RB0LC_1LC1RB_1LD1LA_1RD0RC.
  unfold cden, VS0_0RB0LC_1LC1RB_1LD1LA_1RD0RC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * k + 0) with k by lia. replace (0 * k + 0) with 0 by lia.
  rshape_0RB0LC_1LC1RB_1LD1LA_1RD0RC.
Qed.

Lemma gev0_0RB0LC_1LC1RB_1LD1LA_1RD0RC : forall p k, virt p = true -> pexp p = Some (S k) ->
  podd p = false -> lift (cden [] [] k VT0_0RB0LC_1LC1RB_1LD1LA_1RD0RC) = lift (Cc (Pos.succ p)).
Proof.
  intros p k Hv Hx Hb. f_equal.
  unfold Cc_0RB0LC_1LC1RB_1LD1LA_1RD0RC, frm_0RB0LC_1LC1RB_1LD1LA_1RD0RC. rewrite (hsuccv_0RB0LC_1LC1RB_1LD1LA_1RD0RC p k Hx).
  rewrite (podd_succ_pexp p k Hx), Hb.
  rewrite (pexp_some p (S k) Hx).
  cbn [Pos.succ pow2 Ap_Alph_10_11_11]. rewrite epow_0RB0LC_1LC1RB_1LD1LA_1RD0RC.
  unfold cden, VT0_0RB0LC_1LC1RB_1LD1LA_1RD0RC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * k + 0) with k by lia. replace (0 * k + 0) with 0 by lia.
  rshape_0RB0LC_1LC1RB_1LD1LA_1RD0RC.
Qed.

Lemma gsn0_0RB0LC_1LC1RB_1LD1LA_1RD0RC : forall v i q0, cview v = (i, Some q0) ->
  Cin0 v = cden (Ip q0 ++ [S1]) [] i AI00_0RB0LC_1LC1RB_1LD1LA_1RD0RC.
Proof.
  intros v i q0 E. destruct (ILCounter.cview_some_I v i q0 E) as (H1 & _).
  unfold Cin0_0RB0LC_1LC1RB_1LD1LA_1RD0RC, cden, AI00_0RB0LC_1LC1RB_1LD1LA_1RD0RC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia. replace (0 * i + 0) with 0 by lia.
  rewrite H1. rshape_0RB0LC_1LC1RB_1LD1LA_1RD0RC.
Qed.

Lemma gen0_0RB0LC_1LC1RB_1LD1LA_1RD0RC : forall v i q0, cview v = (i, Some q0) ->
  cden (Ip q0 ++ [S1]) [] i AI10_0RB0LC_1LC1RB_1LD1LA_1RD0RC = Cin0 (Pos.succ v).
Proof.
  intros v i q0 E. destruct (ILCounter.cview_some_I v i q0 E) as (_ & H2).
  unfold Cin0_0RB0LC_1LC1RB_1LD1LA_1RD0RC, cden, AI10_0RB0LC_1LC1RB_1LD1LA_1RD0RC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia. replace (0 * i + 0) with 0 by lia.
  rewrite H2. rshape_0RB0LC_1LC1RB_1LD1LA_1RD0RC.
Qed.

Lemma lapin0_0RB0LC_1LC1RB_1LD1LA_1RD0RC : forall v i q0, cview v = (i, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cin0 v) = Some c'
               /\ lift c' = lift (Cin0 (Pos.succ v)).
Proof.
  intros v i q0 E.
  exists (4 * i + 4), (Cin0 (Pos.succ v)).
  split; [lia|]. split; [| reflexivity].
  rewrite (gsn0_0RB0LC_1LC1RB_1LD1LA_1RD0RC v i q0 E).
  rewrite (srun_sound tm false true chn0_0RB0LC_1LC1RB_1LD1LA_1RD0RC AI00_0RB0LC_1LC1RB_1LD1LA_1RD0RC AI10_0RB0LC_1LC1RB_1LD1LA_1RD0RC 4 4
             run_inner0_0RB0LC_1LC1RB_1LD1LA_1RD0RC (Ip q0 ++ [S1]) [] i
             ltac:(discriminate) ltac:(reflexivity)).
  f_equal. exact (gen0_0RB0LC_1LC1RB_1LD1LA_1RD0RC v i q0 E).
Qed.

Lemma gbo0_0RB0LC_1LC1RB_1LD1LA_1RD0RC : forall k, lift (cden [] [] k CS0_0RB0LC_1LC1RB_1LD1LA_1RD0RC) = lift (Cin0 (pow2 k)).
Proof.
  intro k. f_equal.
  unfold Cin0_0RB0LC_1LC1RB_1LD1LA_1RD0RC, cden, CS0_0RB0LC_1LC1RB_1LD1LA_1RD0RC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * k + 0) with k by lia. replace (0 * k + 0) with 0 by lia.
  rewrite iepow0_0RB0LC_1LC1RB_1LD1LA_1RD0RC. rshape_0RB0LC_1LC1RB_1LD1LA_1RD0RC.
Qed.

Lemma gxi0_0RB0LC_1LC1RB_1LD1LA_1RD0RC : forall k, Cin0 (fill (pow2 k)) = cden [] [] k CF0_0RB0LC_1LC1RB_1LD1LA_1RD0RC.
Proof.
  intro k.
  destruct (ILCounter.cview_none_I (fill (pow2 k)) k (cview_fill_pow2 k)) as (H1 & _).
  unfold Cin0_0RB0LC_1LC1RB_1LD1LA_1RD0RC, cden, CF0_0RB0LC_1LC1RB_1LD1LA_1RD0RC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * k + 0) with k by lia. replace (0 * k + 0) with 0 by lia.
  rewrite H1. rshape_0RB0LC_1LC1RB_1LD1LA_1RD0RC.
Qed.

Lemma hbo0_0RB0LC_1LC1RB_1LD1LA_1RD0RC : forall p k, virt p = true -> pexp p = Some (S k) ->
  podd p = false ->
  exists n c, 0 < n /\ csteps tm n (Cc p) = Some c
              /\ lift c = lift (Cin0 (pow2 k)).
Proof.
  intros p k Hv Hx Hb.
  exists (0 * k + 6), (cden [] [] k CS0_0RB0LC_1LC1RB_1LD1LA_1RD0RC).
  split; [lia|]. split; [| exact (gbo0_0RB0LC_1LC1RB_1LD1LA_1RD0RC k)].
  rewrite (gsv0_0RB0LC_1LC1RB_1LD1LA_1RD0RC p k Hv Hx Hb).
  exact (srun_sound tm true true chb0_0RB0LC_1LC1RB_1LD1LA_1RD0RC VS0_0RB0LC_1LC1RB_1LD1LA_1RD0RC CS0_0RB0LC_1LC1RB_1LD1LA_1RD0RC 0 6
           run_boot0_0RB0LC_1LC1RB_1LD1LA_1RD0RC [] [] k ltac:(reflexivity) ltac:(reflexivity)).
Qed.

Lemma hxe0_0RB0LC_1LC1RB_1LD1LA_1RD0RC : forall p k, virt p = true -> pexp p = Some (S k) ->
  podd p = false ->
  exists n c', csteps tm n (Cin0 (fill (pow2 k))) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof.
  intros p k Hv Hx Hb.
  exists (4 * k + 13), (cden [] [] k VT0_0RB0LC_1LC1RB_1LD1LA_1RD0RC).
  split; [| exact (gev0_0RB0LC_1LC1RB_1LD1LA_1RD0RC p k Hv Hx Hb)].
  rewrite (gxi0_0RB0LC_1LC1RB_1LD1LA_1RD0RC k).
  exact (srun_sound tm true true che0_0RB0LC_1LC1RB_1LD1LA_1RD0RC CF0_0RB0LC_1LC1RB_1LD1LA_1RD0RC VT0_0RB0LC_1LC1RB_1LD1LA_1RD0RC 4 13
           run_exit0_0RB0LC_1LC1RB_1LD1LA_1RD0RC [] [] k ltac:(reflexivity) ltac:(reflexivity)).
Qed.

(** The register step, composed.  The [Theta(2^k)] middle is the [exists n]
    inside [NestedLapLift.inner_to_fill_lift]; no formula for it is written. *)
Lemma lapv0_0RB0LC_1LC1RB_1LD1LA_1RD0RC : forall p k, virt p = true -> pexp p = Some (S k) ->
  podd p = false ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof.
  intros p k Hv Hx Hb.
  destruct (nested_overflow_lift tm Cc Cin0 lapin0_0RB0LC_1LC1RB_1LD1LA_1RD0RC p (pow2 k)
              (hbo0_0RB0LC_1LC1RB_1LD1LA_1RD0RC p k Hv Hx Hb) (hxe0_0RB0LC_1LC1RB_1LD1LA_1RD0RC p k Hv Hx Hb))
    as (n & c' & Hr & Hl & Hn).
  exists n, c'. split; [exact Hn | split; [exact Hr | exact Hl]].
Qed.


Lemma lapv_0RB0LC_1LC1RB_1LD1LA_1RD0RC : forall p k, virt p = true -> pexp p = Some (S k) ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof.
  intros p k Hv Hx. destruct (podd p) eqn:Hb.
  - exfalso. unfold virt_0RB0LC_1LC1RB_1LD1LA_1RD0RC in Hv. rewrite Hx, Hb in Hv.
    discriminate Hv.
  - exact (lapv0_0RB0LC_1LC1RB_1LD1LA_1RD0RC p k Hv Hx Hb).
Qed.

(** ** SkipGlue's hypotheses *)

Lemma hint_0RB0LC_1LC1RB_1LD1LA_1RD0RC : forall p j q0, (8 <= p)%positive ->
  cview p = (j, Some q0) -> virt p = false ->
  exists n, 0 < n /\ csteps tm n (Cc p) = Some (Cc (Pos.succ p)).
Proof. intros p j q0 _ E Hv. exact (lapi_0RB0LC_1LC1RB_1LD1LA_1RD0RC p j q0 E Hv). Qed.

Lemma hsucc_0RB0LC_1LC1RB_1LD1LA_1RD0RC : forall p j q0, cview p = (j, Some q0) ->
  virt p = false -> virt (Pos.succ p) = false.
Proof. intros p j q0 E _. exact (hsucc0_0RB0LC_1LC1RB_1LD1LA_1RD0RC p j q0 E). Qed.

Lemma hvlap_0RB0LC_1LC1RB_1LD1LA_1RD0RC : forall p, (8 <= p)%positive -> virt p = true ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof.
  intros p _ Hv. destruct (vsome_0RB0LC_1LC1RB_1LD1LA_1RD0RC p Hv) as (k & Hx).
  exact (lapv_0RB0LC_1LC1RB_1LD1LA_1RD0RC p k Hv Hx).
Qed.

Lemma hvrun_0RB0LC_1LC1RB_1LD1LA_1RD0RC : forall p, (8 <= p)%positive -> virt p = true ->
  virt (Pos.succ p) = true -> virt (Pos.succ (Pos.succ p)) = false.
Proof.
  intros p _ V1 V2. exfalso.
  destruct (vsome_0RB0LC_1LC1RB_1LD1LA_1RD0RC p V1) as (k & Hx).
  rewrite (hsuccv_0RB0LC_1LC1RB_1LD1LA_1RD0RC p k Hx) in V2. discriminate V2.
Qed.

(** ** The lap *)

Lemma lap_0RB0LC_1LC1RB_1LD1LA_1RD0RC : forall p, (8 <= p)%positive -> exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intros p Hp. destruct (cview p) as [j oq] eqn:E; destruct oq as [q0|].
  - destruct (virt p) eqn:V.
    + destruct (vsome_0RB0LC_1LC1RB_1LD1LA_1RD0RC p V) as (k & Hx).
      destruct (lapv_0RB0LC_1LC1RB_1LD1LA_1RD0RC p k V Hx) as (n & c' & Hn & Hr & Hl).
      exists n, c'. split; [exact Hr | split; [exact Hl | exact Hn]].
    + destruct (lapi_0RB0LC_1LC1RB_1LD1LA_1RD0RC p j q0 E V) as (n & Hn & Hr).
      exists n, (Cc (Pos.succ p)).
      split; [exact Hr | split; [reflexivity | exact Hn]].
  - destruct (cview_pos p j E) as (j' & ->).
    destruct (podd p) eqn:Hb.
    + destruct (lapo1_0RB0LC_1LC1RB_1LD1LA_1RD0RC p j' E Hb) as (n & Hn & Hr).
      exists n, (Cc (Pos.succ p)).
      split; [exact Hr | split; [reflexivity | exact Hn]].
    + destruct (lapo0_0RB0LC_1LC1RB_1LD1LA_1RD0RC p j' E Hb) as (n & Hn & Hr).
      exists n, (Cc (Pos.succ p)).
      split; [exact Hr | split; [reflexivity | exact Hn]].
Qed.

(** ** Bootstrap *)

Lemma boot_0RB0LC_1LC1RB_1LD1LA_1RD0RC : exists t0, stepn tm t0 InitES = Some (lift (Cc 8)).
Proof.
  exists 90.
  assert (H : match csteps tm 90 c0 with
              | Some c => ceqb c (Cc 8) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 90 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** ** Visits

    [SkipGlue.vis_via_skip] asks for a witness at EVERY overflow anchor at or
    above [p0], and the overflow anchors alternate frames -- so the witness
    is a prefix of whichever of the two overflow chains that parity uses. *)

Lemma viso1_0RB0LC_1LC1RB_1LD1LA_1RD0RC : forall (l : list lstep) (q : St),
  srun_st tm true true l B01_0RB0LC_1LC1RB_1LD1LA_1RD0RC = Some q ->
  forall p j, cview p = (S j, None) -> podd p = true ->
  exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros l q Hst p j E Hb.
  apply (vis_of_run tm Cc true true l B01_0RB0LC_1LC1RB_1LD1LA_1RD0RC p j [] []);
    [exact Hst | reflexivity | reflexivity | exact (gso1_0RB0LC_1LC1RB_1LD1LA_1RD0RC p j E Hb)].
Qed.

Lemma viso0_0RB0LC_1LC1RB_1LD1LA_1RD0RC : forall (l : list lstep) (q : St),
  srun_st tm true true l B00_0RB0LC_1LC1RB_1LD1LA_1RD0RC = Some q ->
  forall p j, cview p = (S j, None) -> podd p = false ->
  exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros l q Hst p j E Hb.
  apply (vis_of_run tm Cc true true l B00_0RB0LC_1LC1RB_1LD1LA_1RD0RC p j [] []);
    [exact Hst | reflexivity | reflexivity | exact (gso0_0RB0LC_1LC1RB_1LD1LA_1RD0RC p j E Hb)].
Qed.

Lemma vis_0RB0LC_1LC1RB_1LD1LA_1RD0RC : forall p q, (8 <= p)%positive ->
  exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros p q Hp.
  apply (vis_via_skip tm Cc virt 8 hint_0RB0LC_1LC1RB_1LD1LA_1RD0RC hsucc_0RB0LC_1LC1RB_1LD1LA_1RD0RC hvlap_0RB0LC_1LC1RB_1LD1LA_1RD0RC
           hvrun_0RB0LC_1LC1RB_1LD1LA_1RD0RC q); [| exact Hp].
  intros p1 j1 Hp1 E1. destruct (podd p1) eqn:Hb1.
  - destruct q.
    + exact (viso1_0RB0LC_1LC1RB_1LD1LA_1RD0RC [] StA ltac:(vm_compute; reflexivity) p1 j1 E1 Hb1).
    + exact (viso1_0RB0LC_1LC1RB_1LD1LA_1RD0RC [SRotL 1; SWin 1] StB ltac:(vm_compute; reflexivity) p1 j1 E1 Hb1).
    + exact (viso1_0RB0LC_1LC1RB_1LD1LA_1RD0RC [SRotL 1; SWin 1; SCycL 2 0; SWin 1; SWinL 2] StC ltac:(vm_compute; reflexivity) p1 j1 E1 Hb1).
    + exact (viso1_0RB0LC_1LC1RB_1LD1LA_1RD0RC [SRotL 1; SWin 1; SCycL 2 0; SWin 1; SWinL 3; SCycR 2; SWin 1; SWinR 1] StD ltac:(vm_compute; reflexivity) p1 j1 E1 Hb1).
  - destruct q.
    + exact (viso0_0RB0LC_1LC1RB_1LD1LA_1RD0RC [] StA ltac:(vm_compute; reflexivity) p1 j1 E1 Hb1).
    + exact (viso0_0RB0LC_1LC1RB_1LD1LA_1RD0RC [SRotL 1; SWin 1] StB ltac:(vm_compute; reflexivity) p1 j1 E1 Hb1).
    + exact (viso0_0RB0LC_1LC1RB_1LD1LA_1RD0RC [SRotL 1; SWin 1; SCycL 2 0; SWin 1; SWinL 2] StC ltac:(vm_compute; reflexivity) p1 j1 E1 Hb1).
    + exact (viso0_0RB0LC_1LC1RB_1LD1LA_1RD0RC [SRotL 1; SWin 1; SCycL 2 0; SWin 1; SWinL 3; SCycR 2; SWin 2] StD ltac:(vm_compute; reflexivity) p1 j1 E1 Hb1).
Qed.

Theorem nqhm_0RB0LC_1LC1RB_1LD1LA_1RD0RC : NeverQuasiHaltsSt tm.
Proof. apply (glue_neverqh tm Cc 8). - exact boot_0RB0LC_1LC1RB_1LD1LA_1RD0RC. - intros p Hp. apply (lap_0RB0LC_1LC1RB_1LD1LA_1RD0RC p Hp). - intros p q Hp. apply (vis_0RB0LC_1LC1RB_1LD1LA_1RD0RC p q Hp). Qed.

Theorem nqh_0RB0LC_1LC1RB_1LD1LA_1RD0RC : NeverQuasiHaltsSt tm_0RB0LC_1LC1RB_1LD1LA_1RD0RC.
Proof. apply (mirror_never_qh tm_0RB0LC_1LC1RB_1LD1LA_1RD0RC). rewrite mirror_ok_0RB0LC_1LC1RB_1LD1LA_1RD0RC. exact nqhm_0RB0LC_1LC1RB_1LD1LA_1RD0RC. Qed.

Theorem nonhalt_0RB0LC_1LC1RB_1LD1LA_1RD0RC : NonHalt tm_0RB0LC_1LC1RB_1LD1LA_1RD0RC.
Proof. apply never_qh_nonhalt, nqh_0RB0LC_1LC1RB_1LD1LA_1RD0RC. Qed.
