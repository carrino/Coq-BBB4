(** * REG_1RB1LA_1RC1RD_1LC0LB_0LA0RB: machine 1RB1LA_1RC1RD_1LC0LB_0LA0RB, boarded by CERTIFICATE (REGISTER route).

    Auto-emitted by tools/counters/regcert.py (UNTRUSTED emitter; the Coq
    kernel re-runs the checker on every line below).  A binary counter under
    the Ap_Alph_10_11_11 digit alphabet (Alph_10_11_11.v) whose anchor FRAME depends on the
    OCTAVE: the machine keeps a REGISTER mark past the head and moves it once
    per octave, so the family is (register state x counter) and the anchor is
    PIECEWISE (WAVE28 section 3c, the `period-2+virt` class).

      Cc p = if virt p then (StC, E p ++ tail, S0, frmv p)
             else (StD, E p ++ tail, S0, frm p)

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
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape LapGlue MonoCounter JpCounter
                                  Alph_10_11_11 ILCounter LapCertGlue LapCertGlueLift
                                  IXPGadgets NestedLap NestedLapLift
                                  SkipGlue RegGlue.
From BBB4.Census Require Import TNF_QH.
From BBB4.Checkers Require Import LapDecider.
Import ListNotations.

Definition mk_1RB1LA_1RC1RD_1LC0LB_0LA0RB (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_1RB1LA_1RC1RD_1LC0LB_0LA0RB.

(** 1RB1LA_1RC1RD_1LC0LB_0LA0RB *)
Definition tm_1RB1LA_1RC1RD_1LC0LB_0LA0RB : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S1 DL StA
  | StB, S0 => mk S1 DR StC | StB, S1 => mk S1 DR StD
  | StC, S0 => mk S1 DL StC | StC, S1 => mk S0 DL StB
  | StD, S0 => mk S0 DL StA | StD, S1 => mk S0 DR StB end.
Local Notation tm := tm_1RB1LA_1RC1RD_1LC0LB_0LA0RB.

(** The virtual anchors.  [pexp p = Some 0] (that is, [p = 1]) is excluded by
    the [S _] pattern, so [Cc 1] is an ordinary frame anchor and the overflow
    glue holds at it too. *)
Definition virt_1RB1LA_1RC1RD_1LC0LB_0LA0RB (p : positive) : bool :=
  match pexp p with Some (S _) => negb (podd p) | _ => false end.
Local Notation virt := virt_1RB1LA_1RC1RD_1LC0LB_0LA0RB.

Definition frm_1RB1LA_1RC1RD_1LC0LB_0LA0RB (p : positive) : list Sym :=
  if podd p then [] else [S1].
Local Notation frm := frm_1RB1LA_1RC1RD_1LC0LB_0LA0RB.

Definition frmv_1RB1LA_1RC1RD_1LC0LB_0LA0RB (p : positive) : list Sym :=
  if podd p then [] else [].
Local Notation frmv := frmv_1RB1LA_1RC1RD_1LC0LB_0LA0RB.

Definition Cc_1RB1LA_1RC1RD_1LC0LB_0LA0RB (p : positive) : cconf :=
  if virt_1RB1LA_1RC1RD_1LC0LB_0LA0RB p then (StC, (Ap_Alph_10_11_11 p ++ [], S0, frmv_1RB1LA_1RC1RD_1LC0LB_0LA0RB p))
  else (StD, (Ap_Alph_10_11_11 p ++ [], S0, frm_1RB1LA_1RC1RD_1LC0LB_0LA0RB p)).
Local Notation Cc := Cc_1RB1LA_1RC1RD_1LC0LB_0LA0RB.

(** ** The INNER anchor family of the parity-false register step -- the
    counter that step re-runs *)
Definition Cin0_1RB1LA_1RC1RD_1LC0LB_0LA0RB (v : positive) : cconf :=
  (StD, (Ip v ++ [S1], S0, [S1;S1])).
Local Notation Cin0 := Cin0_1RB1LA_1RC1RD_1LC0LB_0LA0RB.


Ltac rshape_1RB1LA_1RC1RD_1LC0LB_0LA0RB :=
  cbn [rep app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r;
  reflexivity.

(** ** The certificate *)

Definition A01_1RB1LA_1RC1RD_1LC0LB_0LA0RB : sconf := mkC StD (mkS [] [S1;S1] 1 0 [S1;S0]) S0 (mkS [] [] 0 0 []).
Definition A11_1RB1LA_1RC1RD_1LC0LB_0LA0RB : sconf := mkC StD (mkS [] [S1;S0] 1 0 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition chi1_1RB1LA_1RC1RD_1LC0LB_0LA0RB : list lstep := [SRotL 1; SWin 1; SCycL 2 0; SWin 2; SCycR 2; SWin 1; SUnrotL 1].

Lemma run_int1_1RB1LA_1RC1RD_1LC0LB_0LA0RB : srun tm false true chi1_1RB1LA_1RC1RD_1LC0LB_0LA0RB A01_1RB1LA_1RC1RD_1LC0LB_0LA0RB = Some (A11_1RB1LA_1RC1RD_1LC0LB_0LA0RB, 4, 4).
Proof. vm_compute. reflexivity. Qed.

Definition A00_1RB1LA_1RC1RD_1LC0LB_0LA0RB : sconf := mkC StD (mkS [] [S1;S1] 1 0 [S1;S0]) S0 (mkS [S1] [] 0 0 []).
Definition A10_1RB1LA_1RC1RD_1LC0LB_0LA0RB : sconf := mkC StD (mkS [] [S1;S0] 1 0 [S1;S1]) S0 (mkS [S1] [] 0 0 []).
Definition chi0_1RB1LA_1RC1RD_1LC0LB_0LA0RB : list lstep := [SRotL 1; SWin 1; SCycL 2 0; SWin 2; SCycR 2; SWin 1; SUnrotL 1].

Lemma run_int0_1RB1LA_1RC1RD_1LC0LB_0LA0RB : srun tm false true chi0_1RB1LA_1RC1RD_1LC0LB_0LA0RB A00_1RB1LA_1RC1RD_1LC0LB_0LA0RB = Some (A10_1RB1LA_1RC1RD_1LC0LB_0LA0RB, 4, 4).
Proof. vm_compute. reflexivity. Qed.

Definition B01_1RB1LA_1RC1RD_1LC0LB_0LA0RB : sconf := mkC StD (mkS [] [S1;S1] 1 0 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition B11_1RB1LA_1RC1RD_1LC0LB_0LA0RB : sconf := mkC StC (mkS [] [S1;S0] 1 1 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition cho1_1RB1LA_1RC1RD_1LC0LB_0LA0RB : list lstep := [SRotL 1; SWin 1; SCycL 2 0; SWin 1; SWinL 3; SCycR 2; SWin 1; SWinR 1; SFoldL 1].

Lemma run_ovf1_1RB1LA_1RC1RD_1LC0LB_0LA0RB : srun tm true true cho1_1RB1LA_1RC1RD_1LC0LB_0LA0RB B01_1RB1LA_1RC1RD_1LC0LB_0LA0RB = Some (B11_1RB1LA_1RC1RD_1LC0LB_0LA0RB, 4, 7).
Proof. vm_compute. reflexivity. Qed.

Definition B00_1RB1LA_1RC1RD_1LC0LB_0LA0RB : sconf := mkC StD (mkS [] [S1;S1] 1 0 [S1;S1]) S0 (mkS [S1] [] 0 0 []).
Definition B10_1RB1LA_1RC1RD_1LC0LB_0LA0RB : sconf := mkC StD (mkS [] [S1;S0] 1 1 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition cho0_1RB1LA_1RC1RD_1LC0LB_0LA0RB : list lstep := [SRotL 1; SWin 1; SCycL 2 0; SWin 1; SWinL 3; SCycR 2; SWin 4; SFoldL 1].

Lemma run_ovf0_1RB1LA_1RC1RD_1LC0LB_0LA0RB : srun tm true true cho0_1RB1LA_1RC1RD_1LC0LB_0LA0RB B00_1RB1LA_1RC1RD_1LC0LB_0LA0RB = Some (B10_1RB1LA_1RC1RD_1LC0LB_0LA0RB, 4, 9).
Proof. vm_compute. reflexivity. Qed.

(** *** the register step at octave parity false: boot (from the PEELED
    virtual anchor -- the first move is onto the counter's own top block),
    the inner counter's laps, exit *)
Definition VS0_1RB1LA_1RC1RD_1LC0LB_0LA0RB : sconf := mkC StC (mkS [S1;S0] [S1;S0] 1 0 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition CS0_1RB1LA_1RC1RD_1LC0LB_0LA0RB : sconf := mkC StD (mkS [] [S1;S0] 1 0 [S1;S1]) S0 (mkS [S1;S1] [] 0 0 []).
Definition chb0_1RB1LA_1RC1RD_1LC0LB_0LA0RB : list lstep := [SWin 4; SRotL 1; SWin 2; SUnrotL 1].

Lemma run_boot0_1RB1LA_1RC1RD_1LC0LB_0LA0RB : srun tm true true chb0_1RB1LA_1RC1RD_1LC0LB_0LA0RB VS0_1RB1LA_1RC1RD_1LC0LB_0LA0RB = Some (CS0_1RB1LA_1RC1RD_1LC0LB_0LA0RB, 0, 6).
Proof. vm_compute. reflexivity. Qed.

Definition AI00_1RB1LA_1RC1RD_1LC0LB_0LA0RB : sconf := mkC StD (mkS [] [S1;S1] 1 0 [S1;S0]) S0 (mkS [S1;S1] [] 0 0 []).
Definition AI10_1RB1LA_1RC1RD_1LC0LB_0LA0RB : sconf := mkC StD (mkS [] [S1;S0] 1 0 [S1;S1]) S0 (mkS [S1;S1] [] 0 0 []).
Definition chn0_1RB1LA_1RC1RD_1LC0LB_0LA0RB : list lstep := [SRotL 1; SWin 1; SCycL 2 0; SWin 2; SCycR 2; SWin 1; SUnrotL 1].

Lemma run_inner0_1RB1LA_1RC1RD_1LC0LB_0LA0RB : srun tm false true chn0_1RB1LA_1RC1RD_1LC0LB_0LA0RB AI00_1RB1LA_1RC1RD_1LC0LB_0LA0RB = Some (AI10_1RB1LA_1RC1RD_1LC0LB_0LA0RB, 4, 4).
Proof. vm_compute. reflexivity. Qed.

Definition CF0_1RB1LA_1RC1RD_1LC0LB_0LA0RB : sconf := mkC StD (mkS [] [S1;S1] 1 0 [S1;S1]) S0 (mkS [S1;S1] [] 0 0 []).
Definition VT0_1RB1LA_1RC1RD_1LC0LB_0LA0RB : sconf := mkC StD (mkS [S1;S1] [S1;S0] 1 0 [S1;S1]) S0 (mkS [S1] [] 0 0 []).
Definition che0_1RB1LA_1RC1RD_1LC0LB_0LA0RB : list lstep := [SRotL 1; SWin 1; SCycL 2 0; SWin 1; SWinL 3; SCycR 2; SWin 8].

Lemma run_exit0_1RB1LA_1RC1RD_1LC0LB_0LA0RB : srun tm true true che0_1RB1LA_1RC1RD_1LC0LB_0LA0RB CF0_1RB1LA_1RC1RD_1LC0LB_0LA0RB = Some (VT0_1RB1LA_1RC1RD_1LC0LB_0LA0RB, 4, 13).
Proof. vm_compute. reflexivity. Qed.


(** ** Anchor glue -- the only per-machine mathematics *)

Lemma epow_1RB1LA_1RC1RD_1LC0LB_0LA0RB : forall n, Ap_Alph_10_11_11 (pow2 n) = rep [S1;S0] n ++ [S1;S1].
Proof. induction n; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.

Lemma iepow0_1RB1LA_1RC1RD_1LC0LB_0LA0RB : forall n, Ip (pow2 n) = rep [S1;S0] n ++ [S1].
Proof. induction n; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.


Lemma hsucc0_1RB1LA_1RC1RD_1LC0LB_0LA0RB : forall p j q0, cview p = (j, Some q0) ->
  virt (Pos.succ p) = false.
Proof.
  intros p j q0 E. unfold virt_1RB1LA_1RC1RD_1LC0LB_0LA0RB.
  rewrite (pexp_succ_int p j q0 E). reflexivity.
Qed.

Lemma hsuccv_1RB1LA_1RC1RD_1LC0LB_0LA0RB : forall p k, pexp p = Some (S k) -> virt (Pos.succ p) = false.
Proof.
  intros p k Hx. unfold virt_1RB1LA_1RC1RD_1LC0LB_0LA0RB.
  rewrite (pexp_succ_virt p k Hx). reflexivity.
Qed.

Lemma vsome_1RB1LA_1RC1RD_1LC0LB_0LA0RB : forall p, virt p = true -> exists k, pexp p = Some (S k).
Proof.
  intros p Hv. unfold virt_1RB1LA_1RC1RD_1LC0LB_0LA0RB in Hv.
  destruct (pexp p) as [[|m]|]; try discriminate Hv.
  exists m. reflexivity.
Qed.

(** *** the interior branch at octave parity true.  The frame is CONCRETE in
    the chain's own right side: on some machines the head steps onto it. *)
Lemma gsi1_1RB1LA_1RC1RD_1LC0LB_0LA0RB : forall p j q0, cview p = (j, Some q0) -> virt p = false ->
  podd p = true -> Cc p = cden (Ap_Alph_10_11_11 q0 ++ []) [] j A01_1RB1LA_1RC1RD_1LC0LB_0LA0RB.
Proof.
  intros p j q0 E Hv Hb. unfold Cc_1RB1LA_1RC1RD_1LC0LB_0LA0RB. rewrite Hv.
  unfold frm_1RB1LA_1RC1RD_1LC0LB_0LA0RB. rewrite Hb.
  destruct (Alph_10_11_11.cview_some_Alph_10_11_11 p j q0 E) as (H1 & _).
  unfold cden, A01_1RB1LA_1RC1RD_1LC0LB_0LA0RB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia. replace (0 * j + 0) with 0 by lia.
  rewrite H1. rshape_1RB1LA_1RC1RD_1LC0LB_0LA0RB.
Qed.

Lemma gei1_1RB1LA_1RC1RD_1LC0LB_0LA0RB : forall p j q0, cview p = (j, Some q0) -> virt p = false ->
  podd p = true ->
  cden (Ap_Alph_10_11_11 q0 ++ []) [] j A11_1RB1LA_1RC1RD_1LC0LB_0LA0RB = Cc (Pos.succ p).
Proof.
  intros p j q0 E Hv Hb. unfold Cc_1RB1LA_1RC1RD_1LC0LB_0LA0RB.
  rewrite (hsucc0_1RB1LA_1RC1RD_1LC0LB_0LA0RB p j q0 E).
  unfold frm_1RB1LA_1RC1RD_1LC0LB_0LA0RB. rewrite (podd_succ_int p j q0 E), Hb.
  destruct (Alph_10_11_11.cview_some_Alph_10_11_11 p j q0 E) as (_ & H2).
  unfold cden, A11_1RB1LA_1RC1RD_1LC0LB_0LA0RB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia. replace (0 * j + 0) with 0 by lia.
  rewrite H2. rshape_1RB1LA_1RC1RD_1LC0LB_0LA0RB.
Qed.

Lemma lapi1_1RB1LA_1RC1RD_1LC0LB_0LA0RB : forall p j q0, cview p = (j, Some q0) -> virt p = false ->
  podd p = true ->
  exists n, 0 < n /\ csteps tm n (Cc p) = Some (Cc (Pos.succ p)).
Proof.
  intros p j q0 E Hv Hb. exists (4 * j + 4). split; [lia|].
  rewrite (gsi1_1RB1LA_1RC1RD_1LC0LB_0LA0RB p j q0 E Hv Hb).
  rewrite (srun_sound tm false true chi1_1RB1LA_1RC1RD_1LC0LB_0LA0RB A01_1RB1LA_1RC1RD_1LC0LB_0LA0RB A11_1RB1LA_1RC1RD_1LC0LB_0LA0RB 4 4
             run_int1_1RB1LA_1RC1RD_1LC0LB_0LA0RB (Ap_Alph_10_11_11 q0 ++ []) [] j
             ltac:(discriminate) ltac:(reflexivity)).
  f_equal. exact (gei1_1RB1LA_1RC1RD_1LC0LB_0LA0RB p j q0 E Hv Hb).
Qed.

(** *** the interior branch at octave parity false.  The frame is CONCRETE in
    the chain's own right side: on some machines the head steps onto it. *)
Lemma gsi0_1RB1LA_1RC1RD_1LC0LB_0LA0RB : forall p j q0, cview p = (j, Some q0) -> virt p = false ->
  podd p = false -> Cc p = cden (Ap_Alph_10_11_11 q0 ++ []) [] j A00_1RB1LA_1RC1RD_1LC0LB_0LA0RB.
Proof.
  intros p j q0 E Hv Hb. unfold Cc_1RB1LA_1RC1RD_1LC0LB_0LA0RB. rewrite Hv.
  unfold frm_1RB1LA_1RC1RD_1LC0LB_0LA0RB. rewrite Hb.
  destruct (Alph_10_11_11.cview_some_Alph_10_11_11 p j q0 E) as (H1 & _).
  unfold cden, A00_1RB1LA_1RC1RD_1LC0LB_0LA0RB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia. replace (0 * j + 0) with 0 by lia.
  rewrite H1. rshape_1RB1LA_1RC1RD_1LC0LB_0LA0RB.
Qed.

Lemma gei0_1RB1LA_1RC1RD_1LC0LB_0LA0RB : forall p j q0, cview p = (j, Some q0) -> virt p = false ->
  podd p = false ->
  cden (Ap_Alph_10_11_11 q0 ++ []) [] j A10_1RB1LA_1RC1RD_1LC0LB_0LA0RB = Cc (Pos.succ p).
Proof.
  intros p j q0 E Hv Hb. unfold Cc_1RB1LA_1RC1RD_1LC0LB_0LA0RB.
  rewrite (hsucc0_1RB1LA_1RC1RD_1LC0LB_0LA0RB p j q0 E).
  unfold frm_1RB1LA_1RC1RD_1LC0LB_0LA0RB. rewrite (podd_succ_int p j q0 E), Hb.
  destruct (Alph_10_11_11.cview_some_Alph_10_11_11 p j q0 E) as (_ & H2).
  unfold cden, A10_1RB1LA_1RC1RD_1LC0LB_0LA0RB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia. replace (0 * j + 0) with 0 by lia.
  rewrite H2. rshape_1RB1LA_1RC1RD_1LC0LB_0LA0RB.
Qed.

Lemma lapi0_1RB1LA_1RC1RD_1LC0LB_0LA0RB : forall p j q0, cview p = (j, Some q0) -> virt p = false ->
  podd p = false ->
  exists n, 0 < n /\ csteps tm n (Cc p) = Some (Cc (Pos.succ p)).
Proof.
  intros p j q0 E Hv Hb. exists (4 * j + 4). split; [lia|].
  rewrite (gsi0_1RB1LA_1RC1RD_1LC0LB_0LA0RB p j q0 E Hv Hb).
  rewrite (srun_sound tm false true chi0_1RB1LA_1RC1RD_1LC0LB_0LA0RB A00_1RB1LA_1RC1RD_1LC0LB_0LA0RB A10_1RB1LA_1RC1RD_1LC0LB_0LA0RB 4 4
             run_int0_1RB1LA_1RC1RD_1LC0LB_0LA0RB (Ap_Alph_10_11_11 q0 ++ []) [] j
             ltac:(discriminate) ltac:(reflexivity)).
  f_equal. exact (gei0_1RB1LA_1RC1RD_1LC0LB_0LA0RB p j q0 E Hv Hb).
Qed.

Lemma lapi_1RB1LA_1RC1RD_1LC0LB_0LA0RB : forall p j q0, cview p = (j, Some q0) -> virt p = false ->
  exists n, 0 < n /\ csteps tm n (Cc p) = Some (Cc (Pos.succ p)).
Proof.
  intros p j q0 E Hv. destruct (podd p) eqn:Hb.
  - exact (lapi1_1RB1LA_1RC1RD_1LC0LB_0LA0RB p j q0 E Hv Hb).
  - exact (lapi0_1RB1LA_1RC1RD_1LC0LB_0LA0RB p j q0 E Hv Hb).
Qed.


(** *** the overflow branch.  A fill anchor is never virtual: above [1] it is
    not a power of two at all, and [1] fails the [S _] pattern. *)
Lemma vfill_1RB1LA_1RC1RD_1LC0LB_0LA0RB : forall p j, cview p = (S j, None) -> virt p = false.
Proof.
  intros p j E. unfold virt_1RB1LA_1RC1RD_1LC0LB_0LA0RB.
  destruct (pexp p) as [[|k]|] eqn:Epx; [reflexivity | | reflexivity].
  exfalso. exact (pexp_not_fill p j k E Epx).
Qed.

Lemma gso1_1RB1LA_1RC1RD_1LC0LB_0LA0RB : forall p j, cview p = (S j, None) -> podd p = true ->
  Cc p = cden [] [] j B01_1RB1LA_1RC1RD_1LC0LB_0LA0RB.
Proof.
  intros p j E Hb. unfold Cc_1RB1LA_1RC1RD_1LC0LB_0LA0RB. rewrite (vfill_1RB1LA_1RC1RD_1LC0LB_0LA0RB p j E).
  unfold frm_1RB1LA_1RC1RD_1LC0LB_0LA0RB. rewrite Hb.
  destruct (Alph_10_11_11.cview_none_Alph_10_11_11 p j E) as (H1 & _).
  unfold cden, B01_1RB1LA_1RC1RD_1LC0LB_0LA0RB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia. replace (0 * j + 0) with 0 by lia.
  rewrite H1. rshape_1RB1LA_1RC1RD_1LC0LB_0LA0RB.
Qed.

Lemma geo1_1RB1LA_1RC1RD_1LC0LB_0LA0RB : forall p j, cview p = (S j, None) -> podd p = true ->
  cden [] [] j B11_1RB1LA_1RC1RD_1LC0LB_0LA0RB = Cc (Pos.succ p).
Proof.
  intros p j E Hb. unfold Cc_1RB1LA_1RC1RD_1LC0LB_0LA0RB, virt_1RB1LA_1RC1RD_1LC0LB_0LA0RB, frm_1RB1LA_1RC1RD_1LC0LB_0LA0RB, frmv_1RB1LA_1RC1RD_1LC0LB_0LA0RB.
  rewrite (pexp_succ_fill p (S j) E).
  rewrite (podd_succ_fill p j E), Hb. cbn [negb].
  destruct (Alph_10_11_11.cview_none_Alph_10_11_11 p j E) as (_ & H2).
  unfold cden, B11_1RB1LA_1RC1RD_1LC0LB_0LA0RB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 1) with (S j) by lia. replace (0 * j + 0) with 0 by lia.
  rewrite H2. rshape_1RB1LA_1RC1RD_1LC0LB_0LA0RB.
Qed.

Lemma lapo1_1RB1LA_1RC1RD_1LC0LB_0LA0RB : forall p j, cview p = (S j, None) -> podd p = true ->
  exists n, 0 < n /\ csteps tm n (Cc p) = Some (Cc (Pos.succ p)).
Proof.
  intros p j E Hb. exists (4 * j + 7). split; [lia|].
  rewrite (gso1_1RB1LA_1RC1RD_1LC0LB_0LA0RB p j E Hb).
  rewrite (srun_sound tm true true cho1_1RB1LA_1RC1RD_1LC0LB_0LA0RB B01_1RB1LA_1RC1RD_1LC0LB_0LA0RB B11_1RB1LA_1RC1RD_1LC0LB_0LA0RB 4 7
             run_ovf1_1RB1LA_1RC1RD_1LC0LB_0LA0RB [] [] j ltac:(reflexivity) ltac:(reflexivity)).
  f_equal. exact (geo1_1RB1LA_1RC1RD_1LC0LB_0LA0RB p j E Hb).
Qed.

Lemma gso0_1RB1LA_1RC1RD_1LC0LB_0LA0RB : forall p j, cview p = (S j, None) -> podd p = false ->
  Cc p = cden [] [] j B00_1RB1LA_1RC1RD_1LC0LB_0LA0RB.
Proof.
  intros p j E Hb. unfold Cc_1RB1LA_1RC1RD_1LC0LB_0LA0RB. rewrite (vfill_1RB1LA_1RC1RD_1LC0LB_0LA0RB p j E).
  unfold frm_1RB1LA_1RC1RD_1LC0LB_0LA0RB. rewrite Hb.
  destruct (Alph_10_11_11.cview_none_Alph_10_11_11 p j E) as (H1 & _).
  unfold cden, B00_1RB1LA_1RC1RD_1LC0LB_0LA0RB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia. replace (0 * j + 0) with 0 by lia.
  rewrite H1. rshape_1RB1LA_1RC1RD_1LC0LB_0LA0RB.
Qed.

Lemma geo0_1RB1LA_1RC1RD_1LC0LB_0LA0RB : forall p j, cview p = (S j, None) -> podd p = false ->
  cden [] [] j B10_1RB1LA_1RC1RD_1LC0LB_0LA0RB = Cc (Pos.succ p).
Proof.
  intros p j E Hb. unfold Cc_1RB1LA_1RC1RD_1LC0LB_0LA0RB, virt_1RB1LA_1RC1RD_1LC0LB_0LA0RB, frm_1RB1LA_1RC1RD_1LC0LB_0LA0RB, frmv_1RB1LA_1RC1RD_1LC0LB_0LA0RB.
  rewrite (pexp_succ_fill p (S j) E).
  rewrite (podd_succ_fill p j E), Hb. cbn [negb].
  destruct (Alph_10_11_11.cview_none_Alph_10_11_11 p j E) as (_ & H2).
  unfold cden, B10_1RB1LA_1RC1RD_1LC0LB_0LA0RB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 1) with (S j) by lia. replace (0 * j + 0) with 0 by lia.
  rewrite H2. rshape_1RB1LA_1RC1RD_1LC0LB_0LA0RB.
Qed.

Lemma lapo0_1RB1LA_1RC1RD_1LC0LB_0LA0RB : forall p j, cview p = (S j, None) -> podd p = false ->
  exists n, 0 < n /\ csteps tm n (Cc p) = Some (Cc (Pos.succ p)).
Proof.
  intros p j E Hb. exists (4 * j + 9). split; [lia|].
  rewrite (gso0_1RB1LA_1RC1RD_1LC0LB_0LA0RB p j E Hb).
  rewrite (srun_sound tm true true cho0_1RB1LA_1RC1RD_1LC0LB_0LA0RB B00_1RB1LA_1RC1RD_1LC0LB_0LA0RB B10_1RB1LA_1RC1RD_1LC0LB_0LA0RB 4 9
             run_ovf0_1RB1LA_1RC1RD_1LC0LB_0LA0RB [] [] j ltac:(reflexivity) ltac:(reflexivity)).
  f_equal. exact (geo0_1RB1LA_1RC1RD_1LC0LB_0LA0RB p j E Hb).
Qed.

(** ** The register step, one arm per octave parity *)

Lemma gsv0_1RB1LA_1RC1RD_1LC0LB_0LA0RB : forall p k, virt p = true -> pexp p = Some (S k) ->
  podd p = false -> Cc p = cden [] [] k VS0_1RB1LA_1RC1RD_1LC0LB_0LA0RB.
Proof.
  intros p k Hv Hx Hb. unfold Cc_1RB1LA_1RC1RD_1LC0LB_0LA0RB, frmv_1RB1LA_1RC1RD_1LC0LB_0LA0RB. rewrite Hv, Hb.
  rewrite (pexp_some p (S k) Hx), epow_1RB1LA_1RC1RD_1LC0LB_0LA0RB.
  unfold cden, VS0_1RB1LA_1RC1RD_1LC0LB_0LA0RB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * k + 0) with k by lia. replace (0 * k + 0) with 0 by lia.
  rshape_1RB1LA_1RC1RD_1LC0LB_0LA0RB.
Qed.

Lemma gev0_1RB1LA_1RC1RD_1LC0LB_0LA0RB : forall p k, virt p = true -> pexp p = Some (S k) ->
  podd p = false -> lift (cden [] [] k VT0_1RB1LA_1RC1RD_1LC0LB_0LA0RB) = lift (Cc (Pos.succ p)).
Proof.
  intros p k Hv Hx Hb. f_equal.
  unfold Cc_1RB1LA_1RC1RD_1LC0LB_0LA0RB, frm_1RB1LA_1RC1RD_1LC0LB_0LA0RB. rewrite (hsuccv_1RB1LA_1RC1RD_1LC0LB_0LA0RB p k Hx).
  rewrite (podd_succ_pexp p k Hx), Hb.
  rewrite (pexp_some p (S k) Hx).
  cbn [Pos.succ pow2 Ap_Alph_10_11_11]. rewrite epow_1RB1LA_1RC1RD_1LC0LB_0LA0RB.
  unfold cden, VT0_1RB1LA_1RC1RD_1LC0LB_0LA0RB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * k + 0) with k by lia. replace (0 * k + 0) with 0 by lia.
  rshape_1RB1LA_1RC1RD_1LC0LB_0LA0RB.
Qed.

Lemma gsn0_1RB1LA_1RC1RD_1LC0LB_0LA0RB : forall v i q0, cview v = (i, Some q0) ->
  Cin0 v = cden (Ip q0 ++ [S1]) [] i AI00_1RB1LA_1RC1RD_1LC0LB_0LA0RB.
Proof.
  intros v i q0 E. destruct (ILCounter.cview_some_I v i q0 E) as (H1 & _).
  unfold Cin0_1RB1LA_1RC1RD_1LC0LB_0LA0RB, cden, AI00_1RB1LA_1RC1RD_1LC0LB_0LA0RB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia. replace (0 * i + 0) with 0 by lia.
  rewrite H1. rshape_1RB1LA_1RC1RD_1LC0LB_0LA0RB.
Qed.

Lemma gen0_1RB1LA_1RC1RD_1LC0LB_0LA0RB : forall v i q0, cview v = (i, Some q0) ->
  cden (Ip q0 ++ [S1]) [] i AI10_1RB1LA_1RC1RD_1LC0LB_0LA0RB = Cin0 (Pos.succ v).
Proof.
  intros v i q0 E. destruct (ILCounter.cview_some_I v i q0 E) as (_ & H2).
  unfold Cin0_1RB1LA_1RC1RD_1LC0LB_0LA0RB, cden, AI10_1RB1LA_1RC1RD_1LC0LB_0LA0RB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia. replace (0 * i + 0) with 0 by lia.
  rewrite H2. rshape_1RB1LA_1RC1RD_1LC0LB_0LA0RB.
Qed.

Lemma lapin0_1RB1LA_1RC1RD_1LC0LB_0LA0RB : forall v i q0, cview v = (i, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cin0 v) = Some c'
               /\ lift c' = lift (Cin0 (Pos.succ v)).
Proof.
  intros v i q0 E.
  exists (4 * i + 4), (Cin0 (Pos.succ v)).
  split; [lia|]. split; [| reflexivity].
  rewrite (gsn0_1RB1LA_1RC1RD_1LC0LB_0LA0RB v i q0 E).
  rewrite (srun_sound tm false true chn0_1RB1LA_1RC1RD_1LC0LB_0LA0RB AI00_1RB1LA_1RC1RD_1LC0LB_0LA0RB AI10_1RB1LA_1RC1RD_1LC0LB_0LA0RB 4 4
             run_inner0_1RB1LA_1RC1RD_1LC0LB_0LA0RB (Ip q0 ++ [S1]) [] i
             ltac:(discriminate) ltac:(reflexivity)).
  f_equal. exact (gen0_1RB1LA_1RC1RD_1LC0LB_0LA0RB v i q0 E).
Qed.

Lemma gbo0_1RB1LA_1RC1RD_1LC0LB_0LA0RB : forall k, lift (cden [] [] k CS0_1RB1LA_1RC1RD_1LC0LB_0LA0RB) = lift (Cin0 (pow2 k)).
Proof.
  intro k. f_equal.
  unfold Cin0_1RB1LA_1RC1RD_1LC0LB_0LA0RB, cden, CS0_1RB1LA_1RC1RD_1LC0LB_0LA0RB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * k + 0) with k by lia. replace (0 * k + 0) with 0 by lia.
  rewrite iepow0_1RB1LA_1RC1RD_1LC0LB_0LA0RB. rshape_1RB1LA_1RC1RD_1LC0LB_0LA0RB.
Qed.

Lemma gxi0_1RB1LA_1RC1RD_1LC0LB_0LA0RB : forall k, Cin0 (fill (pow2 k)) = cden [] [] k CF0_1RB1LA_1RC1RD_1LC0LB_0LA0RB.
Proof.
  intro k.
  destruct (ILCounter.cview_none_I (fill (pow2 k)) k (cview_fill_pow2 k)) as (H1 & _).
  unfold Cin0_1RB1LA_1RC1RD_1LC0LB_0LA0RB, cden, CF0_1RB1LA_1RC1RD_1LC0LB_0LA0RB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * k + 0) with k by lia. replace (0 * k + 0) with 0 by lia.
  rewrite H1. rshape_1RB1LA_1RC1RD_1LC0LB_0LA0RB.
Qed.

Lemma hbo0_1RB1LA_1RC1RD_1LC0LB_0LA0RB : forall p k, virt p = true -> pexp p = Some (S k) ->
  podd p = false ->
  exists n c, 0 < n /\ csteps tm n (Cc p) = Some c
              /\ lift c = lift (Cin0 (pow2 k)).
Proof.
  intros p k Hv Hx Hb.
  exists (0 * k + 6), (cden [] [] k CS0_1RB1LA_1RC1RD_1LC0LB_0LA0RB).
  split; [lia|]. split; [| exact (gbo0_1RB1LA_1RC1RD_1LC0LB_0LA0RB k)].
  rewrite (gsv0_1RB1LA_1RC1RD_1LC0LB_0LA0RB p k Hv Hx Hb).
  exact (srun_sound tm true true chb0_1RB1LA_1RC1RD_1LC0LB_0LA0RB VS0_1RB1LA_1RC1RD_1LC0LB_0LA0RB CS0_1RB1LA_1RC1RD_1LC0LB_0LA0RB 0 6
           run_boot0_1RB1LA_1RC1RD_1LC0LB_0LA0RB [] [] k ltac:(reflexivity) ltac:(reflexivity)).
Qed.

Lemma hxe0_1RB1LA_1RC1RD_1LC0LB_0LA0RB : forall p k, virt p = true -> pexp p = Some (S k) ->
  podd p = false ->
  exists n c', csteps tm n (Cin0 (fill (pow2 k))) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof.
  intros p k Hv Hx Hb.
  exists (4 * k + 13), (cden [] [] k VT0_1RB1LA_1RC1RD_1LC0LB_0LA0RB).
  split; [| exact (gev0_1RB1LA_1RC1RD_1LC0LB_0LA0RB p k Hv Hx Hb)].
  rewrite (gxi0_1RB1LA_1RC1RD_1LC0LB_0LA0RB k).
  exact (srun_sound tm true true che0_1RB1LA_1RC1RD_1LC0LB_0LA0RB CF0_1RB1LA_1RC1RD_1LC0LB_0LA0RB VT0_1RB1LA_1RC1RD_1LC0LB_0LA0RB 4 13
           run_exit0_1RB1LA_1RC1RD_1LC0LB_0LA0RB [] [] k ltac:(reflexivity) ltac:(reflexivity)).
Qed.

(** The register step, composed.  The [Theta(2^k)] middle is the [exists n]
    inside [NestedLapLift.inner_to_fill_lift]; no formula for it is written. *)
Lemma lapv0_1RB1LA_1RC1RD_1LC0LB_0LA0RB : forall p k, virt p = true -> pexp p = Some (S k) ->
  podd p = false ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof.
  intros p k Hv Hx Hb.
  destruct (nested_overflow_lift tm Cc Cin0 lapin0_1RB1LA_1RC1RD_1LC0LB_0LA0RB p (pow2 k)
              (hbo0_1RB1LA_1RC1RD_1LC0LB_0LA0RB p k Hv Hx Hb) (hxe0_1RB1LA_1RC1RD_1LC0LB_0LA0RB p k Hv Hx Hb))
    as (n & c' & Hr & Hl & Hn).
  exists n, c'. split; [exact Hn | split; [exact Hr | exact Hl]].
Qed.


Lemma lapv_1RB1LA_1RC1RD_1LC0LB_0LA0RB : forall p k, virt p = true -> pexp p = Some (S k) ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof.
  intros p k Hv Hx. destruct (podd p) eqn:Hb.
  - exfalso. unfold virt_1RB1LA_1RC1RD_1LC0LB_0LA0RB in Hv. rewrite Hx, Hb in Hv.
    discriminate Hv.
  - exact (lapv0_1RB1LA_1RC1RD_1LC0LB_0LA0RB p k Hv Hx Hb).
Qed.

(** ** SkipGlue's hypotheses *)

Lemma hint_1RB1LA_1RC1RD_1LC0LB_0LA0RB : forall p j q0, (8 <= p)%positive ->
  cview p = (j, Some q0) -> virt p = false ->
  exists n, 0 < n /\ csteps tm n (Cc p) = Some (Cc (Pos.succ p)).
Proof. intros p j q0 _ E Hv. exact (lapi_1RB1LA_1RC1RD_1LC0LB_0LA0RB p j q0 E Hv). Qed.

Lemma hsucc_1RB1LA_1RC1RD_1LC0LB_0LA0RB : forall p j q0, cview p = (j, Some q0) ->
  virt p = false -> virt (Pos.succ p) = false.
Proof. intros p j q0 E _. exact (hsucc0_1RB1LA_1RC1RD_1LC0LB_0LA0RB p j q0 E). Qed.

Lemma hvlap_1RB1LA_1RC1RD_1LC0LB_0LA0RB : forall p, (8 <= p)%positive -> virt p = true ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof.
  intros p _ Hv. destruct (vsome_1RB1LA_1RC1RD_1LC0LB_0LA0RB p Hv) as (k & Hx).
  exact (lapv_1RB1LA_1RC1RD_1LC0LB_0LA0RB p k Hv Hx).
Qed.

Lemma hvrun_1RB1LA_1RC1RD_1LC0LB_0LA0RB : forall p, (8 <= p)%positive -> virt p = true ->
  virt (Pos.succ p) = true -> virt (Pos.succ (Pos.succ p)) = false.
Proof.
  intros p _ V1 V2. exfalso.
  destruct (vsome_1RB1LA_1RC1RD_1LC0LB_0LA0RB p V1) as (k & Hx).
  rewrite (hsuccv_1RB1LA_1RC1RD_1LC0LB_0LA0RB p k Hx) in V2. discriminate V2.
Qed.

(** ** The lap *)

Lemma lap_1RB1LA_1RC1RD_1LC0LB_0LA0RB : forall p, (8 <= p)%positive -> exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intros p Hp. destruct (cview p) as [j oq] eqn:E; destruct oq as [q0|].
  - destruct (virt p) eqn:V.
    + destruct (vsome_1RB1LA_1RC1RD_1LC0LB_0LA0RB p V) as (k & Hx).
      destruct (lapv_1RB1LA_1RC1RD_1LC0LB_0LA0RB p k V Hx) as (n & c' & Hn & Hr & Hl).
      exists n, c'. split; [exact Hr | split; [exact Hl | exact Hn]].
    + destruct (lapi_1RB1LA_1RC1RD_1LC0LB_0LA0RB p j q0 E V) as (n & Hn & Hr).
      exists n, (Cc (Pos.succ p)).
      split; [exact Hr | split; [reflexivity | exact Hn]].
  - destruct (cview_pos p j E) as (j' & ->).
    destruct (podd p) eqn:Hb.
    + destruct (lapo1_1RB1LA_1RC1RD_1LC0LB_0LA0RB p j' E Hb) as (n & Hn & Hr).
      exists n, (Cc (Pos.succ p)).
      split; [exact Hr | split; [reflexivity | exact Hn]].
    + destruct (lapo0_1RB1LA_1RC1RD_1LC0LB_0LA0RB p j' E Hb) as (n & Hn & Hr).
      exists n, (Cc (Pos.succ p)).
      split; [exact Hr | split; [reflexivity | exact Hn]].
Qed.

(** ** Bootstrap *)

Lemma boot_1RB1LA_1RC1RD_1LC0LB_0LA0RB : exists t0, stepn tm t0 InitES = Some (lift (Cc 8)).
Proof.
  exists 89.
  assert (H : match csteps tm 89 c0 with
              | Some c => ceqb c (Cc 8) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 89 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** ** Visits

    [SkipGlue.vis_via_skip] asks for a witness at EVERY overflow anchor at or
    above [p0], and the overflow anchors alternate frames -- so the witness
    is a prefix of whichever of the two overflow chains that parity uses. *)

Lemma viso1_1RB1LA_1RC1RD_1LC0LB_0LA0RB : forall (l : list lstep) (q : St),
  srun_st tm true true l B01_1RB1LA_1RC1RD_1LC0LB_0LA0RB = Some q ->
  forall p j, cview p = (S j, None) -> podd p = true ->
  exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros l q Hst p j E Hb.
  apply (vis_of_run tm Cc true true l B01_1RB1LA_1RC1RD_1LC0LB_0LA0RB p j [] []);
    [exact Hst | reflexivity | reflexivity | exact (gso1_1RB1LA_1RC1RD_1LC0LB_0LA0RB p j E Hb)].
Qed.

Lemma viso0_1RB1LA_1RC1RD_1LC0LB_0LA0RB : forall (l : list lstep) (q : St),
  srun_st tm true true l B00_1RB1LA_1RC1RD_1LC0LB_0LA0RB = Some q ->
  forall p j, cview p = (S j, None) -> podd p = false ->
  exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros l q Hst p j E Hb.
  apply (vis_of_run tm Cc true true l B00_1RB1LA_1RC1RD_1LC0LB_0LA0RB p j [] []);
    [exact Hst | reflexivity | reflexivity | exact (gso0_1RB1LA_1RC1RD_1LC0LB_0LA0RB p j E Hb)].
Qed.

Lemma vis_1RB1LA_1RC1RD_1LC0LB_0LA0RB : forall p q, (8 <= p)%positive ->
  exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros p q Hp.
  apply (vis_via_skip tm Cc virt 8 hint_1RB1LA_1RC1RD_1LC0LB_0LA0RB hsucc_1RB1LA_1RC1RD_1LC0LB_0LA0RB hvlap_1RB1LA_1RC1RD_1LC0LB_0LA0RB
           hvrun_1RB1LA_1RC1RD_1LC0LB_0LA0RB q); [| exact Hp].
  intros p1 j1 Hp1 E1. destruct (podd p1) eqn:Hb1.
  - destruct q.
    + exact (viso1_1RB1LA_1RC1RD_1LC0LB_0LA0RB [SRotL 1; SWin 1] StA ltac:(vm_compute; reflexivity) p1 j1 E1 Hb1).
    + exact (viso1_1RB1LA_1RC1RD_1LC0LB_0LA0RB [SRotL 1; SWin 1; SCycL 2 0; SWin 1; SWinL 2] StB ltac:(vm_compute; reflexivity) p1 j1 E1 Hb1).
    + exact (viso1_1RB1LA_1RC1RD_1LC0LB_0LA0RB [SRotL 1; SWin 1; SCycL 2 0; SWin 1; SWinL 3; SCycR 2; SWin 1; SWinR 1] StC ltac:(vm_compute; reflexivity) p1 j1 E1 Hb1).
    + exact (viso1_1RB1LA_1RC1RD_1LC0LB_0LA0RB [] StD ltac:(vm_compute; reflexivity) p1 j1 E1 Hb1).
  - destruct q.
    + exact (viso0_1RB1LA_1RC1RD_1LC0LB_0LA0RB [SRotL 1; SWin 1] StA ltac:(vm_compute; reflexivity) p1 j1 E1 Hb1).
    + exact (viso0_1RB1LA_1RC1RD_1LC0LB_0LA0RB [SRotL 1; SWin 1; SCycL 2 0; SWin 1; SWinL 2] StB ltac:(vm_compute; reflexivity) p1 j1 E1 Hb1).
    + exact (viso0_1RB1LA_1RC1RD_1LC0LB_0LA0RB [SRotL 1; SWin 1; SCycL 2 0; SWin 1; SWinL 3; SCycR 2; SWin 2] StC ltac:(vm_compute; reflexivity) p1 j1 E1 Hb1).
    + exact (viso0_1RB1LA_1RC1RD_1LC0LB_0LA0RB [] StD ltac:(vm_compute; reflexivity) p1 j1 E1 Hb1).
Qed.

Theorem nqh_1RB1LA_1RC1RD_1LC0LB_0LA0RB : NeverQuasiHaltsSt tm.
Proof. apply (glue_neverqh tm Cc 8). - exact boot_1RB1LA_1RC1RD_1LC0LB_0LA0RB. - intros p Hp. apply (lap_1RB1LA_1RC1RD_1LC0LB_0LA0RB p Hp). - intros p q Hp. apply (vis_1RB1LA_1RC1RD_1LC0LB_0LA0RB p q Hp). Qed.

Theorem nonhalt_1RB1LA_1RC1RD_1LC0LB_0LA0RB : NonHalt tm.
Proof. apply never_qh_nonhalt, nqh_1RB1LA_1RC1RD_1LC0LB_0LA0RB. Qed.
