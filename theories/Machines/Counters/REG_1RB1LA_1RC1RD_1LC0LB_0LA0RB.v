(** * REG_1RB1LA_1RC1RD_1LC0LB_0LA0RB: machine 1RB1LA_1RC1RD_1LC0LB_0LA0RB, boarded by CERTIFICATE (REGISTER route).

    Auto-emitted by tools/counters/regcert.py (UNTRUSTED emitter; the Coq
    kernel re-runs the checker on every line below).  A binary counter under
    the Ap_Alph_10_11_11 digit alphabet (Alph_10_11_11.v) whose anchor FRAME depends on the
    OCTAVE: the machine keeps a one-cell REGISTER past the head and moves it
    once per octave, so the family is (register state x counter) and the
    anchor is piecewise (WAVE28 section 3c, `period-2+virt`).

      Cc p = if virt p then (StC, E p ++ tail, S0, [])
             else (StD, E p ++ tail, S0, if podd p then [] else [S1])

    [RegGlue.podd] is the octave parity ([podd p = true] iff the octave is
    odd); [virt p] holds at the powers of two the machine rests at in a
    DIFFERENT frame from their own octave's -- the SKIP route's virtual
    anchor, one dimension up.  Four lap branches, and they are NOT four
    ordinary chains:

      interior  (virt p = false, cview p = (j, Some q0)):  4*j+4 steps, exact,
                the frame carried as the RIGHT OPAQUE TAIL so ONE chain
                covers both octave parities
      overflow  (cview p = (S j, None)), one chain per parity:
                podd p = true:  4*j+7 steps   podd p = false: 4*j+9 steps
      register  (virt p = true): boot 0*k+6, then the INNER counter's own laps
                to its all-ones fill, then exit 4*k+13 -- [Theta(2^k)], and the
                exponent is never written down
                ([Counters/NestedLapLift.nested_overflow_lift]).

    The register step is the whole point: the mark cannot be moved without a
    pass that COUNTS, so a nested branch sits inside a piecewise [Cc].
    [Counters/SkipGlue.v] fences the virtual anchors ([reach_ovf_skip] /
    [vis_via_skip], the interior-lap hypothesis GUARDED by "not virtual"),
    [Counters/RegGlue.v] supplies the octave parity, and the closer is
    [LapGlue.glue_neverqh] directly.

    Differentially validated against the raw simulator on EVERY branch --
    step counts AND configurations, every inner lap of every register step --
    for 120 anchors, 2 register steps, 38 inner laps.
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

(** The virtual anchors: the powers of two whose octave parity is the one
    the machine rests at in its transient frame.  [pexp p = Some 0] (that
    is, [p = 1]) is excluded by the [S _] pattern, so [Cc 1] is an ordinary
    frame anchor and the overflow glue holds at it too. *)
Definition virt_1RB1LA_1RC1RD_1LC0LB_0LA0RB (p : positive) : bool :=
  match pexp p with Some (S _) => negb (podd p) | _ => false end.
Local Notation virt := virt_1RB1LA_1RC1RD_1LC0LB_0LA0RB.

Definition frm_1RB1LA_1RC1RD_1LC0LB_0LA0RB (p : positive) : list Sym :=
  if podd p then [] else [S1].
Local Notation frm := frm_1RB1LA_1RC1RD_1LC0LB_0LA0RB.

Definition Cc_1RB1LA_1RC1RD_1LC0LB_0LA0RB (p : positive) : cconf :=
  if virt_1RB1LA_1RC1RD_1LC0LB_0LA0RB p then (StC, (Ap_Alph_10_11_11 p ++ [], S0, []))
  else (StD, (Ap_Alph_10_11_11 p ++ [], S0, frm_1RB1LA_1RC1RD_1LC0LB_0LA0RB p)).
Local Notation Cc := Cc_1RB1LA_1RC1RD_1LC0LB_0LA0RB.

(** ** The INNER anchor family -- the counter the register step re-runs *)
Definition Cin_1RB1LA_1RC1RD_1LC0LB_0LA0RB (v : positive) : cconf :=
  (StD, (Ip v ++ [S1], S0, [S1;S1])).
Local Notation Cin := Cin_1RB1LA_1RC1RD_1LC0LB_0LA0RB.

Ltac rshape_1RB1LA_1RC1RD_1LC0LB_0LA0RB :=
  cbn [rep app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r;
  reflexivity.

(** ** The certificate *)

Definition A0_1RB1LA_1RC1RD_1LC0LB_0LA0RB : sconf := mkC StD (mkS [] [S1;S1] 1 0 [S1;S0]) S0 (mkS [] [] 0 0 []).
Definition A1_1RB1LA_1RC1RD_1LC0LB_0LA0RB : sconf := mkC StD (mkS [] [S1;S0] 1 0 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition chi_1RB1LA_1RC1RD_1LC0LB_0LA0RB : list lstep := [SRotL 1; SWin 1; SCycL 2 0; SWin 2; SCycR 2; SWin 1; SUnrotL 1].

Lemma run_int_1RB1LA_1RC1RD_1LC0LB_0LA0RB : srun tm false false chi_1RB1LA_1RC1RD_1LC0LB_0LA0RB A0_1RB1LA_1RC1RD_1LC0LB_0LA0RB = Some (A1_1RB1LA_1RC1RD_1LC0LB_0LA0RB, 4, 4).
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

(** *** the register step: boot (from the PEELED virtual anchor -- the first
    move is onto the counter's own top block), inner laps, exit *)
Definition VP_1RB1LA_1RC1RD_1LC0LB_0LA0RB : sconf := mkC StC (mkS [S1;S0] [S1;S0] 1 0 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition CS_1RB1LA_1RC1RD_1LC0LB_0LA0RB : sconf := mkC StD (mkS [] [S1;S0] 1 0 [S1;S1]) S0 (mkS [S1;S1] [] 0 0 []).
Definition chb_1RB1LA_1RC1RD_1LC0LB_0LA0RB : list lstep := [SWin 4; SRotL 1; SWin 2; SUnrotL 1].

Lemma run_boot_1RB1LA_1RC1RD_1LC0LB_0LA0RB : srun tm true true chb_1RB1LA_1RC1RD_1LC0LB_0LA0RB VP_1RB1LA_1RC1RD_1LC0LB_0LA0RB = Some (CS_1RB1LA_1RC1RD_1LC0LB_0LA0RB, 0, 6).
Proof. vm_compute. reflexivity. Qed.

Definition AI0_1RB1LA_1RC1RD_1LC0LB_0LA0RB : sconf := mkC StD (mkS [] [S1;S1] 1 0 [S1;S0]) S0 (mkS [S1;S1] [] 0 0 []).
Definition AI1_1RB1LA_1RC1RD_1LC0LB_0LA0RB : sconf := mkC StD (mkS [] [S1;S0] 1 0 [S1;S1]) S0 (mkS [S1;S1] [] 0 0 []).
Definition chn_1RB1LA_1RC1RD_1LC0LB_0LA0RB : list lstep := [SRotL 1; SWin 1; SCycL 2 0; SWin 2; SCycR 2; SWin 1; SUnrotL 1].

Lemma run_inner_1RB1LA_1RC1RD_1LC0LB_0LA0RB : srun tm false true chn_1RB1LA_1RC1RD_1LC0LB_0LA0RB AI0_1RB1LA_1RC1RD_1LC0LB_0LA0RB = Some (AI1_1RB1LA_1RC1RD_1LC0LB_0LA0RB, 4, 4).
Proof. vm_compute. reflexivity. Qed.

Definition CF_1RB1LA_1RC1RD_1LC0LB_0LA0RB : sconf := mkC StD (mkS [] [S1;S1] 1 0 [S1;S1]) S0 (mkS [S1;S1] [] 0 0 []).
Definition VT_1RB1LA_1RC1RD_1LC0LB_0LA0RB : sconf := mkC StD (mkS [S1;S1] [S1;S0] 1 0 [S1;S1]) S0 (mkS [S1] [] 0 0 []).
Definition che_1RB1LA_1RC1RD_1LC0LB_0LA0RB : list lstep := [SRotL 1; SWin 1; SCycL 2 0; SWin 1; SWinL 3; SCycR 2; SWin 8].

Lemma run_exit_1RB1LA_1RC1RD_1LC0LB_0LA0RB : srun tm true true che_1RB1LA_1RC1RD_1LC0LB_0LA0RB CF_1RB1LA_1RC1RD_1LC0LB_0LA0RB = Some (VT_1RB1LA_1RC1RD_1LC0LB_0LA0RB, 4, 13).
Proof. vm_compute. reflexivity. Qed.

(** ** Anchor glue -- the only per-machine mathematics *)

Lemma epow_1RB1LA_1RC1RD_1LC0LB_0LA0RB : forall n, Ap_Alph_10_11_11 (pow2 n) = rep [S1;S0] n ++ [S1;S1].
Proof. induction n; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.

Lemma iepow_1RB1LA_1RC1RD_1LC0LB_0LA0RB : forall n, Ip (pow2 n) = rep [S1;S0] n ++ [S1].
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

(** *** the interior branch.  The frame is the RIGHT OPAQUE TAIL, so the one
    chain speaks at both octave parities at once. *)
Lemma gsi_1RB1LA_1RC1RD_1LC0LB_0LA0RB : forall p j q0, cview p = (j, Some q0) -> virt p = false ->
  Cc p = cden (Ap_Alph_10_11_11 q0 ++ []) (frm p) j A0_1RB1LA_1RC1RD_1LC0LB_0LA0RB.
Proof.
  intros p j q0 E Hv. unfold Cc_1RB1LA_1RC1RD_1LC0LB_0LA0RB. rewrite Hv.
  destruct (Alph_10_11_11.cview_some_Alph_10_11_11 p j q0 E) as (H1 & _).
  unfold cden, A0_1RB1LA_1RC1RD_1LC0LB_0LA0RB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia. replace (0 * j + 0) with 0 by lia.
  rewrite H1. rshape_1RB1LA_1RC1RD_1LC0LB_0LA0RB.
Qed.

Lemma gei_1RB1LA_1RC1RD_1LC0LB_0LA0RB : forall p j q0, cview p = (j, Some q0) -> virt p = false ->
  cden (Ap_Alph_10_11_11 q0 ++ []) (frm p) j A1_1RB1LA_1RC1RD_1LC0LB_0LA0RB = Cc (Pos.succ p).
Proof.
  intros p j q0 E Hv. unfold Cc_1RB1LA_1RC1RD_1LC0LB_0LA0RB.
  rewrite (hsucc0_1RB1LA_1RC1RD_1LC0LB_0LA0RB p j q0 E).
  unfold frm_1RB1LA_1RC1RD_1LC0LB_0LA0RB. rewrite (podd_succ_int p j q0 E).
  destruct (Alph_10_11_11.cview_some_Alph_10_11_11 p j q0 E) as (_ & H2).
  unfold cden, A1_1RB1LA_1RC1RD_1LC0LB_0LA0RB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia. replace (0 * j + 0) with 0 by lia.
  rewrite H2. rshape_1RB1LA_1RC1RD_1LC0LB_0LA0RB.
Qed.

Lemma lapi_1RB1LA_1RC1RD_1LC0LB_0LA0RB : forall p j q0, cview p = (j, Some q0) -> virt p = false ->
  exists n, 0 < n /\ csteps tm n (Cc p) = Some (Cc (Pos.succ p)).
Proof.
  intros p j q0 E Hv. exists (4 * j + 4). split; [lia|].
  rewrite (gsi_1RB1LA_1RC1RD_1LC0LB_0LA0RB p j q0 E Hv).
  rewrite (srun_sound tm false false chi_1RB1LA_1RC1RD_1LC0LB_0LA0RB A0_1RB1LA_1RC1RD_1LC0LB_0LA0RB A1_1RB1LA_1RC1RD_1LC0LB_0LA0RB 4 4
             run_int_1RB1LA_1RC1RD_1LC0LB_0LA0RB (Ap_Alph_10_11_11 q0 ++ []) (frm p) j
             ltac:(discriminate) ltac:(discriminate)).
  f_equal. exact (gei_1RB1LA_1RC1RD_1LC0LB_0LA0RB p j q0 E Hv).
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
  intros p j E Hb. unfold Cc_1RB1LA_1RC1RD_1LC0LB_0LA0RB, virt_1RB1LA_1RC1RD_1LC0LB_0LA0RB, frm_1RB1LA_1RC1RD_1LC0LB_0LA0RB.
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
  intros p j E Hb. unfold Cc_1RB1LA_1RC1RD_1LC0LB_0LA0RB, virt_1RB1LA_1RC1RD_1LC0LB_0LA0RB, frm_1RB1LA_1RC1RD_1LC0LB_0LA0RB.
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


(** *** the register step *)

Lemma vpar_1RB1LA_1RC1RD_1LC0LB_0LA0RB : forall p k, virt p = true -> pexp p = Some (S k) ->
  podd p = false.
Proof.
  intros p k Hv Hx. unfold virt_1RB1LA_1RC1RD_1LC0LB_0LA0RB in Hv. rewrite Hx in Hv.
  destruct (podd p); [discriminate | reflexivity].
Qed.

Lemma gsv_1RB1LA_1RC1RD_1LC0LB_0LA0RB : forall p k, virt p = true -> pexp p = Some (S k) ->
  Cc p = cden [] [] k VP_1RB1LA_1RC1RD_1LC0LB_0LA0RB.
Proof.
  intros p k Hv Hx. unfold Cc_1RB1LA_1RC1RD_1LC0LB_0LA0RB. rewrite Hv.
  rewrite (pexp_some p (S k) Hx), epow_1RB1LA_1RC1RD_1LC0LB_0LA0RB.
  unfold cden, VP_1RB1LA_1RC1RD_1LC0LB_0LA0RB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * k + 0) with k by lia. replace (0 * k + 0) with 0 by lia.
  rshape_1RB1LA_1RC1RD_1LC0LB_0LA0RB.
Qed.

Lemma gsn_1RB1LA_1RC1RD_1LC0LB_0LA0RB : forall v i q0, cview v = (i, Some q0) ->
  Cin v = cden (Ip q0 ++ [S1]) [] i AI0_1RB1LA_1RC1RD_1LC0LB_0LA0RB.
Proof.
  intros v i q0 E. destruct (ILCounter.cview_some_I v i q0 E) as (H1 & _).
  unfold Cin_1RB1LA_1RC1RD_1LC0LB_0LA0RB, cden, AI0_1RB1LA_1RC1RD_1LC0LB_0LA0RB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia. replace (0 * i + 0) with 0 by lia.
  rewrite H1. rshape_1RB1LA_1RC1RD_1LC0LB_0LA0RB.
Qed.

Lemma gen_1RB1LA_1RC1RD_1LC0LB_0LA0RB : forall v i q0, cview v = (i, Some q0) ->
  cden (Ip q0 ++ [S1]) [] i AI1_1RB1LA_1RC1RD_1LC0LB_0LA0RB = Cin (Pos.succ v).
Proof.
  intros v i q0 E. destruct (ILCounter.cview_some_I v i q0 E) as (_ & H2).
  unfold Cin_1RB1LA_1RC1RD_1LC0LB_0LA0RB, cden, AI1_1RB1LA_1RC1RD_1LC0LB_0LA0RB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia. replace (0 * i + 0) with 0 by lia.
  rewrite H2. rshape_1RB1LA_1RC1RD_1LC0LB_0LA0RB.
Qed.

Lemma lapin_1RB1LA_1RC1RD_1LC0LB_0LA0RB : forall v i q0, cview v = (i, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cin v) = Some c'
               /\ lift c' = lift (Cin (Pos.succ v)).
Proof.
  intros v i q0 E.
  exists (4 * i + 4), (Cin (Pos.succ v)).
  split; [lia|]. split; [| reflexivity].
  rewrite (gsn_1RB1LA_1RC1RD_1LC0LB_0LA0RB v i q0 E).
  rewrite (srun_sound tm false true chn_1RB1LA_1RC1RD_1LC0LB_0LA0RB AI0_1RB1LA_1RC1RD_1LC0LB_0LA0RB AI1_1RB1LA_1RC1RD_1LC0LB_0LA0RB 4 4
             run_inner_1RB1LA_1RC1RD_1LC0LB_0LA0RB (Ip q0 ++ [S1]) [] i
             ltac:(discriminate) ltac:(reflexivity)).
  f_equal. exact (gen_1RB1LA_1RC1RD_1LC0LB_0LA0RB v i q0 E).
Qed.

Lemma gbo_1RB1LA_1RC1RD_1LC0LB_0LA0RB : forall k, lift (cden [] [] k CS_1RB1LA_1RC1RD_1LC0LB_0LA0RB) = lift (Cin (pow2 k)).
Proof.
  intro k. f_equal.
  unfold Cin_1RB1LA_1RC1RD_1LC0LB_0LA0RB, cden, CS_1RB1LA_1RC1RD_1LC0LB_0LA0RB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * k + 0) with k by lia. replace (0 * k + 0) with 0 by lia.
  rewrite iepow_1RB1LA_1RC1RD_1LC0LB_0LA0RB. rshape_1RB1LA_1RC1RD_1LC0LB_0LA0RB.
Qed.

Lemma gxi_1RB1LA_1RC1RD_1LC0LB_0LA0RB : forall k, Cin (fill (pow2 k)) = cden [] [] k CF_1RB1LA_1RC1RD_1LC0LB_0LA0RB.
Proof.
  intro k.
  destruct (ILCounter.cview_none_I (fill (pow2 k)) k (cview_fill_pow2 k)) as (H1 & _).
  unfold Cin_1RB1LA_1RC1RD_1LC0LB_0LA0RB, cden, CF_1RB1LA_1RC1RD_1LC0LB_0LA0RB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * k + 0) with k by lia. replace (0 * k + 0) with 0 by lia.
  rewrite H1. rshape_1RB1LA_1RC1RD_1LC0LB_0LA0RB.
Qed.

Lemma gev_1RB1LA_1RC1RD_1LC0LB_0LA0RB : forall p k, virt p = true -> pexp p = Some (S k) ->
  lift (cden [] [] k VT_1RB1LA_1RC1RD_1LC0LB_0LA0RB) = lift (Cc (Pos.succ p)).
Proof.
  intros p k Hv Hx. f_equal.
  unfold Cc_1RB1LA_1RC1RD_1LC0LB_0LA0RB, frm_1RB1LA_1RC1RD_1LC0LB_0LA0RB. rewrite (hsuccv_1RB1LA_1RC1RD_1LC0LB_0LA0RB p k Hx).
  rewrite (podd_succ_pexp p k Hx), (vpar_1RB1LA_1RC1RD_1LC0LB_0LA0RB p k Hv Hx).
  rewrite (pexp_some p (S k) Hx).
  cbn [Pos.succ pow2 Ap_Alph_10_11_11]. rewrite epow_1RB1LA_1RC1RD_1LC0LB_0LA0RB.
  unfold cden, VT_1RB1LA_1RC1RD_1LC0LB_0LA0RB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * k + 0) with k by lia. replace (0 * k + 0) with 0 by lia.
  rshape_1RB1LA_1RC1RD_1LC0LB_0LA0RB.
Qed.

Lemma hbo_1RB1LA_1RC1RD_1LC0LB_0LA0RB : forall p k, virt p = true -> pexp p = Some (S k) ->
  exists n c, 0 < n /\ csteps tm n (Cc p) = Some c
              /\ lift c = lift (Cin (pow2 k)).
Proof.
  intros p k Hv Hx.
  exists (0 * k + 6), (cden [] [] k CS_1RB1LA_1RC1RD_1LC0LB_0LA0RB).
  split; [lia|]. split; [| exact (gbo_1RB1LA_1RC1RD_1LC0LB_0LA0RB k)].
  rewrite (gsv_1RB1LA_1RC1RD_1LC0LB_0LA0RB p k Hv Hx).
  exact (srun_sound tm true true chb_1RB1LA_1RC1RD_1LC0LB_0LA0RB VP_1RB1LA_1RC1RD_1LC0LB_0LA0RB CS_1RB1LA_1RC1RD_1LC0LB_0LA0RB 0 6
           run_boot_1RB1LA_1RC1RD_1LC0LB_0LA0RB [] [] k ltac:(reflexivity) ltac:(reflexivity)).
Qed.

Lemma hxe_1RB1LA_1RC1RD_1LC0LB_0LA0RB : forall p k, virt p = true -> pexp p = Some (S k) ->
  exists n c', csteps tm n (Cin (fill (pow2 k))) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof.
  intros p k Hv Hx.
  exists (4 * k + 13), (cden [] [] k VT_1RB1LA_1RC1RD_1LC0LB_0LA0RB).
  split; [| exact (gev_1RB1LA_1RC1RD_1LC0LB_0LA0RB p k Hv Hx)].
  rewrite (gxi_1RB1LA_1RC1RD_1LC0LB_0LA0RB k).
  exact (srun_sound tm true true che_1RB1LA_1RC1RD_1LC0LB_0LA0RB CF_1RB1LA_1RC1RD_1LC0LB_0LA0RB VT_1RB1LA_1RC1RD_1LC0LB_0LA0RB 4 13
           run_exit_1RB1LA_1RC1RD_1LC0LB_0LA0RB [] [] k ltac:(reflexivity) ltac:(reflexivity)).
Qed.

(** The register step, composed.  The [Theta(2^k)] middle is the [exists n]
    inside [NestedLapLift.inner_to_fill_lift]; no formula for it is written. *)
Lemma lapv_1RB1LA_1RC1RD_1LC0LB_0LA0RB : forall p k, virt p = true -> pexp p = Some (S k) ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof.
  intros p k Hv Hx.
  destruct (nested_overflow_lift tm Cc Cin lapin_1RB1LA_1RC1RD_1LC0LB_0LA0RB p (pow2 k)
              (hbo_1RB1LA_1RC1RD_1LC0LB_0LA0RB p k Hv Hx) (hxe_1RB1LA_1RC1RD_1LC0LB_0LA0RB p k Hv Hx))
    as (n & c' & Hr & Hl & Hn).
  exists n, c'. split; [exact Hn | split; [exact Hr | exact Hl]].
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
