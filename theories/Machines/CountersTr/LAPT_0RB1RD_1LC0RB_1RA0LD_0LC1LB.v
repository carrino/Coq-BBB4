(** * LAPT_0RB1RD_1LC0RB_1RA0LD_0LC1LB: TRANSITION-LEVEL board for machine 0RB1RD_1LC0RB_1RA0LD_0LC1LB, boarded by CERTIFICATE.

    Auto-emitted by tools/counters/emit_lapcert.py (UNTRUSTED emitter; the Coq
    kernel re-runs the checker on every line below).  Left-growth binary
    counter under the Ap_Alph_010_110_1 digit alphabet (Alph_010_110_1.v), anchored at

      Cc p = (StB, (Ap_Alph_010_110_1 p ++ [S0], S0, [S1]))

    The lap is DATA, not a proof script: each branch is a list of steps for
    [Checkers/LapDecider.v], run by the kernel through [vm_compute] and
    discharged by the single theorem [srun_sound].

      interior  (cview p = (j, Some q0)):  10*j+12 steps
      overflow  (cview p = (S j, None)):   boot 10*j+13, then the inner counter's own laps to the
                                           all-ones fill, then exit 10*j+27

    The interior branch closes EXACTLY (which is what feeds
    [LapCertGlue.reach_ovf]); the overflow branch closes one blank short of
    the anchor tail, hence up to [lift].

    Differentially validated against the raw simulator on BOTH branches --
    step counts AND exact configurations -- for 192 interior anchors (interior); 6 overflow phases, j = 2..7 (984 inner laps, 4 counts each) (nested overflow).
    Axiom footprint: [functional_extensionality_dep] (via [CTape.lift]). *)
From Coq Require Import Arith Lia Bool List PArith Wellfounded.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape LapGlue LapGlueQH LapGlueAbs
                                  MonoCounter JpCounter Alph_010_110_1 LapCertGlue LapCertGlueLift IXPGadgets NestedLap NestedLapLift NestedLap2 Alph_001_011_0.
From BBB4.Census Require Import TNF_QH.
From BBB4.Checkers Require Import LapDecider.
From BBB4 Require Import BBBT4_Statement.
From BBB4.Checkers Require Import WrapTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
From BBB4.Counters Require Import LapGlueTr.
Import ListNotations.

Definition mk_0RB1RD_1LC0RB_1RA0LD_0LC1LB (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_0RB1RD_1LC0RB_1RA0LD_0LC1LB.

(** 0RB1RD_1LC0RB_1RA0LD_0LC1LB *)
Definition tm_0RB1RD_1LC0RB_1RA0LD_0LC1LB : TM := fun q s => match q, s with
  | StA, S0 => mk S0 DR StB | StA, S1 => mk S1 DR StD
  | StB, S0 => mk S1 DL StC | StB, S1 => mk S0 DR StB
  | StC, S0 => mk S1 DR StA | StC, S1 => mk S0 DL StD
  | StD, S0 => mk S0 DL StC | StD, S1 => mk S1 DL StB end.
(** the instructions the certificate claims NEVER fire; the lap
    argument runs on the machine WRAPPED at them
    ([WrapTr.tm_wrap_trs]), so a pinned instruction firing would
    halt it and every [srun] below would fail. *)
Definition pins_0RB1RD_1LC0RB_1RA0LD_0LC1LB : list Instr := [].
Definition tmw_0RB1RD_1LC0RB_1RA0LD_0LC1LB : TM := tm_wrap_trs tm_0RB1RD_1LC0RB_1RA0LD_0LC1LB pins_0RB1RD_1LC0RB_1RA0LD_0LC1LB.
Local Notation tm := tmw_0RB1RD_1LC0RB_1RA0LD_0LC1LB.

Definition Cc_0RB1RD_1LC0RB_1RA0LD_0LC1LB (p : positive) : cconf := (StB, (Ap_Alph_010_110_1 p ++ [S0], S0, [S1])).
Local Notation Cc := Cc_0RB1RD_1LC0RB_1RA0LD_0LC1LB.

(** ** The certificate *)

Definition A0_0RB1RD_1LC0RB_1RA0LD_0LC1LB : sconf := mkC StB (mkS [] [S1;S1;S0] 1 0 [S0;S1;S0]) S0 (mkS [S1] [] 0 0 []).
Definition A1_0RB1RD_1LC0RB_1RA0LD_0LC1LB : sconf := mkC StB (mkS [] [S0;S1;S0] 1 0 [S1;S1;S0]) S0 (mkS [S1;S0;S0] [] 0 0 []).
Definition chi_0RB1RD_1LC0RB_1RA0LD_0LC1LB : list lstep := [SCycL 3 0; SWin 2; SRotR 1; SWin 3; SCycR 7; SWinR 6; SRotL 1; SWin 1].

Lemma run_int_0RB1RD_1LC0RB_1RA0LD_0LC1LB : srun tm false true chi_0RB1RD_1LC0RB_1RA0LD_0LC1LB A0_0RB1RD_1LC0RB_1RA0LD_0LC1LB = Some (A1_0RB1RD_1LC0RB_1RA0LD_0LC1LB, 10, 12).
Proof. vm_compute. reflexivity. Qed.

Definition B0_0RB1RD_1LC0RB_1RA0LD_0LC1LB : sconf := mkC StB (mkS [] [S1;S1;S0] 1 0 [S1;S0]) S0 (mkS [S1] [] 0 0 []).
Definition B1_0RB1RD_1LC0RB_1RA0LD_0LC1LB : sconf := mkC StB (mkS [] [S0;S1;S0] 1 1 [S1]) S0 (mkS [S1;S0;S0] [] 0 0 []).
(** ** The FIRST INNER anchor family -- Ap_Alph_001_011_0 at StC *)
Definition Cin_0RB1RD_1LC0RB_1RA0LD_0LC1LB (v : positive) : cconf := (StC, (Ap_Alph_001_011_0 v ++ [S0;S1;S1], S0, [S1])).
Local Notation Cin := Cin_0RB1RD_1LC0RB_1RA0LD_0LC1LB.

(** [E (2^n) = A^n C]: the value this family's count starts at. *)
Lemma epow2_0RB1RD_1LC0RB_1RA0LD_0LC1LB : forall n, Ap_Alph_001_011_0 (pow2 n) = rep [S0;S0;S1] n ++ [S0].
Proof. induction n; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.

(** Its own INTERIOR lap -- ordinary and affine.  Iterating it to the fill is
    where a [Theta(2^j)] lives, and [inner_to_fill_lift] keeps it inside an
    existential. *)
Definition AI0_0RB1RD_1LC0RB_1RA0LD_0LC1LB : sconf := mkC StC (mkS [] [S0;S1;S1] 1 0 [S0;S0;S1]) S0 (mkS [S1] [] 0 0 []).
Definition AI1_0RB1RD_1LC0RB_1RA0LD_0LC1LB : sconf := mkC StC (mkS [] [S0;S0;S1] 1 0 [S0;S1;S1]) S0 (mkS [S1;S0] [] 0 0 []).
Definition chn_0RB1RD_1LC0RB_1RA0LD_0LC1LB : list lstep := [SWin 1; SWinR 3; SCycL 3 0; SWin 6; SCycR 7; SWin 2].

Lemma run_inner_0RB1RD_1LC0RB_1RA0LD_0LC1LB : srun tm false true chn_0RB1RD_1LC0RB_1RA0LD_0LC1LB AI0_0RB1RD_1LC0RB_1RA0LD_0LC1LB = Some (AI1_0RB1RD_1LC0RB_1RA0LD_0LC1LB, 10, 12).
Proof. vm_compute. reflexivity. Qed.

(** ** The SECOND INNER anchor family -- Ap_Alph_001_011_0 at StC *)
Definition Cin2_0RB1RD_1LC0RB_1RA0LD_0LC1LB (v : positive) : cconf := (StC, (Ap_Alph_001_011_0 v ++ [S1;S1;S1], S0, [S1])).
Local Notation Cin2 := Cin2_0RB1RD_1LC0RB_1RA0LD_0LC1LB.

(** [E (2^n) = A^n C]: the value this family's count starts at. *)
Lemma epow22_0RB1RD_1LC0RB_1RA0LD_0LC1LB : forall n, Ap_Alph_001_011_0 (pow2 n) = rep [S0;S0;S1] n ++ [S0].
Proof. induction n; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.

(** Its own INTERIOR lap -- ordinary and affine.  Iterating it to the fill is
    where a [Theta(2^j)] lives, and [inner_to_fill_lift] keeps it inside an
    existential. *)
Definition AI20_0RB1RD_1LC0RB_1RA0LD_0LC1LB : sconf := mkC StC (mkS [] [S0;S1;S1] 1 0 [S0;S0;S1]) S0 (mkS [S1] [] 0 0 []).
Definition AI21_0RB1RD_1LC0RB_1RA0LD_0LC1LB : sconf := mkC StC (mkS [] [S0;S0;S1] 1 0 [S0;S1;S1]) S0 (mkS [S1;S0] [] 0 0 []).
Definition chn2_0RB1RD_1LC0RB_1RA0LD_0LC1LB : list lstep := [SWin 1; SWinR 3; SCycL 3 0; SWin 6; SCycR 7; SWin 2].

Lemma run_inner2_0RB1RD_1LC0RB_1RA0LD_0LC1LB : srun tm false true chn2_0RB1RD_1LC0RB_1RA0LD_0LC1LB AI20_0RB1RD_1LC0RB_1RA0LD_0LC1LB = Some (AI21_0RB1RD_1LC0RB_1RA0LD_0LC1LB, 10, 12).
Proof. vm_compute. reflexivity. Qed.

(** ** The THIRD INNER anchor family -- Ap_Alph_001_011_0 at StC *)
Definition Cin3_0RB1RD_1LC0RB_1RA0LD_0LC1LB (v : positive) : cconf := (StC, (Ap_Alph_001_011_0 v ++ [S0;S1], S0, [S1])).
Local Notation Cin3 := Cin3_0RB1RD_1LC0RB_1RA0LD_0LC1LB.

(** [E (2^n) = A^n C]: the value this family's count starts at. *)
Lemma epow23_0RB1RD_1LC0RB_1RA0LD_0LC1LB : forall n, Ap_Alph_001_011_0 (pow2 n) = rep [S0;S0;S1] n ++ [S0].
Proof. induction n; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.

(** Its own INTERIOR lap -- ordinary and affine.  Iterating it to the fill is
    where a [Theta(2^j)] lives, and [inner_to_fill_lift] keeps it inside an
    existential. *)
Definition AI30_0RB1RD_1LC0RB_1RA0LD_0LC1LB : sconf := mkC StC (mkS [] [S0;S1;S1] 1 0 [S0;S0;S1]) S0 (mkS [S1] [] 0 0 []).
Definition AI31_0RB1RD_1LC0RB_1RA0LD_0LC1LB : sconf := mkC StC (mkS [] [S0;S0;S1] 1 0 [S0;S1;S1]) S0 (mkS [S1;S0] [] 0 0 []).
Definition chn3_0RB1RD_1LC0RB_1RA0LD_0LC1LB : list lstep := [SWin 1; SWinR 3; SCycL 3 0; SWin 6; SCycR 7; SWin 2].

Lemma run_inner3_0RB1RD_1LC0RB_1RA0LD_0LC1LB : srun tm false true chn3_0RB1RD_1LC0RB_1RA0LD_0LC1LB AI30_0RB1RD_1LC0RB_1RA0LD_0LC1LB = Some (AI31_0RB1RD_1LC0RB_1RA0LD_0LC1LB, 10, 12).
Proof. vm_compute. reflexivity. Qed.

(** ** The FOURTH INNER anchor family -- Ap_Alph_001_011_0 at StC *)
Definition Cin4_0RB1RD_1LC0RB_1RA0LD_0LC1LB (v : positive) : cconf := (StC, (Ap_Alph_001_011_0 v ++ [S1;S1], S0, [S1])).
Local Notation Cin4 := Cin4_0RB1RD_1LC0RB_1RA0LD_0LC1LB.

(** [E (2^n) = A^n C]: the value this family's count starts at. *)
Lemma epow24_0RB1RD_1LC0RB_1RA0LD_0LC1LB : forall n, Ap_Alph_001_011_0 (pow2 n) = rep [S0;S0;S1] n ++ [S0].
Proof. induction n; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.

(** Its own INTERIOR lap -- ordinary and affine.  Iterating it to the fill is
    where a [Theta(2^j)] lives, and [inner_to_fill_lift] keeps it inside an
    existential. *)
Definition AI40_0RB1RD_1LC0RB_1RA0LD_0LC1LB : sconf := mkC StC (mkS [] [S0;S1;S1] 1 0 [S0;S0;S1]) S0 (mkS [S1] [] 0 0 []).
Definition AI41_0RB1RD_1LC0RB_1RA0LD_0LC1LB : sconf := mkC StC (mkS [] [S0;S0;S1] 1 0 [S0;S1;S1]) S0 (mkS [S1;S0] [] 0 0 []).
Definition chn4_0RB1RD_1LC0RB_1RA0LD_0LC1LB : list lstep := [SWin 1; SWinR 3; SCycL 3 0; SWin 6; SCycR 7; SWin 2].

Lemma run_inner4_0RB1RD_1LC0RB_1RA0LD_0LC1LB : srun tm false true chn4_0RB1RD_1LC0RB_1RA0LD_0LC1LB AI40_0RB1RD_1LC0RB_1RA0LD_0LC1LB = Some (AI41_0RB1RD_1LC0RB_1RA0LD_0LC1LB, 10, 12).
Proof. vm_compute. reflexivity. Qed.

(** *** boot: the outer overflow anchor -> the first inner anchor at [pow2 j] *)
Definition BB1_0RB1RD_1LC0RB_1RA0LD_0LC1LB : sconf := mkC StC (mkS [] [S0;S0;S1] 1 0 [S0;S0;S1;S1]) S0 (mkS [S1] [] 0 0 []).
Definition chb_0RB1RD_1LC0RB_1RA0LD_0LC1LB : list lstep := [SCycL 3 0; SWin 2; SWinL 8; SCycR 7; SWin 1; SWinR 2; SUnrotL 1].

Lemma run_boot_0RB1RD_1LC0RB_1RA0LD_0LC1LB : srun tm true true chb_0RB1RD_1LC0RB_1RA0LD_0LC1LB B0_0RB1RD_1LC0RB_1RA0LD_0LC1LB = Some (BB1_0RB1RD_1LC0RB_1RA0LD_0LC1LB, 10, 13).
Proof. vm_compute. reflexivity. Qed.

(** *** shift: count 1's all-ones fill -> count 2's anchor.
    WAVE18 section 4c -- "count 8->15, shift, count 8->15 again". *)
Definition BM0_0RB1RD_1LC0RB_1RA0LD_0LC1LB : sconf := mkC StC (mkS [] [S0;S1;S1] 1 0 [S0;S0;S1;S1]) S0 (mkS [S1] [] 0 0 []).
Definition BM1_0RB1RD_1LC0RB_1RA0LD_0LC1LB : sconf := mkC StC (mkS [] [S0;S0;S1] 1 0 [S0;S1;S1;S1]) S0 (mkS [S1;S0] [] 0 0 []).
Definition chm_0RB1RD_1LC0RB_1RA0LD_0LC1LB : list lstep := [SWin 1; SWinR 3; SCycL 3 0; SWin 6; SCycR 7; SWin 2].

Lemma run_shift_0RB1RD_1LC0RB_1RA0LD_0LC1LB : srun tm true true chm_0RB1RD_1LC0RB_1RA0LD_0LC1LB BM0_0RB1RD_1LC0RB_1RA0LD_0LC1LB = Some (BM1_0RB1RD_1LC0RB_1RA0LD_0LC1LB, 10, 12).
Proof. vm_compute. reflexivity. Qed.

(** *** shift: count 2's all-ones fill -> count 3's anchor.
    WAVE18 section 4c -- "count 8->15, shift, count 8->15 again". *)
Definition BM30_0RB1RD_1LC0RB_1RA0LD_0LC1LB : sconf := mkC StC (mkS [] [S0;S1;S1] 1 0 [S0;S1;S1;S1]) S0 (mkS [S1] [] 0 0 []).
Definition BM31_0RB1RD_1LC0RB_1RA0LD_0LC1LB : sconf := mkC StC (mkS [] [S0;S0;S1] 1 0 [S0;S0;S1;S0]) S0 (mkS [S1;S0] [] 0 0 []).
Definition chm3_0RB1RD_1LC0RB_1RA0LD_0LC1LB : list lstep := [SWin 1; SWinR 3; SCycL 3 0; SWin 12; SCycR 7; SWin 2].

Lemma run_shift3_0RB1RD_1LC0RB_1RA0LD_0LC1LB : srun tm true true chm3_0RB1RD_1LC0RB_1RA0LD_0LC1LB BM30_0RB1RD_1LC0RB_1RA0LD_0LC1LB = Some (BM31_0RB1RD_1LC0RB_1RA0LD_0LC1LB, 10, 18).
Proof. vm_compute. reflexivity. Qed.

(** *** shift: count 3's all-ones fill -> count 4's anchor.
    WAVE18 section 4c -- "count 8->15, shift, count 8->15 again". *)
Definition BM40_0RB1RD_1LC0RB_1RA0LD_0LC1LB : sconf := mkC StC (mkS [] [S0;S1;S1] 1 0 [S0;S0;S1]) S0 (mkS [S1] [] 0 0 []).
Definition BM41_0RB1RD_1LC0RB_1RA0LD_0LC1LB : sconf := mkC StC (mkS [] [S0;S0;S1] 1 0 [S0;S1;S1]) S0 (mkS [S1;S0] [] 0 0 []).
Definition chm4_0RB1RD_1LC0RB_1RA0LD_0LC1LB : list lstep := [SWin 1; SWinR 3; SCycL 3 0; SWin 6; SCycR 7; SWin 2].

Lemma run_shift4_0RB1RD_1LC0RB_1RA0LD_0LC1LB : srun tm true true chm4_0RB1RD_1LC0RB_1RA0LD_0LC1LB BM40_0RB1RD_1LC0RB_1RA0LD_0LC1LB = Some (BM41_0RB1RD_1LC0RB_1RA0LD_0LC1LB, 10, 12).
Proof. vm_compute. reflexivity. Qed.

(** *** exit: the last inner all-ones fill -> the outer successor *)
Definition BE0_0RB1RD_1LC0RB_1RA0LD_0LC1LB : sconf := mkC StC (mkS [] [S0;S1;S1] 1 0 [S0;S1;S1]) S0 (mkS [S1] [] 0 0 []).
Definition che_0RB1RD_1LC0RB_1RA0LD_0LC1LB : list lstep := [SWin 1; SWinR 3; SCycL 3 0; SWin 3; SWinL 13; SCycR 7; SWin 6; SRotL 1; SWin 1; SRotL 3; SFoldL 1].

Lemma run_exit_0RB1RD_1LC0RB_1RA0LD_0LC1LB : srun tm true true che_0RB1RD_1LC0RB_1RA0LD_0LC1LB BE0_0RB1RD_1LC0RB_1RA0LD_0LC1LB = Some (B1_0RB1RD_1LC0RB_1RA0LD_0LC1LB, 10, 27).
Proof. vm_compute. reflexivity. Qed.

(** ** Anchor glue -- the only per-machine mathematics *)

Lemma gsi_0RB1RD_1LC0RB_1RA0LD_0LC1LB : forall p j q0, cview p = (j, Some q0) ->
  Cc p = cden (Ap_Alph_010_110_1 q0 ++ [S0]) [] j A0_0RB1RD_1LC0RB_1RA0LD_0LC1LB.
Proof.
  intros p j q0 E. destruct (Alph_010_110_1.cview_some_Alph_010_110_1 p j q0 E) as (H1 & _).
  unfold Cc_0RB1RD_1LC0RB_1RA0LD_0LC1LB, cden, A0_0RB1RD_1LC0RB_1RA0LD_0LC1LB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  rewrite H1. first [ rewrite <- (app_assoc (rep [S1;S1;S0] j)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

(** The lap ends on [S1;S0;S0] where the anchor has [S1] -- one trailing blank,
    which [lift] cannot see. *)
Lemma gei_0RB1RD_1LC0RB_1RA0LD_0LC1LB : forall p j q0, cview p = (j, Some q0) ->
  lift (cden (Ap_Alph_010_110_1 q0 ++ [S0]) [] j A1_0RB1RD_1LC0RB_1RA0LD_0LC1LB) = lift (Cc (Pos.succ p)).
Proof.
  intros p j q0 E. destruct (Alph_010_110_1.cview_some_Alph_010_110_1 p j q0 E) as (_ & H2).
  unfold Cc_0RB1RD_1LC0RB_1RA0LD_0LC1LB, cden, A1_0RB1RD_1LC0RB_1RA0LD_0LC1LB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  replace (0 * j + 0) with 0 by lia.
  cbn [rep app]. rewrite ?app_nil_r.
  change ([S1;S0;S0]) with ((([S1]) ++ [S0]) ++ [S0]).
  rewrite !lift_app_blank.
  rewrite H2. first [ rewrite <- (app_assoc (rep [S0;S1;S0] j)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapi_0RB1RD_1LC0RB_1RA0LD_0LC1LB : forall p j q0, cview p = (j, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof.
  intros p j q0 E.
  exists (10 * j + 12), (cden (Ap_Alph_010_110_1 q0 ++ [S0]) [] j A1_0RB1RD_1LC0RB_1RA0LD_0LC1LB).
  split; [lia|]. split; [| exact (gei_0RB1RD_1LC0RB_1RA0LD_0LC1LB p j q0 E)].
  rewrite (gsi_0RB1RD_1LC0RB_1RA0LD_0LC1LB p j q0 E).
  exact (srun_sound tm false true chi_0RB1RD_1LC0RB_1RA0LD_0LC1LB A0_0RB1RD_1LC0RB_1RA0LD_0LC1LB A1_0RB1RD_1LC0RB_1RA0LD_0LC1LB 10 12
           run_int_0RB1RD_1LC0RB_1RA0LD_0LC1LB (Ap_Alph_010_110_1 q0 ++ [S0]) [] j
           ltac:(discriminate) ltac:(reflexivity)).
Qed.

Lemma gso_0RB1RD_1LC0RB_1RA0LD_0LC1LB : forall p j, cview p = (S j, None) ->
  Cc p = cden [] [] j B0_0RB1RD_1LC0RB_1RA0LD_0LC1LB.
Proof.
  intros p j E. destruct (Alph_010_110_1.cview_none_Alph_010_110_1 p j E) as (H1 & _).
  unfold Cc_0RB1RD_1LC0RB_1RA0LD_0LC1LB, cden, B0_0RB1RD_1LC0RB_1RA0LD_0LC1LB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with (j) by lia.
  rewrite H1; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lbl_0RB1RD_1LC0RB_1RA0LD_0LC1LB : forall q l h r, lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.

Lemma geo_0RB1RD_1LC0RB_1RA0LD_0LC1LB : forall p j, cview p = (S j, None) ->
  lift (cden [] [] j B1_0RB1RD_1LC0RB_1RA0LD_0LC1LB) = lift (Cc (Pos.succ p)).
Proof.
  intros p j E. destruct (Alph_010_110_1.cview_none_Alph_010_110_1 p j E) as (_ & H2).
  assert (HD : cden [] [] j B1_0RB1RD_1LC0RB_1RA0LD_0LC1LB
             = (StB, (rep [S0;S1;S0] (S j) ++ [S1], S0, (([S1]) ++ [S0]) ++ [S0]))).
  { unfold cden, B1_0RB1RD_1LC0RB_1RA0LD_0LC1LB, sden, sflat;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 1) with (S j) by lia.
    replace (0 * j + 0) with 0 by lia.
    cbn [rep app]. first [ reflexivity
      | rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  assert (HC : Cc (Pos.succ p) = (StB, ((rep [S0;S1;S0] (S j) ++ [S1]) ++ [S0], S0, [S1]))).
  { unfold Cc_0RB1RD_1LC0RB_1RA0LD_0LC1LB. rewrite H2.
    first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ]. }
  rewrite HD, HC. rewrite !lift_app_blank. rewrite !lbl_0RB1RD_1LC0RB_1RA0LD_0LC1LB. reflexivity.
Qed.

Lemma gsn_0RB1RD_1LC0RB_1RA0LD_0LC1LB : forall v i q0, cview v = (i, Some q0) ->
  Cin v = cden (Ap_Alph_001_011_0 q0 ++ [S0;S1;S1]) [] i AI0_0RB1RD_1LC0RB_1RA0LD_0LC1LB.
Proof.
  intros v i q0 E. destruct (Alph_001_011_0.cview_some_Alph_001_011_0 v i q0 E) as (H1 & _).
  unfold Cin_0RB1RD_1LC0RB_1RA0LD_0LC1LB, cden, AI0_0RB1RD_1LC0RB_1RA0LD_0LC1LB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia.
  rewrite H1. first [ rewrite <- (app_assoc (rep [S0;S1;S1] i)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma gen_0RB1RD_1LC0RB_1RA0LD_0LC1LB : forall v i q0, cview v = (i, Some q0) ->
  lift (cden (Ap_Alph_001_011_0 q0 ++ [S0;S1;S1]) [] i AI1_0RB1RD_1LC0RB_1RA0LD_0LC1LB) = lift (Cin (Pos.succ v)).
Proof.
  intros v i q0 E. destruct (Alph_001_011_0.cview_some_Alph_001_011_0 v i q0 E) as (_ & H2).
  unfold Cin_0RB1RD_1LC0RB_1RA0LD_0LC1LB, cden, AI1_0RB1RD_1LC0RB_1RA0LD_0LC1LB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia.
  replace (0 * i + 0) with 0 by lia.
  cbn [rep app]. rewrite ?app_nil_r.
  change ([S1;S0]) with (([S1]) ++ [S0]).
  rewrite !lift_app_blank.
  rewrite H2. first [ rewrite <- (app_assoc (rep [S0;S0;S1] i)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapin_0RB1RD_1LC0RB_1RA0LD_0LC1LB : forall v i q0, cview v = (i, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cin v) = Some c'
               /\ lift c' = lift (Cin (Pos.succ v)).
Proof.
  intros v i q0 E.
  exists (10 * i + 12), (cden (Ap_Alph_001_011_0 q0 ++ [S0;S1;S1]) [] i AI1_0RB1RD_1LC0RB_1RA0LD_0LC1LB).
  split; [lia|]. split; [| exact (gen_0RB1RD_1LC0RB_1RA0LD_0LC1LB v i q0 E)].
  rewrite (gsn_0RB1RD_1LC0RB_1RA0LD_0LC1LB v i q0 E).
  exact (srun_sound tm false true chn_0RB1RD_1LC0RB_1RA0LD_0LC1LB AI0_0RB1RD_1LC0RB_1RA0LD_0LC1LB AI1_0RB1RD_1LC0RB_1RA0LD_0LC1LB 10 12
           run_inner_0RB1RD_1LC0RB_1RA0LD_0LC1LB (Ap_Alph_001_011_0 q0 ++ [S0;S1;S1]) [] i
           ltac:(discriminate) ltac:(reflexivity)).
Qed.

(** The chain into this family lands on its anchor up to 0/0
    trailing blanks. *)
Lemma gbo_0RB1RD_1LC0RB_1RA0LD_0LC1LB : forall j, lift (cden [] [] j BB1_0RB1RD_1LC0RB_1RA0LD_0LC1LB) = lift (Cin (pow2 j)).
Proof.
  intro j.
  assert (HD : cden [] [] j BB1_0RB1RD_1LC0RB_1RA0LD_0LC1LB = (StC, (rep [S0;S0;S1] j ++ [S0;S0;S1;S1], S0, [S1]))).
  { unfold cden, BB1_0RB1RD_1LC0RB_1RA0LD_0LC1LB, sden;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 0) with j by lia.
    cbn [rep app]. rewrite <- ?app_assoc. cbn [app]. rewrite ?app_nil_r.
    reflexivity. }
  assert (HC : Cin (pow2 j) = (StC, (rep [S0;S0;S1] j ++ [S0;S0;S1;S1], S0, [S1]))).
  { unfold Cin_0RB1RD_1LC0RB_1RA0LD_0LC1LB. rewrite epow2_0RB1RD_1LC0RB_1RA0LD_0LC1LB.
    first [ rewrite <- app_assoc; reflexivity
          | rewrite ?app_nil_r; reflexivity
          | cbn [app]; rewrite <- ?app_assoc; cbn [app];
            rewrite ?app_nil_r; reflexivity ]. }
  rewrite HD, HC. rewrite ?lbl_0RB1RD_1LC0RB_1RA0LD_0LC1LB. rewrite ?lift_app_blank. reflexivity.
Qed.

(** This family's all-ones fill IS the next chain's start.  [cview (fill
    (pow2 j)) = (S j, None)] ([NestedLapLift.cview_fill_pow2]), so the
    family's own overflow decomposition names the word. *)
Lemma gxi_0RB1RD_1LC0RB_1RA0LD_0LC1LB : forall j, Cin (fill (pow2 j)) = cden [] [] j BM0_0RB1RD_1LC0RB_1RA0LD_0LC1LB.
Proof.
  intro j.
  destruct (Alph_001_011_0.cview_none_Alph_001_011_0 (fill (pow2 j)) j (cview_fill_pow2 j)) as (H1 & _).
  unfold Cin_0RB1RD_1LC0RB_1RA0LD_0LC1LB, cden, BM0_0RB1RD_1LC0RB_1RA0LD_0LC1LB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  replace (0 * j + 0) with 0 by lia.
  rewrite H1; cbn [rep app]. first [ rewrite <- ?app_assoc; cbn [app];
        rewrite ?app_nil_r; reflexivity | reflexivity ].
Qed.

Lemma gsn2_0RB1RD_1LC0RB_1RA0LD_0LC1LB : forall v i q0, cview v = (i, Some q0) ->
  Cin2 v = cden (Ap_Alph_001_011_0 q0 ++ [S1;S1;S1]) [] i AI20_0RB1RD_1LC0RB_1RA0LD_0LC1LB.
Proof.
  intros v i q0 E. destruct (Alph_001_011_0.cview_some_Alph_001_011_0 v i q0 E) as (H1 & _).
  unfold Cin2_0RB1RD_1LC0RB_1RA0LD_0LC1LB, cden, AI20_0RB1RD_1LC0RB_1RA0LD_0LC1LB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia.
  rewrite H1. first [ rewrite <- (app_assoc (rep [S0;S1;S1] i)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma gen2_0RB1RD_1LC0RB_1RA0LD_0LC1LB : forall v i q0, cview v = (i, Some q0) ->
  lift (cden (Ap_Alph_001_011_0 q0 ++ [S1;S1;S1]) [] i AI21_0RB1RD_1LC0RB_1RA0LD_0LC1LB) = lift (Cin2 (Pos.succ v)).
Proof.
  intros v i q0 E. destruct (Alph_001_011_0.cview_some_Alph_001_011_0 v i q0 E) as (_ & H2).
  unfold Cin2_0RB1RD_1LC0RB_1RA0LD_0LC1LB, cden, AI21_0RB1RD_1LC0RB_1RA0LD_0LC1LB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia.
  replace (0 * i + 0) with 0 by lia.
  cbn [rep app]. rewrite ?app_nil_r.
  change ([S1;S0]) with (([S1]) ++ [S0]).
  rewrite !lift_app_blank.
  rewrite H2. first [ rewrite <- (app_assoc (rep [S0;S0;S1] i)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapin2_0RB1RD_1LC0RB_1RA0LD_0LC1LB : forall v i q0, cview v = (i, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cin2 v) = Some c'
               /\ lift c' = lift (Cin2 (Pos.succ v)).
Proof.
  intros v i q0 E.
  exists (10 * i + 12), (cden (Ap_Alph_001_011_0 q0 ++ [S1;S1;S1]) [] i AI21_0RB1RD_1LC0RB_1RA0LD_0LC1LB).
  split; [lia|]. split; [| exact (gen2_0RB1RD_1LC0RB_1RA0LD_0LC1LB v i q0 E)].
  rewrite (gsn2_0RB1RD_1LC0RB_1RA0LD_0LC1LB v i q0 E).
  exact (srun_sound tm false true chn2_0RB1RD_1LC0RB_1RA0LD_0LC1LB AI20_0RB1RD_1LC0RB_1RA0LD_0LC1LB AI21_0RB1RD_1LC0RB_1RA0LD_0LC1LB 10 12
           run_inner2_0RB1RD_1LC0RB_1RA0LD_0LC1LB (Ap_Alph_001_011_0 q0 ++ [S1;S1;S1]) [] i
           ltac:(discriminate) ltac:(reflexivity)).
Qed.

(** The chain into this family lands on its anchor up to 0/1
    trailing blanks. *)
Lemma gbo2_0RB1RD_1LC0RB_1RA0LD_0LC1LB : forall j, lift (cden [] [] j BM1_0RB1RD_1LC0RB_1RA0LD_0LC1LB) = lift (Cin2 (pow2 j)).
Proof.
  intro j.
  assert (HD : cden [] [] j BM1_0RB1RD_1LC0RB_1RA0LD_0LC1LB = (StC, (rep [S0;S0;S1] j ++ [S0;S1;S1;S1], S0, ([S1]) ++ [S0]))).
  { unfold cden, BM1_0RB1RD_1LC0RB_1RA0LD_0LC1LB, sden;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 0) with j by lia.
    cbn [rep app]. rewrite <- ?app_assoc. cbn [app]. rewrite ?app_nil_r.
    reflexivity. }
  assert (HC : Cin2 (pow2 j) = (StC, (rep [S0;S0;S1] j ++ [S0;S1;S1;S1], S0, [S1]))).
  { unfold Cin2_0RB1RD_1LC0RB_1RA0LD_0LC1LB. rewrite epow22_0RB1RD_1LC0RB_1RA0LD_0LC1LB.
    first [ rewrite <- app_assoc; reflexivity
          | rewrite ?app_nil_r; reflexivity
          | cbn [app]; rewrite <- ?app_assoc; cbn [app];
            rewrite ?app_nil_r; reflexivity ]. }
  rewrite HD, HC. rewrite ?lbl_0RB1RD_1LC0RB_1RA0LD_0LC1LB. rewrite ?lift_app_blank. reflexivity.
Qed.

(** This family's all-ones fill IS the next chain's start.  [cview (fill
    (pow2 j)) = (S j, None)] ([NestedLapLift.cview_fill_pow2]), so the
    family's own overflow decomposition names the word. *)
Lemma gxi2_0RB1RD_1LC0RB_1RA0LD_0LC1LB : forall j, Cin2 (fill (pow2 j)) = cden [] [] j BM30_0RB1RD_1LC0RB_1RA0LD_0LC1LB.
Proof.
  intro j.
  destruct (Alph_001_011_0.cview_none_Alph_001_011_0 (fill (pow2 j)) j (cview_fill_pow2 j)) as (H1 & _).
  unfold Cin2_0RB1RD_1LC0RB_1RA0LD_0LC1LB, cden, BM30_0RB1RD_1LC0RB_1RA0LD_0LC1LB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  replace (0 * j + 0) with 0 by lia.
  rewrite H1; cbn [rep app]. first [ rewrite <- ?app_assoc; cbn [app];
        rewrite ?app_nil_r; reflexivity | reflexivity ].
Qed.

Lemma gsn3_0RB1RD_1LC0RB_1RA0LD_0LC1LB : forall v i q0, cview v = (i, Some q0) ->
  Cin3 v = cden (Ap_Alph_001_011_0 q0 ++ [S0;S1]) [] i AI30_0RB1RD_1LC0RB_1RA0LD_0LC1LB.
Proof.
  intros v i q0 E. destruct (Alph_001_011_0.cview_some_Alph_001_011_0 v i q0 E) as (H1 & _).
  unfold Cin3_0RB1RD_1LC0RB_1RA0LD_0LC1LB, cden, AI30_0RB1RD_1LC0RB_1RA0LD_0LC1LB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia.
  rewrite H1. first [ rewrite <- (app_assoc (rep [S0;S1;S1] i)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma gen3_0RB1RD_1LC0RB_1RA0LD_0LC1LB : forall v i q0, cview v = (i, Some q0) ->
  lift (cden (Ap_Alph_001_011_0 q0 ++ [S0;S1]) [] i AI31_0RB1RD_1LC0RB_1RA0LD_0LC1LB) = lift (Cin3 (Pos.succ v)).
Proof.
  intros v i q0 E. destruct (Alph_001_011_0.cview_some_Alph_001_011_0 v i q0 E) as (_ & H2).
  unfold Cin3_0RB1RD_1LC0RB_1RA0LD_0LC1LB, cden, AI31_0RB1RD_1LC0RB_1RA0LD_0LC1LB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia.
  replace (0 * i + 0) with 0 by lia.
  cbn [rep app]. rewrite ?app_nil_r.
  change ([S1;S0]) with (([S1]) ++ [S0]).
  rewrite !lift_app_blank.
  rewrite H2. first [ rewrite <- (app_assoc (rep [S0;S0;S1] i)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapin3_0RB1RD_1LC0RB_1RA0LD_0LC1LB : forall v i q0, cview v = (i, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cin3 v) = Some c'
               /\ lift c' = lift (Cin3 (Pos.succ v)).
Proof.
  intros v i q0 E.
  exists (10 * i + 12), (cden (Ap_Alph_001_011_0 q0 ++ [S0;S1]) [] i AI31_0RB1RD_1LC0RB_1RA0LD_0LC1LB).
  split; [lia|]. split; [| exact (gen3_0RB1RD_1LC0RB_1RA0LD_0LC1LB v i q0 E)].
  rewrite (gsn3_0RB1RD_1LC0RB_1RA0LD_0LC1LB v i q0 E).
  exact (srun_sound tm false true chn3_0RB1RD_1LC0RB_1RA0LD_0LC1LB AI30_0RB1RD_1LC0RB_1RA0LD_0LC1LB AI31_0RB1RD_1LC0RB_1RA0LD_0LC1LB 10 12
           run_inner3_0RB1RD_1LC0RB_1RA0LD_0LC1LB (Ap_Alph_001_011_0 q0 ++ [S0;S1]) [] i
           ltac:(discriminate) ltac:(reflexivity)).
Qed.

(** The chain into this family lands on its anchor up to 1/1
    trailing blanks. *)
Lemma gbo3_0RB1RD_1LC0RB_1RA0LD_0LC1LB : forall j, lift (cden [] [] j BM31_0RB1RD_1LC0RB_1RA0LD_0LC1LB) = lift (Cin3 (pow2 j)).
Proof.
  intro j.
  assert (HD : cden [] [] j BM31_0RB1RD_1LC0RB_1RA0LD_0LC1LB = (StC, ((rep [S0;S0;S1] j ++ [S0;S0;S1]) ++ [S0], S0, ([S1]) ++ [S0]))).
  { unfold cden, BM31_0RB1RD_1LC0RB_1RA0LD_0LC1LB, sden;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 0) with j by lia.
    cbn [rep app]. rewrite <- ?app_assoc. cbn [app]. rewrite ?app_nil_r.
    reflexivity. }
  assert (HC : Cin3 (pow2 j) = (StC, (rep [S0;S0;S1] j ++ [S0;S0;S1], S0, [S1]))).
  { unfold Cin3_0RB1RD_1LC0RB_1RA0LD_0LC1LB. rewrite epow23_0RB1RD_1LC0RB_1RA0LD_0LC1LB.
    first [ rewrite <- app_assoc; reflexivity
          | rewrite ?app_nil_r; reflexivity
          | cbn [app]; rewrite <- ?app_assoc; cbn [app];
            rewrite ?app_nil_r; reflexivity ]. }
  rewrite HD, HC. rewrite ?lbl_0RB1RD_1LC0RB_1RA0LD_0LC1LB. rewrite ?lift_app_blank. reflexivity.
Qed.

(** This family's all-ones fill IS the next chain's start.  [cview (fill
    (pow2 j)) = (S j, None)] ([NestedLapLift.cview_fill_pow2]), so the
    family's own overflow decomposition names the word. *)
Lemma gxi3_0RB1RD_1LC0RB_1RA0LD_0LC1LB : forall j, Cin3 (fill (pow2 j)) = cden [] [] j BM40_0RB1RD_1LC0RB_1RA0LD_0LC1LB.
Proof.
  intro j.
  destruct (Alph_001_011_0.cview_none_Alph_001_011_0 (fill (pow2 j)) j (cview_fill_pow2 j)) as (H1 & _).
  unfold Cin3_0RB1RD_1LC0RB_1RA0LD_0LC1LB, cden, BM40_0RB1RD_1LC0RB_1RA0LD_0LC1LB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  replace (0 * j + 0) with 0 by lia.
  rewrite H1; cbn [rep app]. first [ rewrite <- ?app_assoc; cbn [app];
        rewrite ?app_nil_r; reflexivity | reflexivity ].
Qed.

Lemma gsn4_0RB1RD_1LC0RB_1RA0LD_0LC1LB : forall v i q0, cview v = (i, Some q0) ->
  Cin4 v = cden (Ap_Alph_001_011_0 q0 ++ [S1;S1]) [] i AI40_0RB1RD_1LC0RB_1RA0LD_0LC1LB.
Proof.
  intros v i q0 E. destruct (Alph_001_011_0.cview_some_Alph_001_011_0 v i q0 E) as (H1 & _).
  unfold Cin4_0RB1RD_1LC0RB_1RA0LD_0LC1LB, cden, AI40_0RB1RD_1LC0RB_1RA0LD_0LC1LB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia.
  rewrite H1. first [ rewrite <- (app_assoc (rep [S0;S1;S1] i)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma gen4_0RB1RD_1LC0RB_1RA0LD_0LC1LB : forall v i q0, cview v = (i, Some q0) ->
  lift (cden (Ap_Alph_001_011_0 q0 ++ [S1;S1]) [] i AI41_0RB1RD_1LC0RB_1RA0LD_0LC1LB) = lift (Cin4 (Pos.succ v)).
Proof.
  intros v i q0 E. destruct (Alph_001_011_0.cview_some_Alph_001_011_0 v i q0 E) as (_ & H2).
  unfold Cin4_0RB1RD_1LC0RB_1RA0LD_0LC1LB, cden, AI41_0RB1RD_1LC0RB_1RA0LD_0LC1LB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia.
  replace (0 * i + 0) with 0 by lia.
  cbn [rep app]. rewrite ?app_nil_r.
  change ([S1;S0]) with (([S1]) ++ [S0]).
  rewrite !lift_app_blank.
  rewrite H2. first [ rewrite <- (app_assoc (rep [S0;S0;S1] i)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapin4_0RB1RD_1LC0RB_1RA0LD_0LC1LB : forall v i q0, cview v = (i, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cin4 v) = Some c'
               /\ lift c' = lift (Cin4 (Pos.succ v)).
Proof.
  intros v i q0 E.
  exists (10 * i + 12), (cden (Ap_Alph_001_011_0 q0 ++ [S1;S1]) [] i AI41_0RB1RD_1LC0RB_1RA0LD_0LC1LB).
  split; [lia|]. split; [| exact (gen4_0RB1RD_1LC0RB_1RA0LD_0LC1LB v i q0 E)].
  rewrite (gsn4_0RB1RD_1LC0RB_1RA0LD_0LC1LB v i q0 E).
  exact (srun_sound tm false true chn4_0RB1RD_1LC0RB_1RA0LD_0LC1LB AI40_0RB1RD_1LC0RB_1RA0LD_0LC1LB AI41_0RB1RD_1LC0RB_1RA0LD_0LC1LB 10 12
           run_inner4_0RB1RD_1LC0RB_1RA0LD_0LC1LB (Ap_Alph_001_011_0 q0 ++ [S1;S1]) [] i
           ltac:(discriminate) ltac:(reflexivity)).
Qed.

(** The chain into this family lands on its anchor up to 0/1
    trailing blanks. *)
Lemma gbo4_0RB1RD_1LC0RB_1RA0LD_0LC1LB : forall j, lift (cden [] [] j BM41_0RB1RD_1LC0RB_1RA0LD_0LC1LB) = lift (Cin4 (pow2 j)).
Proof.
  intro j.
  assert (HD : cden [] [] j BM41_0RB1RD_1LC0RB_1RA0LD_0LC1LB = (StC, (rep [S0;S0;S1] j ++ [S0;S1;S1], S0, ([S1]) ++ [S0]))).
  { unfold cden, BM41_0RB1RD_1LC0RB_1RA0LD_0LC1LB, sden;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 0) with j by lia.
    cbn [rep app]. rewrite <- ?app_assoc. cbn [app]. rewrite ?app_nil_r.
    reflexivity. }
  assert (HC : Cin4 (pow2 j) = (StC, (rep [S0;S0;S1] j ++ [S0;S1;S1], S0, [S1]))).
  { unfold Cin4_0RB1RD_1LC0RB_1RA0LD_0LC1LB. rewrite epow24_0RB1RD_1LC0RB_1RA0LD_0LC1LB.
    first [ rewrite <- app_assoc; reflexivity
          | rewrite ?app_nil_r; reflexivity
          | cbn [app]; rewrite <- ?app_assoc; cbn [app];
            rewrite ?app_nil_r; reflexivity ]. }
  rewrite HD, HC. rewrite ?lbl_0RB1RD_1LC0RB_1RA0LD_0LC1LB. rewrite ?lift_app_blank. reflexivity.
Qed.

(** This family's all-ones fill IS the next chain's start.  [cview (fill
    (pow2 j)) = (S j, None)] ([NestedLapLift.cview_fill_pow2]), so the
    family's own overflow decomposition names the word. *)
Lemma gxi4_0RB1RD_1LC0RB_1RA0LD_0LC1LB : forall j, Cin4 (fill (pow2 j)) = cden [] [] j BE0_0RB1RD_1LC0RB_1RA0LD_0LC1LB.
Proof.
  intro j.
  destruct (Alph_001_011_0.cview_none_Alph_001_011_0 (fill (pow2 j)) j (cview_fill_pow2 j)) as (H1 & _).
  unfold Cin4_0RB1RD_1LC0RB_1RA0LD_0LC1LB, cden, BE0_0RB1RD_1LC0RB_1RA0LD_0LC1LB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  replace (0 * j + 0) with 0 by lia.
  rewrite H1; cbn [rep app]. first [ rewrite <- ?app_assoc; cbn [app];
        rewrite ?app_nil_r; reflexivity | reflexivity ].
Qed.

(** The interior lap, restated up to [lift] -- what [vis_via_ovf_lift] and
    [vis_via_fill] consume. *)
Lemma lapil_0RB1RD_1LC0RB_1RA0LD_0LC1LB : forall p j q0, cview p = (j, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof. exact lapi_0RB1RD_1LC0RB_1RA0LD_0LC1LB. Qed.

(** The outer OVERFLOW branch, composed.  The exponential cost is the
    [exists n] inside [inner_to_fill_lift]; no formula for it is ever
    written. *)
Lemma lapo_0RB1RD_1LC0RB_1RA0LD_0LC1LB : forall p j, cview p = (S j, None) ->
  exists n c', csteps tm n (Cc p) = Some c'
          /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intros p j E.
  apply (nested_overflow_lift tm Cc Cin4 lapin4_0RB1RD_1LC0RB_1RA0LD_0LC1LB p (pow2 j)).
  - assert (HB1 : exists n c, 0 < n /\ csteps tm n (Cc p) = Some c
                  /\ lift c = lift (Cin (pow2 j))).
    { exists (10 * j + 13), (cden [] [] j BB1_0RB1RD_1LC0RB_1RA0LD_0LC1LB).
      split; [lia|]. split; [| exact (gbo_0RB1RD_1LC0RB_1RA0LD_0LC1LB j)].
      rewrite (gso_0RB1RD_1LC0RB_1RA0LD_0LC1LB p j E).
      exact (srun_sound tm true true chb_0RB1RD_1LC0RB_1RA0LD_0LC1LB B0_0RB1RD_1LC0RB_1RA0LD_0LC1LB BB1_0RB1RD_1LC0RB_1RA0LD_0LC1LB 10 13
               run_boot_0RB1RD_1LC0RB_1RA0LD_0LC1LB [] [] j ltac:(reflexivity) ltac:(reflexivity)). }
    assert (HB2 : exists n c, 0 < n /\ csteps tm n (Cc p) = Some c
                  /\ lift c = lift (Cin2 (pow2 j))).
    { apply (boot_via_fill tm Cc Cin Cin2 lapin_0RB1RD_1LC0RB_1RA0LD_0LC1LB p (pow2 j) (pow2 j));
        [exact HB1|].
      exists (10 * j + 12), (cden [] [] j BM1_0RB1RD_1LC0RB_1RA0LD_0LC1LB).
      split; [| exact (gbo2_0RB1RD_1LC0RB_1RA0LD_0LC1LB j)].
      rewrite (gxi_0RB1RD_1LC0RB_1RA0LD_0LC1LB j).
      exact (srun_sound tm true true chm_0RB1RD_1LC0RB_1RA0LD_0LC1LB BM0_0RB1RD_1LC0RB_1RA0LD_0LC1LB BM1_0RB1RD_1LC0RB_1RA0LD_0LC1LB 10 12
               run_shift_0RB1RD_1LC0RB_1RA0LD_0LC1LB [] [] j ltac:(reflexivity) ltac:(reflexivity)). }
    assert (HB3 : exists n c, 0 < n /\ csteps tm n (Cc p) = Some c
                  /\ lift c = lift (Cin3 (pow2 j))).
    { apply (boot_via_fill tm Cc Cin2 Cin3 lapin2_0RB1RD_1LC0RB_1RA0LD_0LC1LB p (pow2 j) (pow2 j));
        [exact HB2|].
      exists (10 * j + 18), (cden [] [] j BM31_0RB1RD_1LC0RB_1RA0LD_0LC1LB).
      split; [| exact (gbo3_0RB1RD_1LC0RB_1RA0LD_0LC1LB j)].
      rewrite (gxi2_0RB1RD_1LC0RB_1RA0LD_0LC1LB j).
      exact (srun_sound tm true true chm3_0RB1RD_1LC0RB_1RA0LD_0LC1LB BM30_0RB1RD_1LC0RB_1RA0LD_0LC1LB BM31_0RB1RD_1LC0RB_1RA0LD_0LC1LB 10 18
               run_shift3_0RB1RD_1LC0RB_1RA0LD_0LC1LB [] [] j ltac:(reflexivity) ltac:(reflexivity)). }
    assert (HB4 : exists n c, 0 < n /\ csteps tm n (Cc p) = Some c
                  /\ lift c = lift (Cin4 (pow2 j))).
    { apply (boot_via_fill tm Cc Cin3 Cin4 lapin3_0RB1RD_1LC0RB_1RA0LD_0LC1LB p (pow2 j) (pow2 j));
        [exact HB3|].
      exists (10 * j + 12), (cden [] [] j BM41_0RB1RD_1LC0RB_1RA0LD_0LC1LB).
      split; [| exact (gbo4_0RB1RD_1LC0RB_1RA0LD_0LC1LB j)].
      rewrite (gxi3_0RB1RD_1LC0RB_1RA0LD_0LC1LB j).
      exact (srun_sound tm true true chm4_0RB1RD_1LC0RB_1RA0LD_0LC1LB BM40_0RB1RD_1LC0RB_1RA0LD_0LC1LB BM41_0RB1RD_1LC0RB_1RA0LD_0LC1LB 10 12
               run_shift4_0RB1RD_1LC0RB_1RA0LD_0LC1LB [] [] j ltac:(reflexivity) ltac:(reflexivity)). }
    exact HB4.
  - exists (10 * j + 27), (cden [] [] j B1_0RB1RD_1LC0RB_1RA0LD_0LC1LB).
    split; [| exact (geo_0RB1RD_1LC0RB_1RA0LD_0LC1LB p j E)].
    rewrite (gxi4_0RB1RD_1LC0RB_1RA0LD_0LC1LB j).
    exact (srun_sound tm true true che_0RB1RD_1LC0RB_1RA0LD_0LC1LB BE0_0RB1RD_1LC0RB_1RA0LD_0LC1LB B1_0RB1RD_1LC0RB_1RA0LD_0LC1LB 10 27
             run_exit_0RB1RD_1LC0RB_1RA0LD_0LC1LB [] [] j ltac:(reflexivity) ltac:(reflexivity)).
Qed.



(** ** The lap *)

Lemma lap_0RB1RD_1LC0RB_1RA0LD_0LC1LB : forall p, exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:E. destruct oq as [q0|].
  - destruct (lapi_0RB1RD_1LC0RB_1RA0LD_0LC1LB p j q0 E) as (n & c' & Hn & Hrun & Hlift).
    exists n, c'. split; [exact Hrun | split; [exact Hlift | exact Hn]].
  - destruct (cview_pos p j E) as (j' & ->). exact (lapo_0RB1RD_1LC0RB_1RA0LD_0LC1LB p j' E).
Qed.

(** ** Bootstrap *)

Lemma boot_0RB1RD_1LC0RB_1RA0LD_0LC1LB : exists t0, stepn tm t0 InitES = Some (lift (Cc 1)).
Proof.
  exists 19.
  assert (H : match csteps tm 19 c0 with
              | Some c => ceqb c (Cc 1) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 19 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** ** Visits

    Every state fires inside the OVERFLOW lap, so one prefix chain per state
    plus [LapCertGlue.vis_via_ovf] (run interior laps until the counter
    overflows -- they close exactly) covers every anchor. *)

Lemma fireo_0RB1RD_1LC0RB_1RA0LD_0LC1LB : forall (l : list lstep) (t : Instr),
  srun_instr tm true true l B0_0RB1RD_1LC0RB_1RA0LD_0LC1LB = Some t ->
  forall p j, cview p = (S j, None) ->
  exists k c, csteps tm k (Cc p) = Some c /\ cinstr c = t.
Proof.
  intros l t Hst p j E.
  apply (fire_of_run_instr tm Cc true true l B0_0RB1RD_1LC0RB_1RA0LD_0LC1LB p j [] []);
    [exact Hst | reflexivity | reflexivity | exact (gso_0RB1RD_1LC0RB_1RA0LD_0LC1LB p j E)].
Qed.


(** ** Fires: every UNPINNED instruction fires from every anchor
    (inside the overflow lap; [LapGlueTr.fire_via_ovf] runs the
    interior laps until the counter overflows). *)

Lemma fire_0RB1RD_1LC0RB_1RA0LD_0LC1LB : forall t, ~ In t pins_0RB1RD_1LC0RB_1RA0LD_0LC1LB ->
  forall p, exists k c, csteps tm k (Cc p) = Some c /\ cinstr c = t.
Proof.
  intros t Hnp p.
  assert (Hi : forall p0 j q0, cview p0 = (j, Some q0) ->
            exists n c', 0 < n /\ csteps tm n (Cc p0) = Some c'
                         /\ lift c' = lift (Cc (Pos.succ p0)))
    by exact lapi_0RB1RD_1LC0RB_1RA0LD_0LC1LB.
  destruct t as [q b]; destruct q, b.
  - (* A0 *)
    apply (fire_csteps_of_lift tm Cc).
    apply (fire_via_ovf_lift tm Cc Hi (StA, S0)).
    intros p1 j1 E1. apply (fire_lift_of_csteps tm Cc).
    apply (fireo_0RB1RD_1LC0RB_1RA0LD_0LC1LB [SCycL 3 0; SWin 2; SWinL 2] (StA, S0) ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* A1 *)
    apply (fire_csteps_of_lift tm Cc).
    apply (fire_via_ovf_lift tm Cc Hi (StA, S1)).
    intros p1 j1 E1. apply (fire_lift_of_csteps tm Cc).
    apply (fireo_0RB1RD_1LC0RB_1RA0LD_0LC1LB [SCycL 3 0; SWin 2; SWinL 5] (StA, S1) ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* B0 *)
    apply (fire_csteps_of_lift tm Cc).
    apply (fire_via_ovf_lift tm Cc Hi (StB, S0)).
    intros p1 j1 E1. apply (fire_lift_of_csteps tm Cc).
    apply (fireo_0RB1RD_1LC0RB_1RA0LD_0LC1LB [] (StB, S0) ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* B1 *)
    apply (fire_csteps_of_lift tm Cc).
    apply (fire_via_ovf_lift tm Cc Hi (StB, S1)).
    intros p1 j1 E1. apply (fire_lift_of_csteps tm Cc).
    apply (fireo_0RB1RD_1LC0RB_1RA0LD_0LC1LB [SCycL 3 0; SWin 2; SWinL 7] (StB, S1) ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* C0 *)
    apply (fire_csteps_of_lift tm Cc).
    apply (fire_via_ovf_lift tm Cc Hi (StC, S0)).
    intros p1 j1 E1. apply (fire_lift_of_csteps tm Cc).
    apply (fireo_0RB1RD_1LC0RB_1RA0LD_0LC1LB [SCycL 3 0; SWin 2; SWinL 1] (StC, S0) ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* C1 *)
    apply (fire_csteps_of_lift tm Cc).
    apply (fire_via_ovf_lift tm Cc Hi (StC, S1)).
    intros p1 j1 E1. apply (fire_lift_of_csteps tm Cc).
    apply (fireo_0RB1RD_1LC0RB_1RA0LD_0LC1LB [SCycL 3 0; SWin 1] (StC, S1) ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* D0 *)
    apply (fire_csteps_of_lift tm Cc).
    apply (fire_via_ovf_lift tm Cc Hi (StD, S0)).
    intros p1 j1 E1. apply (fire_lift_of_csteps tm Cc).
    apply (fireo_0RB1RD_1LC0RB_1RA0LD_0LC1LB [SCycL 3 0; SWin 2] (StD, S0) ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
  - (* D1 *)
    apply (fire_csteps_of_lift tm Cc).
    apply (fire_via_ovf_lift tm Cc Hi (StD, S1)).
    intros p1 j1 E1. apply (fire_lift_of_csteps tm Cc).
    apply (fireo_0RB1RD_1LC0RB_1RA0LD_0LC1LB [SCycL 3 0; SWin 2; SWinL 6] (StD, S1) ltac:(vm_compute; reflexivity)
                   p1 j1 E1).
Qed.

Theorem nqhtr_0RB1RD_1LC0RB_1RA0LD_0LC1LB : NeverQuasiHaltsTr tm_0RB1RD_1LC0RB_1RA0LD_0LC1LB.
Proof.
  apply (glue_neverqhtr tm_0RB1RD_1LC0RB_1RA0LD_0LC1LB pins_0RB1RD_1LC0RB_1RA0LD_0LC1LB Cc 1).
  - exact boot_0RB1RD_1LC0RB_1RA0LD_0LC1LB.
  - intros p _. apply lap_0RB1RD_1LC0RB_1RA0LD_0LC1LB.
  - intros t Ht p _. apply fire_0RB1RD_1LC0RB_1RA0LD_0LC1LB. exact Ht.
Qed.

Theorem nonhalt_0RB1RD_1LC0RB_1RA0LD_0LC1LB : NonHalt tm_0RB1RD_1LC0RB_1RA0LD_0LC1LB.
Proof. apply never_qh_tr_nonhalt, nqhtr_0RB1RD_1LC0RB_1RA0LD_0LC1LB. Qed.
