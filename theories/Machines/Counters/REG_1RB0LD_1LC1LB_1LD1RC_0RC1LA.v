(** * REG_1RB0LD_1LC1LB_1LD1RC_0RC1LA: machine 1RB0LD_1LC1LB_1LD1RC_0RC1LA, boarded by CERTIFICATE (TWO-FORM route).

    Auto-emitted by tools/counters/tailcert.py (UNTRUSTED emitter; the Coq
    kernel re-runs the checker on every line below).  A binary counter under
    the Ap_Alph_01_11_11 digit alphabet (Alph_01_11_11.v) whose anchor FRAME -- the state, the
    constant cells past the word and the far side -- is a function of the
    PARITY of the octave [p] lives in:

      Cc p = if podd p then (StD, (Ap_Alph_01_11_11 p ++ [S0;S1;S1], S0, []))
                       else (StD, (Ap_Alph_01_11_11 p ++ [S1], S0, []))

    with [RegGlue.podd] the octave parity ([podd p = true] iff the octave is
    odd).  One counter, two frames, and their UNION covers every value with no
    gaps -- no skip, no virtual anchor, no register.  [LapDecider]'s
    [anchors()] fixes ONE frame and validates it at every anchor, so this
    family fails at the first octave boundary under every earlier reader and
    the rows were filed `no overflow phase at K=6'.

    The lap branches:

      interior  (cview p = (j, Some q0)), SPLIT and per parity:
                j = 0 concrete, j = S j' with one unit copy peeled into the
                chain's prefix -- 0*j+2 / 0*j+2 / 4*j+6 / 4*j+6 by parity
      overflow  (cview p = (S (S j), None)), one arm per parity, CROSSING into
                the other parity's frame: parity true FLAT 4*j+10; parity false NESTED, boot 4*j+16 then the inner counter then exit 4*j+11

    Every branch closes EXACTLY on the next anchor.

    The overflow arm is stated one peel deeper than the flat route's: its
    source carries a unit copy in the prefix and its landing counts
    [1*j+2] blocks, so the reindex leaves [cview p = (1, None)] (that is,
    [p = 1]) behind.  [lap] refutes that case from [8 <= p]; the visit
    premise, which ranges over every overflow anchor, discharges it as one
    concrete run from [Cc 1].

    Differentially validated against the raw simulator on EVERY branch --
    step counts AND configurations, and every inner lap of every nested overflow -- for 192 anchors, 2 nested overflows, 76 inner laps.
    Axiom footprint: [functional_extensionality_dep] (via [CTape.lift]). *)
From Coq Require Import Arith Lia Bool List PArith Wellfounded.
From BBB4 Require Import BBB4_Statement CTape Mirror.
From Coq Require Import FunctionalExtensionality.
From BBB4.Counters Require Import WTape LapGlue MonoCounter JpCounter
                                  Alph_01_11_11 ILCounter LapCertGlue LapCertGlueLift
                                  IXPGadgets NestedLap NestedLapLift
                                  RegGlue LapCertGluePar NestedLapHalf.
From BBB4.Census Require Import TNF_QH.
From BBB4.Checkers Require Import LapDecider.
Import ListNotations.

Definition mk_1RB0LD_1LC1LB_1LD1RC_0RC1LA (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_1RB0LD_1LC1LB_1LD1RC_0RC1LA.

(** 1RB0LD_1LC1LB_1LD1RC_0RC1LA *)
(** 1RB0LD_1LC1LB_1LD1RC_0RC1LA -- the real machine (its counter grows RIGHT). *)
Definition tm_1RB0LD_1LC1LB_1LD1RC_0RC1LA : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S0 DL StD
  | StB, S0 => mk S1 DL StC | StB, S1 => mk S1 DL StB
  | StC, S0 => mk S1 DL StD | StC, S1 => mk S1 DR StC
  | StD, S0 => mk S0 DR StC | StD, S1 => mk S1 DL StA end.

(** Its mirror 1LB0RD_1RC1RB_1RD1LC_0LC1RA: the same counter grown leftward.  Every
    lemma below runs on the MIRRORED table;
    [Mirror.mirror_never_qh] transfers the conclusion back. *)
Definition tmm_1RB0LD_1LC1LB_1LD1RC_0RC1LA : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DL StB | StA, S1 => mk S0 DR StD
  | StB, S0 => mk S1 DR StC | StB, S1 => mk S1 DR StB
  | StC, S0 => mk S1 DR StD | StC, S1 => mk S1 DL StC
  | StD, S0 => mk S0 DL StC | StD, S1 => mk S1 DR StA end.
Local Notation tm := tmm_1RB0LD_1LC1LB_1LD1RC_0RC1LA.

Lemma mirror_ok_1RB0LD_1LC1LB_1LD1RC_0RC1LA : mirror_tm tm_1RB0LD_1LC1LB_1LD1RC_0RC1LA = tmm_1RB0LD_1LC1LB_1LD1RC_0RC1LA.
Proof.
  apply functional_extensionality; intro q;
    apply functional_extensionality; intro b; destruct q, b; reflexivity.
Qed.

Definition Cc_1RB0LD_1LC1LB_1LD1RC_0RC1LA (p : positive) : cconf :=
  if podd p then (StD, (Ap_Alph_01_11_11 p ++ [S0;S1;S1], S0, []))
  else (StD, (Ap_Alph_01_11_11 p ++ [S1], S0, [])).
Local Notation Cc := Cc_1RB0LD_1LC1LB_1LD1RC_0RC1LA.

(** ** The INNER anchor family of the parity-false overflow arm -- the counter
    that arm re-runs, [Theta(2^j)] laps of it *)
Definition Cin0_1RB0LD_1LC1LB_1LD1RC_0RC1LA (v : positive) : cconf :=
  (StC, (Ip v ++ [S0;S1;S1], S0, [])).
Local Notation Cin0 := Cin0_1RB0LD_1LC1LB_1LD1RC_0RC1LA.

Ltac rshape_1RB0LD_1LC1LB_1LD1RC_0RC1LA :=
  cbn [rep app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r;
  reflexivity.

(** ** The certificate *)

(** *** the interior branch at octave parity true, SPLIT.  [j = 0]: the
    repeated block is absent, so the whole lap is concrete. *)
Definition Z01_1RB0LD_1LC1LB_1LD1RC_0RC1LA : sconf := mkC StD (mkS [S0;S1] [] 0 0 []) S0 (mkS [] [] 0 0 []).
Definition Z11_1RB0LD_1LC1LB_1LD1RC_0RC1LA : sconf := mkC StD (mkS [S1;S1] [] 0 0 []) S0 (mkS [] [] 0 0 []).
Definition chz1_1RB0LD_1LC1LB_1LD1RC_0RC1LA : list lstep := [SWin 2].

Lemma run_z1_1RB0LD_1LC1LB_1LD1RC_0RC1LA : srun tm false true chz1_1RB0LD_1LC1LB_1LD1RC_0RC1LA Z01_1RB0LD_1LC1LB_1LD1RC_0RC1LA = Some (Z11_1RB0LD_1LC1LB_1LD1RC_0RC1LA, 0, 2).
Proof. vm_compute. reflexivity. Qed.

(** [j = S j']: one copy of the unit sits in the PREFIX, so the head always
    has a concrete cell to step onto. *)
Definition P01_1RB0LD_1LC1LB_1LD1RC_0RC1LA : sconf := mkC StD (mkS [S1;S1] [S1;S1] 1 0 [S0;S1]) S0 (mkS [] [] 0 0 []).
Definition P11_1RB0LD_1LC1LB_1LD1RC_0RC1LA : sconf := mkC StD (mkS [S0;S1] [S0;S1] 1 0 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition chp1_1RB0LD_1LC1LB_1LD1RC_0RC1LA : list lstep := [SWin 2; SCycL 2 0; SWin 2; SCycR 2; SWin 2].

Lemma run_p1_1RB0LD_1LC1LB_1LD1RC_0RC1LA : srun tm false true chp1_1RB0LD_1LC1LB_1LD1RC_0RC1LA P01_1RB0LD_1LC1LB_1LD1RC_0RC1LA = Some (P11_1RB0LD_1LC1LB_1LD1RC_0RC1LA, 4, 6).
Proof. vm_compute. reflexivity. Qed.

(** *** the interior branch at octave parity false, SPLIT.  [j = 0]: the
    repeated block is absent, so the whole lap is concrete. *)
Definition Z00_1RB0LD_1LC1LB_1LD1RC_0RC1LA : sconf := mkC StD (mkS [S0;S1] [] 0 0 []) S0 (mkS [] [] 0 0 []).
Definition Z10_1RB0LD_1LC1LB_1LD1RC_0RC1LA : sconf := mkC StD (mkS [S1;S1] [] 0 0 []) S0 (mkS [] [] 0 0 []).
Definition chz0_1RB0LD_1LC1LB_1LD1RC_0RC1LA : list lstep := [SWin 2].

Lemma run_z0_1RB0LD_1LC1LB_1LD1RC_0RC1LA : srun tm false true chz0_1RB0LD_1LC1LB_1LD1RC_0RC1LA Z00_1RB0LD_1LC1LB_1LD1RC_0RC1LA = Some (Z10_1RB0LD_1LC1LB_1LD1RC_0RC1LA, 0, 2).
Proof. vm_compute. reflexivity. Qed.

(** [j = S j']: one copy of the unit sits in the PREFIX, so the head always
    has a concrete cell to step onto. *)
Definition P00_1RB0LD_1LC1LB_1LD1RC_0RC1LA : sconf := mkC StD (mkS [S1;S1] [S1;S1] 1 0 [S0;S1]) S0 (mkS [] [] 0 0 []).
Definition P10_1RB0LD_1LC1LB_1LD1RC_0RC1LA : sconf := mkC StD (mkS [S0;S1] [S0;S1] 1 0 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition chp0_1RB0LD_1LC1LB_1LD1RC_0RC1LA : list lstep := [SWin 2; SCycL 2 0; SWin 2; SCycR 2; SWin 2].

Lemma run_p0_1RB0LD_1LC1LB_1LD1RC_0RC1LA : srun tm false true chp0_1RB0LD_1LC1LB_1LD1RC_0RC1LA P00_1RB0LD_1LC1LB_1LD1RC_0RC1LA = Some (P10_1RB0LD_1LC1LB_1LD1RC_0RC1LA, 4, 6).
Proof. vm_compute. reflexivity. Qed.

Definition B01_1RB0LD_1LC1LB_1LD1RC_0RC1LA : sconf := mkC StD (mkS [S1;S1] [S1;S1] 1 0 [S1;S1;S0;S1;S1]) S0 (mkS [] [] 0 0 []).
Definition B11_1RB0LD_1LC1LB_1LD1RC_0RC1LA : sconf := mkC StD (mkS [] [S0;S1] 1 2 [S1;S1;S1]) S0 (mkS [] [] 0 0 []).

(** *** the overflow arm at octave parity true: FLAT, 4*j+10 steps *)
Definition cho1_1RB0LD_1LC1LB_1LD1RC_0RC1LA : list lstep := [SWin 2; SCycL 2 0; SWin 6; SCycR 2; SWin 2; SRotL 2; SFoldL 2].

Lemma run_ovf1_1RB0LD_1LC1LB_1LD1RC_0RC1LA : srun tm true true cho1_1RB0LD_1LC1LB_1LD1RC_0RC1LA B01_1RB0LD_1LC1LB_1LD1RC_0RC1LA = Some (B11_1RB0LD_1LC1LB_1LD1RC_0RC1LA, 4, 10).
Proof. vm_compute. reflexivity. Qed.

Definition B00_1RB0LD_1LC1LB_1LD1RC_0RC1LA : sconf := mkC StD (mkS [S1;S1] [S1;S1] 1 0 [S1;S1;S1]) S0 (mkS [] [] 0 0 []).
Definition B10_1RB0LD_1LC1LB_1LD1RC_0RC1LA : sconf := mkC StD (mkS [] [S0;S1] 1 2 [S1;S1;S0;S1;S1]) S0 (mkS [] [] 0 0 []).

(** *** the overflow arm at octave parity false: boot 4*j+16, then the
    inner counter's laps, then exit 4*j+11 *)
Definition CS0_1RB0LD_1LC1LB_1LD1RC_0RC1LA : sconf := mkC StC (mkS [S1;S1] [S1;S0] 1 1 [S1;S0;S1;S1]) S0 (mkS [] [] 0 0 []).
Definition chb0_1RB0LD_1LC1LB_1LD1RC_0RC1LA : list lstep := [SWin 2; SCycL 2 0; SWin 3; SWinL 5; SCycR 2; SWin 4; SWinR 2; SFoldL 1].

Lemma run_boot0_1RB0LD_1LC1LB_1LD1RC_0RC1LA : srun tm true true chb0_1RB0LD_1LC1LB_1LD1RC_0RC1LA B00_1RB0LD_1LC1LB_1LD1RC_0RC1LA = Some (CS0_1RB0LD_1LC1LB_1LD1RC_0RC1LA, 4, 16).
Proof. vm_compute. reflexivity. Qed.

Definition AI00_1RB0LD_1LC1LB_1LD1RC_0RC1LA : sconf := mkC StC (mkS [] [S1;S1] 1 0 [S1;S0]) S0 (mkS [] [] 0 0 []).
Definition AI10_1RB0LD_1LC1LB_1LD1RC_0RC1LA : sconf := mkC StC (mkS [] [S1;S0] 1 0 [S1;S1]) S0 (mkS [S0] [] 0 0 []).
Definition chn0_1RB0LD_1LC1LB_1LD1RC_0RC1LA : list lstep := [SWinR 2; SCycL 2 0; SWin 4; SCycR 2; SWin 2].

Lemma run_inner0_1RB0LD_1LC1LB_1LD1RC_0RC1LA : srun tm false true chn0_1RB0LD_1LC1LB_1LD1RC_0RC1LA AI00_1RB0LD_1LC1LB_1LD1RC_0RC1LA = Some (AI10_1RB0LD_1LC1LB_1LD1RC_0RC1LA, 4, 8).
Proof. vm_compute. reflexivity. Qed.

Definition CF0_1RB0LD_1LC1LB_1LD1RC_0RC1LA : sconf := mkC StC (mkS [] [S1;S1] 1 1 [S1;S0;S1;S0;S1;S1]) S0 (mkS [] [] 0 0 []).
Definition che0_1RB0LD_1LC1LB_1LD1RC_0RC1LA : list lstep := [SWinR 2; SCycL 2 0; SWin 4; SCycR 2; SWin 1; SRotL 1; SFoldL 1].

Lemma run_exit0_1RB0LD_1LC1LB_1LD1RC_0RC1LA : srun tm true true che0_1RB0LD_1LC1LB_1LD1RC_0RC1LA CF0_1RB0LD_1LC1LB_1LD1RC_0RC1LA = Some (B10_1RB0LD_1LC1LB_1LD1RC_0RC1LA, 4, 11).
Proof. vm_compute. reflexivity. Qed.

(** ** Anchor glue -- the only per-machine mathematics *)

Lemma iepow0_1RB0LD_1LC1LB_1LD1RC_0RC1LA : forall n, Ip (pow2 n) = rep [S1;S0] n ++ [S1].
Proof. induction n; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.

Lemma gz1_1RB0LD_1LC1LB_1LD1RC_0RC1LA : forall p q0, cview p = (0, Some q0) -> podd p = true ->
  Cc p = cden (Ap_Alph_01_11_11 q0 ++ [S0;S1;S1]) [] 0 Z01_1RB0LD_1LC1LB_1LD1RC_0RC1LA /\
  lift (cden (Ap_Alph_01_11_11 q0 ++ [S0;S1;S1]) [] 0 Z11_1RB0LD_1LC1LB_1LD1RC_0RC1LA) = lift (Cc (Pos.succ p)).
Proof.
  intros p q0 E Hb. destruct (Alph_01_11_11.cview_some_Alph_01_11_11 p 0 q0 E) as (H1 & H2).
  unfold Cc_1RB0LD_1LC1LB_1LD1RC_0RC1LA. rewrite (podd_succ_int p 0 q0 E), Hb.
  unfold cden, Z01_1RB0LD_1LC1LB_1LD1RC_0RC1LA, Z11_1RB0LD_1LC1LB_1LD1RC_0RC1LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  split.
  - rewrite H1. rshape_1RB0LD_1LC1LB_1LD1RC_0RC1LA.
  - f_equal. rewrite H2. rshape_1RB0LD_1LC1LB_1LD1RC_0RC1LA.
Qed.

Lemma gp1_1RB0LD_1LC1LB_1LD1RC_0RC1LA : forall p j q0, cview p = (S j, Some q0) -> podd p = true ->
  Cc p = cden (Ap_Alph_01_11_11 q0 ++ [S0;S1;S1]) [] j P01_1RB0LD_1LC1LB_1LD1RC_0RC1LA /\
  lift (cden (Ap_Alph_01_11_11 q0 ++ [S0;S1;S1]) [] j P11_1RB0LD_1LC1LB_1LD1RC_0RC1LA) = lift (Cc (Pos.succ p)).
Proof.
  intros p j q0 E Hb. destruct (Alph_01_11_11.cview_some_Alph_01_11_11 p (S j) q0 E) as (H1 & H2).
  unfold Cc_1RB0LD_1LC1LB_1LD1RC_0RC1LA. rewrite (podd_succ_int p (S j) q0 E), Hb.
  unfold cden, P01_1RB0LD_1LC1LB_1LD1RC_0RC1LA, P11_1RB0LD_1LC1LB_1LD1RC_0RC1LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia. replace (0 * j + 0) with 0 by lia.
  split.
  - rewrite H1. rshape_1RB0LD_1LC1LB_1LD1RC_0RC1LA.
  - f_equal. rewrite H2. rshape_1RB0LD_1LC1LB_1LD1RC_0RC1LA.
Qed.

Lemma lapi1_1RB0LD_1LC1LB_1LD1RC_0RC1LA : forall p j q0, cview p = (j, Some q0) -> podd p = true ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof.
  intros p j q0 E Hb. destruct j as [|j'].
  - destruct (gz1_1RB0LD_1LC1LB_1LD1RC_0RC1LA p q0 E Hb) as (HA & HB).
    exists (0 * 0 + 2), (cden (Ap_Alph_01_11_11 q0 ++ [S0;S1;S1]) [] 0 Z11_1RB0LD_1LC1LB_1LD1RC_0RC1LA).
    split; [lia|]. split; [| exact HB]. rewrite HA.
    exact (srun_sound tm false true chz1_1RB0LD_1LC1LB_1LD1RC_0RC1LA Z01_1RB0LD_1LC1LB_1LD1RC_0RC1LA Z11_1RB0LD_1LC1LB_1LD1RC_0RC1LA 0 2
             run_z1_1RB0LD_1LC1LB_1LD1RC_0RC1LA (Ap_Alph_01_11_11 q0 ++ [S0;S1;S1]) [] 0
             ltac:(discriminate) ltac:(reflexivity)).
  - destruct (gp1_1RB0LD_1LC1LB_1LD1RC_0RC1LA p j' q0 E Hb) as (HA & HB).
    exists (4 * j' + 6), (cden (Ap_Alph_01_11_11 q0 ++ [S0;S1;S1]) [] j' P11_1RB0LD_1LC1LB_1LD1RC_0RC1LA).
    split; [lia|]. split; [| exact HB]. rewrite HA.
    exact (srun_sound tm false true chp1_1RB0LD_1LC1LB_1LD1RC_0RC1LA P01_1RB0LD_1LC1LB_1LD1RC_0RC1LA P11_1RB0LD_1LC1LB_1LD1RC_0RC1LA 4 6
             run_p1_1RB0LD_1LC1LB_1LD1RC_0RC1LA (Ap_Alph_01_11_11 q0 ++ [S0;S1;S1]) [] j'
             ltac:(discriminate) ltac:(reflexivity)).
Qed.

Lemma gz0_1RB0LD_1LC1LB_1LD1RC_0RC1LA : forall p q0, cview p = (0, Some q0) -> podd p = false ->
  Cc p = cden (Ap_Alph_01_11_11 q0 ++ [S1]) [] 0 Z00_1RB0LD_1LC1LB_1LD1RC_0RC1LA /\
  lift (cden (Ap_Alph_01_11_11 q0 ++ [S1]) [] 0 Z10_1RB0LD_1LC1LB_1LD1RC_0RC1LA) = lift (Cc (Pos.succ p)).
Proof.
  intros p q0 E Hb. destruct (Alph_01_11_11.cview_some_Alph_01_11_11 p 0 q0 E) as (H1 & H2).
  unfold Cc_1RB0LD_1LC1LB_1LD1RC_0RC1LA. rewrite (podd_succ_int p 0 q0 E), Hb.
  unfold cden, Z00_1RB0LD_1LC1LB_1LD1RC_0RC1LA, Z10_1RB0LD_1LC1LB_1LD1RC_0RC1LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  split.
  - rewrite H1. rshape_1RB0LD_1LC1LB_1LD1RC_0RC1LA.
  - f_equal. rewrite H2. rshape_1RB0LD_1LC1LB_1LD1RC_0RC1LA.
Qed.

Lemma gp0_1RB0LD_1LC1LB_1LD1RC_0RC1LA : forall p j q0, cview p = (S j, Some q0) -> podd p = false ->
  Cc p = cden (Ap_Alph_01_11_11 q0 ++ [S1]) [] j P00_1RB0LD_1LC1LB_1LD1RC_0RC1LA /\
  lift (cden (Ap_Alph_01_11_11 q0 ++ [S1]) [] j P10_1RB0LD_1LC1LB_1LD1RC_0RC1LA) = lift (Cc (Pos.succ p)).
Proof.
  intros p j q0 E Hb. destruct (Alph_01_11_11.cview_some_Alph_01_11_11 p (S j) q0 E) as (H1 & H2).
  unfold Cc_1RB0LD_1LC1LB_1LD1RC_0RC1LA. rewrite (podd_succ_int p (S j) q0 E), Hb.
  unfold cden, P00_1RB0LD_1LC1LB_1LD1RC_0RC1LA, P10_1RB0LD_1LC1LB_1LD1RC_0RC1LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia. replace (0 * j + 0) with 0 by lia.
  split.
  - rewrite H1. rshape_1RB0LD_1LC1LB_1LD1RC_0RC1LA.
  - f_equal. rewrite H2. rshape_1RB0LD_1LC1LB_1LD1RC_0RC1LA.
Qed.

Lemma lapi0_1RB0LD_1LC1LB_1LD1RC_0RC1LA : forall p j q0, cview p = (j, Some q0) -> podd p = false ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof.
  intros p j q0 E Hb. destruct j as [|j'].
  - destruct (gz0_1RB0LD_1LC1LB_1LD1RC_0RC1LA p q0 E Hb) as (HA & HB).
    exists (0 * 0 + 2), (cden (Ap_Alph_01_11_11 q0 ++ [S1]) [] 0 Z10_1RB0LD_1LC1LB_1LD1RC_0RC1LA).
    split; [lia|]. split; [| exact HB]. rewrite HA.
    exact (srun_sound tm false true chz0_1RB0LD_1LC1LB_1LD1RC_0RC1LA Z00_1RB0LD_1LC1LB_1LD1RC_0RC1LA Z10_1RB0LD_1LC1LB_1LD1RC_0RC1LA 0 2
             run_z0_1RB0LD_1LC1LB_1LD1RC_0RC1LA (Ap_Alph_01_11_11 q0 ++ [S1]) [] 0
             ltac:(discriminate) ltac:(reflexivity)).
  - destruct (gp0_1RB0LD_1LC1LB_1LD1RC_0RC1LA p j' q0 E Hb) as (HA & HB).
    exists (4 * j' + 6), (cden (Ap_Alph_01_11_11 q0 ++ [S1]) [] j' P10_1RB0LD_1LC1LB_1LD1RC_0RC1LA).
    split; [lia|]. split; [| exact HB]. rewrite HA.
    exact (srun_sound tm false true chp0_1RB0LD_1LC1LB_1LD1RC_0RC1LA P00_1RB0LD_1LC1LB_1LD1RC_0RC1LA P10_1RB0LD_1LC1LB_1LD1RC_0RC1LA 4 6
             run_p0_1RB0LD_1LC1LB_1LD1RC_0RC1LA (Ap_Alph_01_11_11 q0 ++ [S1]) [] j'
             ltac:(discriminate) ltac:(reflexivity)).
Qed.

Lemma lapi_1RB0LD_1LC1LB_1LD1RC_0RC1LA : forall p j q0, cview p = (j, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof.
  intros p j q0 E. destruct (podd p) eqn:Hb.
  - exact (lapi1_1RB0LD_1LC1LB_1LD1RC_0RC1LA p j q0 E Hb).
  - exact (lapi0_1RB0LD_1LC1LB_1LD1RC_0RC1LA p j q0 E Hb).
Qed.

(** *** the overflow branch out of an octave of parity true.  It CROSSES into
    the other parity's frame, which is why one chain per parity is not a
    convenience: the two have different landings. *)
Lemma gso1_1RB0LD_1LC1LB_1LD1RC_0RC1LA : forall p j, cview p = (S (S j), None) -> podd p = true ->
  Cc p = cden [] [] j B01_1RB0LD_1LC1LB_1LD1RC_0RC1LA.
Proof.
  intros p j E Hb. destruct (Alph_01_11_11.cview_none_Alph_01_11_11 p (S j) E) as (H1 & _).
  unfold Cc_1RB0LD_1LC1LB_1LD1RC_0RC1LA. rewrite Hb.
  unfold cden, B01_1RB0LD_1LC1LB_1LD1RC_0RC1LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia. replace (0 * j + 0) with 0 by lia.
  rewrite H1. rshape_1RB0LD_1LC1LB_1LD1RC_0RC1LA.
Qed.

Lemma geo1_1RB0LD_1LC1LB_1LD1RC_0RC1LA : forall p j, cview p = (S (S j), None) -> podd p = true ->
  cden [] [] j B11_1RB0LD_1LC1LB_1LD1RC_0RC1LA = Cc (Pos.succ p).
Proof.
  intros p j E Hb. destruct (Alph_01_11_11.cview_none_Alph_01_11_11 p (S j) E) as (_ & H2).
  unfold Cc_1RB0LD_1LC1LB_1LD1RC_0RC1LA. rewrite (podd_succ_fill p (S j) E), Hb. cbn [negb].
  unfold cden, B11_1RB0LD_1LC1LB_1LD1RC_0RC1LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 2) with (S (S j)) by lia. replace (0 * j + 0) with 0 by lia.
  rewrite H2. rshape_1RB0LD_1LC1LB_1LD1RC_0RC1LA.
Qed.

Lemma lapo1_1RB0LD_1LC1LB_1LD1RC_0RC1LA : forall p j, cview p = (S (S j), None) -> podd p = true ->
  exists n c', csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intros p j E Hb.
  exists (4 * j + 10), (cden [] [] j B11_1RB0LD_1LC1LB_1LD1RC_0RC1LA).
  split; [| split; [f_equal; exact (geo1_1RB0LD_1LC1LB_1LD1RC_0RC1LA p j E Hb) | lia]].
  rewrite (gso1_1RB0LD_1LC1LB_1LD1RC_0RC1LA p j E Hb).
  exact (srun_sound tm true true cho1_1RB0LD_1LC1LB_1LD1RC_0RC1LA B01_1RB0LD_1LC1LB_1LD1RC_0RC1LA B11_1RB0LD_1LC1LB_1LD1RC_0RC1LA 4 10
           run_ovf1_1RB0LD_1LC1LB_1LD1RC_0RC1LA [] [] j ltac:(reflexivity) ltac:(reflexivity)).
Qed.

(** *** the overflow branch out of an octave of parity false.  It CROSSES into
    the other parity's frame, which is why one chain per parity is not a
    convenience: the two have different landings. *)
Lemma gso0_1RB0LD_1LC1LB_1LD1RC_0RC1LA : forall p j, cview p = (S (S j), None) -> podd p = false ->
  Cc p = cden [] [] j B00_1RB0LD_1LC1LB_1LD1RC_0RC1LA.
Proof.
  intros p j E Hb. destruct (Alph_01_11_11.cview_none_Alph_01_11_11 p (S j) E) as (H1 & _).
  unfold Cc_1RB0LD_1LC1LB_1LD1RC_0RC1LA. rewrite Hb.
  unfold cden, B00_1RB0LD_1LC1LB_1LD1RC_0RC1LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia. replace (0 * j + 0) with 0 by lia.
  rewrite H1. rshape_1RB0LD_1LC1LB_1LD1RC_0RC1LA.
Qed.

Lemma geo0_1RB0LD_1LC1LB_1LD1RC_0RC1LA : forall p j, cview p = (S (S j), None) -> podd p = false ->
  cden [] [] j B10_1RB0LD_1LC1LB_1LD1RC_0RC1LA = Cc (Pos.succ p).
Proof.
  intros p j E Hb. destruct (Alph_01_11_11.cview_none_Alph_01_11_11 p (S j) E) as (_ & H2).
  unfold Cc_1RB0LD_1LC1LB_1LD1RC_0RC1LA. rewrite (podd_succ_fill p (S j) E), Hb. cbn [negb].
  unfold cden, B10_1RB0LD_1LC1LB_1LD1RC_0RC1LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 2) with (S (S j)) by lia. replace (0 * j + 0) with 0 by lia.
  rewrite H2. rshape_1RB0LD_1LC1LB_1LD1RC_0RC1LA.
Qed.

(** *** the inner run's OFFSET start [2^(j+2) + 1], named. *)
Definition ilo0_1RB0LD_1LC1LB_1LD1RC_0RC1LA (k : nat) : positive := xI (pow2 (k + 1)).

Lemma iloE0_1RB0LD_1LC1LB_1LD1RC_0RC1LA : forall k,
  Ip (ilo0_1RB0LD_1LC1LB_1LD1RC_0RC1LA k) = [S1;S1] ++ rep [S1;S0] (k + 1) ++ [S1].
Proof. intro k. unfold ilo0_1RB0LD_1LC1LB_1LD1RC_0RC1LA. cbn [Ip]. rewrite iepow0_1RB0LD_1LC1LB_1LD1RC_0RC1LA. rshape_1RB0LD_1LC1LB_1LD1RC_0RC1LA. Qed.

Lemma iloN0_1RB0LD_1LC1LB_1LD1RC_0RC1LA : forall k, Pos.to_nat (ilo0_1RB0LD_1LC1LB_1LD1RC_0RC1LA k) = 4 * 2 ^ k + 1.
Proof.
  intro k. unfold ilo0_1RB0LD_1LC1LB_1LD1RC_0RC1LA.
  rewrite ?Pos2Nat.inj_xI, ?Pos2Nat.inj_xO, pos2nat_pow2, Nat.pow_add_r.
  cbn [Nat.pow]. lia.
Qed.

Lemma iloS0_1RB0LD_1LC1LB_1LD1RC_0RC1LA : forall k, Pos.size_nat (ilo0_1RB0LD_1LC1LB_1LD1RC_0RC1LA k) = k + 3.
Proof.
  intro k. unfold ilo0_1RB0LD_1LC1LB_1LD1RC_0RC1LA. cbn [Pos.size_nat]. rewrite size_nat_pow2. lia.
Qed.

Lemma iloLE0_1RB0LD_1LC1LB_1LD1RC_0RC1LA : forall k,
  Pos.to_nat (ilo0_1RB0LD_1LC1LB_1LD1RC_0RC1LA k) <= Pos.to_nat (half2 (k + 1)).
Proof.
  intro k. rewrite iloN0_1RB0LD_1LC1LB_1LD1RC_0RC1LA, pos2nat_half2', Nat.pow_add_r.
  cbn [Nat.pow]. pose proof (one_le_pow2 k). lia.
Qed.

Lemma iloK0_1RB0LD_1LC1LB_1LD1RC_0RC1LA : forall k,
  Pos.to_nat (half2 (k + 1)) - Pos.to_nat (ilo0_1RB0LD_1LC1LB_1LD1RC_0RC1LA k)
    <= tovf (ilo0_1RB0LD_1LC1LB_1LD1RC_0RC1LA k).
Proof.
  intro k. rewrite tovf_size, iloS0_1RB0LD_1LC1LB_1LD1RC_0RC1LA, ?iloN0_1RB0LD_1LC1LB_1LD1RC_0RC1LA, pos2nat_half2',
    !Nat.pow_add_r. cbn [Nat.pow]. pose proof (one_le_pow2 k). lia.
Qed.

Lemma gsn0_1RB0LD_1LC1LB_1LD1RC_0RC1LA : forall v i q0, cview v = (i, Some q0) ->
  Cin0 v = cden (Ip q0 ++ [S0;S1;S1]) [] i AI00_1RB0LD_1LC1LB_1LD1RC_0RC1LA.
Proof.
  intros v i q0 E. destruct (ILCounter.cview_some_I v i q0 E) as (H1 & _).
  unfold Cin0_1RB0LD_1LC1LB_1LD1RC_0RC1LA, cden, AI00_1RB0LD_1LC1LB_1LD1RC_0RC1LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia. replace (0 * i + 0) with 0 by lia.
  rewrite H1. rshape_1RB0LD_1LC1LB_1LD1RC_0RC1LA.
Qed.

Lemma gen0_1RB0LD_1LC1LB_1LD1RC_0RC1LA : forall v i q0, cview v = (i, Some q0) ->
  lift (cden (Ip q0 ++ [S0;S1;S1]) [] i AI10_1RB0LD_1LC1LB_1LD1RC_0RC1LA) = lift (Cin0 (Pos.succ v)).
Proof.
  intros v i q0 E. destruct (ILCounter.cview_some_I v i q0 E) as (_ & H2).
  unfold Cin0_1RB0LD_1LC1LB_1LD1RC_0RC1LA, cden, AI10_1RB0LD_1LC1LB_1LD1RC_0RC1LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia. replace (0 * i + 0) with 0 by lia.
  cbn [rep app Nat.mul Nat.add]; rewrite ?app_nil_r.
    change ([S0]) with (([]) ++ [S0]).
    rewrite !lift_app_blank.
    f_equal. rewrite H2. rshape_1RB0LD_1LC1LB_1LD1RC_0RC1LA.
Qed.

Lemma lapin0_1RB0LD_1LC1LB_1LD1RC_0RC1LA : forall v i q0, cview v = (i, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cin0 v) = Some c'
               /\ lift c' = lift (Cin0 (Pos.succ v)).
Proof.
  intros v i q0 E.
  exists (4 * i + 8), (cden (Ip q0 ++ [S0;S1;S1]) [] i AI10_1RB0LD_1LC1LB_1LD1RC_0RC1LA).
  split; [lia|]. split; [| exact (gen0_1RB0LD_1LC1LB_1LD1RC_0RC1LA v i q0 E)].
  rewrite (gsn0_1RB0LD_1LC1LB_1LD1RC_0RC1LA v i q0 E).
  exact (srun_sound tm false true chn0_1RB0LD_1LC1LB_1LD1RC_0RC1LA AI00_1RB0LD_1LC1LB_1LD1RC_0RC1LA AI10_1RB0LD_1LC1LB_1LD1RC_0RC1LA 4 8
           run_inner0_1RB0LD_1LC1LB_1LD1RC_0RC1LA (Ip q0 ++ [S0;S1;S1]) [] i
           ltac:(discriminate) ltac:(reflexivity)).
Qed.

Lemma gbo0_1RB0LD_1LC1LB_1LD1RC_0RC1LA : forall k, lift (cden [] [] k CS0_1RB0LD_1LC1LB_1LD1RC_0RC1LA) = lift (Cin0 (ilo0_1RB0LD_1LC1LB_1LD1RC_0RC1LA k)).
Proof.
  intro k. f_equal.
  unfold Cin0_1RB0LD_1LC1LB_1LD1RC_0RC1LA, cden, CS0_1RB0LD_1LC1LB_1LD1RC_0RC1LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * k + 1) with (k + 1) by lia. replace (0 * k + 0) with 0 by lia.
  rewrite iloE0_1RB0LD_1LC1LB_1LD1RC_0RC1LA. rshape_1RB0LD_1LC1LB_1LD1RC_0RC1LA.
Qed.

Lemma ihalf0_1RB0LD_1LC1LB_1LD1RC_0RC1LA : forall n, Ip (half2 n) = rep [S1;S1] n ++ [S1;S0] ++ [S1].
Proof. induction n; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.

Lemma gxi0_1RB0LD_1LC1LB_1LD1RC_0RC1LA : forall k, Cin0 (half2 (k + 1)) = cden [] [] k CF0_1RB0LD_1LC1LB_1LD1RC_0RC1LA.
Proof.
  intro k.
  unfold Cin0_1RB0LD_1LC1LB_1LD1RC_0RC1LA, cden, CF0_1RB0LD_1LC1LB_1LD1RC_0RC1LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * k + 1) with (k + 1) by lia. replace (0 * k + 0) with 0 by lia.
  rewrite ihalf0_1RB0LD_1LC1LB_1LD1RC_0RC1LA. rshape_1RB0LD_1LC1LB_1LD1RC_0RC1LA.
Qed.

Lemma hbo0_1RB0LD_1LC1LB_1LD1RC_0RC1LA : forall p j, cview p = (S (S j), None) -> podd p = false ->
  exists n c, 0 < n /\ csteps tm n (Cc p) = Some c
              /\ lift c = lift (Cin0 (ilo0_1RB0LD_1LC1LB_1LD1RC_0RC1LA j)).
Proof.
  intros p j E Hb.
  exists (4 * j + 16), (cden [] [] j CS0_1RB0LD_1LC1LB_1LD1RC_0RC1LA).
  split; [lia|]. split; [| exact (gbo0_1RB0LD_1LC1LB_1LD1RC_0RC1LA j)].
  rewrite (gso0_1RB0LD_1LC1LB_1LD1RC_0RC1LA p j E Hb).
  exact (srun_sound tm true true chb0_1RB0LD_1LC1LB_1LD1RC_0RC1LA B00_1RB0LD_1LC1LB_1LD1RC_0RC1LA CS0_1RB0LD_1LC1LB_1LD1RC_0RC1LA 4 16
           run_boot0_1RB0LD_1LC1LB_1LD1RC_0RC1LA [] [] j ltac:(reflexivity) ltac:(reflexivity)).
Qed.

Lemma hxe0_1RB0LD_1LC1LB_1LD1RC_0RC1LA : forall p j, cview p = (S (S j), None) -> podd p = false ->
  exists n c', csteps tm n (Cin0 (half2 (j + 1))) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof.
  intros p j E Hb.
  exists (4 * j + 11), (cden [] [] j B10_1RB0LD_1LC1LB_1LD1RC_0RC1LA).
  split; [| f_equal; exact (geo0_1RB0LD_1LC1LB_1LD1RC_0RC1LA p j E Hb)].
  rewrite (gxi0_1RB0LD_1LC1LB_1LD1RC_0RC1LA j).
  exact (srun_sound tm true true che0_1RB0LD_1LC1LB_1LD1RC_0RC1LA CF0_1RB0LD_1LC1LB_1LD1RC_0RC1LA B10_1RB0LD_1LC1LB_1LD1RC_0RC1LA 4 11
           run_exit0_1RB0LD_1LC1LB_1LD1RC_0RC1LA [] [] j ltac:(reflexivity) ltac:(reflexivity)).
Qed.

(** The overflow arm, composed.  The inner counter runs from the OFFSET
    start [ilo0_1RB0LD_1LC1LB_1LD1RC_0RC1LA j] to [half2 (j + 1)]; both endpoints are named and
    [NestedLapHalf.nested_overflow_named_lift] takes the two numeric
    premises. *)
Lemma lapo0_1RB0LD_1LC1LB_1LD1RC_0RC1LA : forall p j, cview p = (S (S j), None) -> podd p = false ->
  exists n c', csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intros p j E Hb.
  exact (nested_overflow_named_lift tm Cc Cin0 lapin0_1RB0LD_1LC1LB_1LD1RC_0RC1LA p
           (ilo0_1RB0LD_1LC1LB_1LD1RC_0RC1LA j) (half2 (j + 1)) (iloLE0_1RB0LD_1LC1LB_1LD1RC_0RC1LA j) (iloK0_1RB0LD_1LC1LB_1LD1RC_0RC1LA j)
           (hbo0_1RB0LD_1LC1LB_1LD1RC_0RC1LA p j E Hb) (hxe0_1RB0LD_1LC1LB_1LD1RC_0RC1LA p j E Hb)).
Qed.

(** ** The lap *)

Lemma lapo_1RB0LD_1LC1LB_1LD1RC_0RC1LA : forall p j, cview p = (S (S j), None) ->
  exists n c', csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intros p j E. destruct (podd p) eqn:Hb.
  - exact (lapo1_1RB0LD_1LC1LB_1LD1RC_0RC1LA p j E Hb).
  - exact (lapo0_1RB0LD_1LC1LB_1LD1RC_0RC1LA p j E Hb).
Qed.

(** [j = 0] is [p = 1] ([IXPGadgets.cview_none_shape]), which is below [8]:
    the peel's leftover case is refuted rather than proved. *)
Lemma lap_1RB0LD_1LC1LB_1LD1RC_0RC1LA : forall p, (8 <= p)%positive -> exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intros p Hp. destruct (cview p) as [j oq] eqn:E; destruct oq as [q0|].
  - destruct (lapi_1RB0LD_1LC1LB_1LD1RC_0RC1LA p j q0 E) as (n & c' & Hn & Hr & Hl).
    exists n, c'. split; [exact Hr | split; [exact Hl | exact Hn]].
  - destruct (cview_pos p j E) as (j' & ->).
    destruct j' as [|j''].
    + exfalso. rewrite (cview_none_shape p 0 E) in Hp.
      apply Hp. vm_compute. reflexivity.
    + exact (lapo_1RB0LD_1LC1LB_1LD1RC_0RC1LA p j'' E).
Qed.

(** ** Bootstrap *)

Lemma boot_1RB0LD_1LC1LB_1LD1RC_0RC1LA : exists t0, stepn tm t0 InitES = Some (lift (Cc 8)).
Proof.
  exists 97.
  assert (H : match csteps tm 97 c0 with
              | Some c => ceqb c (Cc 8) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 97 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** ** Visits

    [LapCertGlueLift.vis_via_ovf_lift] asks for a witness at EVERY overflow
    anchor, and the overflow anchors alternate frames -- so the witness is a
    prefix of whichever of the two overflow chains that parity uses, plus the
    peel's leftover [p = 1].

    StB fires in ONE of the two arms only, which is not a reason to give
    up on it: the overflow anchors ALTERNATE parity, so a witness at a single
    parity is reached from every anchor in at most one extra lap.  That is
    [LapCertGluePar.vis_via_ovf_par_lift], whose premise ranges over the
    overflow anchors of one parity and which consumes the OVERFLOW lap
    [lapo_1RB0LD_1LC1LB_1LD1RC_0RC1LA] to cross the octave boundary. *)

Lemma viso1_1RB0LD_1LC1LB_1LD1RC_0RC1LA : forall (l : list lstep) (q : St),
  srun_st tm true true l B01_1RB0LD_1LC1LB_1LD1RC_0RC1LA = Some q ->
  forall p j, cview p = (S (S j), None) -> podd p = true ->
  exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros l q Hst p j E Hb.
  apply (vis_of_run tm Cc true true l B01_1RB0LD_1LC1LB_1LD1RC_0RC1LA p j [] []);
    [exact Hst | reflexivity | reflexivity | exact (gso1_1RB0LD_1LC1LB_1LD1RC_0RC1LA p j E Hb)].
Qed.

Lemma viso0_1RB0LD_1LC1LB_1LD1RC_0RC1LA : forall (l : list lstep) (q : St),
  srun_st tm true true l B00_1RB0LD_1LC1LB_1LD1RC_0RC1LA = Some q ->
  forall p j, cview p = (S (S j), None) -> podd p = false ->
  exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros l q Hst p j E Hb.
  apply (vis_of_run tm Cc true true l B00_1RB0LD_1LC1LB_1LD1RC_0RC1LA p j [] []);
    [exact Hst | reflexivity | reflexivity | exact (gso0_1RB0LD_1LC1LB_1LD1RC_0RC1LA p j E Hb)].
Qed.

(** State StA at the peel's leftover overflow anchor [p = 1]. *)
Lemma viszStA_1RB0LD_1LC1LB_1LD1RC_0RC1LA : exists k c, csteps tm k (Cc 1) = Some c /\ fst c = StA.
Proof. exists 6. eexists. split; [vm_compute; reflexivity | reflexivity]. Qed.

(** State StB at the peel's leftover overflow anchor [p = 1]. *)
Lemma viszStB_1RB0LD_1LC1LB_1LD1RC_0RC1LA : exists k c, csteps tm k (Cc 1) = Some c /\ fst c = StB.
Proof. exists 9. eexists. split; [vm_compute; reflexivity | reflexivity]. Qed.

(** State StC at the peel's leftover overflow anchor [p = 1]. *)
Lemma viszStC_1RB0LD_1LC1LB_1LD1RC_0RC1LA : exists k c, csteps tm k (Cc 1) = Some c /\ fst c = StC.
Proof. exists 1. eexists. split; [vm_compute; reflexivity | reflexivity]. Qed.

(** State StD at the peel's leftover overflow anchor [p = 1]. *)
Lemma viszStD_1RB0LD_1LC1LB_1LD1RC_0RC1LA : exists k c, csteps tm k (Cc 1) = Some c /\ fst c = StD.
Proof. exists 0. eexists. split; [vm_compute; reflexivity | reflexivity]. Qed.

Lemma vis_1RB0LD_1LC1LB_1LD1RC_0RC1LA : forall p q, (8 <= p)%positive ->
  exists k e, stepn tm k (lift (Cc p)) = Some e /\ fst e = q.
Proof.
  intros p q Hp.
  assert (H2 : (2 <= p)%positive).
  { apply Pos.le_trans with (8)%positive; [| exact Hp].
    unfold Pos.le; vm_compute; discriminate. }
  destruct q.
  - (* StA fires in both overflow arms *)
    apply (vis_via_ovf_lift tm Cc lapi_1RB0LD_1LC1LB_1LD1RC_0RC1LA StA).
    intros p1 j1 E1. destruct j1 as [|j2].
    + assert (H1 : p1 = 1%positive)
        by (rewrite (cview_none_shape p1 0 E1); reflexivity).
      subst p1. apply vis_lift_of_csteps. exact viszStA_1RB0LD_1LC1LB_1LD1RC_0RC1LA.
    + apply vis_lift_of_csteps. destruct (podd p1) eqn:Hb1.
      * exact (viso1_1RB0LD_1LC1LB_1LD1RC_0RC1LA [SWin 2; SCycL 2 0; SWin 5] StA ltac:(vm_compute; reflexivity)
                 p1 j2 E1 Hb1).
      * exact (viso0_1RB0LD_1LC1LB_1LD1RC_0RC1LA [SWin 2; SCycL 2 0; SWin 3; SWinL 3] StA ltac:(vm_compute; reflexivity)
                 p1 j2 E1 Hb1).
  - (* StB fires in the parity-false arm ONLY -- LapCertGluePar *)
    apply (vis_via_ovf_par_lift tm Cc lapi_1RB0LD_1LC1LB_1LD1RC_0RC1LA lapo_1RB0LD_1LC1LB_1LD1RC_0RC1LA false StB);
      [| exact H2].
    intros p1 j2 E1 Hb1. apply vis_lift_of_csteps.
    exact (viso0_1RB0LD_1LC1LB_1LD1RC_0RC1LA [SWin 2; SCycL 2 0; SWin 3; SWinL 5; SCycR 2; SWin 3] StB ltac:(vm_compute; reflexivity)
             p1 j2 E1 Hb1).
  - (* StC fires in both overflow arms *)
    apply (vis_via_ovf_lift tm Cc lapi_1RB0LD_1LC1LB_1LD1RC_0RC1LA StC).
    intros p1 j1 E1. destruct j1 as [|j2].
    + assert (H1 : p1 = 1%positive)
        by (rewrite (cview_none_shape p1 0 E1); reflexivity).
      subst p1. apply vis_lift_of_csteps. exact viszStC_1RB0LD_1LC1LB_1LD1RC_0RC1LA.
    + apply vis_lift_of_csteps. destruct (podd p1) eqn:Hb1.
      * exact (viso1_1RB0LD_1LC1LB_1LD1RC_0RC1LA [SWin 1] StC ltac:(vm_compute; reflexivity)
                 p1 j2 E1 Hb1).
      * exact (viso0_1RB0LD_1LC1LB_1LD1RC_0RC1LA [SWin 1] StC ltac:(vm_compute; reflexivity)
                 p1 j2 E1 Hb1).
  - (* StD fires in both overflow arms *)
    apply (vis_via_ovf_lift tm Cc lapi_1RB0LD_1LC1LB_1LD1RC_0RC1LA StD).
    intros p1 j1 E1. destruct j1 as [|j2].
    + assert (H1 : p1 = 1%positive)
        by (rewrite (cview_none_shape p1 0 E1); reflexivity).
      subst p1. apply vis_lift_of_csteps. exact viszStD_1RB0LD_1LC1LB_1LD1RC_0RC1LA.
    + apply vis_lift_of_csteps. destruct (podd p1) eqn:Hb1.
      * exact (viso1_1RB0LD_1LC1LB_1LD1RC_0RC1LA [] StD ltac:(vm_compute; reflexivity)
                 p1 j2 E1 Hb1).
      * exact (viso0_1RB0LD_1LC1LB_1LD1RC_0RC1LA [] StD ltac:(vm_compute; reflexivity)
                 p1 j2 E1 Hb1).
Qed.

Theorem nqhm_1RB0LD_1LC1LB_1LD1RC_0RC1LA : NeverQuasiHaltsSt tm.
Proof. apply (glue_neverqh_lift tm Cc 8). - exact boot_1RB0LD_1LC1LB_1LD1RC_0RC1LA. - intros p Hp. apply (lap_1RB0LD_1LC1LB_1LD1RC_0RC1LA p Hp). - intros p q Hp. apply (vis_1RB0LD_1LC1LB_1LD1RC_0RC1LA p q Hp). Qed.

Theorem nqh_1RB0LD_1LC1LB_1LD1RC_0RC1LA : NeverQuasiHaltsSt tm_1RB0LD_1LC1LB_1LD1RC_0RC1LA.
Proof. apply (mirror_never_qh tm_1RB0LD_1LC1LB_1LD1RC_0RC1LA). rewrite mirror_ok_1RB0LD_1LC1LB_1LD1RC_0RC1LA. exact nqhm_1RB0LD_1LC1LB_1LD1RC_0RC1LA. Qed.

Theorem nonhalt_1RB0LD_1LC1LB_1LD1RC_0RC1LA : NonHalt tm_1RB0LD_1LC1LB_1LD1RC_0RC1LA.
Proof. apply never_qh_nonhalt, nqh_1RB0LD_1LC1LB_1LD1RC_0RC1LA. Qed.
