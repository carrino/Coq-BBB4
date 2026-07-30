(** * REG_0RB1LA_1LC1RD_1LD1RC_1RB0LA: machine 0RB1LA_1LC1RD_1LD1RC_1RB0LA, boarded by CERTIFICATE (TWO-FORM route).

    Auto-emitted by tools/counters/tailcert.py (UNTRUSTED emitter; the Coq
    kernel re-runs the checker on every line below).  A binary counter under
    the Jp digit alphabet (JpCounter.v) whose anchor FRAME -- the state, the
    constant cells past the word and the far side -- is a function of the
    PARITY of the octave [p] lives in:

      Cc p = if podd p then (StA, (Jp p ++ [S0;S1], S0, []))
                       else (StA, (Jp p ++ [S1;S0;S1], S0, []))

    with [RegGlue.podd] the octave parity ([podd p = true] iff the octave is
    odd).  One counter, two frames, and their UNION covers every value with no
    gaps -- no skip, no virtual anchor, no register.  [LapDecider]'s
    [anchors()] fixes ONE frame and validates it at every anchor, so this
    family fails at the first octave boundary under every earlier reader and
    the rows were filed `no overflow phase at K=6'.

    The lap branches:

      interior  (cview p = (j, Some q0)), SPLIT and per parity:
                j = 0 concrete, j = S j' with one unit copy peeled into the
                chain's prefix -- 0*j+4 / 0*j+4 / 4*j+8 / 4*j+8 by parity
      overflow  (cview p = (S (S j), None)), one arm per parity, CROSSING into
                the other parity's frame: parity true FLAT 4*j+18; parity false NESTED, boot 4*j+8 then the inner counter then exit 4*j+16

    Every branch closes EXACTLY on the next anchor.

    The overflow arm is stated one peel deeper than the flat route's: its
    source carries a unit copy in the prefix and its landing counts
    [1*j+2] blocks, so the reindex leaves [cview p = (1, None)] (that is,
    [p = 1]) behind.  [lap] refutes that case from [8 <= p]; the visit
    premise, which ranges over every overflow anchor, discharges it as one
    concrete run from [Cc 1].

    Differentially validated against the raw simulator on EVERY branch --
    step counts AND configurations, and every inner lap of every nested overflow -- for 192 anchors, 2 nested overflows, 78 inner laps.
    Axiom footprint: [functional_extensionality_dep] (via [CTape.lift]). *)
From Coq Require Import Arith Lia Bool List PArith Wellfounded.
From BBB4 Require Import BBB4_Statement CTape Mirror.
From Coq Require Import FunctionalExtensionality.
From BBB4.Counters Require Import WTape LapGlue MonoCounter JpCounter
                                   LapCertGlue LapCertGlueLift
                                  IXPGadgets NestedLap NestedLapLift
                                  RegGlue.
From BBB4.Census Require Import TNF_QH.
From BBB4.Checkers Require Import LapDecider.
Import ListNotations.

Definition mk_0RB1LA_1LC1RD_1LD1RC_1RB0LA (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_0RB1LA_1LC1RD_1LD1RC_1RB0LA.

(** 0RB1LA_1LC1RD_1LD1RC_1RB0LA *)
(** 0RB1LA_1LC1RD_1LD1RC_1RB0LA -- the real machine (its counter grows RIGHT). *)
Definition tm_0RB1LA_1LC1RD_1LD1RC_1RB0LA : TM := fun q s => match q, s with
  | StA, S0 => mk S0 DR StB | StA, S1 => mk S1 DL StA
  | StB, S0 => mk S1 DL StC | StB, S1 => mk S1 DR StD
  | StC, S0 => mk S1 DL StD | StC, S1 => mk S1 DR StC
  | StD, S0 => mk S1 DR StB | StD, S1 => mk S0 DL StA end.

(** Its mirror 0LB1RA_1RC1LD_1RD1LC_1LB0RA: the same counter grown leftward.  Every
    lemma below runs on the MIRRORED table;
    [Mirror.mirror_never_qh] transfers the conclusion back. *)
Definition tmm_0RB1LA_1LC1RD_1LD1RC_1RB0LA : TM := fun q s => match q, s with
  | StA, S0 => mk S0 DL StB | StA, S1 => mk S1 DR StA
  | StB, S0 => mk S1 DR StC | StB, S1 => mk S1 DL StD
  | StC, S0 => mk S1 DR StD | StC, S1 => mk S1 DL StC
  | StD, S0 => mk S1 DL StB | StD, S1 => mk S0 DR StA end.
Local Notation tm := tmm_0RB1LA_1LC1RD_1LD1RC_1RB0LA.

Lemma mirror_ok_0RB1LA_1LC1RD_1LD1RC_1RB0LA : mirror_tm tm_0RB1LA_1LC1RD_1LD1RC_1RB0LA = tmm_0RB1LA_1LC1RD_1LD1RC_1RB0LA.
Proof.
  apply functional_extensionality; intro q;
    apply functional_extensionality; intro b; destruct q, b; reflexivity.
Qed.

Definition Cc_0RB1LA_1LC1RD_1LD1RC_1RB0LA (p : positive) : cconf :=
  if podd p then (StA, (Jp p ++ [S0;S1], S0, []))
  else (StA, (Jp p ++ [S1;S0;S1], S0, [])).
Local Notation Cc := Cc_0RB1LA_1LC1RD_1LD1RC_1RB0LA.

(** ** The INNER anchor family of the parity-false overflow arm -- the counter
    that arm re-runs, [Theta(2^j)] laps of it *)
Definition Cin0_0RB1LA_1LC1RD_1LD1RC_1RB0LA (v : positive) : cconf :=
  (StA, (Jp v ++ [S0;S0;S1], S0, [])).
Local Notation Cin0 := Cin0_0RB1LA_1LC1RD_1LD1RC_1RB0LA.

Ltac rshape_0RB1LA_1LC1RD_1LD1RC_1RB0LA :=
  cbn [rep app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r;
  reflexivity.

(** ** The certificate *)

(** *** the interior branch at octave parity true, SPLIT.  [j = 0]: the
    repeated block is absent, so the whole lap is concrete. *)
Definition Z01_0RB1LA_1LC1RD_1LD1RC_1RB0LA : sconf := mkC StA (mkS [S1;S1] [] 0 0 []) S0 (mkS [] [] 0 0 []).
Definition Z11_0RB1LA_1LC1RD_1LD1RC_1RB0LA : sconf := mkC StA (mkS [S1;S0] [] 0 0 []) S0 (mkS [] [] 0 0 []).
Definition chz1_0RB1LA_1LC1RD_1LD1RC_1RB0LA : list lstep := [SWin 4].

Lemma run_z1_0RB1LA_1LC1RD_1LD1RC_1RB0LA : srun tm false true chz1_0RB1LA_1LC1RD_1LD1RC_1RB0LA Z01_0RB1LA_1LC1RD_1LD1RC_1RB0LA = Some (Z11_0RB1LA_1LC1RD_1LD1RC_1RB0LA, 0, 4).
Proof. vm_compute. reflexivity. Qed.

(** [j = S j']: one copy of the unit sits in the PREFIX, so the head always
    has a concrete cell to step onto. *)
Definition P01_0RB1LA_1LC1RD_1LD1RC_1RB0LA : sconf := mkC StA (mkS [S1;S0] [S1;S0] 1 0 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition P11_0RB1LA_1LC1RD_1LD1RC_1RB0LA : sconf := mkC StA (mkS [S1;S1] [S1;S1] 1 0 [S1;S0]) S0 (mkS [] [] 0 0 []).
Definition chp1_0RB1LA_1LC1RD_1LD1RC_1RB0LA : list lstep := [SWin 2; SCycL 2 0; SWin 4; SCycR 2; SWin 2].

Lemma run_p1_0RB1LA_1LC1RD_1LD1RC_1RB0LA : srun tm false true chp1_0RB1LA_1LC1RD_1LD1RC_1RB0LA P01_0RB1LA_1LC1RD_1LD1RC_1RB0LA = Some (P11_0RB1LA_1LC1RD_1LD1RC_1RB0LA, 4, 8).
Proof. vm_compute. reflexivity. Qed.

(** *** the interior branch at octave parity false, SPLIT.  [j = 0]: the
    repeated block is absent, so the whole lap is concrete. *)
Definition Z00_0RB1LA_1LC1RD_1LD1RC_1RB0LA : sconf := mkC StA (mkS [S1;S1] [] 0 0 []) S0 (mkS [] [] 0 0 []).
Definition Z10_0RB1LA_1LC1RD_1LD1RC_1RB0LA : sconf := mkC StA (mkS [S1;S0] [] 0 0 []) S0 (mkS [] [] 0 0 []).
Definition chz0_0RB1LA_1LC1RD_1LD1RC_1RB0LA : list lstep := [SWin 4].

Lemma run_z0_0RB1LA_1LC1RD_1LD1RC_1RB0LA : srun tm false true chz0_0RB1LA_1LC1RD_1LD1RC_1RB0LA Z00_0RB1LA_1LC1RD_1LD1RC_1RB0LA = Some (Z10_0RB1LA_1LC1RD_1LD1RC_1RB0LA, 0, 4).
Proof. vm_compute. reflexivity. Qed.

(** [j = S j']: one copy of the unit sits in the PREFIX, so the head always
    has a concrete cell to step onto. *)
Definition P00_0RB1LA_1LC1RD_1LD1RC_1RB0LA : sconf := mkC StA (mkS [S1;S0] [S1;S0] 1 0 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition P10_0RB1LA_1LC1RD_1LD1RC_1RB0LA : sconf := mkC StA (mkS [S1;S1] [S1;S1] 1 0 [S1;S0]) S0 (mkS [] [] 0 0 []).
Definition chp0_0RB1LA_1LC1RD_1LD1RC_1RB0LA : list lstep := [SWin 2; SCycL 2 0; SWin 4; SCycR 2; SWin 2].

Lemma run_p0_0RB1LA_1LC1RD_1LD1RC_1RB0LA : srun tm false true chp0_0RB1LA_1LC1RD_1LD1RC_1RB0LA P00_0RB1LA_1LC1RD_1LD1RC_1RB0LA = Some (P10_0RB1LA_1LC1RD_1LD1RC_1RB0LA, 4, 8).
Proof. vm_compute. reflexivity. Qed.

Definition B01_0RB1LA_1LC1RD_1LD1RC_1RB0LA : sconf := mkC StA (mkS [S1;S0] [S1;S0] 1 0 [S1;S0;S1]) S0 (mkS [] [] 0 0 []).
Definition B11_0RB1LA_1LC1RD_1LD1RC_1RB0LA : sconf := mkC StA (mkS [] [S1;S1] 1 2 [S1;S1;S0;S1]) S0 (mkS [] [] 0 0 []).

(** *** the overflow arm at octave parity true: FLAT, 4*j+18 steps *)
Definition cho1_0RB1LA_1LC1RD_1LD1RC_1RB0LA : list lstep := [SWin 2; SCycL 2 0; SWin 3; SWinL 11; SCycR 2; SWin 2; SRotL 2; SFoldL 2].

Lemma run_ovf1_0RB1LA_1LC1RD_1LD1RC_1RB0LA : srun tm true true cho1_0RB1LA_1LC1RD_1LD1RC_1RB0LA B01_0RB1LA_1LC1RD_1LD1RC_1RB0LA = Some (B11_0RB1LA_1LC1RD_1LD1RC_1RB0LA, 4, 18).
Proof. vm_compute. reflexivity. Qed.

Definition B00_0RB1LA_1LC1RD_1LD1RC_1RB0LA : sconf := mkC StA (mkS [S1;S0] [S1;S0] 1 0 [S1;S1;S0;S1]) S0 (mkS [] [] 0 0 []).
Definition B10_0RB1LA_1LC1RD_1LD1RC_1RB0LA : sconf := mkC StA (mkS [] [S1;S1] 1 2 [S1;S0;S1]) S0 (mkS [] [] 0 0 []).

(** *** the overflow arm at octave parity false: boot 4*j+8, then the
    inner counter's laps, then exit 4*j+16 *)
Definition CS0_0RB1LA_1LC1RD_1LD1RC_1RB0LA : sconf := mkC StA (mkS [] [S1;S1] 1 1 [S1;S0;S0;S1]) S0 (mkS [] [] 0 0 []).
Definition chb0_0RB1LA_1LC1RD_1LD1RC_1RB0LA : list lstep := [SWin 2; SCycL 2 0; SWin 4; SCycR 2; SWin 2; SFoldL 1].

Lemma run_boot0_0RB1LA_1LC1RD_1LD1RC_1RB0LA : srun tm true true chb0_0RB1LA_1LC1RD_1LD1RC_1RB0LA B00_0RB1LA_1LC1RD_1LD1RC_1RB0LA = Some (CS0_0RB1LA_1LC1RD_1LD1RC_1RB0LA, 4, 8).
Proof. vm_compute. reflexivity. Qed.

Definition AI00_0RB1LA_1LC1RD_1LD1RC_1RB0LA : sconf := mkC StA (mkS [] [S1;S0] 1 0 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition AI10_0RB1LA_1LC1RD_1LD1RC_1RB0LA : sconf := mkC StA (mkS [] [S1;S1] 1 0 [S1;S0]) S0 (mkS [] [] 0 0 []).
Definition chn0_0RB1LA_1LC1RD_1LD1RC_1RB0LA : list lstep := [SRotL 1; SWin 1; SCycL 2 0; SWin 2; SCycR 2; SWin 1; SUnrotL 1].

Lemma run_inner0_0RB1LA_1LC1RD_1LD1RC_1RB0LA : srun tm false true chn0_0RB1LA_1LC1RD_1LD1RC_1RB0LA AI00_0RB1LA_1LC1RD_1LD1RC_1RB0LA = Some (AI10_0RB1LA_1LC1RD_1LD1RC_1RB0LA, 4, 4).
Proof. vm_compute. reflexivity. Qed.

Definition CF0_0RB1LA_1LC1RD_1LD1RC_1RB0LA : sconf := mkC StA (mkS [] [S1;S0] 1 1 [S1;S0;S0;S1]) S0 (mkS [] [] 0 0 []).
Definition che0_0RB1LA_1LC1RD_1LD1RC_1RB0LA : list lstep := [SRotL 1; SWin 1; SCycL 2 0; SWin 5; SWinL 5; SCycR 2; SWin 1; SRotL 1; SFoldL 1].

Lemma run_exit0_0RB1LA_1LC1RD_1LD1RC_1RB0LA : srun tm true true che0_0RB1LA_1LC1RD_1LD1RC_1RB0LA CF0_0RB1LA_1LC1RD_1LD1RC_1RB0LA = Some (B10_0RB1LA_1LC1RD_1LD1RC_1RB0LA, 4, 16).
Proof. vm_compute. reflexivity. Qed.

(** ** Anchor glue -- the only per-machine mathematics *)

Lemma iepow0_0RB1LA_1LC1RD_1LD1RC_1RB0LA : forall n, Jp (pow2 n) = rep [S1;S1] n ++ [S1].
Proof. induction n; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.

Lemma gz1_0RB1LA_1LC1RD_1LD1RC_1RB0LA : forall p q0, cview p = (0, Some q0) -> podd p = true ->
  Cc p = cden (Jp q0 ++ [S0;S1]) [] 0 Z01_0RB1LA_1LC1RD_1LD1RC_1RB0LA /\
  lift (cden (Jp q0 ++ [S0;S1]) [] 0 Z11_0RB1LA_1LC1RD_1LD1RC_1RB0LA) = lift (Cc (Pos.succ p)).
Proof.
  intros p q0 E Hb. destruct (JpCounter.cview_some_J p 0 q0 E) as (H1 & H2).
  unfold Cc_0RB1LA_1LC1RD_1LD1RC_1RB0LA. rewrite (podd_succ_int p 0 q0 E), Hb.
  unfold cden, Z01_0RB1LA_1LC1RD_1LD1RC_1RB0LA, Z11_0RB1LA_1LC1RD_1LD1RC_1RB0LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  split.
  - rewrite H1. rshape_0RB1LA_1LC1RD_1LD1RC_1RB0LA.
  - f_equal. rewrite H2. rshape_0RB1LA_1LC1RD_1LD1RC_1RB0LA.
Qed.

Lemma gp1_0RB1LA_1LC1RD_1LD1RC_1RB0LA : forall p j q0, cview p = (S j, Some q0) -> podd p = true ->
  Cc p = cden (Jp q0 ++ [S0;S1]) [] j P01_0RB1LA_1LC1RD_1LD1RC_1RB0LA /\
  lift (cden (Jp q0 ++ [S0;S1]) [] j P11_0RB1LA_1LC1RD_1LD1RC_1RB0LA) = lift (Cc (Pos.succ p)).
Proof.
  intros p j q0 E Hb. destruct (JpCounter.cview_some_J p (S j) q0 E) as (H1 & H2).
  unfold Cc_0RB1LA_1LC1RD_1LD1RC_1RB0LA. rewrite (podd_succ_int p (S j) q0 E), Hb.
  unfold cden, P01_0RB1LA_1LC1RD_1LD1RC_1RB0LA, P11_0RB1LA_1LC1RD_1LD1RC_1RB0LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia. replace (0 * j + 0) with 0 by lia.
  split.
  - rewrite H1. rshape_0RB1LA_1LC1RD_1LD1RC_1RB0LA.
  - f_equal. rewrite H2. rshape_0RB1LA_1LC1RD_1LD1RC_1RB0LA.
Qed.

Lemma lapi1_0RB1LA_1LC1RD_1LD1RC_1RB0LA : forall p j q0, cview p = (j, Some q0) -> podd p = true ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof.
  intros p j q0 E Hb. destruct j as [|j'].
  - destruct (gz1_0RB1LA_1LC1RD_1LD1RC_1RB0LA p q0 E Hb) as (HA & HB).
    exists (0 * 0 + 4), (cden (Jp q0 ++ [S0;S1]) [] 0 Z11_0RB1LA_1LC1RD_1LD1RC_1RB0LA).
    split; [lia|]. split; [| exact HB]. rewrite HA.
    exact (srun_sound tm false true chz1_0RB1LA_1LC1RD_1LD1RC_1RB0LA Z01_0RB1LA_1LC1RD_1LD1RC_1RB0LA Z11_0RB1LA_1LC1RD_1LD1RC_1RB0LA 0 4
             run_z1_0RB1LA_1LC1RD_1LD1RC_1RB0LA (Jp q0 ++ [S0;S1]) [] 0
             ltac:(discriminate) ltac:(reflexivity)).
  - destruct (gp1_0RB1LA_1LC1RD_1LD1RC_1RB0LA p j' q0 E Hb) as (HA & HB).
    exists (4 * j' + 8), (cden (Jp q0 ++ [S0;S1]) [] j' P11_0RB1LA_1LC1RD_1LD1RC_1RB0LA).
    split; [lia|]. split; [| exact HB]. rewrite HA.
    exact (srun_sound tm false true chp1_0RB1LA_1LC1RD_1LD1RC_1RB0LA P01_0RB1LA_1LC1RD_1LD1RC_1RB0LA P11_0RB1LA_1LC1RD_1LD1RC_1RB0LA 4 8
             run_p1_0RB1LA_1LC1RD_1LD1RC_1RB0LA (Jp q0 ++ [S0;S1]) [] j'
             ltac:(discriminate) ltac:(reflexivity)).
Qed.

Lemma gz0_0RB1LA_1LC1RD_1LD1RC_1RB0LA : forall p q0, cview p = (0, Some q0) -> podd p = false ->
  Cc p = cden (Jp q0 ++ [S1;S0;S1]) [] 0 Z00_0RB1LA_1LC1RD_1LD1RC_1RB0LA /\
  lift (cden (Jp q0 ++ [S1;S0;S1]) [] 0 Z10_0RB1LA_1LC1RD_1LD1RC_1RB0LA) = lift (Cc (Pos.succ p)).
Proof.
  intros p q0 E Hb. destruct (JpCounter.cview_some_J p 0 q0 E) as (H1 & H2).
  unfold Cc_0RB1LA_1LC1RD_1LD1RC_1RB0LA. rewrite (podd_succ_int p 0 q0 E), Hb.
  unfold cden, Z00_0RB1LA_1LC1RD_1LD1RC_1RB0LA, Z10_0RB1LA_1LC1RD_1LD1RC_1RB0LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  split.
  - rewrite H1. rshape_0RB1LA_1LC1RD_1LD1RC_1RB0LA.
  - f_equal. rewrite H2. rshape_0RB1LA_1LC1RD_1LD1RC_1RB0LA.
Qed.

Lemma gp0_0RB1LA_1LC1RD_1LD1RC_1RB0LA : forall p j q0, cview p = (S j, Some q0) -> podd p = false ->
  Cc p = cden (Jp q0 ++ [S1;S0;S1]) [] j P00_0RB1LA_1LC1RD_1LD1RC_1RB0LA /\
  lift (cden (Jp q0 ++ [S1;S0;S1]) [] j P10_0RB1LA_1LC1RD_1LD1RC_1RB0LA) = lift (Cc (Pos.succ p)).
Proof.
  intros p j q0 E Hb. destruct (JpCounter.cview_some_J p (S j) q0 E) as (H1 & H2).
  unfold Cc_0RB1LA_1LC1RD_1LD1RC_1RB0LA. rewrite (podd_succ_int p (S j) q0 E), Hb.
  unfold cden, P00_0RB1LA_1LC1RD_1LD1RC_1RB0LA, P10_0RB1LA_1LC1RD_1LD1RC_1RB0LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia. replace (0 * j + 0) with 0 by lia.
  split.
  - rewrite H1. rshape_0RB1LA_1LC1RD_1LD1RC_1RB0LA.
  - f_equal. rewrite H2. rshape_0RB1LA_1LC1RD_1LD1RC_1RB0LA.
Qed.

Lemma lapi0_0RB1LA_1LC1RD_1LD1RC_1RB0LA : forall p j q0, cview p = (j, Some q0) -> podd p = false ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof.
  intros p j q0 E Hb. destruct j as [|j'].
  - destruct (gz0_0RB1LA_1LC1RD_1LD1RC_1RB0LA p q0 E Hb) as (HA & HB).
    exists (0 * 0 + 4), (cden (Jp q0 ++ [S1;S0;S1]) [] 0 Z10_0RB1LA_1LC1RD_1LD1RC_1RB0LA).
    split; [lia|]. split; [| exact HB]. rewrite HA.
    exact (srun_sound tm false true chz0_0RB1LA_1LC1RD_1LD1RC_1RB0LA Z00_0RB1LA_1LC1RD_1LD1RC_1RB0LA Z10_0RB1LA_1LC1RD_1LD1RC_1RB0LA 0 4
             run_z0_0RB1LA_1LC1RD_1LD1RC_1RB0LA (Jp q0 ++ [S1;S0;S1]) [] 0
             ltac:(discriminate) ltac:(reflexivity)).
  - destruct (gp0_0RB1LA_1LC1RD_1LD1RC_1RB0LA p j' q0 E Hb) as (HA & HB).
    exists (4 * j' + 8), (cden (Jp q0 ++ [S1;S0;S1]) [] j' P10_0RB1LA_1LC1RD_1LD1RC_1RB0LA).
    split; [lia|]. split; [| exact HB]. rewrite HA.
    exact (srun_sound tm false true chp0_0RB1LA_1LC1RD_1LD1RC_1RB0LA P00_0RB1LA_1LC1RD_1LD1RC_1RB0LA P10_0RB1LA_1LC1RD_1LD1RC_1RB0LA 4 8
             run_p0_0RB1LA_1LC1RD_1LD1RC_1RB0LA (Jp q0 ++ [S1;S0;S1]) [] j'
             ltac:(discriminate) ltac:(reflexivity)).
Qed.

Lemma lapi_0RB1LA_1LC1RD_1LD1RC_1RB0LA : forall p j q0, cview p = (j, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof.
  intros p j q0 E. destruct (podd p) eqn:Hb.
  - exact (lapi1_0RB1LA_1LC1RD_1LD1RC_1RB0LA p j q0 E Hb).
  - exact (lapi0_0RB1LA_1LC1RD_1LD1RC_1RB0LA p j q0 E Hb).
Qed.

(** *** the overflow branch out of an octave of parity true.  It CROSSES into
    the other parity's frame, which is why one chain per parity is not a
    convenience: the two have different landings. *)
Lemma gso1_0RB1LA_1LC1RD_1LD1RC_1RB0LA : forall p j, cview p = (S (S j), None) -> podd p = true ->
  Cc p = cden [] [] j B01_0RB1LA_1LC1RD_1LD1RC_1RB0LA.
Proof.
  intros p j E Hb. destruct (JpCounter.cview_none_J p (S j) E) as (H1 & _).
  unfold Cc_0RB1LA_1LC1RD_1LD1RC_1RB0LA. rewrite Hb.
  unfold cden, B01_0RB1LA_1LC1RD_1LD1RC_1RB0LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia. replace (0 * j + 0) with 0 by lia.
  rewrite H1. rshape_0RB1LA_1LC1RD_1LD1RC_1RB0LA.
Qed.

Lemma geo1_0RB1LA_1LC1RD_1LD1RC_1RB0LA : forall p j, cview p = (S (S j), None) -> podd p = true ->
  cden [] [] j B11_0RB1LA_1LC1RD_1LD1RC_1RB0LA = Cc (Pos.succ p).
Proof.
  intros p j E Hb. destruct (JpCounter.cview_none_J p (S j) E) as (_ & H2).
  unfold Cc_0RB1LA_1LC1RD_1LD1RC_1RB0LA. rewrite (podd_succ_fill p (S j) E), Hb. cbn [negb].
  unfold cden, B11_0RB1LA_1LC1RD_1LD1RC_1RB0LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 2) with (S (S j)) by lia. replace (0 * j + 0) with 0 by lia.
  rewrite H2. rshape_0RB1LA_1LC1RD_1LD1RC_1RB0LA.
Qed.

Lemma lapo1_0RB1LA_1LC1RD_1LD1RC_1RB0LA : forall p j, cview p = (S (S j), None) -> podd p = true ->
  exists n c', csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intros p j E Hb.
  exists (4 * j + 18), (cden [] [] j B11_0RB1LA_1LC1RD_1LD1RC_1RB0LA).
  split; [| split; [f_equal; exact (geo1_0RB1LA_1LC1RD_1LD1RC_1RB0LA p j E Hb) | lia]].
  rewrite (gso1_0RB1LA_1LC1RD_1LD1RC_1RB0LA p j E Hb).
  exact (srun_sound tm true true cho1_0RB1LA_1LC1RD_1LD1RC_1RB0LA B01_0RB1LA_1LC1RD_1LD1RC_1RB0LA B11_0RB1LA_1LC1RD_1LD1RC_1RB0LA 4 18
           run_ovf1_0RB1LA_1LC1RD_1LD1RC_1RB0LA [] [] j ltac:(reflexivity) ltac:(reflexivity)).
Qed.

(** *** the overflow branch out of an octave of parity false.  It CROSSES into
    the other parity's frame, which is why one chain per parity is not a
    convenience: the two have different landings. *)
Lemma gso0_0RB1LA_1LC1RD_1LD1RC_1RB0LA : forall p j, cview p = (S (S j), None) -> podd p = false ->
  Cc p = cden [] [] j B00_0RB1LA_1LC1RD_1LD1RC_1RB0LA.
Proof.
  intros p j E Hb. destruct (JpCounter.cview_none_J p (S j) E) as (H1 & _).
  unfold Cc_0RB1LA_1LC1RD_1LD1RC_1RB0LA. rewrite Hb.
  unfold cden, B00_0RB1LA_1LC1RD_1LD1RC_1RB0LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia. replace (0 * j + 0) with 0 by lia.
  rewrite H1. rshape_0RB1LA_1LC1RD_1LD1RC_1RB0LA.
Qed.

Lemma geo0_0RB1LA_1LC1RD_1LD1RC_1RB0LA : forall p j, cview p = (S (S j), None) -> podd p = false ->
  cden [] [] j B10_0RB1LA_1LC1RD_1LD1RC_1RB0LA = Cc (Pos.succ p).
Proof.
  intros p j E Hb. destruct (JpCounter.cview_none_J p (S j) E) as (_ & H2).
  unfold Cc_0RB1LA_1LC1RD_1LD1RC_1RB0LA. rewrite (podd_succ_fill p (S j) E), Hb. cbn [negb].
  unfold cden, B10_0RB1LA_1LC1RD_1LD1RC_1RB0LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 2) with (S (S j)) by lia. replace (0 * j + 0) with 0 by lia.
  rewrite H2. rshape_0RB1LA_1LC1RD_1LD1RC_1RB0LA.
Qed.

Lemma gsn0_0RB1LA_1LC1RD_1LD1RC_1RB0LA : forall v i q0, cview v = (i, Some q0) ->
  Cin0 v = cden (Jp q0 ++ [S0;S0;S1]) [] i AI00_0RB1LA_1LC1RD_1LD1RC_1RB0LA.
Proof.
  intros v i q0 E. destruct (JpCounter.cview_some_J v i q0 E) as (H1 & _).
  unfold Cin0_0RB1LA_1LC1RD_1LD1RC_1RB0LA, cden, AI00_0RB1LA_1LC1RD_1LD1RC_1RB0LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia. replace (0 * i + 0) with 0 by lia.
  rewrite H1. rshape_0RB1LA_1LC1RD_1LD1RC_1RB0LA.
Qed.

Lemma gen0_0RB1LA_1LC1RD_1LD1RC_1RB0LA : forall v i q0, cview v = (i, Some q0) ->
  cden (Jp q0 ++ [S0;S0;S1]) [] i AI10_0RB1LA_1LC1RD_1LD1RC_1RB0LA = Cin0 (Pos.succ v).
Proof.
  intros v i q0 E. destruct (JpCounter.cview_some_J v i q0 E) as (_ & H2).
  unfold Cin0_0RB1LA_1LC1RD_1LD1RC_1RB0LA, cden, AI10_0RB1LA_1LC1RD_1LD1RC_1RB0LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia. replace (0 * i + 0) with 0 by lia.
  rewrite H2. rshape_0RB1LA_1LC1RD_1LD1RC_1RB0LA.
Qed.

Lemma lapin0_0RB1LA_1LC1RD_1LD1RC_1RB0LA : forall v i q0, cview v = (i, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cin0 v) = Some c'
               /\ lift c' = lift (Cin0 (Pos.succ v)).
Proof.
  intros v i q0 E.
  exists (4 * i + 4), (Cin0 (Pos.succ v)).
  split; [lia|]. split; [| reflexivity].
  rewrite (gsn0_0RB1LA_1LC1RD_1LD1RC_1RB0LA v i q0 E).
  rewrite (srun_sound tm false true chn0_0RB1LA_1LC1RD_1LD1RC_1RB0LA AI00_0RB1LA_1LC1RD_1LD1RC_1RB0LA AI10_0RB1LA_1LC1RD_1LD1RC_1RB0LA 4 4
             run_inner0_0RB1LA_1LC1RD_1LD1RC_1RB0LA (Jp q0 ++ [S0;S0;S1]) [] i
             ltac:(discriminate) ltac:(reflexivity)).
  f_equal. exact (gen0_0RB1LA_1LC1RD_1LD1RC_1RB0LA v i q0 E).
Qed.

Lemma gbo0_0RB1LA_1LC1RD_1LD1RC_1RB0LA : forall k, lift (cden [] [] k CS0_0RB1LA_1LC1RD_1LD1RC_1RB0LA) = lift (Cin0 (pow2 (k + 1))).
Proof.
  intro k. f_equal.
  unfold Cin0_0RB1LA_1LC1RD_1LD1RC_1RB0LA, cden, CS0_0RB1LA_1LC1RD_1LD1RC_1RB0LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * k + 1) with (k + 1) by lia. replace (0 * k + 0) with 0 by lia.
  rewrite iepow0_0RB1LA_1LC1RD_1LD1RC_1RB0LA. rshape_0RB1LA_1LC1RD_1LD1RC_1RB0LA.
Qed.

Lemma gxi0_0RB1LA_1LC1RD_1LD1RC_1RB0LA : forall k, Cin0 (fill (pow2 (k + 1))) = cden [] [] k CF0_0RB1LA_1LC1RD_1LD1RC_1RB0LA.
Proof.
  intro k.
  destruct (JpCounter.cview_none_J (fill (pow2 (k + 1))) (k + 1) (cview_fill_pow2 (k + 1))) as (H1 & _).
  unfold Cin0_0RB1LA_1LC1RD_1LD1RC_1RB0LA, cden, CF0_0RB1LA_1LC1RD_1LD1RC_1RB0LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * k + 1) with (k + 1) by lia. replace (0 * k + 0) with 0 by lia.
  rewrite H1. rshape_0RB1LA_1LC1RD_1LD1RC_1RB0LA.
Qed.

Lemma hbo0_0RB1LA_1LC1RD_1LD1RC_1RB0LA : forall p j, cview p = (S (S j), None) -> podd p = false ->
  exists n c, 0 < n /\ csteps tm n (Cc p) = Some c
              /\ lift c = lift (Cin0 (pow2 (j + 1))).
Proof.
  intros p j E Hb.
  exists (4 * j + 8), (cden [] [] j CS0_0RB1LA_1LC1RD_1LD1RC_1RB0LA).
  split; [lia|]. split; [| exact (gbo0_0RB1LA_1LC1RD_1LD1RC_1RB0LA j)].
  rewrite (gso0_0RB1LA_1LC1RD_1LD1RC_1RB0LA p j E Hb).
  exact (srun_sound tm true true chb0_0RB1LA_1LC1RD_1LD1RC_1RB0LA B00_0RB1LA_1LC1RD_1LD1RC_1RB0LA CS0_0RB1LA_1LC1RD_1LD1RC_1RB0LA 4 8
           run_boot0_0RB1LA_1LC1RD_1LD1RC_1RB0LA [] [] j ltac:(reflexivity) ltac:(reflexivity)).
Qed.

Lemma hxe0_0RB1LA_1LC1RD_1LD1RC_1RB0LA : forall p j, cview p = (S (S j), None) -> podd p = false ->
  exists n c', csteps tm n (Cin0 (fill (pow2 (j + 1)))) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof.
  intros p j E Hb.
  exists (4 * j + 16), (cden [] [] j B10_0RB1LA_1LC1RD_1LD1RC_1RB0LA).
  split; [| f_equal; exact (geo0_0RB1LA_1LC1RD_1LD1RC_1RB0LA p j E Hb)].
  rewrite (gxi0_0RB1LA_1LC1RD_1LD1RC_1RB0LA j).
  exact (srun_sound tm true true che0_0RB1LA_1LC1RD_1LD1RC_1RB0LA CF0_0RB1LA_1LC1RD_1LD1RC_1RB0LA B10_0RB1LA_1LC1RD_1LD1RC_1RB0LA 4 16
           run_exit0_0RB1LA_1LC1RD_1LD1RC_1RB0LA [] [] j ltac:(reflexivity) ltac:(reflexivity)).
Qed.

(** The overflow arm, composed.  The [Theta(2^j)] middle is the [exists n]
    inside [NestedLapLift.inner_to_fill_lift]; no formula for it is written. *)
Lemma lapo0_0RB1LA_1LC1RD_1LD1RC_1RB0LA : forall p j, cview p = (S (S j), None) -> podd p = false ->
  exists n c', csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intros p j E Hb.
  exact (nested_overflow_lift tm Cc Cin0 lapin0_0RB1LA_1LC1RD_1LD1RC_1RB0LA p (pow2 (j + 1))
           (hbo0_0RB1LA_1LC1RD_1LD1RC_1RB0LA p j E Hb) (hxe0_0RB1LA_1LC1RD_1LD1RC_1RB0LA p j E Hb)).
Qed.

(** ** The lap *)

Lemma lapo_0RB1LA_1LC1RD_1LD1RC_1RB0LA : forall p j, cview p = (S (S j), None) ->
  exists n c', csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intros p j E. destruct (podd p) eqn:Hb.
  - exact (lapo1_0RB1LA_1LC1RD_1LD1RC_1RB0LA p j E Hb).
  - exact (lapo0_0RB1LA_1LC1RD_1LD1RC_1RB0LA p j E Hb).
Qed.

(** [j = 0] is [p = 1] ([IXPGadgets.cview_none_shape]), which is below [8]:
    the peel's leftover case is refuted rather than proved. *)
Lemma lap_0RB1LA_1LC1RD_1LD1RC_1RB0LA : forall p, (8 <= p)%positive -> exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intros p Hp. destruct (cview p) as [j oq] eqn:E; destruct oq as [q0|].
  - destruct (lapi_0RB1LA_1LC1RD_1LD1RC_1RB0LA p j q0 E) as (n & c' & Hn & Hr & Hl).
    exists n, c'. split; [exact Hr | split; [exact Hl | exact Hn]].
  - destruct (cview_pos p j E) as (j' & ->).
    destruct j' as [|j''].
    + exfalso. rewrite (cview_none_shape p 0 E) in Hp.
      apply Hp. vm_compute. reflexivity.
    + exact (lapo_0RB1LA_1LC1RD_1LD1RC_1RB0LA p j'' E).
Qed.

(** ** Bootstrap *)

Lemma boot_0RB1LA_1LC1RD_1LD1RC_1RB0LA : exists t0, stepn tm t0 InitES = Some (lift (Cc 8)).
Proof.
  exists 124.
  assert (H : match csteps tm 124 c0 with
              | Some c => ceqb c (Cc 8) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 124 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** ** Visits

    [LapCertGlueLift.vis_via_ovf_lift] asks for a witness at EVERY overflow
    anchor, and the overflow anchors alternate frames -- so the witness is a
    prefix of whichever of the two overflow chains that parity uses, plus the
    peel's leftover [p = 1]. *)

Lemma viso1_0RB1LA_1LC1RD_1LD1RC_1RB0LA : forall (l : list lstep) (q : St),
  srun_st tm true true l B01_0RB1LA_1LC1RD_1LD1RC_1RB0LA = Some q ->
  forall p j, cview p = (S (S j), None) -> podd p = true ->
  exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros l q Hst p j E Hb.
  apply (vis_of_run tm Cc true true l B01_0RB1LA_1LC1RD_1LD1RC_1RB0LA p j [] []);
    [exact Hst | reflexivity | reflexivity | exact (gso1_0RB1LA_1LC1RD_1LD1RC_1RB0LA p j E Hb)].
Qed.

Lemma viso0_0RB1LA_1LC1RD_1LD1RC_1RB0LA : forall (l : list lstep) (q : St),
  srun_st tm true true l B00_0RB1LA_1LC1RD_1LD1RC_1RB0LA = Some q ->
  forall p j, cview p = (S (S j), None) -> podd p = false ->
  exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros l q Hst p j E Hb.
  apply (vis_of_run tm Cc true true l B00_0RB1LA_1LC1RD_1LD1RC_1RB0LA p j [] []);
    [exact Hst | reflexivity | reflexivity | exact (gso0_0RB1LA_1LC1RD_1LD1RC_1RB0LA p j E Hb)].
Qed.

(** A state that fires in the parity-false arm's EXIT chain -- i.e. only after
    the inner counter has run its [Theta(2^j)] laps -- has no witness in the
    BOOT chain, and [vis_of_run] can see a prefix of one chain only.
    [NestedLapLift.vis_via_fill] bridges the two with the same [exists n] the
    lap uses, so nothing exponential is written down here either.

    Stated in the CONCRETE [csteps] form [viso0_0RB1LA_1LC1RD_1LD1RC_1RB0LA] has, so the two are
    interchangeable at the use site: [vis_via_fill] lands in [lift] space and
    [LapCertGlueLift.vis_csteps_of_lift] pulls it straight back. *)
Lemma visx0_0RB1LA_1LC1RD_1LD1RC_1RB0LA : forall (l : list lstep) (q : St),
  srun_st tm true true l CF0_0RB1LA_1LC1RD_1LD1RC_1RB0LA = Some q ->
  forall p j, cview p = (S (S j), None) -> podd p = false ->
  exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros l q Hst p j E Hb.
  apply (vis_csteps_of_lift tm Cc p q).
  apply (vis_via_fill tm Cc Cin0 lapin0_0RB1LA_1LC1RD_1LD1RC_1RB0LA q p (pow2 (j + 1))).
  - destruct (hbo0_0RB1LA_1LC1RD_1LD1RC_1RB0LA p j E Hb) as (n & c & _ & Hn & Hl).
    exists n, c. exact (conj Hn Hl).
  - apply (vis_lift_of_csteps tm
             (fun _ : positive => Cin0 (fill (pow2 (j + 1)))) xH).
    apply (vis_of_run tm (fun _ : positive => Cin0 (fill (pow2 (j + 1))))
                      true true l CF0_0RB1LA_1LC1RD_1LD1RC_1RB0LA xH j [] []);
      [exact Hst | reflexivity | reflexivity | exact (gxi0_0RB1LA_1LC1RD_1LD1RC_1RB0LA j)].
Qed.

(** State StA at the peel's leftover overflow anchor [p = 1]. *)
Lemma viszStA_0RB1LA_1LC1RD_1LD1RC_1RB0LA : exists k c, csteps tm k (Cc 1) = Some c /\ fst c = StA.
Proof. exists 0. eexists. split; [vm_compute; reflexivity | reflexivity]. Qed.

(** State StB at the peel's leftover overflow anchor [p = 1]. *)
Lemma viszStB_0RB1LA_1LC1RD_1LD1RC_1RB0LA : exists k c, csteps tm k (Cc 1) = Some c /\ fst c = StB.
Proof. exists 1. eexists. split; [vm_compute; reflexivity | reflexivity]. Qed.

(** State StC at the peel's leftover overflow anchor [p = 1]. *)
Lemma viszStC_0RB1LA_1LC1RD_1LD1RC_1RB0LA : exists k c, csteps tm k (Cc 1) = Some c /\ fst c = StC.
Proof. exists 8. eexists. split; [vm_compute; reflexivity | reflexivity]. Qed.

(** State StD at the peel's leftover overflow anchor [p = 1]. *)
Lemma viszStD_0RB1LA_1LC1RD_1LD1RC_1RB0LA : exists k c, csteps tm k (Cc 1) = Some c /\ fst c = StD.
Proof. exists 2. eexists. split; [vm_compute; reflexivity | reflexivity]. Qed.

Lemma vis_0RB1LA_1LC1RD_1LD1RC_1RB0LA : forall p q, (8 <= p)%positive ->
  exists k e, stepn tm k (lift (Cc p)) = Some e /\ fst e = q.
Proof.
  intros p q _.
  apply (vis_via_ovf_lift tm Cc lapi_0RB1LA_1LC1RD_1LD1RC_1RB0LA q).
  intros p1 j1 E1. destruct j1 as [|j2].
  - assert (H1 : p1 = 1%positive)
      by (rewrite (cview_none_shape p1 0 E1); reflexivity).
    subst p1. apply vis_lift_of_csteps. destruct q.
    + exact (viszStA_0RB1LA_1LC1RD_1LD1RC_1RB0LA).
    + exact (viszStB_0RB1LA_1LC1RD_1LD1RC_1RB0LA).
    + exact (viszStC_0RB1LA_1LC1RD_1LD1RC_1RB0LA).
    + exact (viszStD_0RB1LA_1LC1RD_1LD1RC_1RB0LA).
  - apply vis_lift_of_csteps. destruct (podd p1) eqn:Hb1.
    + destruct q.
      * exact (viso1_0RB1LA_1LC1RD_1LD1RC_1RB0LA [] StA ltac:(vm_compute; reflexivity) p1 j2 E1 Hb1).
      * exact (viso1_0RB1LA_1LC1RD_1LD1RC_1RB0LA [SWin 1] StB ltac:(vm_compute; reflexivity) p1 j2 E1 Hb1).
      * exact (viso1_0RB1LA_1LC1RD_1LD1RC_1RB0LA [SWin 2; SCycL 2 0; SWin 3; SWinL 3] StC ltac:(vm_compute; reflexivity) p1 j2 E1 Hb1).
      * exact (viso1_0RB1LA_1LC1RD_1LD1RC_1RB0LA [SWin 2] StD ltac:(vm_compute; reflexivity) p1 j2 E1 Hb1).
    + destruct q.
      * exact (viso0_0RB1LA_1LC1RD_1LD1RC_1RB0LA [] StA ltac:(vm_compute; reflexivity) p1 j2 E1 Hb1).
      * exact (viso0_0RB1LA_1LC1RD_1LD1RC_1RB0LA [SWin 1] StB ltac:(vm_compute; reflexivity) p1 j2 E1 Hb1).
      * exact (visx0_0RB1LA_1LC1RD_1LD1RC_1RB0LA [SRotL 1; SWin 1; SCycL 2 0; SWin 3] StC ltac:(vm_compute; reflexivity) p1 j2 E1 Hb1).
      * exact (viso0_0RB1LA_1LC1RD_1LD1RC_1RB0LA [SWin 2] StD ltac:(vm_compute; reflexivity) p1 j2 E1 Hb1).
Qed.

Theorem nqhm_0RB1LA_1LC1RD_1LD1RC_1RB0LA : NeverQuasiHaltsSt tm.
Proof. apply (glue_neverqh_lift tm Cc 8). - exact boot_0RB1LA_1LC1RD_1LD1RC_1RB0LA. - intros p Hp. apply (lap_0RB1LA_1LC1RD_1LD1RC_1RB0LA p Hp). - intros p q Hp. apply (vis_0RB1LA_1LC1RD_1LD1RC_1RB0LA p q Hp). Qed.

Theorem nqh_0RB1LA_1LC1RD_1LD1RC_1RB0LA : NeverQuasiHaltsSt tm_0RB1LA_1LC1RD_1LD1RC_1RB0LA.
Proof. apply (mirror_never_qh tm_0RB1LA_1LC1RD_1LD1RC_1RB0LA). rewrite mirror_ok_0RB1LA_1LC1RD_1LD1RC_1RB0LA. exact nqhm_0RB1LA_1LC1RD_1LD1RC_1RB0LA. Qed.

Theorem nonhalt_0RB1LA_1LC1RD_1LD1RC_1RB0LA : NonHalt tm_0RB1LA_1LC1RD_1LD1RC_1RB0LA.
Proof. apply never_qh_nonhalt, nqh_0RB1LA_1LC1RD_1LD1RC_1RB0LA. Qed.
