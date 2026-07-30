(** * REG_0RB0RC_1LC0RD_0LD1RA_1RC1LD: machine 0RB0RC_1LC0RD_0LD1RA_1RC1LD, boarded by CERTIFICATE (TWO-FORM route).

    Auto-emitted by tools/counters/tailcert.py (UNTRUSTED emitter; the Coq
    kernel re-runs the checker on every line below).  A binary counter under
    the Ap_Alph_01_11_11 digit alphabet (Alph_01_11_11.v) whose anchor FRAME -- the state, the
    constant cells past the word and the far side -- is a function of the
    PARITY of the octave [p] lives in:

      Cc p = if podd p then (StC, (Ap_Alph_01_11_11 p ++ [S1], S0, [S1]))
                       else (StC, (Ap_Alph_01_11_11 p ++ [S0;S1;S1], S0, [S1]))

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
                the other parity's frame: parity true NESTED, boot 4*j+24 then the inner counter then exit 4*j+15; parity false FLAT 4*j+10

    Every branch closes EXACTLY on the next anchor.

    The overflow arm is stated one peel deeper than the flat route's: its
    source carries a unit copy in the prefix and its landing counts
    [1*j+2] blocks, so the reindex leaves [cview p = (1, None)] (that is,
    [p = 1]) behind.  [lap] refutes that case from [8 <= p]; the visit
    premise, which ranges over every overflow anchor, discharges it as one
    concrete run from [Cc 1].

    Differentially validated against the raw simulator on EVERY branch --
    step counts AND configurations, and every inner lap of every nested overflow -- for 192 anchors, 2 nested overflows, 18 inner laps.
    Axiom footprint: [functional_extensionality_dep] (via [CTape.lift]). *)
From Coq Require Import Arith Lia Bool List PArith Wellfounded.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape LapGlue MonoCounter JpCounter
                                  Alph_01_11_11 ILCounter LapCertGlue LapCertGlueLift
                                  IXPGadgets NestedLap NestedLapLift
                                  RegGlue LapCertGluePar NestedLapHalf.
From BBB4.Census Require Import TNF_QH.
From BBB4.Checkers Require Import LapDecider.
Import ListNotations.

Definition mk_0RB0RC_1LC0RD_0LD1RA_1RC1LD (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_0RB0RC_1LC0RD_0LD1RA_1RC1LD.

(** 0RB0RC_1LC0RD_0LD1RA_1RC1LD *)
Definition tm_0RB0RC_1LC0RD_0LD1RA_1RC1LD : TM := fun q s => match q, s with
  | StA, S0 => mk S0 DR StB | StA, S1 => mk S0 DR StC
  | StB, S0 => mk S1 DL StC | StB, S1 => mk S0 DR StD
  | StC, S0 => mk S0 DL StD | StC, S1 => mk S1 DR StA
  | StD, S0 => mk S1 DR StC | StD, S1 => mk S1 DL StD end.
Local Notation tm := tm_0RB0RC_1LC0RD_0LD1RA_1RC1LD.

Definition Cc_0RB0RC_1LC0RD_0LD1RA_1RC1LD (p : positive) : cconf :=
  if podd p then (StC, (Ap_Alph_01_11_11 p ++ [S1], S0, [S1]))
  else (StC, (Ap_Alph_01_11_11 p ++ [S0;S1;S1], S0, [S1])).
Local Notation Cc := Cc_0RB0RC_1LC0RD_0LD1RA_1RC1LD.

(** ** The INNER anchor family of the parity-true overflow arm -- the counter
    that arm re-runs, [Theta(2^j)] laps of it *)
Definition Cin1_0RB0RC_1LC0RD_0LD1RA_1RC1LD (v : positive) : cconf :=
  (StD, (Ip v ++ [S0;S1;S1], S0, [S1;S1;S0;S1])).
Local Notation Cin1 := Cin1_0RB0RC_1LC0RD_0LD1RA_1RC1LD.

Ltac rshape_0RB0RC_1LC0RD_0LD1RA_1RC1LD :=
  cbn [rep app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r;
  reflexivity.

(** ** The certificate *)

(** *** the interior branch at octave parity true, SPLIT.  [j = 0]: the
    repeated block is absent, so the whole lap is concrete. *)
Definition Z01_0RB0RC_1LC0RD_0LD1RA_1RC1LD : sconf := mkC StC (mkS [S0;S1] [] 0 0 []) S0 (mkS [S1] [] 0 0 []).
Definition Z11_0RB0RC_1LC0RD_0LD1RA_1RC1LD : sconf := mkC StC (mkS [S1;S1] [] 0 0 []) S0 (mkS [S1] [] 0 0 []).
Definition chz1_0RB0RC_1LC0RD_0LD1RA_1RC1LD : list lstep := [SWin 2].

Lemma run_z1_0RB0RC_1LC0RD_0LD1RA_1RC1LD : srun tm false true chz1_0RB0RC_1LC0RD_0LD1RA_1RC1LD Z01_0RB0RC_1LC0RD_0LD1RA_1RC1LD = Some (Z11_0RB0RC_1LC0RD_0LD1RA_1RC1LD, 0, 2).
Proof. vm_compute. reflexivity. Qed.

(** [j = S j']: one copy of the unit sits in the PREFIX, so the head always
    has a concrete cell to step onto. *)
Definition P01_0RB0RC_1LC0RD_0LD1RA_1RC1LD : sconf := mkC StC (mkS [S1;S1] [S1;S1] 1 0 [S0;S1]) S0 (mkS [S1] [] 0 0 []).
Definition P11_0RB0RC_1LC0RD_0LD1RA_1RC1LD : sconf := mkC StC (mkS [S0;S1] [S0;S1] 1 0 [S1;S1]) S0 (mkS [S1] [] 0 0 []).
Definition chp1_0RB0RC_1LC0RD_0LD1RA_1RC1LD : list lstep := [SWin 2; SCycL 2 0; SWin 2; SCycR 2; SWin 2].

Lemma run_p1_0RB0RC_1LC0RD_0LD1RA_1RC1LD : srun tm false true chp1_0RB0RC_1LC0RD_0LD1RA_1RC1LD P01_0RB0RC_1LC0RD_0LD1RA_1RC1LD = Some (P11_0RB0RC_1LC0RD_0LD1RA_1RC1LD, 4, 6).
Proof. vm_compute. reflexivity. Qed.

(** *** the interior branch at octave parity false, SPLIT.  [j = 0]: the
    repeated block is absent, so the whole lap is concrete. *)
Definition Z00_0RB0RC_1LC0RD_0LD1RA_1RC1LD : sconf := mkC StC (mkS [S0;S1] [] 0 0 []) S0 (mkS [S1] [] 0 0 []).
Definition Z10_0RB0RC_1LC0RD_0LD1RA_1RC1LD : sconf := mkC StC (mkS [S1;S1] [] 0 0 []) S0 (mkS [S1] [] 0 0 []).
Definition chz0_0RB0RC_1LC0RD_0LD1RA_1RC1LD : list lstep := [SWin 2].

Lemma run_z0_0RB0RC_1LC0RD_0LD1RA_1RC1LD : srun tm false true chz0_0RB0RC_1LC0RD_0LD1RA_1RC1LD Z00_0RB0RC_1LC0RD_0LD1RA_1RC1LD = Some (Z10_0RB0RC_1LC0RD_0LD1RA_1RC1LD, 0, 2).
Proof. vm_compute. reflexivity. Qed.

(** [j = S j']: one copy of the unit sits in the PREFIX, so the head always
    has a concrete cell to step onto. *)
Definition P00_0RB0RC_1LC0RD_0LD1RA_1RC1LD : sconf := mkC StC (mkS [S1;S1] [S1;S1] 1 0 [S0;S1]) S0 (mkS [S1] [] 0 0 []).
Definition P10_0RB0RC_1LC0RD_0LD1RA_1RC1LD : sconf := mkC StC (mkS [S0;S1] [S0;S1] 1 0 [S1;S1]) S0 (mkS [S1] [] 0 0 []).
Definition chp0_0RB0RC_1LC0RD_0LD1RA_1RC1LD : list lstep := [SWin 2; SCycL 2 0; SWin 2; SCycR 2; SWin 2].

Lemma run_p0_0RB0RC_1LC0RD_0LD1RA_1RC1LD : srun tm false true chp0_0RB0RC_1LC0RD_0LD1RA_1RC1LD P00_0RB0RC_1LC0RD_0LD1RA_1RC1LD = Some (P10_0RB0RC_1LC0RD_0LD1RA_1RC1LD, 4, 6).
Proof. vm_compute. reflexivity. Qed.

Definition B01_0RB0RC_1LC0RD_0LD1RA_1RC1LD : sconf := mkC StC (mkS [S1;S1] [S1;S1] 1 0 [S1;S1;S1]) S0 (mkS [S1] [] 0 0 []).
Definition B11_0RB0RC_1LC0RD_0LD1RA_1RC1LD : sconf := mkC StC (mkS [] [S0;S1] 1 2 [S1;S1;S0;S1;S1]) S0 (mkS [S1] [] 0 0 []).

(** *** the overflow arm at octave parity true: boot 4*j+24, then the
    inner counter's laps, then exit 4*j+15 *)
Definition CS1_0RB0RC_1LC0RD_0LD1RA_1RC1LD : sconf := mkC StD (mkS [] [S1;S0] 1 1 [S1;S0;S1;S1]) S0 (mkS [S1;S1;S0;S1] [] 0 0 []).
Definition chb1_0RB0RC_1LC0RD_0LD1RA_1RC1LD : list lstep := [SWin 2; SCycL 2 0; SWin 3; SWinL 5; SCycR 2; SWin 3; SWinR 11; SFoldL 1].

Lemma run_boot1_0RB0RC_1LC0RD_0LD1RA_1RC1LD : srun tm true true chb1_0RB0RC_1LC0RD_0LD1RA_1RC1LD B01_0RB0RC_1LC0RD_0LD1RA_1RC1LD = Some (CS1_0RB0RC_1LC0RD_0LD1RA_1RC1LD, 4, 24).
Proof. vm_compute. reflexivity. Qed.

Definition AI01_0RB0RC_1LC0RD_0LD1RA_1RC1LD : sconf := mkC StD (mkS [] [S1;S1] 1 0 [S1;S0]) S0 (mkS [S1;S1;S0;S1] [] 0 0 []).
Definition AI11_0RB0RC_1LC0RD_0LD1RA_1RC1LD : sconf := mkC StD (mkS [] [S1;S0] 1 0 [S1;S1]) S0 (mkS [S1;S1;S0;S1] [] 0 0 []).
Definition chn1_0RB0RC_1LC0RD_0LD1RA_1RC1LD : list lstep := [SWin 8; SCycL 2 0; SWin 4; SCycR 2; SWin 8].

Lemma run_inner1_0RB0RC_1LC0RD_0LD1RA_1RC1LD : srun tm false true chn1_0RB0RC_1LC0RD_0LD1RA_1RC1LD AI01_0RB0RC_1LC0RD_0LD1RA_1RC1LD = Some (AI11_0RB0RC_1LC0RD_0LD1RA_1RC1LD, 4, 20).
Proof. vm_compute. reflexivity. Qed.

Definition CF1_0RB0RC_1LC0RD_0LD1RA_1RC1LD : sconf := mkC StD (mkS [] [S1;S1] 1 0 [S1;S0;S1;S0;S1;S1]) S0 (mkS [S1;S1;S0;S1] [] 0 0 []).
Definition che1_0RB0RC_1LC0RD_0LD1RA_1RC1LD : list lstep := [SWin 8; SCycL 2 0; SWin 4; SCycR 2; SWin 3; SRotL 1; SFoldL 2].

Lemma run_exit1_0RB0RC_1LC0RD_0LD1RA_1RC1LD : srun tm true true che1_0RB0RC_1LC0RD_0LD1RA_1RC1LD CF1_0RB0RC_1LC0RD_0LD1RA_1RC1LD = Some (B11_0RB0RC_1LC0RD_0LD1RA_1RC1LD, 4, 15).
Proof. vm_compute. reflexivity. Qed.

Definition B00_0RB0RC_1LC0RD_0LD1RA_1RC1LD : sconf := mkC StC (mkS [S1;S1] [S1;S1] 1 0 [S1;S1;S0;S1;S1]) S0 (mkS [S1] [] 0 0 []).
Definition B10_0RB0RC_1LC0RD_0LD1RA_1RC1LD : sconf := mkC StC (mkS [] [S0;S1] 1 2 [S1;S1;S1]) S0 (mkS [S1] [] 0 0 []).

(** *** the overflow arm at octave parity false: FLAT, 4*j+10 steps *)
Definition cho0_0RB0RC_1LC0RD_0LD1RA_1RC1LD : list lstep := [SWin 2; SCycL 2 0; SWin 6; SCycR 2; SWin 2; SRotL 2; SFoldL 2].

Lemma run_ovf0_0RB0RC_1LC0RD_0LD1RA_1RC1LD : srun tm true true cho0_0RB0RC_1LC0RD_0LD1RA_1RC1LD B00_0RB0RC_1LC0RD_0LD1RA_1RC1LD = Some (B10_0RB0RC_1LC0RD_0LD1RA_1RC1LD, 4, 10).
Proof. vm_compute. reflexivity. Qed.

(** ** Anchor glue -- the only per-machine mathematics *)

Lemma iepow1_0RB0RC_1LC0RD_0LD1RA_1RC1LD : forall n, Ip (pow2 n) = rep [S1;S0] n ++ [S1].
Proof. induction n; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.

Lemma gz1_0RB0RC_1LC0RD_0LD1RA_1RC1LD : forall p q0, cview p = (0, Some q0) -> podd p = true ->
  Cc p = cden (Ap_Alph_01_11_11 q0 ++ [S1]) [] 0 Z01_0RB0RC_1LC0RD_0LD1RA_1RC1LD /\
  lift (cden (Ap_Alph_01_11_11 q0 ++ [S1]) [] 0 Z11_0RB0RC_1LC0RD_0LD1RA_1RC1LD) = lift (Cc (Pos.succ p)).
Proof.
  intros p q0 E Hb. destruct (Alph_01_11_11.cview_some_Alph_01_11_11 p 0 q0 E) as (H1 & H2).
  unfold Cc_0RB0RC_1LC0RD_0LD1RA_1RC1LD. rewrite (podd_succ_int p 0 q0 E), Hb.
  unfold cden, Z01_0RB0RC_1LC0RD_0LD1RA_1RC1LD, Z11_0RB0RC_1LC0RD_0LD1RA_1RC1LD; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  split.
  - rewrite H1. rshape_0RB0RC_1LC0RD_0LD1RA_1RC1LD.
  - f_equal. rewrite H2. rshape_0RB0RC_1LC0RD_0LD1RA_1RC1LD.
Qed.

Lemma gp1_0RB0RC_1LC0RD_0LD1RA_1RC1LD : forall p j q0, cview p = (S j, Some q0) -> podd p = true ->
  Cc p = cden (Ap_Alph_01_11_11 q0 ++ [S1]) [] j P01_0RB0RC_1LC0RD_0LD1RA_1RC1LD /\
  lift (cden (Ap_Alph_01_11_11 q0 ++ [S1]) [] j P11_0RB0RC_1LC0RD_0LD1RA_1RC1LD) = lift (Cc (Pos.succ p)).
Proof.
  intros p j q0 E Hb. destruct (Alph_01_11_11.cview_some_Alph_01_11_11 p (S j) q0 E) as (H1 & H2).
  unfold Cc_0RB0RC_1LC0RD_0LD1RA_1RC1LD. rewrite (podd_succ_int p (S j) q0 E), Hb.
  unfold cden, P01_0RB0RC_1LC0RD_0LD1RA_1RC1LD, P11_0RB0RC_1LC0RD_0LD1RA_1RC1LD; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia. replace (0 * j + 0) with 0 by lia.
  split.
  - rewrite H1. rshape_0RB0RC_1LC0RD_0LD1RA_1RC1LD.
  - f_equal. rewrite H2. rshape_0RB0RC_1LC0RD_0LD1RA_1RC1LD.
Qed.

Lemma lapi1_0RB0RC_1LC0RD_0LD1RA_1RC1LD : forall p j q0, cview p = (j, Some q0) -> podd p = true ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof.
  intros p j q0 E Hb. destruct j as [|j'].
  - destruct (gz1_0RB0RC_1LC0RD_0LD1RA_1RC1LD p q0 E Hb) as (HA & HB).
    exists (0 * 0 + 2), (cden (Ap_Alph_01_11_11 q0 ++ [S1]) [] 0 Z11_0RB0RC_1LC0RD_0LD1RA_1RC1LD).
    split; [lia|]. split; [| exact HB]. rewrite HA.
    exact (srun_sound tm false true chz1_0RB0RC_1LC0RD_0LD1RA_1RC1LD Z01_0RB0RC_1LC0RD_0LD1RA_1RC1LD Z11_0RB0RC_1LC0RD_0LD1RA_1RC1LD 0 2
             run_z1_0RB0RC_1LC0RD_0LD1RA_1RC1LD (Ap_Alph_01_11_11 q0 ++ [S1]) [] 0
             ltac:(discriminate) ltac:(reflexivity)).
  - destruct (gp1_0RB0RC_1LC0RD_0LD1RA_1RC1LD p j' q0 E Hb) as (HA & HB).
    exists (4 * j' + 6), (cden (Ap_Alph_01_11_11 q0 ++ [S1]) [] j' P11_0RB0RC_1LC0RD_0LD1RA_1RC1LD).
    split; [lia|]. split; [| exact HB]. rewrite HA.
    exact (srun_sound tm false true chp1_0RB0RC_1LC0RD_0LD1RA_1RC1LD P01_0RB0RC_1LC0RD_0LD1RA_1RC1LD P11_0RB0RC_1LC0RD_0LD1RA_1RC1LD 4 6
             run_p1_0RB0RC_1LC0RD_0LD1RA_1RC1LD (Ap_Alph_01_11_11 q0 ++ [S1]) [] j'
             ltac:(discriminate) ltac:(reflexivity)).
Qed.

Lemma gz0_0RB0RC_1LC0RD_0LD1RA_1RC1LD : forall p q0, cview p = (0, Some q0) -> podd p = false ->
  Cc p = cden (Ap_Alph_01_11_11 q0 ++ [S0;S1;S1]) [] 0 Z00_0RB0RC_1LC0RD_0LD1RA_1RC1LD /\
  lift (cden (Ap_Alph_01_11_11 q0 ++ [S0;S1;S1]) [] 0 Z10_0RB0RC_1LC0RD_0LD1RA_1RC1LD) = lift (Cc (Pos.succ p)).
Proof.
  intros p q0 E Hb. destruct (Alph_01_11_11.cview_some_Alph_01_11_11 p 0 q0 E) as (H1 & H2).
  unfold Cc_0RB0RC_1LC0RD_0LD1RA_1RC1LD. rewrite (podd_succ_int p 0 q0 E), Hb.
  unfold cden, Z00_0RB0RC_1LC0RD_0LD1RA_1RC1LD, Z10_0RB0RC_1LC0RD_0LD1RA_1RC1LD; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  split.
  - rewrite H1. rshape_0RB0RC_1LC0RD_0LD1RA_1RC1LD.
  - f_equal. rewrite H2. rshape_0RB0RC_1LC0RD_0LD1RA_1RC1LD.
Qed.

Lemma gp0_0RB0RC_1LC0RD_0LD1RA_1RC1LD : forall p j q0, cview p = (S j, Some q0) -> podd p = false ->
  Cc p = cden (Ap_Alph_01_11_11 q0 ++ [S0;S1;S1]) [] j P00_0RB0RC_1LC0RD_0LD1RA_1RC1LD /\
  lift (cden (Ap_Alph_01_11_11 q0 ++ [S0;S1;S1]) [] j P10_0RB0RC_1LC0RD_0LD1RA_1RC1LD) = lift (Cc (Pos.succ p)).
Proof.
  intros p j q0 E Hb. destruct (Alph_01_11_11.cview_some_Alph_01_11_11 p (S j) q0 E) as (H1 & H2).
  unfold Cc_0RB0RC_1LC0RD_0LD1RA_1RC1LD. rewrite (podd_succ_int p (S j) q0 E), Hb.
  unfold cden, P00_0RB0RC_1LC0RD_0LD1RA_1RC1LD, P10_0RB0RC_1LC0RD_0LD1RA_1RC1LD; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia. replace (0 * j + 0) with 0 by lia.
  split.
  - rewrite H1. rshape_0RB0RC_1LC0RD_0LD1RA_1RC1LD.
  - f_equal. rewrite H2. rshape_0RB0RC_1LC0RD_0LD1RA_1RC1LD.
Qed.

Lemma lapi0_0RB0RC_1LC0RD_0LD1RA_1RC1LD : forall p j q0, cview p = (j, Some q0) -> podd p = false ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof.
  intros p j q0 E Hb. destruct j as [|j'].
  - destruct (gz0_0RB0RC_1LC0RD_0LD1RA_1RC1LD p q0 E Hb) as (HA & HB).
    exists (0 * 0 + 2), (cden (Ap_Alph_01_11_11 q0 ++ [S0;S1;S1]) [] 0 Z10_0RB0RC_1LC0RD_0LD1RA_1RC1LD).
    split; [lia|]. split; [| exact HB]. rewrite HA.
    exact (srun_sound tm false true chz0_0RB0RC_1LC0RD_0LD1RA_1RC1LD Z00_0RB0RC_1LC0RD_0LD1RA_1RC1LD Z10_0RB0RC_1LC0RD_0LD1RA_1RC1LD 0 2
             run_z0_0RB0RC_1LC0RD_0LD1RA_1RC1LD (Ap_Alph_01_11_11 q0 ++ [S0;S1;S1]) [] 0
             ltac:(discriminate) ltac:(reflexivity)).
  - destruct (gp0_0RB0RC_1LC0RD_0LD1RA_1RC1LD p j' q0 E Hb) as (HA & HB).
    exists (4 * j' + 6), (cden (Ap_Alph_01_11_11 q0 ++ [S0;S1;S1]) [] j' P10_0RB0RC_1LC0RD_0LD1RA_1RC1LD).
    split; [lia|]. split; [| exact HB]. rewrite HA.
    exact (srun_sound tm false true chp0_0RB0RC_1LC0RD_0LD1RA_1RC1LD P00_0RB0RC_1LC0RD_0LD1RA_1RC1LD P10_0RB0RC_1LC0RD_0LD1RA_1RC1LD 4 6
             run_p0_0RB0RC_1LC0RD_0LD1RA_1RC1LD (Ap_Alph_01_11_11 q0 ++ [S0;S1;S1]) [] j'
             ltac:(discriminate) ltac:(reflexivity)).
Qed.

Lemma lapi_0RB0RC_1LC0RD_0LD1RA_1RC1LD : forall p j q0, cview p = (j, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof.
  intros p j q0 E. destruct (podd p) eqn:Hb.
  - exact (lapi1_0RB0RC_1LC0RD_0LD1RA_1RC1LD p j q0 E Hb).
  - exact (lapi0_0RB0RC_1LC0RD_0LD1RA_1RC1LD p j q0 E Hb).
Qed.

(** *** the overflow branch out of an octave of parity true.  It CROSSES into
    the other parity's frame, which is why one chain per parity is not a
    convenience: the two have different landings. *)
Lemma gso1_0RB0RC_1LC0RD_0LD1RA_1RC1LD : forall p j, cview p = (S (S j), None) -> podd p = true ->
  Cc p = cden [] [] j B01_0RB0RC_1LC0RD_0LD1RA_1RC1LD.
Proof.
  intros p j E Hb. destruct (Alph_01_11_11.cview_none_Alph_01_11_11 p (S j) E) as (H1 & _).
  unfold Cc_0RB0RC_1LC0RD_0LD1RA_1RC1LD. rewrite Hb.
  unfold cden, B01_0RB0RC_1LC0RD_0LD1RA_1RC1LD; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia. replace (0 * j + 0) with 0 by lia.
  rewrite H1. rshape_0RB0RC_1LC0RD_0LD1RA_1RC1LD.
Qed.

Lemma geo1_0RB0RC_1LC0RD_0LD1RA_1RC1LD : forall p j, cview p = (S (S j), None) -> podd p = true ->
  cden [] [] j B11_0RB0RC_1LC0RD_0LD1RA_1RC1LD = Cc (Pos.succ p).
Proof.
  intros p j E Hb. destruct (Alph_01_11_11.cview_none_Alph_01_11_11 p (S j) E) as (_ & H2).
  unfold Cc_0RB0RC_1LC0RD_0LD1RA_1RC1LD. rewrite (podd_succ_fill p (S j) E), Hb. cbn [negb].
  unfold cden, B11_0RB0RC_1LC0RD_0LD1RA_1RC1LD; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 2) with (S (S j)) by lia. replace (0 * j + 0) with 0 by lia.
  rewrite H2. rshape_0RB0RC_1LC0RD_0LD1RA_1RC1LD.
Qed.

Lemma gsn1_0RB0RC_1LC0RD_0LD1RA_1RC1LD : forall v i q0, cview v = (i, Some q0) ->
  Cin1 v = cden (Ip q0 ++ [S0;S1;S1]) [] i AI01_0RB0RC_1LC0RD_0LD1RA_1RC1LD.
Proof.
  intros v i q0 E. destruct (ILCounter.cview_some_I v i q0 E) as (H1 & _).
  unfold Cin1_0RB0RC_1LC0RD_0LD1RA_1RC1LD, cden, AI01_0RB0RC_1LC0RD_0LD1RA_1RC1LD; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia. replace (0 * i + 0) with 0 by lia.
  rewrite H1. rshape_0RB0RC_1LC0RD_0LD1RA_1RC1LD.
Qed.

Lemma gen1_0RB0RC_1LC0RD_0LD1RA_1RC1LD : forall v i q0, cview v = (i, Some q0) ->
  cden (Ip q0 ++ [S0;S1;S1]) [] i AI11_0RB0RC_1LC0RD_0LD1RA_1RC1LD = Cin1 (Pos.succ v).
Proof.
  intros v i q0 E. destruct (ILCounter.cview_some_I v i q0 E) as (_ & H2).
  unfold Cin1_0RB0RC_1LC0RD_0LD1RA_1RC1LD, cden, AI11_0RB0RC_1LC0RD_0LD1RA_1RC1LD; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia. replace (0 * i + 0) with 0 by lia.
  rewrite H2. rshape_0RB0RC_1LC0RD_0LD1RA_1RC1LD.
Qed.

Lemma lapin1_0RB0RC_1LC0RD_0LD1RA_1RC1LD : forall v i q0, cview v = (i, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cin1 v) = Some c'
               /\ lift c' = lift (Cin1 (Pos.succ v)).
Proof.
  intros v i q0 E.
  exists (4 * i + 20), (Cin1 (Pos.succ v)).
  split; [lia|]. split; [| reflexivity].
  rewrite (gsn1_0RB0RC_1LC0RD_0LD1RA_1RC1LD v i q0 E).
  rewrite (srun_sound tm false true chn1_0RB0RC_1LC0RD_0LD1RA_1RC1LD AI01_0RB0RC_1LC0RD_0LD1RA_1RC1LD AI11_0RB0RC_1LC0RD_0LD1RA_1RC1LD 4 20
             run_inner1_0RB0RC_1LC0RD_0LD1RA_1RC1LD (Ip q0 ++ [S0;S1;S1]) [] i
             ltac:(discriminate) ltac:(reflexivity)).
  f_equal. exact (gen1_0RB0RC_1LC0RD_0LD1RA_1RC1LD v i q0 E).
Qed.

Lemma gbo1_0RB0RC_1LC0RD_0LD1RA_1RC1LD : forall k, lift (cden [] [] k CS1_0RB0RC_1LC0RD_0LD1RA_1RC1LD) = lift (Cin1 (pow2 (S k))).
Proof.
  intro k. f_equal.
  unfold Cin1_0RB0RC_1LC0RD_0LD1RA_1RC1LD, cden, CS1_0RB0RC_1LC0RD_0LD1RA_1RC1LD; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * k + 1) with (S k) by lia. replace (0 * k + 0) with 0 by lia.
  rewrite iepow1_0RB0RC_1LC0RD_0LD1RA_1RC1LD. rshape_0RB0RC_1LC0RD_0LD1RA_1RC1LD.
Qed.

Lemma ihalf1_0RB0RC_1LC0RD_0LD1RA_1RC1LD : forall n, Ip (half2 n) = rep [S1;S1] n ++ [S1;S0] ++ [S1].
Proof. induction n; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.

Lemma gxi1_0RB0RC_1LC0RD_0LD1RA_1RC1LD : forall k, Cin1 (half2 k) = cden [] [] k CF1_0RB0RC_1LC0RD_0LD1RA_1RC1LD.
Proof.
  intro k.
  unfold Cin1_0RB0RC_1LC0RD_0LD1RA_1RC1LD, cden, CF1_0RB0RC_1LC0RD_0LD1RA_1RC1LD; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * k + 0) with k by lia. replace (0 * k + 0) with 0 by lia.
  rewrite ihalf1_0RB0RC_1LC0RD_0LD1RA_1RC1LD. rshape_0RB0RC_1LC0RD_0LD1RA_1RC1LD.
Qed.

Lemma hbo1_0RB0RC_1LC0RD_0LD1RA_1RC1LD : forall p j, cview p = (S (S j), None) -> podd p = true ->
  exists n c, 0 < n /\ csteps tm n (Cc p) = Some c
              /\ lift c = lift (Cin1 (pow2 (S j))).
Proof.
  intros p j E Hb.
  exists (4 * j + 24), (cden [] [] j CS1_0RB0RC_1LC0RD_0LD1RA_1RC1LD).
  split; [lia|]. split; [| exact (gbo1_0RB0RC_1LC0RD_0LD1RA_1RC1LD j)].
  rewrite (gso1_0RB0RC_1LC0RD_0LD1RA_1RC1LD p j E Hb).
  exact (srun_sound tm true true chb1_0RB0RC_1LC0RD_0LD1RA_1RC1LD B01_0RB0RC_1LC0RD_0LD1RA_1RC1LD CS1_0RB0RC_1LC0RD_0LD1RA_1RC1LD 4 24
           run_boot1_0RB0RC_1LC0RD_0LD1RA_1RC1LD [] [] j ltac:(reflexivity) ltac:(reflexivity)).
Qed.

Lemma hxe1_0RB0RC_1LC0RD_0LD1RA_1RC1LD : forall p j, cview p = (S (S j), None) -> podd p = true ->
  exists n c', csteps tm n (Cin1 (half2 j)) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof.
  intros p j E Hb.
  exists (4 * j + 15), (cden [] [] j B11_0RB0RC_1LC0RD_0LD1RA_1RC1LD).
  split; [| f_equal; exact (geo1_0RB0RC_1LC0RD_0LD1RA_1RC1LD p j E Hb)].
  rewrite (gxi1_0RB0RC_1LC0RD_0LD1RA_1RC1LD j).
  exact (srun_sound tm true true che1_0RB0RC_1LC0RD_0LD1RA_1RC1LD CF1_0RB0RC_1LC0RD_0LD1RA_1RC1LD B11_0RB0RC_1LC0RD_0LD1RA_1RC1LD 4 15
           run_exit1_0RB0RC_1LC0RD_0LD1RA_1RC1LD [] [] j ltac:(reflexivity) ltac:(reflexivity)).
Qed.

(** The overflow arm, composed.  The [Theta(2^j)] middle is the [exists n]
    inside [NestedLapHalf.inner_to_half_lift]: the inner counter runs from
    [pow2 (S j)] to [half2 j] -- HALF its octave -- and stops there. *)
Lemma lapo1_0RB0RC_1LC0RD_0LD1RA_1RC1LD : forall p j, cview p = (S (S j), None) -> podd p = true ->
  exists n c', csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intros p j E Hb.
  exact (nested_overflow_half_lift tm Cc Cin1 lapin1_0RB0RC_1LC0RD_0LD1RA_1RC1LD p j
           (hbo1_0RB0RC_1LC0RD_0LD1RA_1RC1LD p j E Hb) (hxe1_0RB0RC_1LC0RD_0LD1RA_1RC1LD p j E Hb)).
Qed.

(** *** the overflow branch out of an octave of parity false.  It CROSSES into
    the other parity's frame, which is why one chain per parity is not a
    convenience: the two have different landings. *)
Lemma gso0_0RB0RC_1LC0RD_0LD1RA_1RC1LD : forall p j, cview p = (S (S j), None) -> podd p = false ->
  Cc p = cden [] [] j B00_0RB0RC_1LC0RD_0LD1RA_1RC1LD.
Proof.
  intros p j E Hb. destruct (Alph_01_11_11.cview_none_Alph_01_11_11 p (S j) E) as (H1 & _).
  unfold Cc_0RB0RC_1LC0RD_0LD1RA_1RC1LD. rewrite Hb.
  unfold cden, B00_0RB0RC_1LC0RD_0LD1RA_1RC1LD; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia. replace (0 * j + 0) with 0 by lia.
  rewrite H1. rshape_0RB0RC_1LC0RD_0LD1RA_1RC1LD.
Qed.

Lemma geo0_0RB0RC_1LC0RD_0LD1RA_1RC1LD : forall p j, cview p = (S (S j), None) -> podd p = false ->
  cden [] [] j B10_0RB0RC_1LC0RD_0LD1RA_1RC1LD = Cc (Pos.succ p).
Proof.
  intros p j E Hb. destruct (Alph_01_11_11.cview_none_Alph_01_11_11 p (S j) E) as (_ & H2).
  unfold Cc_0RB0RC_1LC0RD_0LD1RA_1RC1LD. rewrite (podd_succ_fill p (S j) E), Hb. cbn [negb].
  unfold cden, B10_0RB0RC_1LC0RD_0LD1RA_1RC1LD; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 2) with (S (S j)) by lia. replace (0 * j + 0) with 0 by lia.
  rewrite H2. rshape_0RB0RC_1LC0RD_0LD1RA_1RC1LD.
Qed.

Lemma lapo0_0RB0RC_1LC0RD_0LD1RA_1RC1LD : forall p j, cview p = (S (S j), None) -> podd p = false ->
  exists n c', csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intros p j E Hb.
  exists (4 * j + 10), (cden [] [] j B10_0RB0RC_1LC0RD_0LD1RA_1RC1LD).
  split; [| split; [f_equal; exact (geo0_0RB0RC_1LC0RD_0LD1RA_1RC1LD p j E Hb) | lia]].
  rewrite (gso0_0RB0RC_1LC0RD_0LD1RA_1RC1LD p j E Hb).
  exact (srun_sound tm true true cho0_0RB0RC_1LC0RD_0LD1RA_1RC1LD B00_0RB0RC_1LC0RD_0LD1RA_1RC1LD B10_0RB0RC_1LC0RD_0LD1RA_1RC1LD 4 10
           run_ovf0_0RB0RC_1LC0RD_0LD1RA_1RC1LD [] [] j ltac:(reflexivity) ltac:(reflexivity)).
Qed.

(** ** The lap *)

Lemma lapo_0RB0RC_1LC0RD_0LD1RA_1RC1LD : forall p j, cview p = (S (S j), None) ->
  exists n c', csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intros p j E. destruct (podd p) eqn:Hb.
  - exact (lapo1_0RB0RC_1LC0RD_0LD1RA_1RC1LD p j E Hb).
  - exact (lapo0_0RB0RC_1LC0RD_0LD1RA_1RC1LD p j E Hb).
Qed.

(** [j = 0] is [p = 1] ([IXPGadgets.cview_none_shape]), which is below [8]:
    the peel's leftover case is refuted rather than proved. *)
Lemma lap_0RB0RC_1LC0RD_0LD1RA_1RC1LD : forall p, (8 <= p)%positive -> exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intros p Hp. destruct (cview p) as [j oq] eqn:E; destruct oq as [q0|].
  - destruct (lapi_0RB0RC_1LC0RD_0LD1RA_1RC1LD p j q0 E) as (n & c' & Hn & Hr & Hl).
    exists n, c'. split; [exact Hr | split; [exact Hl | exact Hn]].
  - destruct (cview_pos p j E) as (j' & ->).
    destruct j' as [|j''].
    + exfalso. rewrite (cview_none_shape p 0 E) in Hp.
      apply Hp. vm_compute. reflexivity.
    + exact (lapo_0RB0RC_1LC0RD_0LD1RA_1RC1LD p j'' E).
Qed.

(** ** Bootstrap *)

Lemma boot_0RB0RC_1LC0RD_0LD1RA_1RC1LD : exists t0, stepn tm t0 InitES = Some (lift (Cc 8)).
Proof.
  exists 88.
  assert (H : match csteps tm 88 c0 with
              | Some c => ceqb c (Cc 8) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 88 c0) as [c|] eqn:E; [|discriminate].
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
    [lapo_0RB0RC_1LC0RD_0LD1RA_1RC1LD] to cross the octave boundary. *)

Lemma viso1_0RB0RC_1LC0RD_0LD1RA_1RC1LD : forall (l : list lstep) (q : St),
  srun_st tm true true l B01_0RB0RC_1LC0RD_0LD1RA_1RC1LD = Some q ->
  forall p j, cview p = (S (S j), None) -> podd p = true ->
  exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros l q Hst p j E Hb.
  apply (vis_of_run tm Cc true true l B01_0RB0RC_1LC0RD_0LD1RA_1RC1LD p j [] []);
    [exact Hst | reflexivity | reflexivity | exact (gso1_0RB0RC_1LC0RD_0LD1RA_1RC1LD p j E Hb)].
Qed.

Lemma viso0_0RB0RC_1LC0RD_0LD1RA_1RC1LD : forall (l : list lstep) (q : St),
  srun_st tm true true l B00_0RB0RC_1LC0RD_0LD1RA_1RC1LD = Some q ->
  forall p j, cview p = (S (S j), None) -> podd p = false ->
  exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros l q Hst p j E Hb.
  apply (vis_of_run tm Cc true true l B00_0RB0RC_1LC0RD_0LD1RA_1RC1LD p j [] []);
    [exact Hst | reflexivity | reflexivity | exact (gso0_0RB0RC_1LC0RD_0LD1RA_1RC1LD p j E Hb)].
Qed.

(** State StA at the peel's leftover overflow anchor [p = 1]. *)
Lemma viszStA_0RB0RC_1LC0RD_0LD1RA_1RC1LD : exists k c, csteps tm k (Cc 1) = Some c /\ fst c = StA.
Proof. exists 5. eexists. split; [vm_compute; reflexivity | reflexivity]. Qed.

(** State StB at the peel's leftover overflow anchor [p = 1]. *)
Lemma viszStB_0RB0RC_1LC0RD_0LD1RA_1RC1LD : exists k c, csteps tm k (Cc 1) = Some c /\ fst c = StB.
Proof. exists 21. eexists. split; [vm_compute; reflexivity | reflexivity]. Qed.

(** State StC at the peel's leftover overflow anchor [p = 1]. *)
Lemma viszStC_0RB0RC_1LC0RD_0LD1RA_1RC1LD : exists k c, csteps tm k (Cc 1) = Some c /\ fst c = StC.
Proof. exists 0. eexists. split; [vm_compute; reflexivity | reflexivity]. Qed.

(** State StD at the peel's leftover overflow anchor [p = 1]. *)
Lemma viszStD_0RB0RC_1LC0RD_0LD1RA_1RC1LD : exists k c, csteps tm k (Cc 1) = Some c /\ fst c = StD.
Proof. exists 1. eexists. split; [vm_compute; reflexivity | reflexivity]. Qed.

Lemma vis_0RB0RC_1LC0RD_0LD1RA_1RC1LD : forall p q, (8 <= p)%positive ->
  exists k e, stepn tm k (lift (Cc p)) = Some e /\ fst e = q.
Proof.
  intros p q Hp.
  assert (H2 : (2 <= p)%positive).
  { apply Pos.le_trans with (8)%positive; [| exact Hp].
    unfold Pos.le; vm_compute; discriminate. }
  destruct q.
  - (* StA fires in both overflow arms *)
    apply (vis_via_ovf_lift tm Cc lapi_0RB0RC_1LC0RD_0LD1RA_1RC1LD StA).
    intros p1 j1 E1. destruct j1 as [|j2].
    + assert (H1 : p1 = 1%positive)
        by (rewrite (cview_none_shape p1 0 E1); reflexivity).
      subst p1. apply vis_lift_of_csteps. exact viszStA_0RB0RC_1LC0RD_0LD1RA_1RC1LD.
    + apply vis_lift_of_csteps. destruct (podd p1) eqn:Hb1.
      * exact (viso1_0RB0RC_1LC0RD_0LD1RA_1RC1LD [SWin 2; SCycL 2 0; SWin 3; SWinL 3] StA ltac:(vm_compute; reflexivity)
                 p1 j2 E1 Hb1).
      * exact (viso0_0RB0RC_1LC0RD_0LD1RA_1RC1LD [SWin 2; SCycL 2 0; SWin 5] StA ltac:(vm_compute; reflexivity)
                 p1 j2 E1 Hb1).
  - (* StB fires in the parity-true arm ONLY -- LapCertGluePar *)
    apply (vis_via_ovf_par_lift tm Cc lapi_0RB0RC_1LC0RD_0LD1RA_1RC1LD lapo_0RB0RC_1LC0RD_0LD1RA_1RC1LD true StB);
      [| exact H2].
    intros p1 j2 E1 Hb1. apply vis_lift_of_csteps.
    exact (viso1_0RB0RC_1LC0RD_0LD1RA_1RC1LD [SWin 2; SCycL 2 0; SWin 3; SWinL 5; SCycR 2; SWin 3] StB ltac:(vm_compute; reflexivity)
             p1 j2 E1 Hb1).
  - (* StC fires in both overflow arms *)
    apply (vis_via_ovf_lift tm Cc lapi_0RB0RC_1LC0RD_0LD1RA_1RC1LD StC).
    intros p1 j1 E1. destruct j1 as [|j2].
    + assert (H1 : p1 = 1%positive)
        by (rewrite (cview_none_shape p1 0 E1); reflexivity).
      subst p1. apply vis_lift_of_csteps. exact viszStC_0RB0RC_1LC0RD_0LD1RA_1RC1LD.
    + apply vis_lift_of_csteps. destruct (podd p1) eqn:Hb1.
      * exact (viso1_0RB0RC_1LC0RD_0LD1RA_1RC1LD [] StC ltac:(vm_compute; reflexivity)
                 p1 j2 E1 Hb1).
      * exact (viso0_0RB0RC_1LC0RD_0LD1RA_1RC1LD [] StC ltac:(vm_compute; reflexivity)
                 p1 j2 E1 Hb1).
  - (* StD fires in both overflow arms *)
    apply (vis_via_ovf_lift tm Cc lapi_0RB0RC_1LC0RD_0LD1RA_1RC1LD StD).
    intros p1 j1 E1. destruct j1 as [|j2].
    + assert (H1 : p1 = 1%positive)
        by (rewrite (cview_none_shape p1 0 E1); reflexivity).
      subst p1. apply vis_lift_of_csteps. exact viszStD_0RB0RC_1LC0RD_0LD1RA_1RC1LD.
    + apply vis_lift_of_csteps. destruct (podd p1) eqn:Hb1.
      * exact (viso1_0RB0RC_1LC0RD_0LD1RA_1RC1LD [SWin 1] StD ltac:(vm_compute; reflexivity)
                 p1 j2 E1 Hb1).
      * exact (viso0_0RB0RC_1LC0RD_0LD1RA_1RC1LD [SWin 1] StD ltac:(vm_compute; reflexivity)
                 p1 j2 E1 Hb1).
Qed.

Theorem nqh_0RB0RC_1LC0RD_0LD1RA_1RC1LD : NeverQuasiHaltsSt tm.
Proof. apply (glue_neverqh_lift tm Cc 8). - exact boot_0RB0RC_1LC0RD_0LD1RA_1RC1LD. - intros p Hp. apply (lap_0RB0RC_1LC0RD_0LD1RA_1RC1LD p Hp). - intros p q Hp. apply (vis_0RB0RC_1LC0RD_0LD1RA_1RC1LD p q Hp). Qed.

Theorem nonhalt_0RB0RC_1LC0RD_0LD1RA_1RC1LD : NonHalt tm.
Proof. apply never_qh_nonhalt, nqh_0RB0RC_1LC0RD_0LD1RA_1RC1LD. Qed.
