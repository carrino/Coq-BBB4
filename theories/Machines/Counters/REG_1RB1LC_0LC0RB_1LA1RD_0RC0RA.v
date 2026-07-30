(** * REG_1RB1LC_0LC0RB_1LA1RD_0RC0RA: machine 1RB1LC_0LC0RB_1LA1RD_0RC0RA, boarded by CERTIFICATE (TWO-FORM route).

    Auto-emitted by tools/counters/tailcert.py (UNTRUSTED emitter; the Coq
    kernel re-runs the checker on every line below).  A binary counter under
    the Ap_Alph_00_01_1 digit alphabet (Alph_00_01_1.v) whose anchor FRAME -- the state, the
    constant cells past the word and the far side -- is a function of the
    PARITY of the octave [p] lives in:

      Cc p = if podd p then (StB, (Ap_Alph_00_01_1 p ++ [], S0, []))
                       else (StB, (Ap_Alph_00_01_1 p ++ [], S0, []))

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
                the other parity's frame: parity true FLAT 4*j+14; parity false FLAT 4*j+14

    The overflow arm is stated one peel deeper than the flat route's: its
    source carries a unit copy in the prefix and its landing counts
    [1*j+2] blocks, so the reindex leaves [cview p = (1, None)] (that is,
    [p = 1]) behind.  [lap] refutes that case from [8 <= p]; the visit
    premise, which ranges over every overflow anchor, discharges it as one
    concrete run from [Cc 1].

    Differentially validated against the raw simulator on EVERY branch --
    step counts AND configurations -- for 192 anchors, 0 nested overflows, 0 inner laps.
    Axiom footprint: [functional_extensionality_dep] (via [CTape.lift]). *)
From Coq Require Import Arith Lia Bool List PArith Wellfounded.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape LapGlue MonoCounter JpCounter
                                  Alph_00_01_1 LapCertGlue LapCertGlueLift
                                  IXPGadgets NestedLap NestedLapLift
                                  RegGlue.
From BBB4.Census Require Import TNF_QH.
From BBB4.Checkers Require Import LapDecider.
Import ListNotations.

Definition mk_1RB1LC_0LC0RB_1LA1RD_0RC0RA (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_1RB1LC_0LC0RB_1LA1RD_0RC0RA.

(** 1RB1LC_0LC0RB_1LA1RD_0RC0RA *)
Definition tm_1RB1LC_0LC0RB_1LA1RD_0RC0RA : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S1 DL StC
  | StB, S0 => mk S0 DL StC | StB, S1 => mk S0 DR StB
  | StC, S0 => mk S1 DL StA | StC, S1 => mk S1 DR StD
  | StD, S0 => mk S0 DR StC | StD, S1 => mk S0 DR StA end.
Local Notation tm := tm_1RB1LC_0LC0RB_1LA1RD_0RC0RA.

Definition Cc_1RB1LC_0LC0RB_1LA1RD_0RC0RA (p : positive) : cconf :=
  if podd p then (StB, (Ap_Alph_00_01_1 p ++ [], S0, []))
  else (StB, (Ap_Alph_00_01_1 p ++ [], S0, [])).
Local Notation Cc := Cc_1RB1LC_0LC0RB_1LA1RD_0RC0RA.

Ltac rshape_1RB1LC_0LC0RB_1LA1RD_0RC0RA :=
  cbn [rep app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r;
  reflexivity.

(** ** The certificate *)

(** *** the interior branch at octave parity true, SPLIT.  [j = 0]: the
    repeated block is absent, so the whole lap is concrete. *)
Definition Z01_1RB1LC_0LC0RB_1LA1RD_0RC0RA : sconf := mkC StB (mkS [S0;S0] [] 0 0 []) S0 (mkS [] [] 0 0 []).
Definition Z11_1RB1LC_0LC0RB_1LA1RD_0RC0RA : sconf := mkC StB (mkS [S0;S1] [] 0 0 []) S0 (mkS [] [] 0 0 []).
Definition chz1_1RB1LC_0LC0RB_1LA1RD_0RC0RA : list lstep := [SWin 4].

Lemma run_z1_1RB1LC_0LC0RB_1LA1RD_0RC0RA : srun tm false true chz1_1RB1LC_0LC0RB_1LA1RD_0RC0RA Z01_1RB1LC_0LC0RB_1LA1RD_0RC0RA = Some (Z11_1RB1LC_0LC0RB_1LA1RD_0RC0RA, 0, 4).
Proof. vm_compute. reflexivity. Qed.

(** [j = S j']: one copy of the unit sits in the PREFIX, so the head always
    has a concrete cell to step onto. *)
Definition P01_1RB1LC_0LC0RB_1LA1RD_0RC0RA : sconf := mkC StB (mkS [S0;S1] [S0;S1] 1 0 [S0;S0]) S0 (mkS [] [] 0 0 []).
Definition P11_1RB1LC_0LC0RB_1LA1RD_0RC0RA : sconf := mkC StB (mkS [S0;S0] [S0;S0] 1 0 [S0;S1]) S0 (mkS [] [] 0 0 []).
Definition chp1_1RB1LC_0LC0RB_1LA1RD_0RC0RA : list lstep := [SWin 2; SCycL 2 0; SWin 4; SCycR 2; SWin 2].

Lemma run_p1_1RB1LC_0LC0RB_1LA1RD_0RC0RA : srun tm false true chp1_1RB1LC_0LC0RB_1LA1RD_0RC0RA P01_1RB1LC_0LC0RB_1LA1RD_0RC0RA = Some (P11_1RB1LC_0LC0RB_1LA1RD_0RC0RA, 4, 8).
Proof. vm_compute. reflexivity. Qed.

(** *** the interior branch at octave parity false, SPLIT.  [j = 0]: the
    repeated block is absent, so the whole lap is concrete. *)
Definition Z00_1RB1LC_0LC0RB_1LA1RD_0RC0RA : sconf := mkC StB (mkS [S0;S0] [] 0 0 []) S0 (mkS [] [] 0 0 []).
Definition Z10_1RB1LC_0LC0RB_1LA1RD_0RC0RA : sconf := mkC StB (mkS [S0;S1] [] 0 0 []) S0 (mkS [] [] 0 0 []).
Definition chz0_1RB1LC_0LC0RB_1LA1RD_0RC0RA : list lstep := [SWin 4].

Lemma run_z0_1RB1LC_0LC0RB_1LA1RD_0RC0RA : srun tm false true chz0_1RB1LC_0LC0RB_1LA1RD_0RC0RA Z00_1RB1LC_0LC0RB_1LA1RD_0RC0RA = Some (Z10_1RB1LC_0LC0RB_1LA1RD_0RC0RA, 0, 4).
Proof. vm_compute. reflexivity. Qed.

(** [j = S j']: one copy of the unit sits in the PREFIX, so the head always
    has a concrete cell to step onto. *)
Definition P00_1RB1LC_0LC0RB_1LA1RD_0RC0RA : sconf := mkC StB (mkS [S0;S1] [S0;S1] 1 0 [S0;S0]) S0 (mkS [] [] 0 0 []).
Definition P10_1RB1LC_0LC0RB_1LA1RD_0RC0RA : sconf := mkC StB (mkS [S0;S0] [S0;S0] 1 0 [S0;S1]) S0 (mkS [] [] 0 0 []).
Definition chp0_1RB1LC_0LC0RB_1LA1RD_0RC0RA : list lstep := [SWin 2; SCycL 2 0; SWin 4; SCycR 2; SWin 2].

Lemma run_p0_1RB1LC_0LC0RB_1LA1RD_0RC0RA : srun tm false true chp0_1RB1LC_0LC0RB_1LA1RD_0RC0RA P00_1RB1LC_0LC0RB_1LA1RD_0RC0RA = Some (P10_1RB1LC_0LC0RB_1LA1RD_0RC0RA, 4, 8).
Proof. vm_compute. reflexivity. Qed.

Definition B01_1RB1LC_0LC0RB_1LA1RD_0RC0RA : sconf := mkC StB (mkS [S0;S1] [S0;S1] 1 0 [S1]) S0 (mkS [] [] 0 0 []).
Definition B11_1RB1LC_0LC0RB_1LA1RD_0RC0RA : sconf := mkC StB (mkS [] [S0;S0] 1 2 [S1]) S0 (mkS [] [] 0 0 []).

(** *** the overflow arm at octave parity true: FLAT, 4*j+14 steps *)
Definition cho1_1RB1LC_0LC0RB_1LA1RD_0RC0RA : list lstep := [SWin 2; SCycL 2 0; SWin 2; SRotR 1; SWin 3; SWinL 6; SCycR 2; SWin 1; SRotL 1; SRotL 2; SFoldL 2].

Lemma run_ovf1_1RB1LC_0LC0RB_1LA1RD_0RC0RA : srun tm true true cho1_1RB1LC_0LC0RB_1LA1RD_0RC0RA B01_1RB1LC_0LC0RB_1LA1RD_0RC0RA = Some (B11_1RB1LC_0LC0RB_1LA1RD_0RC0RA, 4, 14).
Proof. vm_compute. reflexivity. Qed.

Definition B00_1RB1LC_0LC0RB_1LA1RD_0RC0RA : sconf := mkC StB (mkS [S0;S1] [S0;S1] 1 0 [S1]) S0 (mkS [] [] 0 0 []).
Definition B10_1RB1LC_0LC0RB_1LA1RD_0RC0RA : sconf := mkC StB (mkS [] [S0;S0] 1 2 [S1]) S0 (mkS [] [] 0 0 []).

(** *** the overflow arm at octave parity false: FLAT, 4*j+14 steps *)
Definition cho0_1RB1LC_0LC0RB_1LA1RD_0RC0RA : list lstep := [SWin 2; SCycL 2 0; SWin 2; SRotR 1; SWin 3; SWinL 6; SCycR 2; SWin 1; SRotL 1; SRotL 2; SFoldL 2].

Lemma run_ovf0_1RB1LC_0LC0RB_1LA1RD_0RC0RA : srun tm true true cho0_1RB1LC_0LC0RB_1LA1RD_0RC0RA B00_1RB1LC_0LC0RB_1LA1RD_0RC0RA = Some (B10_1RB1LC_0LC0RB_1LA1RD_0RC0RA, 4, 14).
Proof. vm_compute. reflexivity. Qed.

(** ** Anchor glue -- the only per-machine mathematics *)

Lemma gz1_1RB1LC_0LC0RB_1LA1RD_0RC0RA : forall p q0, cview p = (0, Some q0) -> podd p = true ->
  Cc p = cden (Ap_Alph_00_01_1 q0 ++ []) [] 0 Z01_1RB1LC_0LC0RB_1LA1RD_0RC0RA /\
  lift (cden (Ap_Alph_00_01_1 q0 ++ []) [] 0 Z11_1RB1LC_0LC0RB_1LA1RD_0RC0RA) = lift (Cc (Pos.succ p)).
Proof.
  intros p q0 E Hb. destruct (Alph_00_01_1.cview_some_Alph_00_01_1 p 0 q0 E) as (H1 & H2).
  unfold Cc_1RB1LC_0LC0RB_1LA1RD_0RC0RA. rewrite (podd_succ_int p 0 q0 E), Hb.
  unfold cden, Z01_1RB1LC_0LC0RB_1LA1RD_0RC0RA, Z11_1RB1LC_0LC0RB_1LA1RD_0RC0RA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  split.
  - rewrite H1. rshape_1RB1LC_0LC0RB_1LA1RD_0RC0RA.
  - f_equal. rewrite H2. rshape_1RB1LC_0LC0RB_1LA1RD_0RC0RA.
Qed.

Lemma gp1_1RB1LC_0LC0RB_1LA1RD_0RC0RA : forall p j q0, cview p = (S j, Some q0) -> podd p = true ->
  Cc p = cden (Ap_Alph_00_01_1 q0 ++ []) [] j P01_1RB1LC_0LC0RB_1LA1RD_0RC0RA /\
  lift (cden (Ap_Alph_00_01_1 q0 ++ []) [] j P11_1RB1LC_0LC0RB_1LA1RD_0RC0RA) = lift (Cc (Pos.succ p)).
Proof.
  intros p j q0 E Hb. destruct (Alph_00_01_1.cview_some_Alph_00_01_1 p (S j) q0 E) as (H1 & H2).
  unfold Cc_1RB1LC_0LC0RB_1LA1RD_0RC0RA. rewrite (podd_succ_int p (S j) q0 E), Hb.
  unfold cden, P01_1RB1LC_0LC0RB_1LA1RD_0RC0RA, P11_1RB1LC_0LC0RB_1LA1RD_0RC0RA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia. replace (0 * j + 0) with 0 by lia.
  split.
  - rewrite H1. rshape_1RB1LC_0LC0RB_1LA1RD_0RC0RA.
  - f_equal. rewrite H2. rshape_1RB1LC_0LC0RB_1LA1RD_0RC0RA.
Qed.

Lemma lapi1_1RB1LC_0LC0RB_1LA1RD_0RC0RA : forall p j q0, cview p = (j, Some q0) -> podd p = true ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof.
  intros p j q0 E Hb. destruct j as [|j'].
  - destruct (gz1_1RB1LC_0LC0RB_1LA1RD_0RC0RA p q0 E Hb) as (HA & HB).
    exists (0 * 0 + 4), (cden (Ap_Alph_00_01_1 q0 ++ []) [] 0 Z11_1RB1LC_0LC0RB_1LA1RD_0RC0RA).
    split; [lia|]. split; [| exact HB]. rewrite HA.
    exact (srun_sound tm false true chz1_1RB1LC_0LC0RB_1LA1RD_0RC0RA Z01_1RB1LC_0LC0RB_1LA1RD_0RC0RA Z11_1RB1LC_0LC0RB_1LA1RD_0RC0RA 0 4
             run_z1_1RB1LC_0LC0RB_1LA1RD_0RC0RA (Ap_Alph_00_01_1 q0 ++ []) [] 0
             ltac:(discriminate) ltac:(reflexivity)).
  - destruct (gp1_1RB1LC_0LC0RB_1LA1RD_0RC0RA p j' q0 E Hb) as (HA & HB).
    exists (4 * j' + 8), (cden (Ap_Alph_00_01_1 q0 ++ []) [] j' P11_1RB1LC_0LC0RB_1LA1RD_0RC0RA).
    split; [lia|]. split; [| exact HB]. rewrite HA.
    exact (srun_sound tm false true chp1_1RB1LC_0LC0RB_1LA1RD_0RC0RA P01_1RB1LC_0LC0RB_1LA1RD_0RC0RA P11_1RB1LC_0LC0RB_1LA1RD_0RC0RA 4 8
             run_p1_1RB1LC_0LC0RB_1LA1RD_0RC0RA (Ap_Alph_00_01_1 q0 ++ []) [] j'
             ltac:(discriminate) ltac:(reflexivity)).
Qed.

Lemma gz0_1RB1LC_0LC0RB_1LA1RD_0RC0RA : forall p q0, cview p = (0, Some q0) -> podd p = false ->
  Cc p = cden (Ap_Alph_00_01_1 q0 ++ []) [] 0 Z00_1RB1LC_0LC0RB_1LA1RD_0RC0RA /\
  lift (cden (Ap_Alph_00_01_1 q0 ++ []) [] 0 Z10_1RB1LC_0LC0RB_1LA1RD_0RC0RA) = lift (Cc (Pos.succ p)).
Proof.
  intros p q0 E Hb. destruct (Alph_00_01_1.cview_some_Alph_00_01_1 p 0 q0 E) as (H1 & H2).
  unfold Cc_1RB1LC_0LC0RB_1LA1RD_0RC0RA. rewrite (podd_succ_int p 0 q0 E), Hb.
  unfold cden, Z00_1RB1LC_0LC0RB_1LA1RD_0RC0RA, Z10_1RB1LC_0LC0RB_1LA1RD_0RC0RA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  split.
  - rewrite H1. rshape_1RB1LC_0LC0RB_1LA1RD_0RC0RA.
  - f_equal. rewrite H2. rshape_1RB1LC_0LC0RB_1LA1RD_0RC0RA.
Qed.

Lemma gp0_1RB1LC_0LC0RB_1LA1RD_0RC0RA : forall p j q0, cview p = (S j, Some q0) -> podd p = false ->
  Cc p = cden (Ap_Alph_00_01_1 q0 ++ []) [] j P00_1RB1LC_0LC0RB_1LA1RD_0RC0RA /\
  lift (cden (Ap_Alph_00_01_1 q0 ++ []) [] j P10_1RB1LC_0LC0RB_1LA1RD_0RC0RA) = lift (Cc (Pos.succ p)).
Proof.
  intros p j q0 E Hb. destruct (Alph_00_01_1.cview_some_Alph_00_01_1 p (S j) q0 E) as (H1 & H2).
  unfold Cc_1RB1LC_0LC0RB_1LA1RD_0RC0RA. rewrite (podd_succ_int p (S j) q0 E), Hb.
  unfold cden, P00_1RB1LC_0LC0RB_1LA1RD_0RC0RA, P10_1RB1LC_0LC0RB_1LA1RD_0RC0RA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia. replace (0 * j + 0) with 0 by lia.
  split.
  - rewrite H1. rshape_1RB1LC_0LC0RB_1LA1RD_0RC0RA.
  - f_equal. rewrite H2. rshape_1RB1LC_0LC0RB_1LA1RD_0RC0RA.
Qed.

Lemma lapi0_1RB1LC_0LC0RB_1LA1RD_0RC0RA : forall p j q0, cview p = (j, Some q0) -> podd p = false ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof.
  intros p j q0 E Hb. destruct j as [|j'].
  - destruct (gz0_1RB1LC_0LC0RB_1LA1RD_0RC0RA p q0 E Hb) as (HA & HB).
    exists (0 * 0 + 4), (cden (Ap_Alph_00_01_1 q0 ++ []) [] 0 Z10_1RB1LC_0LC0RB_1LA1RD_0RC0RA).
    split; [lia|]. split; [| exact HB]. rewrite HA.
    exact (srun_sound tm false true chz0_1RB1LC_0LC0RB_1LA1RD_0RC0RA Z00_1RB1LC_0LC0RB_1LA1RD_0RC0RA Z10_1RB1LC_0LC0RB_1LA1RD_0RC0RA 0 4
             run_z0_1RB1LC_0LC0RB_1LA1RD_0RC0RA (Ap_Alph_00_01_1 q0 ++ []) [] 0
             ltac:(discriminate) ltac:(reflexivity)).
  - destruct (gp0_1RB1LC_0LC0RB_1LA1RD_0RC0RA p j' q0 E Hb) as (HA & HB).
    exists (4 * j' + 8), (cden (Ap_Alph_00_01_1 q0 ++ []) [] j' P10_1RB1LC_0LC0RB_1LA1RD_0RC0RA).
    split; [lia|]. split; [| exact HB]. rewrite HA.
    exact (srun_sound tm false true chp0_1RB1LC_0LC0RB_1LA1RD_0RC0RA P00_1RB1LC_0LC0RB_1LA1RD_0RC0RA P10_1RB1LC_0LC0RB_1LA1RD_0RC0RA 4 8
             run_p0_1RB1LC_0LC0RB_1LA1RD_0RC0RA (Ap_Alph_00_01_1 q0 ++ []) [] j'
             ltac:(discriminate) ltac:(reflexivity)).
Qed.

Lemma lapi_1RB1LC_0LC0RB_1LA1RD_0RC0RA : forall p j q0, cview p = (j, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof.
  intros p j q0 E. destruct (podd p) eqn:Hb.
  - exact (lapi1_1RB1LC_0LC0RB_1LA1RD_0RC0RA p j q0 E Hb).
  - exact (lapi0_1RB1LC_0LC0RB_1LA1RD_0RC0RA p j q0 E Hb).
Qed.

(** *** the overflow branch out of an octave of parity true.  It CROSSES into
    the other parity's frame, which is why one chain per parity is not a
    convenience: the two have different landings. *)
Lemma gso1_1RB1LC_0LC0RB_1LA1RD_0RC0RA : forall p j, cview p = (S (S j), None) -> podd p = true ->
  Cc p = cden [] [] j B01_1RB1LC_0LC0RB_1LA1RD_0RC0RA.
Proof.
  intros p j E Hb. destruct (Alph_00_01_1.cview_none_Alph_00_01_1 p (S j) E) as (H1 & _).
  unfold Cc_1RB1LC_0LC0RB_1LA1RD_0RC0RA. rewrite Hb.
  unfold cden, B01_1RB1LC_0LC0RB_1LA1RD_0RC0RA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia. replace (0 * j + 0) with 0 by lia.
  rewrite H1. rshape_1RB1LC_0LC0RB_1LA1RD_0RC0RA.
Qed.

Lemma geo1_1RB1LC_0LC0RB_1LA1RD_0RC0RA : forall p j, cview p = (S (S j), None) -> podd p = true ->
  cden [] [] j B11_1RB1LC_0LC0RB_1LA1RD_0RC0RA = Cc (Pos.succ p).
Proof.
  intros p j E Hb. destruct (Alph_00_01_1.cview_none_Alph_00_01_1 p (S j) E) as (_ & H2).
  unfold Cc_1RB1LC_0LC0RB_1LA1RD_0RC0RA. rewrite (podd_succ_fill p (S j) E), Hb. cbn [negb].
  unfold cden, B11_1RB1LC_0LC0RB_1LA1RD_0RC0RA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 2) with (S (S j)) by lia. replace (0 * j + 0) with 0 by lia.
  rewrite H2. rshape_1RB1LC_0LC0RB_1LA1RD_0RC0RA.
Qed.

Lemma lapo1_1RB1LC_0LC0RB_1LA1RD_0RC0RA : forall p j, cview p = (S (S j), None) -> podd p = true ->
  exists n c', csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intros p j E Hb.
  exists (4 * j + 14), (cden [] [] j B11_1RB1LC_0LC0RB_1LA1RD_0RC0RA).
  split; [| split; [f_equal; exact (geo1_1RB1LC_0LC0RB_1LA1RD_0RC0RA p j E Hb) | lia]].
  rewrite (gso1_1RB1LC_0LC0RB_1LA1RD_0RC0RA p j E Hb).
  exact (srun_sound tm true true cho1_1RB1LC_0LC0RB_1LA1RD_0RC0RA B01_1RB1LC_0LC0RB_1LA1RD_0RC0RA B11_1RB1LC_0LC0RB_1LA1RD_0RC0RA 4 14
           run_ovf1_1RB1LC_0LC0RB_1LA1RD_0RC0RA [] [] j ltac:(reflexivity) ltac:(reflexivity)).
Qed.

(** *** the overflow branch out of an octave of parity false.  It CROSSES into
    the other parity's frame, which is why one chain per parity is not a
    convenience: the two have different landings. *)
Lemma gso0_1RB1LC_0LC0RB_1LA1RD_0RC0RA : forall p j, cview p = (S (S j), None) -> podd p = false ->
  Cc p = cden [] [] j B00_1RB1LC_0LC0RB_1LA1RD_0RC0RA.
Proof.
  intros p j E Hb. destruct (Alph_00_01_1.cview_none_Alph_00_01_1 p (S j) E) as (H1 & _).
  unfold Cc_1RB1LC_0LC0RB_1LA1RD_0RC0RA. rewrite Hb.
  unfold cden, B00_1RB1LC_0LC0RB_1LA1RD_0RC0RA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia. replace (0 * j + 0) with 0 by lia.
  rewrite H1. rshape_1RB1LC_0LC0RB_1LA1RD_0RC0RA.
Qed.

Lemma geo0_1RB1LC_0LC0RB_1LA1RD_0RC0RA : forall p j, cview p = (S (S j), None) -> podd p = false ->
  cden [] [] j B10_1RB1LC_0LC0RB_1LA1RD_0RC0RA = Cc (Pos.succ p).
Proof.
  intros p j E Hb. destruct (Alph_00_01_1.cview_none_Alph_00_01_1 p (S j) E) as (_ & H2).
  unfold Cc_1RB1LC_0LC0RB_1LA1RD_0RC0RA. rewrite (podd_succ_fill p (S j) E), Hb. cbn [negb].
  unfold cden, B10_1RB1LC_0LC0RB_1LA1RD_0RC0RA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 2) with (S (S j)) by lia. replace (0 * j + 0) with 0 by lia.
  rewrite H2. rshape_1RB1LC_0LC0RB_1LA1RD_0RC0RA.
Qed.

Lemma lapo0_1RB1LC_0LC0RB_1LA1RD_0RC0RA : forall p j, cview p = (S (S j), None) -> podd p = false ->
  exists n c', csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intros p j E Hb.
  exists (4 * j + 14), (cden [] [] j B10_1RB1LC_0LC0RB_1LA1RD_0RC0RA).
  split; [| split; [f_equal; exact (geo0_1RB1LC_0LC0RB_1LA1RD_0RC0RA p j E Hb) | lia]].
  rewrite (gso0_1RB1LC_0LC0RB_1LA1RD_0RC0RA p j E Hb).
  exact (srun_sound tm true true cho0_1RB1LC_0LC0RB_1LA1RD_0RC0RA B00_1RB1LC_0LC0RB_1LA1RD_0RC0RA B10_1RB1LC_0LC0RB_1LA1RD_0RC0RA 4 14
           run_ovf0_1RB1LC_0LC0RB_1LA1RD_0RC0RA [] [] j ltac:(reflexivity) ltac:(reflexivity)).
Qed.

(** ** The lap *)

Lemma lapo_1RB1LC_0LC0RB_1LA1RD_0RC0RA : forall p j, cview p = (S (S j), None) ->
  exists n c', csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intros p j E. destruct (podd p) eqn:Hb.
  - exact (lapo1_1RB1LC_0LC0RB_1LA1RD_0RC0RA p j E Hb).
  - exact (lapo0_1RB1LC_0LC0RB_1LA1RD_0RC0RA p j E Hb).
Qed.

(** [j = 0] is [p = 1] ([IXPGadgets.cview_none_shape]), which is below [8]:
    the peel's leftover case is refuted rather than proved. *)
Lemma lap_1RB1LC_0LC0RB_1LA1RD_0RC0RA : forall p, (8 <= p)%positive -> exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intros p Hp. destruct (cview p) as [j oq] eqn:E; destruct oq as [q0|].
  - destruct (lapi_1RB1LC_0LC0RB_1LA1RD_0RC0RA p j q0 E) as (n & c' & Hn & Hr & Hl).
    exists n, c'. split; [exact Hr | split; [exact Hl | exact Hn]].
  - destruct (cview_pos p j E) as (j' & ->).
    destruct j' as [|j''].
    + exfalso. rewrite (cview_none_shape p 0 E) in Hp.
      apply Hp. vm_compute. reflexivity.
    + exact (lapo_1RB1LC_0LC0RB_1LA1RD_0RC0RA p j'' E).
Qed.

(** ** Bootstrap *)

Lemma boot_1RB1LC_0LC0RB_1LA1RD_0RC0RA : exists t0, stepn tm t0 InitES = Some (lift (Cc 8)).
Proof.
  exists 55.
  assert (H : match csteps tm 55 c0 with
              | Some c => ceqb c (Cc 8) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 55 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** ** Visits

    [LapCertGlueLift.vis_via_ovf_lift] asks for a witness at EVERY overflow
    anchor, and the overflow anchors alternate frames -- so the witness is a
    prefix of whichever of the two overflow chains that parity uses, plus the
    peel's leftover [p = 1]. *)

Lemma viso1_1RB1LC_0LC0RB_1LA1RD_0RC0RA : forall (l : list lstep) (q : St),
  srun_st tm true true l B01_1RB1LC_0LC0RB_1LA1RD_0RC0RA = Some q ->
  forall p j, cview p = (S (S j), None) -> podd p = true ->
  exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros l q Hst p j E Hb.
  apply (vis_of_run tm Cc true true l B01_1RB1LC_0LC0RB_1LA1RD_0RC0RA p j [] []);
    [exact Hst | reflexivity | reflexivity | exact (gso1_1RB1LC_0LC0RB_1LA1RD_0RC0RA p j E Hb)].
Qed.

Lemma viso0_1RB1LC_0LC0RB_1LA1RD_0RC0RA : forall (l : list lstep) (q : St),
  srun_st tm true true l B00_1RB1LC_0LC0RB_1LA1RD_0RC0RA = Some q ->
  forall p j, cview p = (S (S j), None) -> podd p = false ->
  exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros l q Hst p j E Hb.
  apply (vis_of_run tm Cc true true l B00_1RB1LC_0LC0RB_1LA1RD_0RC0RA p j [] []);
    [exact Hst | reflexivity | reflexivity | exact (gso0_1RB1LC_0LC0RB_1LA1RD_0RC0RA p j E Hb)].
Qed.

(** State StA at the peel's leftover overflow anchor [p = 1]. *)
Lemma viszStA_1RB1LC_0LC0RB_1LA1RD_0RC0RA : exists k c, csteps tm k (Cc 1) = Some c /\ fst c = StA.
Proof. exists 4. eexists. split; [vm_compute; reflexivity | reflexivity]. Qed.

(** State StB at the peel's leftover overflow anchor [p = 1]. *)
Lemma viszStB_1RB1LC_0LC0RB_1LA1RD_0RC0RA : exists k c, csteps tm k (Cc 1) = Some c /\ fst c = StB.
Proof. exists 0. eexists. split; [vm_compute; reflexivity | reflexivity]. Qed.

(** State StC at the peel's leftover overflow anchor [p = 1]. *)
Lemma viszStC_1RB1LC_0LC0RB_1LA1RD_0RC0RA : exists k c, csteps tm k (Cc 1) = Some c /\ fst c = StC.
Proof. exists 1. eexists. split; [vm_compute; reflexivity | reflexivity]. Qed.

(** State StD at the peel's leftover overflow anchor [p = 1]. *)
Lemma viszStD_1RB1LC_0LC0RB_1LA1RD_0RC0RA : exists k c, csteps tm k (Cc 1) = Some c /\ fst c = StD.
Proof. exists 2. eexists. split; [vm_compute; reflexivity | reflexivity]. Qed.

Lemma vis_1RB1LC_0LC0RB_1LA1RD_0RC0RA : forall p q, (8 <= p)%positive ->
  exists k e, stepn tm k (lift (Cc p)) = Some e /\ fst e = q.
Proof.
  intros p q _.
  apply (vis_via_ovf_lift tm Cc lapi_1RB1LC_0LC0RB_1LA1RD_0RC0RA q).
  intros p1 j1 E1. destruct j1 as [|j2].
  - assert (H1 : p1 = 1%positive)
      by (rewrite (cview_none_shape p1 0 E1); reflexivity).
    subst p1. apply vis_lift_of_csteps. destruct q.
    + exact (viszStA_1RB1LC_0LC0RB_1LA1RD_0RC0RA).
    + exact (viszStB_1RB1LC_0LC0RB_1LA1RD_0RC0RA).
    + exact (viszStC_1RB1LC_0LC0RB_1LA1RD_0RC0RA).
    + exact (viszStD_1RB1LC_0LC0RB_1LA1RD_0RC0RA).
  - apply vis_lift_of_csteps. destruct (podd p1) eqn:Hb1.
    + destruct q.
      * exact (viso1_1RB1LC_0LC0RB_1LA1RD_0RC0RA [SWin 2] StA ltac:(vm_compute; reflexivity) p1 j2 E1 Hb1).
      * exact (viso1_1RB1LC_0LC0RB_1LA1RD_0RC0RA [] StB ltac:(vm_compute; reflexivity) p1 j2 E1 Hb1).
      * exact (viso1_1RB1LC_0LC0RB_1LA1RD_0RC0RA [SWin 1] StC ltac:(vm_compute; reflexivity) p1 j2 E1 Hb1).
      * exact (viso1_1RB1LC_0LC0RB_1LA1RD_0RC0RA [SWin 2; SCycL 2 0; SWin 2] StD ltac:(vm_compute; reflexivity) p1 j2 E1 Hb1).
    + destruct q.
      * exact (viso0_1RB1LC_0LC0RB_1LA1RD_0RC0RA [SWin 2] StA ltac:(vm_compute; reflexivity) p1 j2 E1 Hb1).
      * exact (viso0_1RB1LC_0LC0RB_1LA1RD_0RC0RA [] StB ltac:(vm_compute; reflexivity) p1 j2 E1 Hb1).
      * exact (viso0_1RB1LC_0LC0RB_1LA1RD_0RC0RA [SWin 1] StC ltac:(vm_compute; reflexivity) p1 j2 E1 Hb1).
      * exact (viso0_1RB1LC_0LC0RB_1LA1RD_0RC0RA [SWin 2; SCycL 2 0; SWin 2] StD ltac:(vm_compute; reflexivity) p1 j2 E1 Hb1).
Qed.

Theorem nqh_1RB1LC_0LC0RB_1LA1RD_0RC0RA : NeverQuasiHaltsSt tm.
Proof. apply (glue_neverqh_lift tm Cc 8). - exact boot_1RB1LC_0LC0RB_1LA1RD_0RC0RA. - intros p Hp. apply (lap_1RB1LC_0LC0RB_1LA1RD_0RC0RA p Hp). - intros p q Hp. apply (vis_1RB1LC_0LC0RB_1LA1RD_0RC0RA p q Hp). Qed.

Theorem nonhalt_1RB1LC_0LC0RB_1LA1RD_0RC0RA : NonHalt tm.
Proof. apply never_qh_nonhalt, nqh_1RB1LC_0LC0RB_1LA1RD_0RC0RA. Qed.
