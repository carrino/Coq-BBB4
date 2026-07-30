(** * REG_1RB1LA_0RC1RD_1LD0LB_0LA0RB: machine 1RB1LA_0RC1RD_1LD0LB_0LA0RB, boarded by CERTIFICATE (TWO-FORM route).

    Auto-emitted by tools/counters/tailcert.py (UNTRUSTED emitter; the Coq
    kernel re-runs the checker on every line below).  A binary counter under
    the Ap_Alph_10_11_11 digit alphabet (Alph_10_11_11.v) whose anchor FRAME -- the state, the
    constant cells past the word and the far side -- is a function of the
    PARITY of the octave [p] lives in:

      Cc p = if podd p then (StD, (Ap_Alph_10_11_11 p ++ [], S0, [S1]))
                       else (StD, (Ap_Alph_10_11_11 p ++ [], S0, [S1]))

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
                the other parity's frame: parity true NESTED, boot 4*j+23 then the inner counter then exit 4*j+25; parity false NESTED, boot 4*j+23 then the inner counter then exit 4*j+25

    The overflow arm is stated one peel deeper than the flat route's: its
    source carries a unit copy in the prefix and its landing counts
    [1*j+2] blocks, so the reindex leaves [cview p = (1, None)] (that is,
    [p = 1]) behind.  [lap] refutes that case from [8 <= p]; the visit
    premise, which ranges over every overflow anchor, discharges it as one
    concrete run from [Cc 1].

    Differentially validated against the raw simulator on EVERY branch --
    step counts AND configurations, and every inner lap of every nested overflow -- for 192 anchors, 4 nested overflows, 56 inner laps.
    Axiom footprint: [functional_extensionality_dep] (via [CTape.lift]). *)
From Coq Require Import Arith Lia Bool List PArith Wellfounded.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape LapGlue MonoCounter JpCounter
                                  Alph_10_11_11 ILCounter LapCertGlue LapCertGlueLift
                                  IXPGadgets NestedLap NestedLapLift
                                  RegGlue.
From BBB4.Census Require Import TNF_QH.
From BBB4.Checkers Require Import LapDecider.
Import ListNotations.

Definition mk_1RB1LA_0RC1RD_1LD0LB_0LA0RB (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_1RB1LA_0RC1RD_1LD0LB_0LA0RB.

(** 1RB1LA_0RC1RD_1LD0LB_0LA0RB *)
Definition tm_1RB1LA_0RC1RD_1LD0LB_0LA0RB : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S1 DL StA
  | StB, S0 => mk S0 DR StC | StB, S1 => mk S1 DR StD
  | StC, S0 => mk S1 DL StD | StC, S1 => mk S0 DL StB
  | StD, S0 => mk S0 DL StA | StD, S1 => mk S0 DR StB end.
Local Notation tm := tm_1RB1LA_0RC1RD_1LD0LB_0LA0RB.

Definition Cc_1RB1LA_0RC1RD_1LD0LB_0LA0RB (p : positive) : cconf :=
  if podd p then (StD, (Ap_Alph_10_11_11 p ++ [], S0, [S1]))
  else (StD, (Ap_Alph_10_11_11 p ++ [], S0, [S1])).
Local Notation Cc := Cc_1RB1LA_0RC1RD_1LD0LB_0LA0RB.

(** ** The INNER anchor family of the parity-true overflow arm -- the counter
    that arm re-runs, [Theta(2^j)] laps of it *)
Definition Cin1_1RB1LA_0RC1RD_1LD0LB_0LA0RB (v : positive) : cconf :=
  (StA, (Ip v ++ [S1], S0, [S1;S1;S0;S1])).
Local Notation Cin1 := Cin1_1RB1LA_0RC1RD_1LD0LB_0LA0RB.

(** ** The INNER anchor family of the parity-false overflow arm -- the counter
    that arm re-runs, [Theta(2^j)] laps of it *)
Definition Cin0_1RB1LA_0RC1RD_1LD0LB_0LA0RB (v : positive) : cconf :=
  (StA, (Ip v ++ [S1], S0, [S1;S1;S0;S1])).
Local Notation Cin0 := Cin0_1RB1LA_0RC1RD_1LD0LB_0LA0RB.

Ltac rshape_1RB1LA_0RC1RD_1LD0LB_0LA0RB :=
  cbn [rep app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r;
  reflexivity.

(** ** The certificate *)

(** *** the interior branch at octave parity true, SPLIT.  [j = 0]: the
    repeated block is absent, so the whole lap is concrete. *)
Definition Z01_1RB1LA_0RC1RD_1LD0LB_0LA0RB : sconf := mkC StD (mkS [S1;S0] [] 0 0 []) S0 (mkS [S1] [] 0 0 []).
Definition Z11_1RB1LA_0RC1RD_1LD0LB_0LA0RB : sconf := mkC StD (mkS [S1;S1] [] 0 0 []) S0 (mkS [S1] [] 0 0 []).
Definition chz1_1RB1LA_0RC1RD_1LD0LB_0LA0RB : list lstep := [SWin 4].

Lemma run_z1_1RB1LA_0RC1RD_1LD0LB_0LA0RB : srun tm false true chz1_1RB1LA_0RC1RD_1LD0LB_0LA0RB Z01_1RB1LA_0RC1RD_1LD0LB_0LA0RB = Some (Z11_1RB1LA_0RC1RD_1LD0LB_0LA0RB, 0, 4).
Proof. vm_compute. reflexivity. Qed.

(** [j = S j']: one copy of the unit sits in the PREFIX, so the head always
    has a concrete cell to step onto. *)
Definition P01_1RB1LA_0RC1RD_1LD0LB_0LA0RB : sconf := mkC StD (mkS [S1;S1] [S1;S1] 1 0 [S1;S0]) S0 (mkS [S1] [] 0 0 []).
Definition P11_1RB1LA_0RC1RD_1LD0LB_0LA0RB : sconf := mkC StD (mkS [S1;S0] [S1;S0] 1 0 [S1;S1]) S0 (mkS [S1] [] 0 0 []).
Definition chp1_1RB1LA_0RC1RD_1LD0LB_0LA0RB : list lstep := [SWin 2; SCycL 2 0; SWin 4; SCycR 2; SWin 2].

Lemma run_p1_1RB1LA_0RC1RD_1LD0LB_0LA0RB : srun tm false true chp1_1RB1LA_0RC1RD_1LD0LB_0LA0RB P01_1RB1LA_0RC1RD_1LD0LB_0LA0RB = Some (P11_1RB1LA_0RC1RD_1LD0LB_0LA0RB, 4, 8).
Proof. vm_compute. reflexivity. Qed.

(** *** the interior branch at octave parity false, SPLIT.  [j = 0]: the
    repeated block is absent, so the whole lap is concrete. *)
Definition Z00_1RB1LA_0RC1RD_1LD0LB_0LA0RB : sconf := mkC StD (mkS [S1;S0] [] 0 0 []) S0 (mkS [S1] [] 0 0 []).
Definition Z10_1RB1LA_0RC1RD_1LD0LB_0LA0RB : sconf := mkC StD (mkS [S1;S1] [] 0 0 []) S0 (mkS [S1] [] 0 0 []).
Definition chz0_1RB1LA_0RC1RD_1LD0LB_0LA0RB : list lstep := [SWin 4].

Lemma run_z0_1RB1LA_0RC1RD_1LD0LB_0LA0RB : srun tm false true chz0_1RB1LA_0RC1RD_1LD0LB_0LA0RB Z00_1RB1LA_0RC1RD_1LD0LB_0LA0RB = Some (Z10_1RB1LA_0RC1RD_1LD0LB_0LA0RB, 0, 4).
Proof. vm_compute. reflexivity. Qed.

(** [j = S j']: one copy of the unit sits in the PREFIX, so the head always
    has a concrete cell to step onto. *)
Definition P00_1RB1LA_0RC1RD_1LD0LB_0LA0RB : sconf := mkC StD (mkS [S1;S1] [S1;S1] 1 0 [S1;S0]) S0 (mkS [S1] [] 0 0 []).
Definition P10_1RB1LA_0RC1RD_1LD0LB_0LA0RB : sconf := mkC StD (mkS [S1;S0] [S1;S0] 1 0 [S1;S1]) S0 (mkS [S1] [] 0 0 []).
Definition chp0_1RB1LA_0RC1RD_1LD0LB_0LA0RB : list lstep := [SWin 2; SCycL 2 0; SWin 4; SCycR 2; SWin 2].

Lemma run_p0_1RB1LA_0RC1RD_1LD0LB_0LA0RB : srun tm false true chp0_1RB1LA_0RC1RD_1LD0LB_0LA0RB P00_1RB1LA_0RC1RD_1LD0LB_0LA0RB = Some (P10_1RB1LA_0RC1RD_1LD0LB_0LA0RB, 4, 8).
Proof. vm_compute. reflexivity. Qed.

Definition B01_1RB1LA_0RC1RD_1LD0LB_0LA0RB : sconf := mkC StD (mkS [S1;S1] [S1;S1] 1 0 [S1;S1]) S0 (mkS [S1] [] 0 0 []).
Definition B11_1RB1LA_0RC1RD_1LD0LB_0LA0RB : sconf := mkC StD (mkS [] [S1;S0] 1 2 [S1;S1]) S0 (mkS [S1] [] 0 0 []).

(** *** the overflow arm at octave parity true: boot 4*j+23, then the
    inner counter's laps, then exit 4*j+25 *)
Definition CS1_1RB1LA_0RC1RD_1LD0LB_0LA0RB : sconf := mkC StA (mkS [] [S1;S0] 1 0 [S1;S1]) S0 (mkS [S1;S1;S0;S1] [] 0 0 []).
Definition chb1_1RB1LA_0RC1RD_1LD0LB_0LA0RB : list lstep := [SWin 2; SCycL 2 0; SWin 2; SWinL 4; SCycR 2; SWin 14; SRotL 1; SWin 1].

Lemma run_boot1_1RB1LA_0RC1RD_1LD0LB_0LA0RB : srun tm true true chb1_1RB1LA_0RC1RD_1LD0LB_0LA0RB B01_1RB1LA_0RC1RD_1LD0LB_0LA0RB = Some (CS1_1RB1LA_0RC1RD_1LD0LB_0LA0RB, 4, 23).
Proof. vm_compute. reflexivity. Qed.

Definition AI01_1RB1LA_0RC1RD_1LD0LB_0LA0RB : sconf := mkC StA (mkS [] [S1;S1] 1 0 [S1;S0]) S0 (mkS [S1;S1;S0;S1] [] 0 0 []).
Definition AI11_1RB1LA_0RC1RD_1LD0LB_0LA0RB : sconf := mkC StA (mkS [] [S1;S0] 1 0 [S1;S1]) S0 (mkS [S1;S1;S0;S1] [] 0 0 []).
Definition chn1_1RB1LA_0RC1RD_1LD0LB_0LA0RB : list lstep := [SWin 16; SCycL 2 0; SWin 4; SCycR 2; SWin 16].

Lemma run_inner1_1RB1LA_0RC1RD_1LD0LB_0LA0RB : srun tm false true chn1_1RB1LA_0RC1RD_1LD0LB_0LA0RB AI01_1RB1LA_0RC1RD_1LD0LB_0LA0RB = Some (AI11_1RB1LA_0RC1RD_1LD0LB_0LA0RB, 4, 36).
Proof. vm_compute. reflexivity. Qed.

Definition CF1_1RB1LA_0RC1RD_1LD0LB_0LA0RB : sconf := mkC StA (mkS [] [S1;S1] 1 0 [S1;S1]) S0 (mkS [S1;S1;S0;S1] [] 0 0 []).
Definition che1_1RB1LA_0RC1RD_1LD0LB_0LA0RB : list lstep := [SWin 16; SCycL 2 0; SWin 2; SWinL 4; SCycR 2; SWin 3; SRotL 1; SFoldL 2].

Lemma run_exit1_1RB1LA_0RC1RD_1LD0LB_0LA0RB : srun tm true true che1_1RB1LA_0RC1RD_1LD0LB_0LA0RB CF1_1RB1LA_0RC1RD_1LD0LB_0LA0RB = Some (B11_1RB1LA_0RC1RD_1LD0LB_0LA0RB, 4, 25).
Proof. vm_compute. reflexivity. Qed.

Definition B00_1RB1LA_0RC1RD_1LD0LB_0LA0RB : sconf := mkC StD (mkS [S1;S1] [S1;S1] 1 0 [S1;S1]) S0 (mkS [S1] [] 0 0 []).
Definition B10_1RB1LA_0RC1RD_1LD0LB_0LA0RB : sconf := mkC StD (mkS [] [S1;S0] 1 2 [S1;S1]) S0 (mkS [S1] [] 0 0 []).

(** *** the overflow arm at octave parity false: boot 4*j+23, then the
    inner counter's laps, then exit 4*j+25 *)
Definition CS0_1RB1LA_0RC1RD_1LD0LB_0LA0RB : sconf := mkC StA (mkS [] [S1;S0] 1 0 [S1;S1]) S0 (mkS [S1;S1;S0;S1] [] 0 0 []).
Definition chb0_1RB1LA_0RC1RD_1LD0LB_0LA0RB : list lstep := [SWin 2; SCycL 2 0; SWin 2; SWinL 4; SCycR 2; SWin 14; SRotL 1; SWin 1].

Lemma run_boot0_1RB1LA_0RC1RD_1LD0LB_0LA0RB : srun tm true true chb0_1RB1LA_0RC1RD_1LD0LB_0LA0RB B00_1RB1LA_0RC1RD_1LD0LB_0LA0RB = Some (CS0_1RB1LA_0RC1RD_1LD0LB_0LA0RB, 4, 23).
Proof. vm_compute. reflexivity. Qed.

Definition AI00_1RB1LA_0RC1RD_1LD0LB_0LA0RB : sconf := mkC StA (mkS [] [S1;S1] 1 0 [S1;S0]) S0 (mkS [S1;S1;S0;S1] [] 0 0 []).
Definition AI10_1RB1LA_0RC1RD_1LD0LB_0LA0RB : sconf := mkC StA (mkS [] [S1;S0] 1 0 [S1;S1]) S0 (mkS [S1;S1;S0;S1] [] 0 0 []).
Definition chn0_1RB1LA_0RC1RD_1LD0LB_0LA0RB : list lstep := [SWin 16; SCycL 2 0; SWin 4; SCycR 2; SWin 16].

Lemma run_inner0_1RB1LA_0RC1RD_1LD0LB_0LA0RB : srun tm false true chn0_1RB1LA_0RC1RD_1LD0LB_0LA0RB AI00_1RB1LA_0RC1RD_1LD0LB_0LA0RB = Some (AI10_1RB1LA_0RC1RD_1LD0LB_0LA0RB, 4, 36).
Proof. vm_compute. reflexivity. Qed.

Definition CF0_1RB1LA_0RC1RD_1LD0LB_0LA0RB : sconf := mkC StA (mkS [] [S1;S1] 1 0 [S1;S1]) S0 (mkS [S1;S1;S0;S1] [] 0 0 []).
Definition che0_1RB1LA_0RC1RD_1LD0LB_0LA0RB : list lstep := [SWin 16; SCycL 2 0; SWin 2; SWinL 4; SCycR 2; SWin 3; SRotL 1; SFoldL 2].

Lemma run_exit0_1RB1LA_0RC1RD_1LD0LB_0LA0RB : srun tm true true che0_1RB1LA_0RC1RD_1LD0LB_0LA0RB CF0_1RB1LA_0RC1RD_1LD0LB_0LA0RB = Some (B10_1RB1LA_0RC1RD_1LD0LB_0LA0RB, 4, 25).
Proof. vm_compute. reflexivity. Qed.

(** ** Anchor glue -- the only per-machine mathematics *)

Lemma iepow1_1RB1LA_0RC1RD_1LD0LB_0LA0RB : forall n, Ip (pow2 n) = rep [S1;S0] n ++ [S1].
Proof. induction n; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.

Lemma iepow0_1RB1LA_0RC1RD_1LD0LB_0LA0RB : forall n, Ip (pow2 n) = rep [S1;S0] n ++ [S1].
Proof. induction n; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.

Lemma gz1_1RB1LA_0RC1RD_1LD0LB_0LA0RB : forall p q0, cview p = (0, Some q0) -> podd p = true ->
  Cc p = cden (Ap_Alph_10_11_11 q0 ++ []) [] 0 Z01_1RB1LA_0RC1RD_1LD0LB_0LA0RB /\
  lift (cden (Ap_Alph_10_11_11 q0 ++ []) [] 0 Z11_1RB1LA_0RC1RD_1LD0LB_0LA0RB) = lift (Cc (Pos.succ p)).
Proof.
  intros p q0 E Hb. destruct (Alph_10_11_11.cview_some_Alph_10_11_11 p 0 q0 E) as (H1 & H2).
  unfold Cc_1RB1LA_0RC1RD_1LD0LB_0LA0RB. rewrite (podd_succ_int p 0 q0 E), Hb.
  unfold cden, Z01_1RB1LA_0RC1RD_1LD0LB_0LA0RB, Z11_1RB1LA_0RC1RD_1LD0LB_0LA0RB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  split.
  - rewrite H1. rshape_1RB1LA_0RC1RD_1LD0LB_0LA0RB.
  - f_equal. rewrite H2. rshape_1RB1LA_0RC1RD_1LD0LB_0LA0RB.
Qed.

Lemma gp1_1RB1LA_0RC1RD_1LD0LB_0LA0RB : forall p j q0, cview p = (S j, Some q0) -> podd p = true ->
  Cc p = cden (Ap_Alph_10_11_11 q0 ++ []) [] j P01_1RB1LA_0RC1RD_1LD0LB_0LA0RB /\
  lift (cden (Ap_Alph_10_11_11 q0 ++ []) [] j P11_1RB1LA_0RC1RD_1LD0LB_0LA0RB) = lift (Cc (Pos.succ p)).
Proof.
  intros p j q0 E Hb. destruct (Alph_10_11_11.cview_some_Alph_10_11_11 p (S j) q0 E) as (H1 & H2).
  unfold Cc_1RB1LA_0RC1RD_1LD0LB_0LA0RB. rewrite (podd_succ_int p (S j) q0 E), Hb.
  unfold cden, P01_1RB1LA_0RC1RD_1LD0LB_0LA0RB, P11_1RB1LA_0RC1RD_1LD0LB_0LA0RB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia. replace (0 * j + 0) with 0 by lia.
  split.
  - rewrite H1. rshape_1RB1LA_0RC1RD_1LD0LB_0LA0RB.
  - f_equal. rewrite H2. rshape_1RB1LA_0RC1RD_1LD0LB_0LA0RB.
Qed.

Lemma lapi1_1RB1LA_0RC1RD_1LD0LB_0LA0RB : forall p j q0, cview p = (j, Some q0) -> podd p = true ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof.
  intros p j q0 E Hb. destruct j as [|j'].
  - destruct (gz1_1RB1LA_0RC1RD_1LD0LB_0LA0RB p q0 E Hb) as (HA & HB).
    exists (0 * 0 + 4), (cden (Ap_Alph_10_11_11 q0 ++ []) [] 0 Z11_1RB1LA_0RC1RD_1LD0LB_0LA0RB).
    split; [lia|]. split; [| exact HB]. rewrite HA.
    exact (srun_sound tm false true chz1_1RB1LA_0RC1RD_1LD0LB_0LA0RB Z01_1RB1LA_0RC1RD_1LD0LB_0LA0RB Z11_1RB1LA_0RC1RD_1LD0LB_0LA0RB 0 4
             run_z1_1RB1LA_0RC1RD_1LD0LB_0LA0RB (Ap_Alph_10_11_11 q0 ++ []) [] 0
             ltac:(discriminate) ltac:(reflexivity)).
  - destruct (gp1_1RB1LA_0RC1RD_1LD0LB_0LA0RB p j' q0 E Hb) as (HA & HB).
    exists (4 * j' + 8), (cden (Ap_Alph_10_11_11 q0 ++ []) [] j' P11_1RB1LA_0RC1RD_1LD0LB_0LA0RB).
    split; [lia|]. split; [| exact HB]. rewrite HA.
    exact (srun_sound tm false true chp1_1RB1LA_0RC1RD_1LD0LB_0LA0RB P01_1RB1LA_0RC1RD_1LD0LB_0LA0RB P11_1RB1LA_0RC1RD_1LD0LB_0LA0RB 4 8
             run_p1_1RB1LA_0RC1RD_1LD0LB_0LA0RB (Ap_Alph_10_11_11 q0 ++ []) [] j'
             ltac:(discriminate) ltac:(reflexivity)).
Qed.

Lemma gz0_1RB1LA_0RC1RD_1LD0LB_0LA0RB : forall p q0, cview p = (0, Some q0) -> podd p = false ->
  Cc p = cden (Ap_Alph_10_11_11 q0 ++ []) [] 0 Z00_1RB1LA_0RC1RD_1LD0LB_0LA0RB /\
  lift (cden (Ap_Alph_10_11_11 q0 ++ []) [] 0 Z10_1RB1LA_0RC1RD_1LD0LB_0LA0RB) = lift (Cc (Pos.succ p)).
Proof.
  intros p q0 E Hb. destruct (Alph_10_11_11.cview_some_Alph_10_11_11 p 0 q0 E) as (H1 & H2).
  unfold Cc_1RB1LA_0RC1RD_1LD0LB_0LA0RB. rewrite (podd_succ_int p 0 q0 E), Hb.
  unfold cden, Z00_1RB1LA_0RC1RD_1LD0LB_0LA0RB, Z10_1RB1LA_0RC1RD_1LD0LB_0LA0RB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  split.
  - rewrite H1. rshape_1RB1LA_0RC1RD_1LD0LB_0LA0RB.
  - f_equal. rewrite H2. rshape_1RB1LA_0RC1RD_1LD0LB_0LA0RB.
Qed.

Lemma gp0_1RB1LA_0RC1RD_1LD0LB_0LA0RB : forall p j q0, cview p = (S j, Some q0) -> podd p = false ->
  Cc p = cden (Ap_Alph_10_11_11 q0 ++ []) [] j P00_1RB1LA_0RC1RD_1LD0LB_0LA0RB /\
  lift (cden (Ap_Alph_10_11_11 q0 ++ []) [] j P10_1RB1LA_0RC1RD_1LD0LB_0LA0RB) = lift (Cc (Pos.succ p)).
Proof.
  intros p j q0 E Hb. destruct (Alph_10_11_11.cview_some_Alph_10_11_11 p (S j) q0 E) as (H1 & H2).
  unfold Cc_1RB1LA_0RC1RD_1LD0LB_0LA0RB. rewrite (podd_succ_int p (S j) q0 E), Hb.
  unfold cden, P00_1RB1LA_0RC1RD_1LD0LB_0LA0RB, P10_1RB1LA_0RC1RD_1LD0LB_0LA0RB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia. replace (0 * j + 0) with 0 by lia.
  split.
  - rewrite H1. rshape_1RB1LA_0RC1RD_1LD0LB_0LA0RB.
  - f_equal. rewrite H2. rshape_1RB1LA_0RC1RD_1LD0LB_0LA0RB.
Qed.

Lemma lapi0_1RB1LA_0RC1RD_1LD0LB_0LA0RB : forall p j q0, cview p = (j, Some q0) -> podd p = false ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof.
  intros p j q0 E Hb. destruct j as [|j'].
  - destruct (gz0_1RB1LA_0RC1RD_1LD0LB_0LA0RB p q0 E Hb) as (HA & HB).
    exists (0 * 0 + 4), (cden (Ap_Alph_10_11_11 q0 ++ []) [] 0 Z10_1RB1LA_0RC1RD_1LD0LB_0LA0RB).
    split; [lia|]. split; [| exact HB]. rewrite HA.
    exact (srun_sound tm false true chz0_1RB1LA_0RC1RD_1LD0LB_0LA0RB Z00_1RB1LA_0RC1RD_1LD0LB_0LA0RB Z10_1RB1LA_0RC1RD_1LD0LB_0LA0RB 0 4
             run_z0_1RB1LA_0RC1RD_1LD0LB_0LA0RB (Ap_Alph_10_11_11 q0 ++ []) [] 0
             ltac:(discriminate) ltac:(reflexivity)).
  - destruct (gp0_1RB1LA_0RC1RD_1LD0LB_0LA0RB p j' q0 E Hb) as (HA & HB).
    exists (4 * j' + 8), (cden (Ap_Alph_10_11_11 q0 ++ []) [] j' P10_1RB1LA_0RC1RD_1LD0LB_0LA0RB).
    split; [lia|]. split; [| exact HB]. rewrite HA.
    exact (srun_sound tm false true chp0_1RB1LA_0RC1RD_1LD0LB_0LA0RB P00_1RB1LA_0RC1RD_1LD0LB_0LA0RB P10_1RB1LA_0RC1RD_1LD0LB_0LA0RB 4 8
             run_p0_1RB1LA_0RC1RD_1LD0LB_0LA0RB (Ap_Alph_10_11_11 q0 ++ []) [] j'
             ltac:(discriminate) ltac:(reflexivity)).
Qed.

Lemma lapi_1RB1LA_0RC1RD_1LD0LB_0LA0RB : forall p j q0, cview p = (j, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof.
  intros p j q0 E. destruct (podd p) eqn:Hb.
  - exact (lapi1_1RB1LA_0RC1RD_1LD0LB_0LA0RB p j q0 E Hb).
  - exact (lapi0_1RB1LA_0RC1RD_1LD0LB_0LA0RB p j q0 E Hb).
Qed.

(** *** the overflow branch out of an octave of parity true.  It CROSSES into
    the other parity's frame, which is why one chain per parity is not a
    convenience: the two have different landings. *)
Lemma gso1_1RB1LA_0RC1RD_1LD0LB_0LA0RB : forall p j, cview p = (S (S j), None) -> podd p = true ->
  Cc p = cden [] [] j B01_1RB1LA_0RC1RD_1LD0LB_0LA0RB.
Proof.
  intros p j E Hb. destruct (Alph_10_11_11.cview_none_Alph_10_11_11 p (S j) E) as (H1 & _).
  unfold Cc_1RB1LA_0RC1RD_1LD0LB_0LA0RB. rewrite Hb.
  unfold cden, B01_1RB1LA_0RC1RD_1LD0LB_0LA0RB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia. replace (0 * j + 0) with 0 by lia.
  rewrite H1. rshape_1RB1LA_0RC1RD_1LD0LB_0LA0RB.
Qed.

Lemma geo1_1RB1LA_0RC1RD_1LD0LB_0LA0RB : forall p j, cview p = (S (S j), None) -> podd p = true ->
  cden [] [] j B11_1RB1LA_0RC1RD_1LD0LB_0LA0RB = Cc (Pos.succ p).
Proof.
  intros p j E Hb. destruct (Alph_10_11_11.cview_none_Alph_10_11_11 p (S j) E) as (_ & H2).
  unfold Cc_1RB1LA_0RC1RD_1LD0LB_0LA0RB. rewrite (podd_succ_fill p (S j) E), Hb. cbn [negb].
  unfold cden, B11_1RB1LA_0RC1RD_1LD0LB_0LA0RB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 2) with (S (S j)) by lia. replace (0 * j + 0) with 0 by lia.
  rewrite H2. rshape_1RB1LA_0RC1RD_1LD0LB_0LA0RB.
Qed.

Lemma gsn1_1RB1LA_0RC1RD_1LD0LB_0LA0RB : forall v i q0, cview v = (i, Some q0) ->
  Cin1 v = cden (Ip q0 ++ [S1]) [] i AI01_1RB1LA_0RC1RD_1LD0LB_0LA0RB.
Proof.
  intros v i q0 E. destruct (ILCounter.cview_some_I v i q0 E) as (H1 & _).
  unfold Cin1_1RB1LA_0RC1RD_1LD0LB_0LA0RB, cden, AI01_1RB1LA_0RC1RD_1LD0LB_0LA0RB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia. replace (0 * i + 0) with 0 by lia.
  rewrite H1. rshape_1RB1LA_0RC1RD_1LD0LB_0LA0RB.
Qed.

Lemma gen1_1RB1LA_0RC1RD_1LD0LB_0LA0RB : forall v i q0, cview v = (i, Some q0) ->
  cden (Ip q0 ++ [S1]) [] i AI11_1RB1LA_0RC1RD_1LD0LB_0LA0RB = Cin1 (Pos.succ v).
Proof.
  intros v i q0 E. destruct (ILCounter.cview_some_I v i q0 E) as (_ & H2).
  unfold Cin1_1RB1LA_0RC1RD_1LD0LB_0LA0RB, cden, AI11_1RB1LA_0RC1RD_1LD0LB_0LA0RB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia. replace (0 * i + 0) with 0 by lia.
  rewrite H2. rshape_1RB1LA_0RC1RD_1LD0LB_0LA0RB.
Qed.

Lemma lapin1_1RB1LA_0RC1RD_1LD0LB_0LA0RB : forall v i q0, cview v = (i, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cin1 v) = Some c'
               /\ lift c' = lift (Cin1 (Pos.succ v)).
Proof.
  intros v i q0 E.
  exists (4 * i + 36), (Cin1 (Pos.succ v)).
  split; [lia|]. split; [| reflexivity].
  rewrite (gsn1_1RB1LA_0RC1RD_1LD0LB_0LA0RB v i q0 E).
  rewrite (srun_sound tm false true chn1_1RB1LA_0RC1RD_1LD0LB_0LA0RB AI01_1RB1LA_0RC1RD_1LD0LB_0LA0RB AI11_1RB1LA_0RC1RD_1LD0LB_0LA0RB 4 36
             run_inner1_1RB1LA_0RC1RD_1LD0LB_0LA0RB (Ip q0 ++ [S1]) [] i
             ltac:(discriminate) ltac:(reflexivity)).
  f_equal. exact (gen1_1RB1LA_0RC1RD_1LD0LB_0LA0RB v i q0 E).
Qed.

Lemma gbo1_1RB1LA_0RC1RD_1LD0LB_0LA0RB : forall k, lift (cden [] [] k CS1_1RB1LA_0RC1RD_1LD0LB_0LA0RB) = lift (Cin1 (pow2 k)).
Proof.
  intro k. f_equal.
  unfold Cin1_1RB1LA_0RC1RD_1LD0LB_0LA0RB, cden, CS1_1RB1LA_0RC1RD_1LD0LB_0LA0RB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * k + 0) with k by lia. replace (0 * k + 0) with 0 by lia.
  rewrite iepow1_1RB1LA_0RC1RD_1LD0LB_0LA0RB. rshape_1RB1LA_0RC1RD_1LD0LB_0LA0RB.
Qed.

Lemma gxi1_1RB1LA_0RC1RD_1LD0LB_0LA0RB : forall k, Cin1 (fill (pow2 k)) = cden [] [] k CF1_1RB1LA_0RC1RD_1LD0LB_0LA0RB.
Proof.
  intro k.
  destruct (ILCounter.cview_none_I (fill (pow2 k)) k (cview_fill_pow2 k)) as (H1 & _).
  unfold Cin1_1RB1LA_0RC1RD_1LD0LB_0LA0RB, cden, CF1_1RB1LA_0RC1RD_1LD0LB_0LA0RB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * k + 0) with k by lia. replace (0 * k + 0) with 0 by lia.
  rewrite H1. rshape_1RB1LA_0RC1RD_1LD0LB_0LA0RB.
Qed.

Lemma hbo1_1RB1LA_0RC1RD_1LD0LB_0LA0RB : forall p j, cview p = (S (S j), None) -> podd p = true ->
  exists n c, 0 < n /\ csteps tm n (Cc p) = Some c
              /\ lift c = lift (Cin1 (pow2 j)).
Proof.
  intros p j E Hb.
  exists (4 * j + 23), (cden [] [] j CS1_1RB1LA_0RC1RD_1LD0LB_0LA0RB).
  split; [lia|]. split; [| exact (gbo1_1RB1LA_0RC1RD_1LD0LB_0LA0RB j)].
  rewrite (gso1_1RB1LA_0RC1RD_1LD0LB_0LA0RB p j E Hb).
  exact (srun_sound tm true true chb1_1RB1LA_0RC1RD_1LD0LB_0LA0RB B01_1RB1LA_0RC1RD_1LD0LB_0LA0RB CS1_1RB1LA_0RC1RD_1LD0LB_0LA0RB 4 23
           run_boot1_1RB1LA_0RC1RD_1LD0LB_0LA0RB [] [] j ltac:(reflexivity) ltac:(reflexivity)).
Qed.

Lemma hxe1_1RB1LA_0RC1RD_1LD0LB_0LA0RB : forall p j, cview p = (S (S j), None) -> podd p = true ->
  exists n c', csteps tm n (Cin1 (fill (pow2 j))) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof.
  intros p j E Hb.
  exists (4 * j + 25), (cden [] [] j B11_1RB1LA_0RC1RD_1LD0LB_0LA0RB).
  split; [| f_equal; exact (geo1_1RB1LA_0RC1RD_1LD0LB_0LA0RB p j E Hb)].
  rewrite (gxi1_1RB1LA_0RC1RD_1LD0LB_0LA0RB j).
  exact (srun_sound tm true true che1_1RB1LA_0RC1RD_1LD0LB_0LA0RB CF1_1RB1LA_0RC1RD_1LD0LB_0LA0RB B11_1RB1LA_0RC1RD_1LD0LB_0LA0RB 4 25
           run_exit1_1RB1LA_0RC1RD_1LD0LB_0LA0RB [] [] j ltac:(reflexivity) ltac:(reflexivity)).
Qed.

(** The overflow arm, composed.  The [Theta(2^j)] middle is the [exists n]
    inside [NestedLapLift.inner_to_fill_lift]; no formula for it is written. *)
Lemma lapo1_1RB1LA_0RC1RD_1LD0LB_0LA0RB : forall p j, cview p = (S (S j), None) -> podd p = true ->
  exists n c', csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intros p j E Hb.
  exact (nested_overflow_lift tm Cc Cin1 lapin1_1RB1LA_0RC1RD_1LD0LB_0LA0RB p (pow2 j)
           (hbo1_1RB1LA_0RC1RD_1LD0LB_0LA0RB p j E Hb) (hxe1_1RB1LA_0RC1RD_1LD0LB_0LA0RB p j E Hb)).
Qed.

(** *** the overflow branch out of an octave of parity false.  It CROSSES into
    the other parity's frame, which is why one chain per parity is not a
    convenience: the two have different landings. *)
Lemma gso0_1RB1LA_0RC1RD_1LD0LB_0LA0RB : forall p j, cview p = (S (S j), None) -> podd p = false ->
  Cc p = cden [] [] j B00_1RB1LA_0RC1RD_1LD0LB_0LA0RB.
Proof.
  intros p j E Hb. destruct (Alph_10_11_11.cview_none_Alph_10_11_11 p (S j) E) as (H1 & _).
  unfold Cc_1RB1LA_0RC1RD_1LD0LB_0LA0RB. rewrite Hb.
  unfold cden, B00_1RB1LA_0RC1RD_1LD0LB_0LA0RB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia. replace (0 * j + 0) with 0 by lia.
  rewrite H1. rshape_1RB1LA_0RC1RD_1LD0LB_0LA0RB.
Qed.

Lemma geo0_1RB1LA_0RC1RD_1LD0LB_0LA0RB : forall p j, cview p = (S (S j), None) -> podd p = false ->
  cden [] [] j B10_1RB1LA_0RC1RD_1LD0LB_0LA0RB = Cc (Pos.succ p).
Proof.
  intros p j E Hb. destruct (Alph_10_11_11.cview_none_Alph_10_11_11 p (S j) E) as (_ & H2).
  unfold Cc_1RB1LA_0RC1RD_1LD0LB_0LA0RB. rewrite (podd_succ_fill p (S j) E), Hb. cbn [negb].
  unfold cden, B10_1RB1LA_0RC1RD_1LD0LB_0LA0RB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 2) with (S (S j)) by lia. replace (0 * j + 0) with 0 by lia.
  rewrite H2. rshape_1RB1LA_0RC1RD_1LD0LB_0LA0RB.
Qed.

Lemma gsn0_1RB1LA_0RC1RD_1LD0LB_0LA0RB : forall v i q0, cview v = (i, Some q0) ->
  Cin0 v = cden (Ip q0 ++ [S1]) [] i AI00_1RB1LA_0RC1RD_1LD0LB_0LA0RB.
Proof.
  intros v i q0 E. destruct (ILCounter.cview_some_I v i q0 E) as (H1 & _).
  unfold Cin0_1RB1LA_0RC1RD_1LD0LB_0LA0RB, cden, AI00_1RB1LA_0RC1RD_1LD0LB_0LA0RB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia. replace (0 * i + 0) with 0 by lia.
  rewrite H1. rshape_1RB1LA_0RC1RD_1LD0LB_0LA0RB.
Qed.

Lemma gen0_1RB1LA_0RC1RD_1LD0LB_0LA0RB : forall v i q0, cview v = (i, Some q0) ->
  cden (Ip q0 ++ [S1]) [] i AI10_1RB1LA_0RC1RD_1LD0LB_0LA0RB = Cin0 (Pos.succ v).
Proof.
  intros v i q0 E. destruct (ILCounter.cview_some_I v i q0 E) as (_ & H2).
  unfold Cin0_1RB1LA_0RC1RD_1LD0LB_0LA0RB, cden, AI10_1RB1LA_0RC1RD_1LD0LB_0LA0RB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia. replace (0 * i + 0) with 0 by lia.
  rewrite H2. rshape_1RB1LA_0RC1RD_1LD0LB_0LA0RB.
Qed.

Lemma lapin0_1RB1LA_0RC1RD_1LD0LB_0LA0RB : forall v i q0, cview v = (i, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cin0 v) = Some c'
               /\ lift c' = lift (Cin0 (Pos.succ v)).
Proof.
  intros v i q0 E.
  exists (4 * i + 36), (Cin0 (Pos.succ v)).
  split; [lia|]. split; [| reflexivity].
  rewrite (gsn0_1RB1LA_0RC1RD_1LD0LB_0LA0RB v i q0 E).
  rewrite (srun_sound tm false true chn0_1RB1LA_0RC1RD_1LD0LB_0LA0RB AI00_1RB1LA_0RC1RD_1LD0LB_0LA0RB AI10_1RB1LA_0RC1RD_1LD0LB_0LA0RB 4 36
             run_inner0_1RB1LA_0RC1RD_1LD0LB_0LA0RB (Ip q0 ++ [S1]) [] i
             ltac:(discriminate) ltac:(reflexivity)).
  f_equal. exact (gen0_1RB1LA_0RC1RD_1LD0LB_0LA0RB v i q0 E).
Qed.

Lemma gbo0_1RB1LA_0RC1RD_1LD0LB_0LA0RB : forall k, lift (cden [] [] k CS0_1RB1LA_0RC1RD_1LD0LB_0LA0RB) = lift (Cin0 (pow2 k)).
Proof.
  intro k. f_equal.
  unfold Cin0_1RB1LA_0RC1RD_1LD0LB_0LA0RB, cden, CS0_1RB1LA_0RC1RD_1LD0LB_0LA0RB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * k + 0) with k by lia. replace (0 * k + 0) with 0 by lia.
  rewrite iepow0_1RB1LA_0RC1RD_1LD0LB_0LA0RB. rshape_1RB1LA_0RC1RD_1LD0LB_0LA0RB.
Qed.

Lemma gxi0_1RB1LA_0RC1RD_1LD0LB_0LA0RB : forall k, Cin0 (fill (pow2 k)) = cden [] [] k CF0_1RB1LA_0RC1RD_1LD0LB_0LA0RB.
Proof.
  intro k.
  destruct (ILCounter.cview_none_I (fill (pow2 k)) k (cview_fill_pow2 k)) as (H1 & _).
  unfold Cin0_1RB1LA_0RC1RD_1LD0LB_0LA0RB, cden, CF0_1RB1LA_0RC1RD_1LD0LB_0LA0RB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * k + 0) with k by lia. replace (0 * k + 0) with 0 by lia.
  rewrite H1. rshape_1RB1LA_0RC1RD_1LD0LB_0LA0RB.
Qed.

Lemma hbo0_1RB1LA_0RC1RD_1LD0LB_0LA0RB : forall p j, cview p = (S (S j), None) -> podd p = false ->
  exists n c, 0 < n /\ csteps tm n (Cc p) = Some c
              /\ lift c = lift (Cin0 (pow2 j)).
Proof.
  intros p j E Hb.
  exists (4 * j + 23), (cden [] [] j CS0_1RB1LA_0RC1RD_1LD0LB_0LA0RB).
  split; [lia|]. split; [| exact (gbo0_1RB1LA_0RC1RD_1LD0LB_0LA0RB j)].
  rewrite (gso0_1RB1LA_0RC1RD_1LD0LB_0LA0RB p j E Hb).
  exact (srun_sound tm true true chb0_1RB1LA_0RC1RD_1LD0LB_0LA0RB B00_1RB1LA_0RC1RD_1LD0LB_0LA0RB CS0_1RB1LA_0RC1RD_1LD0LB_0LA0RB 4 23
           run_boot0_1RB1LA_0RC1RD_1LD0LB_0LA0RB [] [] j ltac:(reflexivity) ltac:(reflexivity)).
Qed.

Lemma hxe0_1RB1LA_0RC1RD_1LD0LB_0LA0RB : forall p j, cview p = (S (S j), None) -> podd p = false ->
  exists n c', csteps tm n (Cin0 (fill (pow2 j))) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof.
  intros p j E Hb.
  exists (4 * j + 25), (cden [] [] j B10_1RB1LA_0RC1RD_1LD0LB_0LA0RB).
  split; [| f_equal; exact (geo0_1RB1LA_0RC1RD_1LD0LB_0LA0RB p j E Hb)].
  rewrite (gxi0_1RB1LA_0RC1RD_1LD0LB_0LA0RB j).
  exact (srun_sound tm true true che0_1RB1LA_0RC1RD_1LD0LB_0LA0RB CF0_1RB1LA_0RC1RD_1LD0LB_0LA0RB B10_1RB1LA_0RC1RD_1LD0LB_0LA0RB 4 25
           run_exit0_1RB1LA_0RC1RD_1LD0LB_0LA0RB [] [] j ltac:(reflexivity) ltac:(reflexivity)).
Qed.

(** The overflow arm, composed.  The [Theta(2^j)] middle is the [exists n]
    inside [NestedLapLift.inner_to_fill_lift]; no formula for it is written. *)
Lemma lapo0_1RB1LA_0RC1RD_1LD0LB_0LA0RB : forall p j, cview p = (S (S j), None) -> podd p = false ->
  exists n c', csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intros p j E Hb.
  exact (nested_overflow_lift tm Cc Cin0 lapin0_1RB1LA_0RC1RD_1LD0LB_0LA0RB p (pow2 j)
           (hbo0_1RB1LA_0RC1RD_1LD0LB_0LA0RB p j E Hb) (hxe0_1RB1LA_0RC1RD_1LD0LB_0LA0RB p j E Hb)).
Qed.

(** ** The lap *)

Lemma lapo_1RB1LA_0RC1RD_1LD0LB_0LA0RB : forall p j, cview p = (S (S j), None) ->
  exists n c', csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intros p j E. destruct (podd p) eqn:Hb.
  - exact (lapo1_1RB1LA_0RC1RD_1LD0LB_0LA0RB p j E Hb).
  - exact (lapo0_1RB1LA_0RC1RD_1LD0LB_0LA0RB p j E Hb).
Qed.

(** [j = 0] is [p = 1] ([IXPGadgets.cview_none_shape]), which is below [8]:
    the peel's leftover case is refuted rather than proved. *)
Lemma lap_1RB1LA_0RC1RD_1LD0LB_0LA0RB : forall p, (8 <= p)%positive -> exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intros p Hp. destruct (cview p) as [j oq] eqn:E; destruct oq as [q0|].
  - destruct (lapi_1RB1LA_0RC1RD_1LD0LB_0LA0RB p j q0 E) as (n & c' & Hn & Hr & Hl).
    exists n, c'. split; [exact Hr | split; [exact Hl | exact Hn]].
  - destruct (cview_pos p j E) as (j' & ->).
    destruct j' as [|j''].
    + exfalso. rewrite (cview_none_shape p 0 E) in Hp.
      apply Hp. vm_compute. reflexivity.
    + exact (lapo_1RB1LA_0RC1RD_1LD0LB_0LA0RB p j'' E).
Qed.

(** ** Bootstrap *)

Lemma boot_1RB1LA_0RC1RD_1LD0LB_0LA0RB : exists t0, stepn tm t0 InitES = Some (lift (Cc 8)).
Proof.
  exists 191.
  assert (H : match csteps tm 191 c0 with
              | Some c => ceqb c (Cc 8) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 191 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** ** Visits

    [LapCertGlueLift.vis_via_ovf_lift] asks for a witness at EVERY overflow
    anchor, and the overflow anchors alternate frames -- so the witness is a
    prefix of whichever of the two overflow chains that parity uses, plus the
    peel's leftover [p = 1]. *)

Lemma viso1_1RB1LA_0RC1RD_1LD0LB_0LA0RB : forall (l : list lstep) (q : St),
  srun_st tm true true l B01_1RB1LA_0RC1RD_1LD0LB_0LA0RB = Some q ->
  forall p j, cview p = (S (S j), None) -> podd p = true ->
  exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros l q Hst p j E Hb.
  apply (vis_of_run tm Cc true true l B01_1RB1LA_0RC1RD_1LD0LB_0LA0RB p j [] []);
    [exact Hst | reflexivity | reflexivity | exact (gso1_1RB1LA_0RC1RD_1LD0LB_0LA0RB p j E Hb)].
Qed.

Lemma viso0_1RB1LA_0RC1RD_1LD0LB_0LA0RB : forall (l : list lstep) (q : St),
  srun_st tm true true l B00_1RB1LA_0RC1RD_1LD0LB_0LA0RB = Some q ->
  forall p j, cview p = (S (S j), None) -> podd p = false ->
  exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros l q Hst p j E Hb.
  apply (vis_of_run tm Cc true true l B00_1RB1LA_0RC1RD_1LD0LB_0LA0RB p j [] []);
    [exact Hst | reflexivity | reflexivity | exact (gso0_1RB1LA_0RC1RD_1LD0LB_0LA0RB p j E Hb)].
Qed.

(** State StA at the peel's leftover overflow anchor [p = 1]. *)
Lemma viszStA_1RB1LA_0RC1RD_1LD0LB_0LA0RB : exists k c, csteps tm k (Cc 1) = Some c /\ fst c = StA.
Proof. exists 1. eexists. split; [vm_compute; reflexivity | reflexivity]. Qed.

(** State StB at the peel's leftover overflow anchor [p = 1]. *)
Lemma viszStB_1RB1LA_0RC1RD_1LD0LB_0LA0RB : exists k c, csteps tm k (Cc 1) = Some c /\ fst c = StB.
Proof. exists 4. eexists. split; [vm_compute; reflexivity | reflexivity]. Qed.

(** State StC at the peel's leftover overflow anchor [p = 1]. *)
Lemma viszStC_1RB1LA_0RC1RD_1LD0LB_0LA0RB : exists k c, csteps tm k (Cc 1) = Some c /\ fst c = StC.
Proof. exists 7. eexists. split; [vm_compute; reflexivity | reflexivity]. Qed.

(** State StD at the peel's leftover overflow anchor [p = 1]. *)
Lemma viszStD_1RB1LA_0RC1RD_1LD0LB_0LA0RB : exists k c, csteps tm k (Cc 1) = Some c /\ fst c = StD.
Proof. exists 0. eexists. split; [vm_compute; reflexivity | reflexivity]. Qed.

Lemma vis_1RB1LA_0RC1RD_1LD0LB_0LA0RB : forall p q, (8 <= p)%positive ->
  exists k e, stepn tm k (lift (Cc p)) = Some e /\ fst e = q.
Proof.
  intros p q _.
  apply (vis_via_ovf_lift tm Cc lapi_1RB1LA_0RC1RD_1LD0LB_0LA0RB q).
  intros p1 j1 E1. destruct j1 as [|j2].
  - assert (H1 : p1 = 1%positive)
      by (rewrite (cview_none_shape p1 0 E1); reflexivity).
    subst p1. apply vis_lift_of_csteps. destruct q.
    + exact (viszStA_1RB1LA_0RC1RD_1LD0LB_0LA0RB).
    + exact (viszStB_1RB1LA_0RC1RD_1LD0LB_0LA0RB).
    + exact (viszStC_1RB1LA_0RC1RD_1LD0LB_0LA0RB).
    + exact (viszStD_1RB1LA_0RC1RD_1LD0LB_0LA0RB).
  - apply vis_lift_of_csteps. destruct (podd p1) eqn:Hb1.
    + destruct q.
      * exact (viso1_1RB1LA_0RC1RD_1LD0LB_0LA0RB [SWin 1] StA ltac:(vm_compute; reflexivity) p1 j2 E1 Hb1).
      * exact (viso1_1RB1LA_0RC1RD_1LD0LB_0LA0RB [SWin 2; SCycL 2 0; SWin 2; SWinL 2] StB ltac:(vm_compute; reflexivity) p1 j2 E1 Hb1).
      * exact (viso1_1RB1LA_0RC1RD_1LD0LB_0LA0RB [SWin 2; SCycL 2 0; SWin 2; SWinL 4; SCycR 2; SWin 3] StC ltac:(vm_compute; reflexivity) p1 j2 E1 Hb1).
      * exact (viso1_1RB1LA_0RC1RD_1LD0LB_0LA0RB [] StD ltac:(vm_compute; reflexivity) p1 j2 E1 Hb1).
    + destruct q.
      * exact (viso0_1RB1LA_0RC1RD_1LD0LB_0LA0RB [SWin 1] StA ltac:(vm_compute; reflexivity) p1 j2 E1 Hb1).
      * exact (viso0_1RB1LA_0RC1RD_1LD0LB_0LA0RB [SWin 2; SCycL 2 0; SWin 2; SWinL 2] StB ltac:(vm_compute; reflexivity) p1 j2 E1 Hb1).
      * exact (viso0_1RB1LA_0RC1RD_1LD0LB_0LA0RB [SWin 2; SCycL 2 0; SWin 2; SWinL 4; SCycR 2; SWin 3] StC ltac:(vm_compute; reflexivity) p1 j2 E1 Hb1).
      * exact (viso0_1RB1LA_0RC1RD_1LD0LB_0LA0RB [] StD ltac:(vm_compute; reflexivity) p1 j2 E1 Hb1).
Qed.

Theorem nqh_1RB1LA_0RC1RD_1LD0LB_0LA0RB : NeverQuasiHaltsSt tm.
Proof. apply (glue_neverqh_lift tm Cc 8). - exact boot_1RB1LA_0RC1RD_1LD0LB_0LA0RB. - intros p Hp. apply (lap_1RB1LA_0RC1RD_1LD0LB_0LA0RB p Hp). - intros p q Hp. apply (vis_1RB1LA_0RC1RD_1LD0LB_0LA0RB p q Hp). Qed.

Theorem nonhalt_1RB1LA_0RC1RD_1LD0LB_0LA0RB : NonHalt tm.
Proof. apply never_qh_nonhalt, nqh_1RB1LA_0RC1RD_1LD0LB_0LA0RB. Qed.
