(** * CASB_0RB1LA_1RC0LA_0LD1RB____1LB: machine 0RB1LA_1RC0LA_0LD1RB_---1LB, boarded by the CASCADE route.

    Auto-emitted by tools/counters/cascade_emit.py (UNTRUSTED emitter; the Coq
    kernel re-runs the checker on every line below).  Left-growth binary
    counter under the Jp digit alphabet, anchored at

      Cc p = (StB, (Jp p ++ [S1;S0;S1;S0], S0, []))

    The INTERIOR branch is an ordinary lap certificate (4*j+8 steps,
    closing up to [lift]).  The OVERFLOW branch is a DESCENDING-OCTAVE
    CASCADE: j+1 inner counts, `2j+1` of them, down from level j to
    level 0, each level's tail one unit longer than the last, then a
    closing sweep to the outer successor.  The number of counts is
    AFFINE IN j, which is why no fixed list of chains expresses it; the
    induction is [NestedLapCascade.cascade_overflow].

    Every level runs the SAME counter over the SAME digits.  What grows is the
    region past them, and the counter never reads it -- so [Cin] below is
    stated at an ARBITRARY TAIL [T], one interior-lap certificate discharges
    every level at once, and the two per-level chains are ordinary
    single-index chains with the growth in the sside's opaque region.

      inner lap        4*i+8 steps, at any tail
      boot             4*j+8         -> the level-j count
      B(l+1) -> A(l)   4*l+14
      A(l)   -> B(l)   4*l+8
      close            4*j+31       -> the outer successor

    VISITS: only the boot and the closing sweep fire at EVERY outer index
    (at j = 0 there is no descent), so a state firing in neither the boot
    chain nor the interior lap must fire in the sweep, reached through the
    whole cascade by [NestedLapCascade.cascade_vis].

    Differentially validated against the raw simulator -- step counts AND
    exact configurations: 192 interior anchors (interior); every count of every level of
    every overflow phase, cascade: 7 overflow phases, j = 2..8 (42 levels, 77 counts, 1433 inner laps).
    Axiom footprint: [functional_extensionality_dep] (via [CTape.lift]). *)
From Coq Require Import Arith Lia Bool List PArith Wellfounded.
From BBB4 Require Import BBB4_Statement CTape Mirror.
From Coq Require Import FunctionalExtensionality.
From BBB4.Counters Require Import WTape MonoCounter JpCounter IXPGadgets
                                  LapCertGlue LapCertGlueLift NestedLap
                                  NestedLapLift NestedLapCascade.
From BBB4.Checkers Require Import LapDecider.
Import ListNotations.

Definition mk_0RB1LA_1RC0LA_0LD1RB____1LB (w : Sym) (d : Dir) (n : St) : option Trans :=
  Some (mkTrans w d n).
Local Notation mk := mk_0RB1LA_1RC0LA_0LD1RB____1LB.

(** 0RB1LA_1RC0LA_0LD1RB_---1LB -- the table every lemma below runs on. *)
(** 0RB1LA_1RC0LA_0LD1RB_---1LB -- the real machine (its counter grows RIGHT). *)
Definition tm_0RB1LA_1RC0LA_0LD1RB____1LB : TM := fun q s => match q, s with
  | StA, S0 => mk S0 DR StB | StA, S1 => mk S1 DL StA
  | StB, S0 => mk S1 DR StC | StB, S1 => mk S0 DL StA
  | StC, S0 => mk S0 DL StD | StC, S1 => mk S1 DR StB
  | StD, S0 => None | StD, S1 => mk S1 DL StB end.

(** Its mirror 0LB1RA_1LC0RA_0RD1LB_---1RB: the same counter grown leftward.  Every
    lemma below runs on the MIRRORED table;
    [Mirror.mirror_never_qh] transfers the conclusion back. *)
Definition tmm_0RB1LA_1RC0LA_0LD1RB____1LB : TM := fun q s => match q, s with
  | StA, S0 => mk S0 DL StB | StA, S1 => mk S1 DR StA
  | StB, S0 => mk S1 DL StC | StB, S1 => mk S0 DR StA
  | StC, S0 => mk S0 DR StD | StC, S1 => mk S1 DL StB
  | StD, S0 => None | StD, S1 => mk S1 DR StB end.
Local Notation tm := tmm_0RB1LA_1RC0LA_0LD1RB____1LB.

Lemma mirror_ok_0RB1LA_1RC0LA_0LD1RB____1LB : mirror_tm tm_0RB1LA_1RC0LA_0LD1RB____1LB = tmm_0RB1LA_1RC0LA_0LD1RB____1LB.
Proof.
  apply functional_extensionality; intro q;
    apply functional_extensionality; intro b; destruct q, b; reflexivity.
Qed.

Definition Cc_0RB1LA_1RC0LA_0LD1RB____1LB (p : positive) : cconf := (StB, (Jp p ++ [S1;S0;S1;S0], S0, [])).
Local Notation Cc := Cc_0RB1LA_1RC0LA_0LD1RB____1LB.

(** A chain accepted up to [lift] can stop a blank past the anchor -- the
    leniency [NestedLapLift] measured to be the binding one on this bucket --
    and [CTape.lift_side] cannot see it.  Every landing bridge below ends
    here, so it is stated before the first of them. *)
Lemma lbl_0RB1LA_1RC0LA_0LD1RB____1LB : forall q l h r, lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.


(** ** The inner family, at an ARBITRARY tail

    [T] is the cascade's growing region.  The counter's own laps never read
    it, so quantifying over it costs nothing and buys every level. *)
Definition Cin_0RB1LA_1RC0LA_0LD1RB____1LB (T : list Sym) (v : positive) : cconf :=
  (StB, (Jp v ++ T, S0, [])).
Local Notation Cin := Cin_0RB1LA_1RC0LA_0LD1RB____1LB.

Definition Uc_0RB1LA_1RC0LA_0LD1RB____1LB : list Sym := [S0;S1].
Local Notation Uc := Uc_0RB1LA_1RC0LA_0LD1RB____1LB.

(** The two tails a level carries: the count that ENTERS it and the count the
    level's own transition produces.  One unit longer per level down. *)
Definition TB_0RB1LA_1RC0LA_0LD1RB____1LB (m : nat) : list Sym := [S0] ++ rep Uc (m + 1).
Definition TA_0RB1LA_1RC0LA_0LD1RB____1LB (m : nat) : list Sym := [S1] ++ rep Uc (m + 1).
Local Notation TB := TB_0RB1LA_1RC0LA_0LD1RB____1LB.
Local Notation TA := TA_0RB1LA_1RC0LA_0LD1RB____1LB.

(** The level-[l] entry configuration, with [m] units of tail beyond the
    top level's.  Both indices are explicit and both are built by [S]: a
    single index would force [j - l] into an anchor, which is the wave-15
    index-shift trap. *)
Definition Dc_0RB1LA_1RC0LA_0LD1RB____1LB (l m : nat) : cconf := Cin (TB m) (pow2 l).
Local Notation Dc := Dc_0RB1LA_1RC0LA_0LD1RB____1LB.

(** [E (2^n)] and [E (2^(n+1)-1)]: the value each count starts and ends at. *)
Lemma epow2_0RB1LA_1RC0LA_0LD1RB____1LB : forall n, Jp (pow2 n) = rep [S1;S1] n ++ [S1].
Proof. induction n; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.

Lemma efill_0RB1LA_1RC0LA_0LD1RB____1LB : forall n, Jp (fill (pow2 n)) = rep [S1;S0] n ++ [S1].
Proof.
  intro n.
  destruct (JpCounter.cview_none_J (fill (pow2 n)) n (cview_fill_pow2 n)) as (H & _).
  exact H.
Qed.

(** ** The inner family's own interior lap -- ordinary, affine, tail-blind *)

Definition AI0_0RB1LA_1RC0LA_0LD1RB____1LB : sconf := mkC StB (mkS [] [S1;S0] 1 0 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition AI1_0RB1LA_1RC0LA_0LD1RB____1LB : sconf := mkC StB (mkS [] [S1;S1] 1 0 [S1;S0]) S0 (mkS [S0] [] 0 0 []).
Definition chn_0RB1LA_1RC0LA_0LD1RB____1LB : list lstep := [SCycL 2 0; SWin 4; SCycR 2; SWinR 4].

Lemma run_inner_0RB1LA_1RC0LA_0LD1RB____1LB :
  srun tm false true chn_0RB1LA_1RC0LA_0LD1RB____1LB AI0_0RB1LA_1RC0LA_0LD1RB____1LB = Some (AI1_0RB1LA_1RC0LA_0LD1RB____1LB, 4, 8).
Proof. vm_compute. reflexivity. Qed.

Lemma gsn_0RB1LA_1RC0LA_0LD1RB____1LB : forall T v i q0, cview v = (i, Some q0) ->
  Cin T v = cden (Jp q0 ++ T) [] i AI0_0RB1LA_1RC0LA_0LD1RB____1LB.
Proof.
  intros T v i q0 Ev. destruct (JpCounter.cview_some_J v i q0 Ev) as (H1 & _).
  unfold Cin_0RB1LA_1RC0LA_0LD1RB____1LB, cden, AI0_0RB1LA_1RC0LA_0LD1RB____1LB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia. rewrite H1.
  cbn [rep app]. rewrite <- ?app_assoc. cbn [app]. rewrite ?app_nil_r.
  reflexivity.
Qed.

Lemma gen_0RB1LA_1RC0LA_0LD1RB____1LB : forall T v i q0, cview v = (i, Some q0) ->
  lift (cden (Jp q0 ++ T) [] i AI1_0RB1LA_1RC0LA_0LD1RB____1LB) = lift (Cin T (Pos.succ v)).
Proof.
  intros T v i q0 Ev. destruct (JpCounter.cview_some_J v i q0 Ev) as (_ & H2).
  unfold Cin_0RB1LA_1RC0LA_0LD1RB____1LB, cden, AI1_0RB1LA_1RC0LA_0LD1RB____1LB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia. replace (0 * i + 0) with 0 by lia.
  rewrite H2. cbn [rep app]. rewrite <- ?app_assoc. cbn [app].
  rewrite ?app_nil_r.
  change ([S0]) with (([]) ++ [S0]).
  rewrite ?lift_app_blank. reflexivity.
Qed.

(** The lap, up to [lift] and at every tail at once -- this is
    [NestedLapCascade]'s [Hin]. *)
Lemma lapin_0RB1LA_1RC0LA_0LD1RB____1LB : forall T v i q0, cview v = (i, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cin T v) = Some c'
               /\ lift c' = lift (Cin T (Pos.succ v)).
Proof.
  intros T v i q0 Ev.
  exists (4 * i + 8), (cden (Jp q0 ++ T) [] i AI1_0RB1LA_1RC0LA_0LD1RB____1LB).
  split; [lia|]. split; [| exact (gen_0RB1LA_1RC0LA_0LD1RB____1LB T v i q0 Ev)].
  rewrite (gsn_0RB1LA_1RC0LA_0LD1RB____1LB T v i q0 Ev).
  exact (srun_sound tm false true chn_0RB1LA_1RC0LA_0LD1RB____1LB AI0_0RB1LA_1RC0LA_0LD1RB____1LB AI1_0RB1LA_1RC0LA_0LD1RB____1LB 4 8
           run_inner_0RB1LA_1RC0LA_0LD1RB____1LB (Jp q0 ++ T) [] i
           ltac:(discriminate) ltac:(reflexivity)).
Qed.

(** ** The four chains *)

Definition B0_0RB1LA_1RC0LA_0LD1RB____1LB : sconf := mkC StB (mkS [] [S1;S0] 1 0 [S1;S1;S0;S1;S0]) S0 (mkS [] [] 0 0 []).
Definition B1_0RB1LA_1RC0LA_0LD1RB____1LB : sconf := mkC StB (mkS [] [S1;S1] 1 1 [S1;S1;S0;S1;S0]) S0 (mkS [] [] 0 0 []).

(** *** boot: the outer overflow anchor -> the level-j count *)
Definition BB1_0RB1LA_1RC0LA_0LD1RB____1LB : sconf := mkC StB (mkS [] [S1;S1] 1 0 [S1;S0;S0;S1;S0]) S0 (mkS [S0] [] 0 0 []).
Definition chb_0RB1LA_1RC0LA_0LD1RB____1LB : list lstep := [SCycL 2 0; SWin 4; SCycR 2; SWinR 4].

Lemma run_boot_0RB1LA_1RC0LA_0LD1RB____1LB :
  srun tm true true chb_0RB1LA_1RC0LA_0LD1RB____1LB B0_0RB1LA_1RC0LA_0LD1RB____1LB = Some (BB1_0RB1LA_1RC0LA_0LD1RB____1LB, 4, 8).
Proof. vm_compute. reflexivity. Qed.

(** *** B(S l) fill -> A(l) start.  Section 4c of the brief left this one
    open: its turnaround walks back out over cells it has just written and
    runs one short unless a whole unit is PEELED out of the count, and its eat
    reads one cell INTO the growing region -- that misread is what ends the
    eat -- so its opaque split sits one cell deeper than A->B's. *)
Definition BA0_0RB1LA_1RC0LA_0LD1RB____1LB : sconf := mkC StB (mkS [] [S1;S0] 1 1 [S1;S0;S0]) S0 (mkS [] [] 0 0 []).
Definition BA1_0RB1LA_1RC0LA_0LD1RB____1LB : sconf := mkC StB (mkS [] [S1;S1] 1 1 [S0;S1;S0]) S0 (mkS [S0] [] 0 0 []).
Definition chBA_0RB1LA_1RC0LA_0LD1RB____1LB : list lstep := [SCycL 2 0; SWin 6; SCycR 2; SWinR 4].

Lemma run_BA_0RB1LA_1RC0LA_0LD1RB____1LB :
  srun tm false true chBA_0RB1LA_1RC0LA_0LD1RB____1LB BA0_0RB1LA_1RC0LA_0LD1RB____1LB = Some (BA1_0RB1LA_1RC0LA_0LD1RB____1LB, 4, 14).
Proof. vm_compute. reflexivity. Qed.

(** *** A(l) fill -> B(l) start, the level's second half. *)
Definition AB0_0RB1LA_1RC0LA_0LD1RB____1LB : sconf := mkC StB (mkS [] [S1;S0] 1 0 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition AB1_0RB1LA_1RC0LA_0LD1RB____1LB : sconf := mkC StB (mkS [] [S1;S1] 1 0 [S1;S0]) S0 (mkS [S0] [] 0 0 []).
Definition chAB_0RB1LA_1RC0LA_0LD1RB____1LB : list lstep := [SCycL 2 0; SWin 4; SCycR 2; SWinR 4].

Lemma run_AB_0RB1LA_1RC0LA_0LD1RB____1LB :
  srun tm false true chAB_0RB1LA_1RC0LA_0LD1RB____1LB AB0_0RB1LA_1RC0LA_0LD1RB____1LB = Some (AB1_0RB1LA_1RC0LA_0LD1RB____1LB, 4, 8).
Proof. vm_compute. reflexivity. Qed.

(** *** the closing sweep: the level-0 count -> the outer successor.  Unlike
    the per-level chains this one READS the whole grown tail, so it is affine
    in [j] and its tail is a rep rather than an opaque region. *)
Definition CL0_0RB1LA_1RC0LA_0LD1RB____1LB : sconf := mkC StB (mkS [S1;S0] [S0;S1] 1 0 [S0;S1]) S0 (mkS [] [] 0 0 []).
Definition CL1_0RB1LA_1RC0LA_0LD1RB____1LB : sconf := mkC StB (mkS [] [S1;S1] 1 1 [S1;S1;S0;S1;S0]) S0 (mkS [S0] [] 0 0 []).
Definition chCL_0RB1LA_1RC0LA_0LD1RB____1LB : list lstep := [SWin 2; SRotL 1; SWin 4; SWinR 11; SCycL 2 0; SWin 1; SWinL 5; SCycR 2; SWin 4; SWinR 4; SUnrotL 2; SFoldL 1].

Lemma run_close_0RB1LA_1RC0LA_0LD1RB____1LB :
  srun tm true true chCL_0RB1LA_1RC0LA_0LD1RB____1LB CL0_0RB1LA_1RC0LA_0LD1RB____1LB = Some (CL1_0RB1LA_1RC0LA_0LD1RB____1LB, 4, 31).
Proof. vm_compute. reflexivity. Qed.

(** The sweep stops 0/1 trailing blanks past the outer successor's
    anchor -- [lift] cannot see them, but the syntactic form has to be
    bridged, and after normalisation the side is one fused literal, so the
    blanks are re-split rather than rewritten away. *)
Lemma gcx_0RB1LA_1RC0LA_0LD1RB____1LB : forall j,
  lift (cden [] [] j CL1_0RB1LA_1RC0LA_0LD1RB____1LB) = lift (cden [] [] j B1_0RB1LA_1RC0LA_0LD1RB____1LB).
Proof.
  intro j.
  assert (HD : cden [] [] j CL1_0RB1LA_1RC0LA_0LD1RB____1LB = (StB, (rep [S1;S1] (j + 1) ++ [S1;S1;S0;S1;S0], S0, ([]) ++ [S0]))).
  { unfold cden, CL1_0RB1LA_1RC0LA_0LD1RB____1LB, sden;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 1) with (j + 1) by lia.
    replace (0 * j + 0) with 0 by lia.
    cbn [rep app]. rewrite <- ?app_assoc. cbn [app]. rewrite ?app_nil_r.
    reflexivity. }
  assert (HE : cden [] [] j B1_0RB1LA_1RC0LA_0LD1RB____1LB = (StB, (rep [S1;S1] (j + 1) ++ [S1;S1;S0;S1;S0], S0, []))).
  { unfold cden, B1_0RB1LA_1RC0LA_0LD1RB____1LB, sden;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 1) with (j + 1) by lia.
    replace (0 * j + 0) with 0 by lia.
    cbn [rep app]. rewrite <- ?app_assoc. cbn [app]. rewrite ?app_nil_r.
    reflexivity. }
  rewrite HD, HE. rewrite ?lbl_0RB1LA_1RC0LA_0LD1RB____1LB. rewrite ?lift_app_blank. reflexivity.
Qed.

(** ** The per-level glue

    The opaque region each chain carries, as a function of the level's tail
    length.  Every exponent is built by [S] and [+]; none is a subtraction. *)
Definition XBA_0RB1LA_1RC0LA_0LD1RB____1LB (m : nat) : list Sym := [S1] ++ rep Uc m.
Definition XAB_0RB1LA_1RC0LA_0LD1RB____1LB (m : nat) : list Sym := rep Uc (2 + m).

Lemma gBAs_0RB1LA_1RC0LA_0LD1RB____1LB : forall l m,
  Cin (TB m) (fill (pow2 (S l))) = cden (XBA_0RB1LA_1RC0LA_0LD1RB____1LB m) [] l BA0_0RB1LA_1RC0LA_0LD1RB____1LB.
Proof.
  intros l m.
  unfold Cin_0RB1LA_1RC0LA_0LD1RB____1LB, TB_0RB1LA_1RC0LA_0LD1RB____1LB, XBA_0RB1LA_1RC0LA_0LD1RB____1LB, Uc_0RB1LA_1RC0LA_0LD1RB____1LB, cden, BA0_0RB1LA_1RC0LA_0LD1RB____1LB, sden;
    cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
  rewrite efill_0RB1LA_1RC0LA_0LD1RB____1LB.
  replace (1 * l + 1) with (l + 1) by lia.
  replace (0 * l + 0) with 0 by lia.
  replace (S l) with (l + 1) by lia.
  replace (m + 1) with (1 + m) by lia.
  rewrite ?rep_add. cbn [rep app]. rewrite <- ?app_assoc.
  cbn [app]. rewrite ?app_nil_r. reflexivity.
Qed.

Lemma gBAd_0RB1LA_1RC0LA_0LD1RB____1LB : forall l m,
  lift (cden (XBA_0RB1LA_1RC0LA_0LD1RB____1LB m) [] l BA1_0RB1LA_1RC0LA_0LD1RB____1LB) = lift (Cin (TA (S m)) (pow2 l)).
Proof.
  intros l m.
  unfold Cin_0RB1LA_1RC0LA_0LD1RB____1LB, TA_0RB1LA_1RC0LA_0LD1RB____1LB, XBA_0RB1LA_1RC0LA_0LD1RB____1LB, Uc_0RB1LA_1RC0LA_0LD1RB____1LB, cden, BA1_0RB1LA_1RC0LA_0LD1RB____1LB, sden;
    cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
  rewrite epow2_0RB1LA_1RC0LA_0LD1RB____1LB.
  replace (1 * l + 1) with (l + 1) by lia.
  replace (0 * l + 0) with 0 by lia.
  replace (S m + 1) with (2 + m) by lia.
  rewrite ?rep_add. cbn [rep app]. rewrite <- ?app_assoc.
  cbn [app]. rewrite ?app_nil_r.
  change ([S0]) with (([]) ++ [S0]).
  rewrite ?lift_app_blank. reflexivity.
Qed.

Lemma gABs_0RB1LA_1RC0LA_0LD1RB____1LB : forall l m,
  Cin (TA (S m)) (fill (pow2 l)) = cden (XAB_0RB1LA_1RC0LA_0LD1RB____1LB m) [] l AB0_0RB1LA_1RC0LA_0LD1RB____1LB.
Proof.
  intros l m.
  unfold Cin_0RB1LA_1RC0LA_0LD1RB____1LB, TA_0RB1LA_1RC0LA_0LD1RB____1LB, XAB_0RB1LA_1RC0LA_0LD1RB____1LB, Uc_0RB1LA_1RC0LA_0LD1RB____1LB, cden, AB0_0RB1LA_1RC0LA_0LD1RB____1LB, sden;
    cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
  rewrite efill_0RB1LA_1RC0LA_0LD1RB____1LB.
  replace (1 * l + 0) with l by lia.
  replace (0 * l + 0) with 0 by lia.
  replace (S m + 1) with (2 + m) by lia.
  rewrite ?rep_add. cbn [rep app]. rewrite <- ?app_assoc.
  cbn [app]. rewrite ?app_nil_r. reflexivity.
Qed.

Lemma gABd_0RB1LA_1RC0LA_0LD1RB____1LB : forall l m,
  lift (cden (XAB_0RB1LA_1RC0LA_0LD1RB____1LB m) [] l AB1_0RB1LA_1RC0LA_0LD1RB____1LB) = lift (Cin (TB (S m)) (pow2 l)).
Proof.
  intros l m.
  unfold Cin_0RB1LA_1RC0LA_0LD1RB____1LB, TB_0RB1LA_1RC0LA_0LD1RB____1LB, XAB_0RB1LA_1RC0LA_0LD1RB____1LB, Uc_0RB1LA_1RC0LA_0LD1RB____1LB, cden, AB1_0RB1LA_1RC0LA_0LD1RB____1LB, sden;
    cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
  rewrite epow2_0RB1LA_1RC0LA_0LD1RB____1LB.
  replace (1 * l + 0) with l by lia.
  replace (0 * l + 0) with 0 by lia.
  replace (S m + 1) with (2 + m) by lia.
  rewrite ?rep_add. cbn [rep app]. rewrite <- ?app_assoc.
  cbn [app]. rewrite ?app_nil_r.
  change ([S0]) with (([]) ++ [S0]).
  rewrite ?lift_app_blank. reflexivity.
Qed.

(** ONE LEVEL.  Two counts, each an [exists n] hiding a [Theta(2^l)], and the
    two chains between them -- and it is the SAME step at every level, which
    is the whole content of the cascade. *)
Lemma hstep_0RB1LA_1RC0LA_0LD1RB____1LB : forall l m,
  exists n, stepn tm n (lift (Dc (S l) m)) = Some (lift (Dc l (S m))).
Proof.
  intros l m. unfold Dc_0RB1LA_1RC0LA_0LD1RB____1LB.
  apply (level_hop tm Cin lapin_0RB1LA_1RC0LA_0LD1RB____1LB (TB m) (TA (S m))
                   (pow2 (S l)) (pow2 l)).
  - exists (4 * l + 14). rewrite gBAs_0RB1LA_1RC0LA_0LD1RB____1LB, <- gBAd_0RB1LA_1RC0LA_0LD1RB____1LB.
    apply csteps_lift.
    exact (srun_sound tm false true chBA_0RB1LA_1RC0LA_0LD1RB____1LB BA0_0RB1LA_1RC0LA_0LD1RB____1LB BA1_0RB1LA_1RC0LA_0LD1RB____1LB 4 14
             run_BA_0RB1LA_1RC0LA_0LD1RB____1LB (XBA_0RB1LA_1RC0LA_0LD1RB____1LB m) [] l
             ltac:(discriminate) ltac:(reflexivity)).
  - exists (4 * l + 8). rewrite gABs_0RB1LA_1RC0LA_0LD1RB____1LB, <- gABd_0RB1LA_1RC0LA_0LD1RB____1LB.
    apply csteps_lift.
    exact (srun_sound tm false true chAB_0RB1LA_1RC0LA_0LD1RB____1LB AB0_0RB1LA_1RC0LA_0LD1RB____1LB AB1_0RB1LA_1RC0LA_0LD1RB____1LB 4 8
             run_AB_0RB1LA_1RC0LA_0LD1RB____1LB (XAB_0RB1LA_1RC0LA_0LD1RB____1LB m) [] l
             ltac:(discriminate) ltac:(reflexivity)).
Qed.

(** ** The outer glue: boot in, sweep out *)

Lemma gso_0RB1LA_1RC0LA_0LD1RB____1LB : forall p j, cview p = (S j, None) -> Cc p = cden [] [] j B0_0RB1LA_1RC0LA_0LD1RB____1LB.
Proof.
  intros p j Ev. destruct (JpCounter.cview_none_J p j Ev) as (H1 & _).
  unfold Cc_0RB1LA_1RC0LA_0LD1RB____1LB, cden, B0_0RB1LA_1RC0LA_0LD1RB____1LB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with (j) by lia.
  rewrite H1; cbn [rep app]. rewrite <- ?app_assoc. cbn [app].
  rewrite ?app_nil_r. reflexivity.
Qed.

Lemma geo_0RB1LA_1RC0LA_0LD1RB____1LB : forall p j, cview p = (S j, None) ->
  lift (cden [] [] j B1_0RB1LA_1RC0LA_0LD1RB____1LB) = lift (Cc (Pos.succ p)).
Proof.
  intros p j Ev. destruct (JpCounter.cview_none_J p j Ev) as (_ & H2).
  unfold Cc_0RB1LA_1RC0LA_0LD1RB____1LB, cden, B1_0RB1LA_1RC0LA_0LD1RB____1LB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 1) with (S j) by lia. replace (0 * j + 0) with 0 by lia.
  rewrite H2. cbn [rep app]. rewrite <- ?app_assoc. cbn [app].
  rewrite ?app_nil_r. rewrite ?lift_app_blank. reflexivity.
Qed.

(** The boot lands on the level-j count's anchor, up to 1/1
    trailing blanks -- the [lift] leniency [NestedLapLift] measured to be the
    binding one on this whole bucket. *)
Lemma gbo_0RB1LA_1RC0LA_0LD1RB____1LB : forall j, lift (cden [] [] j BB1_0RB1LA_1RC0LA_0LD1RB____1LB) = lift (Dc j 0).
Proof.
  intro j.
  assert (HD : cden [] [] j BB1_0RB1LA_1RC0LA_0LD1RB____1LB = (StB, ((rep [S1;S1] j ++ [S1;S0;S0;S1]) ++ [S0], S0, ([]) ++ [S0]))).
  { unfold cden, BB1_0RB1LA_1RC0LA_0LD1RB____1LB, sden;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  replace (0 * j + 0) with 0 by lia.
    rewrite ?rep_add. cbn [rep app]. rewrite <- ?app_assoc.
    cbn [app]. rewrite ?app_nil_r. reflexivity. }
  assert (HC : Dc j 0 = (StB, (rep [S1;S1] j ++ [S1;S0;S0;S1], S0, []))).
  { unfold Dc_0RB1LA_1RC0LA_0LD1RB____1LB, Cin_0RB1LA_1RC0LA_0LD1RB____1LB, TB_0RB1LA_1RC0LA_0LD1RB____1LB, Uc_0RB1LA_1RC0LA_0LD1RB____1LB. rewrite epow2_0RB1LA_1RC0LA_0LD1RB____1LB.
    replace (0 + 1) with 1 by lia.
    cbn [rep app]. rewrite <- ?app_assoc. cbn [app]. rewrite ?app_nil_r.
    reflexivity. }
  rewrite HD, HC. rewrite ?lbl_0RB1LA_1RC0LA_0LD1RB____1LB. rewrite ?lift_app_blank. reflexivity.
Qed.

(** The closing sweep starts from the level-0 count, whose tail is by then
    [j] units longer than the top level's -- so unlike the per-level chains it
    is indexed by the OUTER index. *)
Lemma gcl_0RB1LA_1RC0LA_0LD1RB____1LB : forall j, Dc 0 (j + 0) = cden [] [] j CL0_0RB1LA_1RC0LA_0LD1RB____1LB.
Proof.
  intro j.
  unfold Dc_0RB1LA_1RC0LA_0LD1RB____1LB, Cin_0RB1LA_1RC0LA_0LD1RB____1LB, TB_0RB1LA_1RC0LA_0LD1RB____1LB, Uc_0RB1LA_1RC0LA_0LD1RB____1LB, cden, CL0_0RB1LA_1RC0LA_0LD1RB____1LB, sden;
    cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
  rewrite (epow2_0RB1LA_1RC0LA_0LD1RB____1LB 0).
  replace (1 * j + 0) with j by lia.
  replace (0 * j + 0) with 0 by lia.
  replace (j + 0 + 1) with (j + 1) by lia.
  rewrite ?rep_add. cbn [pow2 rep app]. rewrite <- ?app_assoc.
  cbn [app]. rewrite ?app_nil_r. reflexivity.
Qed.

(** ** The overflow branch

    [NestedLapCascade.cascade_overflow] with the level step above: boot in at
    level [j], [j] level steps down (exponentially many counts, none of them
    named), the sweep out.  The conclusion is verbatim the [LapStep]
    obligation, so this drops into a board wherever [lapo_] goes. *)
Lemma lapo_0RB1LA_1RC0LA_0LD1RB____1LB : forall p j, cview p = (S j, None) ->
  exists n c', csteps tm n (Cc p) = Some c'
          /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intros p j Ev.
  apply (cascade_overflow tm Cc Dc hstep_0RB1LA_1RC0LA_0LD1RB____1LB p j 0).
  - exists (4 * j + 8), (cden [] [] j BB1_0RB1LA_1RC0LA_0LD1RB____1LB).
    split; [lia|]. split; [| exact (gbo_0RB1LA_1RC0LA_0LD1RB____1LB j)].
    rewrite (gso_0RB1LA_1RC0LA_0LD1RB____1LB p j Ev).
    exact (srun_sound tm true true chb_0RB1LA_1RC0LA_0LD1RB____1LB B0_0RB1LA_1RC0LA_0LD1RB____1LB BB1_0RB1LA_1RC0LA_0LD1RB____1LB 4 8
             run_boot_0RB1LA_1RC0LA_0LD1RB____1LB [] [] j ltac:(reflexivity) ltac:(reflexivity)).
  - exists (4 * j + 31).
    rewrite gcl_0RB1LA_1RC0LA_0LD1RB____1LB, <- (geo_0RB1LA_1RC0LA_0LD1RB____1LB p j Ev), <- gcx_0RB1LA_1RC0LA_0LD1RB____1LB.
    apply csteps_lift.
    exact (srun_sound tm true true chCL_0RB1LA_1RC0LA_0LD1RB____1LB CL0_0RB1LA_1RC0LA_0LD1RB____1LB CL1_0RB1LA_1RC0LA_0LD1RB____1LB 4 31
             run_close_0RB1LA_1RC0LA_0LD1RB____1LB [] [] j ltac:(reflexivity) ltac:(reflexivity)).
Qed.

(** ** The INTERIOR branch, at the outer anchor *)

Definition A0_0RB1LA_1RC0LA_0LD1RB____1LB : sconf := mkC StB (mkS [] [S1;S0] 1 0 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition A1_0RB1LA_1RC0LA_0LD1RB____1LB : sconf := mkC StB (mkS [] [S1;S1] 1 0 [S1;S0]) S0 (mkS [S0] [] 0 0 []).
Definition chi_0RB1LA_1RC0LA_0LD1RB____1LB : list lstep := [SCycL 2 0; SWin 4; SCycR 2; SWinR 4].

Lemma run_int_0RB1LA_1RC0LA_0LD1RB____1LB : srun tm false true chi_0RB1LA_1RC0LA_0LD1RB____1LB A0_0RB1LA_1RC0LA_0LD1RB____1LB = Some (A1_0RB1LA_1RC0LA_0LD1RB____1LB, 4, 8).
Proof. vm_compute. reflexivity. Qed.

Lemma gsi_0RB1LA_1RC0LA_0LD1RB____1LB : forall p j q0, cview p = (j, Some q0) ->
  Cc p = cden (Jp q0 ++ [S1;S0;S1;S0]) [] j A0_0RB1LA_1RC0LA_0LD1RB____1LB.
Proof.
  intros p j q0 E. destruct (JpCounter.cview_some_J p j q0 E) as (H1 & _).
  unfold Cc_0RB1LA_1RC0LA_0LD1RB____1LB, cden, A0_0RB1LA_1RC0LA_0LD1RB____1LB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  rewrite H1. first [ rewrite <- (app_assoc (rep [S1;S0] j)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

(** The lap ends on [S0] where the anchor has [] -- one trailing blank,
    which [lift] cannot see. *)
Lemma gei_0RB1LA_1RC0LA_0LD1RB____1LB : forall p j q0, cview p = (j, Some q0) ->
  lift (cden (Jp q0 ++ [S1;S0;S1;S0]) [] j A1_0RB1LA_1RC0LA_0LD1RB____1LB) = lift (Cc (Pos.succ p)).
Proof.
  intros p j q0 E. destruct (JpCounter.cview_some_J p j q0 E) as (_ & H2).
  unfold Cc_0RB1LA_1RC0LA_0LD1RB____1LB, cden, A1_0RB1LA_1RC0LA_0LD1RB____1LB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  replace (0 * j + 0) with 0 by lia.
  cbn [rep app]. rewrite ?app_nil_r.
  change ([S0]) with (([]) ++ [S0]).
  rewrite !lift_app_blank.
  rewrite H2. first [ rewrite <- (app_assoc (rep [S1;S1] j)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapi_0RB1LA_1RC0LA_0LD1RB____1LB : forall p j q0, cview p = (j, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof.
  intros p j q0 E.
  exists (4 * j + 8), (cden (Jp q0 ++ [S1;S0;S1;S0]) [] j A1_0RB1LA_1RC0LA_0LD1RB____1LB).
  split; [lia|]. split; [| exact (gei_0RB1LA_1RC0LA_0LD1RB____1LB p j q0 E)].
  rewrite (gsi_0RB1LA_1RC0LA_0LD1RB____1LB p j q0 E).
  exact (srun_sound tm false true chi_0RB1LA_1RC0LA_0LD1RB____1LB A0_0RB1LA_1RC0LA_0LD1RB____1LB A1_0RB1LA_1RC0LA_0LD1RB____1LB 4 8
           run_int_0RB1LA_1RC0LA_0LD1RB____1LB (Jp q0 ++ [S1;S0;S1;S0]) [] j
           ltac:(discriminate) ltac:(reflexivity)).
Qed.

(** [lapi_0RB1LA_1RC0LA_0LD1RB____1LB] is already in [lift] space; alias it for the plumbing. *)
Lemma lapil_0RB1LA_1RC0LA_0LD1RB____1LB : forall p j q0, cview p = (j, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof. exact lapi_0RB1LA_1RC0LA_0LD1RB____1LB. Qed.

(** ** The lap *)

Lemma lap_0RB1LA_1RC0LA_0LD1RB____1LB : forall p, exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:E. destruct oq as [q0|].
  - destruct (lapi_0RB1LA_1RC0LA_0LD1RB____1LB p j q0 E) as (n & c' & Hn & Hrun & Hlift).
    exists n, c'. split; [exact Hrun | split; [exact Hlift | exact Hn]].
  - destruct (cview_pos p j E) as (j' & ->).
    exact (lapo_0RB1LA_1RC0LA_0LD1RB____1LB p j' E).
Qed.

(** ** Bootstrap *)

Lemma boot_0RB1LA_1RC0LA_0LD1RB____1LB : exists t0, stepn tm t0 InitES = Some (lift (Cc 1)).
Proof.
  exists 31.
  assert (H : match csteps tm 31 c0 with
              | Some c => ceqb c (Cc 1) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 31 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** ** Visits

    Only the boot and the closing sweep fire at EVERY outer index -- at
    j = 0 the cascade has no descent, so a witness inside a per-level chain
    would not be universal.  A state missing from the boot chain is found in
    the SWEEP, reached through the whole cascade ([cascade_vis]: boot to
    level j, [cascade_down] to level 0, then a prefix of the sweep). *)

Lemma viso_0RB1LA_1RC0LA_0LD1RB____1LB : forall (l : list lstep) (q : St),
  srun_st tm true true l B0_0RB1LA_1RC0LA_0LD1RB____1LB = Some q ->
  forall p j, cview p = (S j, None) ->
  exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros l q Hst p j E.
  apply (vis_of_run tm Cc true true l B0_0RB1LA_1RC0LA_0LD1RB____1LB p j [] []);
    [exact Hst | reflexivity | reflexivity | exact (gso_0RB1LA_1RC0LA_0LD1RB____1LB p j E)].
Qed.

Lemma visc_0RB1LA_1RC0LA_0LD1RB____1LB : forall (l : list lstep) (q : St),
  srun_st tm true true l CL0_0RB1LA_1RC0LA_0LD1RB____1LB = Some q ->
  forall p j, cview p = (S j, None) ->
  exists k e, stepn tm k (lift (Cc p)) = Some e /\ fst e = q.
Proof.
  intros l q Hst p j Ev.
  apply (cascade_vis tm Cc Dc hstep_0RB1LA_1RC0LA_0LD1RB____1LB q p j 0).
  - exists (4 * j + 8), (cden [] [] j BB1_0RB1LA_1RC0LA_0LD1RB____1LB).
    split; [| exact (gbo_0RB1LA_1RC0LA_0LD1RB____1LB j)].
    rewrite (gso_0RB1LA_1RC0LA_0LD1RB____1LB p j Ev).
    exact (srun_sound tm true true chb_0RB1LA_1RC0LA_0LD1RB____1LB B0_0RB1LA_1RC0LA_0LD1RB____1LB BB1_0RB1LA_1RC0LA_0LD1RB____1LB 4 8
             run_boot_0RB1LA_1RC0LA_0LD1RB____1LB [] [] j ltac:(reflexivity) ltac:(reflexivity)).
  - rewrite gcl_0RB1LA_1RC0LA_0LD1RB____1LB.
    destruct (vis_of_run tm (fun _ => cden [] [] j CL0_0RB1LA_1RC0LA_0LD1RB____1LB) true true l
                CL0_0RB1LA_1RC0LA_0LD1RB____1LB 1%positive j [] [] q Hst
                ltac:(reflexivity) ltac:(reflexivity) eq_refl)
      as (k & c & Hk & Hq).
    exists k, (lift c).
    split; [apply csteps_lift; exact Hk | rewrite lift_state; exact Hq].
Qed.

Lemma vis_0RB1LA_1RC0LA_0LD1RB____1LB : forall p q,
  exists k e, stepn tm k (lift (Cc p)) = Some e /\ fst e = q.
Proof.
  intros p q.
  destruct q.
  - (* StA *)
    apply (vis_via_ovf_lift tm Cc lapil_0RB1LA_1RC0LA_0LD1RB____1LB StA).
    intros p1 j1 E1. apply (vis_lift_of_csteps tm Cc).
    apply (viso_0RB1LA_1RC0LA_0LD1RB____1LB [SCycL 2 0; SWin 3] StA ltac:(vm_compute; reflexivity)
                 p1 j1 E1).
  - (* StB *)
    apply (vis_via_ovf_lift tm Cc lapil_0RB1LA_1RC0LA_0LD1RB____1LB StB).
    intros p1 j1 E1. apply (vis_lift_of_csteps tm Cc).
    apply (viso_0RB1LA_1RC0LA_0LD1RB____1LB [] StB ltac:(vm_compute; reflexivity)
                 p1 j1 E1).
  - (* StC *)
    apply (vis_via_ovf_lift tm Cc lapil_0RB1LA_1RC0LA_0LD1RB____1LB StC).
    intros p1 j1 E1. apply (vis_lift_of_csteps tm Cc).
    apply (viso_0RB1LA_1RC0LA_0LD1RB____1LB [SCycL 2 0; SWin 1] StC ltac:(vm_compute; reflexivity)
                 p1 j1 E1).
  - (* StD: fires only in the closing sweep *)
    apply (vis_via_ovf_lift tm Cc lapil_0RB1LA_1RC0LA_0LD1RB____1LB StD).
    intros p1 j1 E1.
    apply (visc_0RB1LA_1RC0LA_0LD1RB____1LB [SWin 2; SRotL 1; SWin 2] StD ltac:(vm_compute; reflexivity)
                 p1 j1 E1).
Qed.

(** The interior lap closes only up to [lift] (one trailing blank past the
    anchor's far side), so the closer is [LapCertGlueLift.glue_neverqh_lift]:
    [LapGlue.glue_neverqh] with the visit premise in [stepn] space, which is
    what its own proof consumes. *)
Theorem nqhm_0RB1LA_1RC0LA_0LD1RB____1LB : NeverQuasiHaltsSt tm.
Proof. apply (glue_neverqh_lift tm Cc 1). - exact boot_0RB1LA_1RC0LA_0LD1RB____1LB. - intros p _. apply lap_0RB1LA_1RC0LA_0LD1RB____1LB. - intros p q _. apply vis_0RB1LA_1RC0LA_0LD1RB____1LB. Qed.

Theorem nqh_0RB1LA_1RC0LA_0LD1RB____1LB : NeverQuasiHaltsSt tm_0RB1LA_1RC0LA_0LD1RB____1LB.
Proof. apply (mirror_never_qh tm_0RB1LA_1RC0LA_0LD1RB____1LB). rewrite mirror_ok_0RB1LA_1RC0LA_0LD1RB____1LB. exact nqhm_0RB1LA_1RC0LA_0LD1RB____1LB. Qed.

Theorem nonhalt_0RB1LA_1RC0LA_0LD1RB____1LB : NonHalt tm_0RB1LA_1RC0LA_0LD1RB____1LB.
Proof. apply never_qh_nonhalt, nqh_0RB1LA_1RC0LA_0LD1RB____1LB. Qed.
