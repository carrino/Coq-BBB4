(** * CASB_0RB1LA_1LC1RD_1RD1LD_1RB0LA: machine 0RB1LA_1LC1RD_1RD1LD_1RB0LA, boarded by the CASCADE route (octave down).

    Auto-emitted by tools/counters/cascade_emit.py (UNTRUSTED emitter; the Coq
    kernel re-runs the checker on every line below).  Left-growth binary
    counter under the Jp digit alphabet, anchored at

      Cc p = (StA, (Jp p ++ [S0], S0, []))

    The INTERIOR branch is an ordinary lap certificate (4*j+4 steps,
    closing exactly).  The OVERFLOW branch is a DESCENDING-OCTAVE CASCADE
    sitting ONE OCTAVE DOWN: at outer index S j' the boot lands on the top
    level's FIRST count A(j'), one A->B hop enters the standard descent
    ([fill_hop] hides the count), and after level 0 the machine runs ONE
    MORE ASCENDING COUNT at octave j+1 -- the same inner family over the
    constant tail [BT] -- before the outer successor.  The p = 1 overflow
    (outer index 0) has no cascade at all and is a concrete lap.  The
    induction is [NestedLapCascade.cascade_overflow] at [d0 = 1].

      inner lap        4*i+4 steps, at any tail
      boot             4*j+10  at the REINDEXED anchor -> A(top)
      B(l+1) -> A(l)   4*l+10
      A(l)   -> B(l)   4*l+4
      closeA           0*j+11  level 0 -> the closing count
      closeB           4*j+4  its fill -> the outer successor

    VISITS: every state fires inside the boot chain, whose witness covers
    the reindexed anchors; the p = 1 anchor gets concrete [visz_]
    witnesses (the offset route's device).

    Differentially validated against the raw simulator -- step counts AND
    exact configurations: 192 interior anchors (interior); cascade (octave down): p=1 concrete + 7 overflow phases, j = 2..8 (35 levels, 70 counts, 1934 inner laps).
    Axiom footprint: [functional_extensionality_dep] (via [CTape.lift]). *)
From Coq Require Import Arith Lia Bool List PArith Wellfounded.
From BBB4 Require Import BBB4_Statement CTape Mirror.
From Coq Require Import FunctionalExtensionality.
From BBB4.Counters Require Import WTape MonoCounter JpCounter IXPGadgets
                                  LapCertGlue LapCertGlueLift NestedLap
                                  NestedLapLift NestedLapCascade.
From BBB4.Checkers Require Import LapDecider.
Import ListNotations.

Definition mk_0RB1LA_1LC1RD_1RD1LD_1RB0LA (w : Sym) (d : Dir) (n : St) : option Trans :=
  Some (mkTrans w d n).
Local Notation mk := mk_0RB1LA_1LC1RD_1RD1LD_1RB0LA.

(** 0RB1LA_1LC1RD_1RD1LD_1RB0LA -- the table every lemma below runs on. *)
(** 0RB1LA_1LC1RD_1RD1LD_1RB0LA -- the real machine (its counter grows RIGHT). *)
Definition tm_0RB1LA_1LC1RD_1RD1LD_1RB0LA : TM := fun q s => match q, s with
  | StA, S0 => mk S0 DR StB | StA, S1 => mk S1 DL StA
  | StB, S0 => mk S1 DL StC | StB, S1 => mk S1 DR StD
  | StC, S0 => mk S1 DR StD | StC, S1 => mk S1 DL StD
  | StD, S0 => mk S1 DR StB | StD, S1 => mk S0 DL StA end.

(** Its mirror 0LB1RA_1RC1LD_1LD1RD_1LB0RA: the same counter grown leftward.  Every
    lemma below runs on the MIRRORED table;
    [Mirror.mirror_never_qh] transfers the conclusion back. *)
Definition tmm_0RB1LA_1LC1RD_1RD1LD_1RB0LA : TM := fun q s => match q, s with
  | StA, S0 => mk S0 DL StB | StA, S1 => mk S1 DR StA
  | StB, S0 => mk S1 DR StC | StB, S1 => mk S1 DL StD
  | StC, S0 => mk S1 DL StD | StC, S1 => mk S1 DR StD
  | StD, S0 => mk S1 DL StB | StD, S1 => mk S0 DR StA end.
Local Notation tm := tmm_0RB1LA_1LC1RD_1RD1LD_1RB0LA.

Lemma mirror_ok_0RB1LA_1LC1RD_1RD1LD_1RB0LA : mirror_tm tm_0RB1LA_1LC1RD_1RD1LD_1RB0LA = tmm_0RB1LA_1LC1RD_1RD1LD_1RB0LA.
Proof.
  apply functional_extensionality; intro q;
    apply functional_extensionality; intro b; destruct q, b; reflexivity.
Qed.

Definition Cc_0RB1LA_1LC1RD_1RD1LD_1RB0LA (p : positive) : cconf := (StA, (Jp p ++ [S0], S0, [])).
Local Notation Cc := Cc_0RB1LA_1LC1RD_1RD1LD_1RB0LA.

(** A chain accepted up to [lift] can stop a blank past the anchor -- the
    leniency [NestedLapLift] measured to be the binding one on this bucket --
    and [CTape.lift_side] cannot see it.  Every landing bridge below ends
    here, so it is stated before the first of them. *)
Lemma lbl_0RB1LA_1LC1RD_1RD1LD_1RB0LA : forall q l h r, lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.


(** ** The inner family, at an ARBITRARY tail

    [T] is the cascade's growing region.  The counter's own laps never read
    it, so quantifying over it costs nothing and buys every level. *)
Definition Cin_0RB1LA_1LC1RD_1RD1LD_1RB0LA (T : list Sym) (v : positive) : cconf :=
  (StA, (Jp v ++ T, S0, [])).
Local Notation Cin := Cin_0RB1LA_1LC1RD_1RD1LD_1RB0LA.

Definition Uc_0RB1LA_1LC1RD_1RD1LD_1RB0LA : list Sym := [S1;S1].
Local Notation Uc := Uc_0RB1LA_1LC1RD_1RD1LD_1RB0LA.

(** The two tails a level carries: the count that ENTERS it and the count the
    level's own transition produces.  One unit longer per level down. *)
Definition TB_0RB1LA_1LC1RD_1RD1LD_1RB0LA (m : nat) : list Sym := [S0;S0] ++ rep Uc (m + 0).
Definition TA_0RB1LA_1LC1RD_1RD1LD_1RB0LA (m : nat) : list Sym := [S1;S0] ++ rep Uc (m + 0).
Local Notation TB := TB_0RB1LA_1LC1RD_1RD1LD_1RB0LA.
Local Notation TA := TA_0RB1LA_1LC1RD_1RD1LD_1RB0LA.

(** The level-[l] entry configuration, with [m] units of tail beyond the
    top level's.  Both indices are explicit and both are built by [S]: a
    single index would force [j - l] into an anchor, which is the wave-15
    index-shift trap. *)
Definition Dc_0RB1LA_1LC1RD_1RD1LD_1RB0LA (l m : nat) : cconf := Cin (TB m) (pow2 l).
Local Notation Dc := Dc_0RB1LA_1LC1RD_1RD1LD_1RB0LA.

(** [E (2^n)] and [E (2^(n+1)-1)]: the value each count starts and ends at. *)
Lemma epow2_0RB1LA_1LC1RD_1RD1LD_1RB0LA : forall n, Jp (pow2 n) = rep [S1;S1] n ++ [S1].
Proof. induction n; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.

Lemma efill_0RB1LA_1LC1RD_1RD1LD_1RB0LA : forall n, Jp (fill (pow2 n)) = rep [S1;S0] n ++ [S1].
Proof.
  intro n.
  destruct (JpCounter.cview_none_J (fill (pow2 n)) n (cview_fill_pow2 n)) as (H & _).
  exact H.
Qed.

(** ** The inner family's own interior lap -- ordinary, affine, tail-blind *)

Definition AI0_0RB1LA_1LC1RD_1RD1LD_1RB0LA : sconf := mkC StA (mkS [] [S1;S0] 1 0 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition AI1_0RB1LA_1LC1RD_1RD1LD_1RB0LA : sconf := mkC StA (mkS [] [S1;S1] 1 0 [S1;S0]) S0 (mkS [] [] 0 0 []).
Definition chn_0RB1LA_1LC1RD_1RD1LD_1RB0LA : list lstep := [SRotL 1; SWin 1; SCycL 2 0; SWin 2; SCycR 2; SWin 1; SUnrotL 1].

Lemma run_inner_0RB1LA_1LC1RD_1RD1LD_1RB0LA :
  srun tm false true chn_0RB1LA_1LC1RD_1RD1LD_1RB0LA AI0_0RB1LA_1LC1RD_1RD1LD_1RB0LA = Some (AI1_0RB1LA_1LC1RD_1RD1LD_1RB0LA, 4, 4).
Proof. vm_compute. reflexivity. Qed.

Lemma gsn_0RB1LA_1LC1RD_1RD1LD_1RB0LA : forall T v i q0, cview v = (i, Some q0) ->
  Cin T v = cden (Jp q0 ++ T) [] i AI0_0RB1LA_1LC1RD_1RD1LD_1RB0LA.
Proof.
  intros T v i q0 Ev. destruct (JpCounter.cview_some_J v i q0 Ev) as (H1 & _).
  unfold Cin_0RB1LA_1LC1RD_1RD1LD_1RB0LA, cden, AI0_0RB1LA_1LC1RD_1RD1LD_1RB0LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia. rewrite H1.
  cbn [rep app]. rewrite <- ?app_assoc. cbn [app]. rewrite ?app_nil_r.
  reflexivity.
Qed.

Lemma gen_0RB1LA_1LC1RD_1RD1LD_1RB0LA : forall T v i q0, cview v = (i, Some q0) ->
  lift (cden (Jp q0 ++ T) [] i AI1_0RB1LA_1LC1RD_1RD1LD_1RB0LA) = lift (Cin T (Pos.succ v)).
Proof.
  intros T v i q0 Ev. destruct (JpCounter.cview_some_J v i q0 Ev) as (_ & H2).
  unfold Cin_0RB1LA_1LC1RD_1RD1LD_1RB0LA, cden, AI1_0RB1LA_1LC1RD_1RD1LD_1RB0LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia. replace (0 * i + 0) with 0 by lia.
  rewrite H2. cbn [rep app]. rewrite <- ?app_assoc. cbn [app].
  rewrite ?app_nil_r.
  rewrite ?lift_app_blank. reflexivity.
Qed.

(** The lap, up to [lift] and at every tail at once -- this is
    [NestedLapCascade]'s [Hin]. *)
Lemma lapin_0RB1LA_1LC1RD_1RD1LD_1RB0LA : forall T v i q0, cview v = (i, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cin T v) = Some c'
               /\ lift c' = lift (Cin T (Pos.succ v)).
Proof.
  intros T v i q0 Ev.
  exists (4 * i + 4), (cden (Jp q0 ++ T) [] i AI1_0RB1LA_1LC1RD_1RD1LD_1RB0LA).
  split; [lia|]. split; [| exact (gen_0RB1LA_1LC1RD_1RD1LD_1RB0LA T v i q0 Ev)].
  rewrite (gsn_0RB1LA_1LC1RD_1RD1LD_1RB0LA T v i q0 Ev).
  exact (srun_sound tm false true chn_0RB1LA_1LC1RD_1RD1LD_1RB0LA AI0_0RB1LA_1LC1RD_1RD1LD_1RB0LA AI1_0RB1LA_1LC1RD_1RD1LD_1RB0LA 4 4
           run_inner_0RB1LA_1LC1RD_1RD1LD_1RB0LA (Jp q0 ++ T) [] i
           ltac:(discriminate) ltac:(reflexivity)).
Qed.

(** ** The four chains *)

Definition B0_0RB1LA_1LC1RD_1RD1LD_1RB0LA : sconf := mkC StA (mkS [S1;S0] [S1;S0] 1 0 [S1;S0]) S0 (mkS [] [] 0 0 []).
Definition B1_0RB1LA_1LC1RD_1RD1LD_1RB0LA : sconf := mkC StA (mkS [] [S1;S1] 1 1 [S1;S0]) S0 (mkS [] [] 0 0 []).

(** *** boot: the outer overflow anchor -> the level-j count *)
Definition BB1_0RB1LA_1LC1RD_1RD1LD_1RB0LA : sconf := mkC StA (mkS [] [S1;S1] 1 0 [S1;S1;S0;S1;S1]) S0 (mkS [] [] 0 0 []).
Definition chb_0RB1LA_1LC1RD_1RD1LD_1RB0LA : list lstep := [SWin 2; SCycL 2 0; SWin 2; SWinL 4; SCycR 2; SWin 2; SUnrotL 2].

Lemma run_boot_0RB1LA_1LC1RD_1RD1LD_1RB0LA :
  srun tm true true chb_0RB1LA_1LC1RD_1RD1LD_1RB0LA B0_0RB1LA_1LC1RD_1RD1LD_1RB0LA = Some (BB1_0RB1LA_1LC1RD_1RD1LD_1RB0LA, 4, 10).
Proof. vm_compute. reflexivity. Qed.

(** *** B(S l) fill -> A(l) start.  Section 4c of the brief left this one
    open: its turnaround walks back out over cells it has just written and
    runs one short unless a whole unit is PEELED out of the count, and its eat
    reads one cell INTO the growing region -- that misread is what ends the
    eat -- so its opaque split sits one cell deeper than A->B's. *)
Definition BA0_0RB1LA_1LC1RD_1RD1LD_1RB0LA : sconf := mkC StA (mkS [] [S1;S0] 1 0 [S1;S0;S1;S0;S0]) S0 (mkS [] [] 0 0 []).
Definition BA1_0RB1LA_1LC1RD_1RD1LD_1RB0LA : sconf := mkC StA (mkS [] [S1;S1] 1 0 [S1;S1;S0;S1;S1]) S0 (mkS [] [] 0 0 []).
Definition chBA_0RB1LA_1LC1RD_1RD1LD_1RB0LA : list lstep := [SRotL 1; SWin 1; SCycL 2 0; SWin 8; SCycR 2; SWin 1; SUnrotL 1].

Lemma run_BA_0RB1LA_1LC1RD_1RD1LD_1RB0LA :
  srun tm false true chBA_0RB1LA_1LC1RD_1RD1LD_1RB0LA BA0_0RB1LA_1LC1RD_1RD1LD_1RB0LA = Some (BA1_0RB1LA_1LC1RD_1RD1LD_1RB0LA, 4, 10).
Proof. vm_compute. reflexivity. Qed.

(** *** A(l) fill -> B(l) start, the level's second half. *)
Definition AB0_0RB1LA_1LC1RD_1RD1LD_1RB0LA : sconf := mkC StA (mkS [] [S1;S0] 1 0 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition AB1_0RB1LA_1LC1RD_1RD1LD_1RB0LA : sconf := mkC StA (mkS [] [S1;S1] 1 0 [S1;S0]) S0 (mkS [] [] 0 0 []).
Definition chAB_0RB1LA_1LC1RD_1RD1LD_1RB0LA : list lstep := [SRotL 1; SWin 1; SCycL 2 0; SWin 2; SCycR 2; SWin 1; SUnrotL 1].

Lemma run_AB_0RB1LA_1LC1RD_1RD1LD_1RB0LA :
  srun tm false true chAB_0RB1LA_1LC1RD_1RD1LD_1RB0LA AB0_0RB1LA_1LC1RD_1RD1LD_1RB0LA = Some (AB1_0RB1LA_1LC1RD_1RD1LD_1RB0LA, 4, 4).
Proof. vm_compute. reflexivity. Qed.

(** *** the close, octave-down: after level 0 the machine runs ONE MORE
    ASCENDING COUNT at octave j+1 -- the same inner family over the constant
    tail [BT], its exponentially many laps living in [fill_hop] -- framed by
    two affine chains. *)
(** The closing count ENTERS ONE VALUE IN, at [xI (pow2 n)] = 2^(n+1)+1
    rather than at [pow2 (S n)]: its word is the octave's with the odd digit
    peeled off the front and one fewer unit copy behind it.  Its FILL is the
    same all-ones value, so only the way IN moves. *)
Lemma exi_0RB1LA_1LC1RD_1RD1LD_1RB0LA : forall n,
  Jp (xI (pow2 n)) = [S1;S0] ++ rep [S1;S1] n ++ [S1].
Proof. intro n. rewrite <- epow2_0RB1LA_1LC1RD_1RD1LD_1RB0LA. reflexivity. Qed.

Lemma exif_0RB1LA_1LC1RD_1RD1LD_1RB0LA : forall n,
  Jp (fill (xI (pow2 n))) = rep [S1;S0] (S n) ++ [S1].
Proof. intro n. exact (efill_0RB1LA_1LC1RD_1RD1LD_1RB0LA (S n)). Qed.

Definition BT_0RB1LA_1LC1RD_1RD1LD_1RB0LA : list Sym := [S1].
Local Notation BT := BT_0RB1LA_1LC1RD_1RD1LD_1RB0LA.

Definition CLA0_0RB1LA_1LC1RD_1RD1LD_1RB0LA : sconf := mkC StA (mkS [S1;S0;S0] [S1;S1] 1 0 []) S0 (mkS [] [] 0 0 []).
Definition CLA1_0RB1LA_1LC1RD_1RD1LD_1RB0LA : sconf := mkC StA (mkS [S1;S0] [S1;S1] 1 0 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition chCLA_0RB1LA_1LC1RD_1RD1LD_1RB0LA : list lstep := [SWin 10; SWinR 1; SUnrotL 2].

Lemma run_closeA_0RB1LA_1LC1RD_1RD1LD_1RB0LA :
  srun tm true true chCLA_0RB1LA_1LC1RD_1RD1LD_1RB0LA CLA0_0RB1LA_1LC1RD_1RD1LD_1RB0LA = Some (CLA1_0RB1LA_1LC1RD_1RD1LD_1RB0LA, 0, 11).
Proof. vm_compute. reflexivity. Qed.

Definition CLB0_0RB1LA_1LC1RD_1RD1LD_1RB0LA : sconf := mkC StA (mkS [] [S1;S0] 1 0 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition CLB1_0RB1LA_1LC1RD_1RD1LD_1RB0LA : sconf := mkC StA (mkS [] [S1;S1] 1 0 [S1;S0]) S0 (mkS [] [] 0 0 []).
Definition chCLB_0RB1LA_1LC1RD_1RD1LD_1RB0LA : list lstep := [SRotL 1; SWin 1; SCycL 2 0; SWin 2; SCycR 2; SWin 1; SUnrotL 1].

Lemma run_closeB_0RB1LA_1LC1RD_1RD1LD_1RB0LA :
  srun tm true true chCLB_0RB1LA_1LC1RD_1RD1LD_1RB0LA CLB0_0RB1LA_1LC1RD_1RD1LD_1RB0LA = Some (CLB1_0RB1LA_1LC1RD_1RD1LD_1RB0LA, 4, 4).
Proof. vm_compute. reflexivity. Qed.

(** ** The per-level glue

    The opaque region each chain carries, as a function of the level's tail
    length.  Every exponent is built by [S] and [+]; none is a subtraction. *)
Definition XBA_0RB1LA_1LC1RD_1RD1LD_1RB0LA (m : nat) : list Sym := rep Uc m.
Definition XAB_0RB1LA_1LC1RD_1RD1LD_1RB0LA (m : nat) : list Sym := [S0] ++ rep Uc (1 + m).

Lemma gBAs_0RB1LA_1LC1RD_1RD1LD_1RB0LA : forall l m,
  Cin (TB m) (fill (pow2 (S l))) = cden (XBA_0RB1LA_1LC1RD_1RD1LD_1RB0LA m) [] l BA0_0RB1LA_1LC1RD_1RD1LD_1RB0LA.
Proof.
  intros l m.
  unfold Cin_0RB1LA_1LC1RD_1RD1LD_1RB0LA, TB_0RB1LA_1LC1RD_1RD1LD_1RB0LA, XBA_0RB1LA_1LC1RD_1RD1LD_1RB0LA, Uc_0RB1LA_1LC1RD_1RD1LD_1RB0LA, cden, BA0_0RB1LA_1LC1RD_1RD1LD_1RB0LA, sden;
    cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
  rewrite efill_0RB1LA_1LC1RD_1RD1LD_1RB0LA.
  replace (1 * l + 0) with l by lia.
  replace (0 * l + 0) with 0 by lia.
  replace (S l) with (l + 1) by lia.
  replace (m + 0) with (0 + m) by lia.
  rewrite ?rep_add. cbn [rep app]. rewrite <- ?app_assoc.
  cbn [app]. rewrite ?app_nil_r. reflexivity.
Qed.

Lemma gBAd_0RB1LA_1LC1RD_1RD1LD_1RB0LA : forall l m,
  lift (cden (XBA_0RB1LA_1LC1RD_1RD1LD_1RB0LA m) [] l BA1_0RB1LA_1LC1RD_1RD1LD_1RB0LA) = lift (Cin (TA (S m)) (pow2 l)).
Proof.
  intros l m.
  unfold Cin_0RB1LA_1LC1RD_1RD1LD_1RB0LA, TA_0RB1LA_1LC1RD_1RD1LD_1RB0LA, XBA_0RB1LA_1LC1RD_1RD1LD_1RB0LA, Uc_0RB1LA_1LC1RD_1RD1LD_1RB0LA, cden, BA1_0RB1LA_1LC1RD_1RD1LD_1RB0LA, sden;
    cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
  rewrite epow2_0RB1LA_1LC1RD_1RD1LD_1RB0LA.
  replace (1 * l + 0) with l by lia.
  replace (0 * l + 0) with 0 by lia.
  replace (S m + 0) with (1 + m) by lia.
  rewrite ?rep_add. cbn [rep app]. rewrite <- ?app_assoc.
  cbn [app]. rewrite ?app_nil_r.
  rewrite ?lift_app_blank. reflexivity.
Qed.

Lemma gABs_0RB1LA_1LC1RD_1RD1LD_1RB0LA : forall l m,
  Cin (TA (S m)) (fill (pow2 l)) = cden (XAB_0RB1LA_1LC1RD_1RD1LD_1RB0LA m) [] l AB0_0RB1LA_1LC1RD_1RD1LD_1RB0LA.
Proof.
  intros l m.
  unfold Cin_0RB1LA_1LC1RD_1RD1LD_1RB0LA, TA_0RB1LA_1LC1RD_1RD1LD_1RB0LA, XAB_0RB1LA_1LC1RD_1RD1LD_1RB0LA, Uc_0RB1LA_1LC1RD_1RD1LD_1RB0LA, cden, AB0_0RB1LA_1LC1RD_1RD1LD_1RB0LA, sden;
    cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
  rewrite efill_0RB1LA_1LC1RD_1RD1LD_1RB0LA.
  replace (1 * l + 0) with l by lia.
  replace (0 * l + 0) with 0 by lia.
  replace (S m + 0) with (1 + m) by lia.
  rewrite ?rep_add. cbn [rep app]. rewrite <- ?app_assoc.
  cbn [app]. rewrite ?app_nil_r. reflexivity.
Qed.

Lemma gABd_0RB1LA_1LC1RD_1RD1LD_1RB0LA : forall l m,
  lift (cden (XAB_0RB1LA_1LC1RD_1RD1LD_1RB0LA m) [] l AB1_0RB1LA_1LC1RD_1RD1LD_1RB0LA) = lift (Cin (TB (S m)) (pow2 l)).
Proof.
  intros l m.
  unfold Cin_0RB1LA_1LC1RD_1RD1LD_1RB0LA, TB_0RB1LA_1LC1RD_1RD1LD_1RB0LA, XAB_0RB1LA_1LC1RD_1RD1LD_1RB0LA, Uc_0RB1LA_1LC1RD_1RD1LD_1RB0LA, cden, AB1_0RB1LA_1LC1RD_1RD1LD_1RB0LA, sden;
    cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
  rewrite epow2_0RB1LA_1LC1RD_1RD1LD_1RB0LA.
  replace (1 * l + 0) with l by lia.
  replace (0 * l + 0) with 0 by lia.
  replace (S m + 0) with (1 + m) by lia.
  rewrite ?rep_add. cbn [rep app]. rewrite <- ?app_assoc.
  cbn [app]. rewrite ?app_nil_r.
  rewrite ?lift_app_blank. reflexivity.
Qed.

(** ONE LEVEL.  Two counts, each an [exists n] hiding a [Theta(2^l)], and the
    two chains between them -- and it is the SAME step at every level, which
    is the whole content of the cascade. *)
Lemma hstep_0RB1LA_1LC1RD_1RD1LD_1RB0LA : forall l m,
  exists n, stepn tm n (lift (Dc (S l) m)) = Some (lift (Dc l (S m))).
Proof.
  intros l m. unfold Dc_0RB1LA_1LC1RD_1RD1LD_1RB0LA.
  apply (level_hop tm Cin lapin_0RB1LA_1LC1RD_1RD1LD_1RB0LA (TB m) (TA (S m))
                   (pow2 (S l)) (pow2 l)).
  - exists (4 * l + 10). rewrite gBAs_0RB1LA_1LC1RD_1RD1LD_1RB0LA, <- gBAd_0RB1LA_1LC1RD_1RD1LD_1RB0LA.
    apply csteps_lift.
    exact (srun_sound tm false true chBA_0RB1LA_1LC1RD_1RD1LD_1RB0LA BA0_0RB1LA_1LC1RD_1RD1LD_1RB0LA BA1_0RB1LA_1LC1RD_1RD1LD_1RB0LA 4 10
             run_BA_0RB1LA_1LC1RD_1RD1LD_1RB0LA (XBA_0RB1LA_1LC1RD_1RD1LD_1RB0LA m) [] l
             ltac:(discriminate) ltac:(reflexivity)).
  - exists (4 * l + 4). rewrite gABs_0RB1LA_1LC1RD_1RD1LD_1RB0LA, <- gABd_0RB1LA_1LC1RD_1RD1LD_1RB0LA.
    apply csteps_lift.
    exact (srun_sound tm false true chAB_0RB1LA_1LC1RD_1RD1LD_1RB0LA AB0_0RB1LA_1LC1RD_1RD1LD_1RB0LA AB1_0RB1LA_1LC1RD_1RD1LD_1RB0LA 4 4
             run_AB_0RB1LA_1LC1RD_1RD1LD_1RB0LA (XAB_0RB1LA_1LC1RD_1RD1LD_1RB0LA m) [] l
             ltac:(discriminate) ltac:(reflexivity)).
Qed.

(** ** The outer glue: boot in, sweep out *)

Lemma gso_0RB1LA_1LC1RD_1RD1LD_1RB0LA : forall p j, cview p = (S (S j), None) ->
  Cc p = cden [] [] j B0_0RB1LA_1LC1RD_1RD1LD_1RB0LA.
Proof.
  intros p j Ev. destruct (JpCounter.cview_none_J p (S j) Ev) as (H1 & _).
  unfold Cc_0RB1LA_1LC1RD_1RD1LD_1RB0LA, cden, B0_0RB1LA_1LC1RD_1RD1LD_1RB0LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with (j) by lia.
  rewrite H1; cbn [rep app]. rewrite <- ?app_assoc. cbn [app].
  rewrite ?app_nil_r. reflexivity.
Qed.

Lemma geo_0RB1LA_1LC1RD_1RD1LD_1RB0LA : forall p j, cview p = (S j, None) ->
  lift (cden [] [] j B1_0RB1LA_1LC1RD_1RD1LD_1RB0LA) = lift (Cc (Pos.succ p)).
Proof.
  intros p j Ev. destruct (JpCounter.cview_none_J p j Ev) as (_ & H2).
  unfold Cc_0RB1LA_1LC1RD_1RD1LD_1RB0LA, cden, B1_0RB1LA_1LC1RD_1RD1LD_1RB0LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 1) with (S j) by lia. replace (0 * j + 0) with 0 by lia.
  rewrite H2. cbn [rep app]. rewrite <- ?app_assoc. cbn [app].
  rewrite ?app_nil_r. rewrite ?lift_app_blank. reflexivity.
Qed.

(** The boot chain lands on the TOP level's FIRST count -- A at one level
    BELOW the outer index, tail one unit past the top's -- up to 0/0
    trailing blanks. *)
Lemma gboa_0RB1LA_1LC1RD_1RD1LD_1RB0LA : forall j, lift (cden [] [] j BB1_0RB1LA_1LC1RD_1RD1LD_1RB0LA) = lift (Cin (TA 1) (pow2 j)).
Proof.
  intro j.
  assert (HD : cden [] [] j BB1_0RB1LA_1LC1RD_1RD1LD_1RB0LA = (StA, (rep [S1;S1] j ++ [S1;S1;S0;S1;S1], S0, []))).
  { unfold cden, BB1_0RB1LA_1LC1RD_1RD1LD_1RB0LA, sden;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  replace (0 * j + 0) with 0 by lia.
    rewrite ?rep_add. cbn [rep app]. rewrite <- ?app_assoc.
    cbn [app]. rewrite ?app_nil_r. reflexivity. }
  assert (HC : Cin (TA 1) (pow2 j) = (StA, (rep [S1;S1] j ++ [S1;S1;S0;S1;S1], S0, []))).
  { unfold Cin_0RB1LA_1LC1RD_1RD1LD_1RB0LA, TA_0RB1LA_1LC1RD_1RD1LD_1RB0LA, Uc_0RB1LA_1LC1RD_1RD1LD_1RB0LA. rewrite epow2_0RB1LA_1LC1RD_1RD1LD_1RB0LA.
    replace (1 + 0) with 1 by lia.
    cbn [rep app]. rewrite <- ?app_assoc. cbn [app]. rewrite ?app_nil_r.
    reflexivity. }
  rewrite HD, HC. rewrite ?lbl_0RB1LA_1LC1RD_1RD1LD_1RB0LA. rewrite ?lift_app_blank. reflexivity.
Qed.

(** The level-0 count's tail is [j + 1] units past the top's; the closing
    count starts at [xI (pow2 (S j))] over [BT]. *)
Lemma gcla_0RB1LA_1LC1RD_1RD1LD_1RB0LA : forall j, Dc 0 (j + 1) = cden [] [] (S j) CLA0_0RB1LA_1LC1RD_1RD1LD_1RB0LA.
Proof.
  intro j.
  unfold Dc_0RB1LA_1LC1RD_1RD1LD_1RB0LA, Cin_0RB1LA_1LC1RD_1RD1LD_1RB0LA, TB_0RB1LA_1LC1RD_1RD1LD_1RB0LA, Uc_0RB1LA_1LC1RD_1RD1LD_1RB0LA, cden, CLA0_0RB1LA_1LC1RD_1RD1LD_1RB0LA, sden;
    cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
  rewrite (epow2_0RB1LA_1LC1RD_1RD1LD_1RB0LA 0).
  replace (1 * S j + 0) with (j + 1 + 0) by lia.
  replace (0 * S j + 0) with 0 by lia.
  rewrite ?rep_add. cbn [pow2 rep app]. rewrite <- ?app_assoc.
  cbn [app]. rewrite ?app_nil_r. reflexivity.
Qed.

Lemma gclab_0RB1LA_1LC1RD_1RD1LD_1RB0LA : forall j,
  lift (cden [] [] (S j) CLA1_0RB1LA_1LC1RD_1RD1LD_1RB0LA) = lift (Cin BT (xI (pow2 (S j)))).
Proof.
  intro j.
  assert (HD : cden [] [] (S j) CLA1_0RB1LA_1LC1RD_1RD1LD_1RB0LA = (StA, ([S1;S0] ++ rep [S1;S1] (S j) ++ [S1;S1], S0, []))).
  { unfold cden, CLA1_0RB1LA_1LC1RD_1RD1LD_1RB0LA, sden;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * S j + 0) with (S j) by lia.
    replace (0 * S j + 0) with 0 by lia.
    rewrite ?rep_add. cbn [rep app]. rewrite <- ?app_assoc.
    cbn [app]. rewrite ?app_nil_r. reflexivity. }
  assert (HC : Cin BT (xI (pow2 (S j))) = (StA, ([S1;S0] ++ rep [S1;S1] (S j) ++ [S1;S1], S0, []))).
  { unfold Cin_0RB1LA_1LC1RD_1RD1LD_1RB0LA, BT_0RB1LA_1LC1RD_1RD1LD_1RB0LA. rewrite exi_0RB1LA_1LC1RD_1RD1LD_1RB0LA.
    cbn [rep app]. rewrite <- ?app_assoc. cbn [app]. rewrite ?app_nil_r.
    reflexivity. }
  rewrite HD, HC. rewrite ?lbl_0RB1LA_1LC1RD_1RD1LD_1RB0LA. rewrite ?lift_app_blank. reflexivity.
Qed.

Lemma gclb_0RB1LA_1LC1RD_1RD1LD_1RB0LA : forall j,
  Cin BT (fill (xI (pow2 (S j)))) = cden [] [] (S (S j)) CLB0_0RB1LA_1LC1RD_1RD1LD_1RB0LA.
Proof.
  intro j.
  unfold Cin_0RB1LA_1LC1RD_1RD1LD_1RB0LA, BT_0RB1LA_1LC1RD_1RD1LD_1RB0LA, cden, CLB0_0RB1LA_1LC1RD_1RD1LD_1RB0LA, sden;
    cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
  rewrite exif_0RB1LA_1LC1RD_1RD1LD_1RB0LA.
  replace (1 * S (S j) + 0) with (S (S j)) by lia.
  replace (0 * S (S j) + 0) with 0 by lia.
  rewrite ?rep_add. cbn [rep app]. rewrite <- ?app_assoc.
  cbn [app]. rewrite ?app_nil_r. reflexivity.
Qed.

(** The closing count lands one index up from [geo_]'s [B1] frame; both
    normalise to the same explicit successor word. *)
Lemma gclbx_0RB1LA_1LC1RD_1RD1LD_1RB0LA : forall j,
  lift (cden [] [] (S (S j)) CLB1_0RB1LA_1LC1RD_1RD1LD_1RB0LA) = lift (cden [] [] (S j) B1_0RB1LA_1LC1RD_1RD1LD_1RB0LA).
Proof.
  intro j.
  assert (HD : cden [] [] (S (S j)) CLB1_0RB1LA_1LC1RD_1RD1LD_1RB0LA = (StA, (rep [S1;S1] (S (S j)) ++ [S1;S0], S0, []))).
  { unfold cden, CLB1_0RB1LA_1LC1RD_1RD1LD_1RB0LA, sden;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * S (S j) + 0) with (S (S j)) by lia.
    replace (0 * S (S j) + 0) with 0 by lia.
    rewrite ?rep_add. cbn [rep app]. rewrite <- ?app_assoc.
    cbn [app]. rewrite ?app_nil_r. reflexivity. }
  assert (HE : cden [] [] (S j) B1_0RB1LA_1LC1RD_1RD1LD_1RB0LA = (StA, (rep [S1;S1] (S (S j)) ++ [S1;S0], S0, []))).
  { unfold cden, B1_0RB1LA_1LC1RD_1RD1LD_1RB0LA, sden;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * S j + 1) with (S (S j)) by lia.
    replace (0 * S j + 0) with 0 by lia.
    rewrite ?rep_add. cbn [rep app]. rewrite <- ?app_assoc.
    cbn [app]. rewrite ?app_nil_r. reflexivity. }
  rewrite HD, HE. rewrite ?lbl_0RB1LA_1LC1RD_1RD1LD_1RB0LA. rewrite ?lift_app_blank. reflexivity.
Qed.

(** ** The overflow branch, reindexed

    The top level sits ONE OCTAVE DOWN, so the generic route runs at
    [j = S j']: boot to A(j'), one A->B hop ([fill_hop] hides that count),
    [j'] level steps down, the closing count, out.  [j = 0] is a concrete
    lap -- the p = 1 overflow has no cascade at all. *)

Lemma gbor_0RB1LA_1LC1RD_1RD1LD_1RB0LA : forall p j, cview p = (S (S j), None) ->
  exists n c, 0 < n /\ csteps tm n (Cc p) = Some c /\ lift c = lift (Dc j 1).
Proof.
  intros p j Ev.
  assert (HAB : exists n, stepn tm n (lift (Cin (TA 1) (fill (pow2 j))))
                = Some (lift (Dc j 1))).
  { exists (4 * j + 4). unfold Dc_0RB1LA_1LC1RD_1RD1LD_1RB0LA.
    rewrite (gABs_0RB1LA_1LC1RD_1RD1LD_1RB0LA j 0), <- (gABd_0RB1LA_1LC1RD_1RD1LD_1RB0LA j 0).
    apply csteps_lift.
    exact (srun_sound tm false true chAB_0RB1LA_1LC1RD_1RD1LD_1RB0LA AB0_0RB1LA_1LC1RD_1RD1LD_1RB0LA AB1_0RB1LA_1LC1RD_1RD1LD_1RB0LA 4 4
             run_AB_0RB1LA_1LC1RD_1RD1LD_1RB0LA (XAB_0RB1LA_1LC1RD_1RD1LD_1RB0LA 0) [] j
             ltac:(discriminate) ltac:(reflexivity)). }
  destruct (fill_hop tm Cin lapin_0RB1LA_1LC1RD_1RD1LD_1RB0LA (TA 1) (pow2 j) _ HAB) as (n2 & H2).
  rewrite <- (gboa_0RB1LA_1LC1RD_1RD1LD_1RB0LA j) in H2.
  destruct (stepn_csteps_at tm n2 (cden [] [] j BB1_0RB1LA_1LC1RD_1RD1LD_1RB0LA) _ H2)
    as (cc & Hcc & Hl).
  exists (4 * j + 10 + n2), cc.
  split; [lia|]. split; [| exact Hl].
  rewrite csteps_add, (gso_0RB1LA_1LC1RD_1RD1LD_1RB0LA p j Ev).
  rewrite (srun_sound tm true true chb_0RB1LA_1LC1RD_1RD1LD_1RB0LA B0_0RB1LA_1LC1RD_1RD1LD_1RB0LA BB1_0RB1LA_1LC1RD_1RD1LD_1RB0LA 4 10
             run_boot_0RB1LA_1LC1RD_1RD1LD_1RB0LA [] [] j ltac:(reflexivity) ltac:(reflexivity)).
  exact Hcc.
Qed.

(** j = 0: the p = 1 overflow, concrete. *)
Lemma lapz_0RB1LA_1LC1RD_1RD1LD_1RB0LA : exists n c', csteps tm n (Cc 1) = Some c'
  /\ lift c' = lift (Cc 2) /\ 0 < n.
Proof.
  exists 19.
  assert (H : match csteps tm 19 (Cc 1) with
              | Some c => ceqb c (Cc 2) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 19 (Cc 1)) as [c|] eqn:E0; [|discriminate].
  exists c. split; [reflexivity|]. split; [apply ceqb_lift; exact H | lia].
Qed.

Lemma lapo_0RB1LA_1LC1RD_1RD1LD_1RB0LA : forall p j, cview p = (S j, None) ->
  exists n c', csteps tm n (Cc p) = Some c'
          /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intros p j Ev.
  destruct j as [|j'].
  - rewrite (cview_none_shape p 0 Ev). exact lapz_0RB1LA_1LC1RD_1RD1LD_1RB0LA.
  - apply (cascade_overflow tm Cc Dc hstep_0RB1LA_1LC1RD_1RD1LD_1RB0LA p j' 1).
    + exact (gbor_0RB1LA_1LC1RD_1RD1LD_1RB0LA p j' Ev).
    + assert (HB : exists n,
        stepn tm n (lift (Cin BT (fill (xI (pow2 (S j'))))))
        = Some (lift (Cc (Pos.succ p)))).
      { exists (4 * S (S j') + 4).
        rewrite (gclb_0RB1LA_1LC1RD_1RD1LD_1RB0LA j'), <- (geo_0RB1LA_1LC1RD_1RD1LD_1RB0LA p (S j') Ev), <- (gclbx_0RB1LA_1LC1RD_1RD1LD_1RB0LA j').
        apply csteps_lift.
        exact (srun_sound tm true true chCLB_0RB1LA_1LC1RD_1RD1LD_1RB0LA CLB0_0RB1LA_1LC1RD_1RD1LD_1RB0LA CLB1_0RB1LA_1LC1RD_1RD1LD_1RB0LA
                 4 4 run_closeB_0RB1LA_1LC1RD_1RD1LD_1RB0LA [] [] (S (S j'))
                 ltac:(reflexivity) ltac:(reflexivity)). }
      destruct (fill_hop tm Cin lapin_0RB1LA_1LC1RD_1RD1LD_1RB0LA BT (xI (pow2 (S j'))) _ HB)
        as (n2 & H2).
      exists (0 * S j' + 11 + n2).
      rewrite (gcla_0RB1LA_1LC1RD_1RD1LD_1RB0LA j'), stepn_add.
      rewrite (csteps_lift _ _ _ _
        (srun_sound tm true true chCLA_0RB1LA_1LC1RD_1RD1LD_1RB0LA CLA0_0RB1LA_1LC1RD_1RD1LD_1RB0LA CLA1_0RB1LA_1LC1RD_1RD1LD_1RB0LA 0 11
           run_closeA_0RB1LA_1LC1RD_1RD1LD_1RB0LA [] [] (S j')
           ltac:(reflexivity) ltac:(reflexivity))).
      rewrite (gclab_0RB1LA_1LC1RD_1RD1LD_1RB0LA j'). exact H2.
Qed.

(** ** The INTERIOR branch, at the outer anchor *)

Definition A0_0RB1LA_1LC1RD_1RD1LD_1RB0LA : sconf := mkC StA (mkS [] [S1;S0] 1 0 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition A1_0RB1LA_1LC1RD_1RD1LD_1RB0LA : sconf := mkC StA (mkS [] [S1;S1] 1 0 [S1;S0]) S0 (mkS [] [] 0 0 []).
Definition chi_0RB1LA_1LC1RD_1RD1LD_1RB0LA : list lstep := [SRotL 1; SWin 1; SCycL 2 0; SWin 2; SCycR 2; SWin 1; SUnrotL 1].

Lemma run_int_0RB1LA_1LC1RD_1RD1LD_1RB0LA : srun tm false true chi_0RB1LA_1LC1RD_1RD1LD_1RB0LA A0_0RB1LA_1LC1RD_1RD1LD_1RB0LA = Some (A1_0RB1LA_1LC1RD_1RD1LD_1RB0LA, 4, 4).
Proof. vm_compute. reflexivity. Qed.

Lemma gsi_0RB1LA_1LC1RD_1RD1LD_1RB0LA : forall p j q0, cview p = (j, Some q0) ->
  Cc p = cden (Jp q0 ++ [S0]) [] j A0_0RB1LA_1LC1RD_1RD1LD_1RB0LA.
Proof.
  intros p j q0 E. destruct (JpCounter.cview_some_J p j q0 E) as (H1 & _).
  unfold Cc_0RB1LA_1LC1RD_1RD1LD_1RB0LA, cden, A0_0RB1LA_1LC1RD_1RD1LD_1RB0LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  rewrite H1. first [ rewrite <- (app_assoc (rep [S1;S0] j)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma gei_0RB1LA_1LC1RD_1RD1LD_1RB0LA : forall p j q0, cview p = (j, Some q0) ->
  cden (Jp q0 ++ [S0]) [] j A1_0RB1LA_1LC1RD_1RD1LD_1RB0LA = Cc (Pos.succ p).
Proof.
  intros p j q0 E. destruct (JpCounter.cview_some_J p j q0 E) as (_ & H2).
  unfold Cc_0RB1LA_1LC1RD_1RD1LD_1RB0LA, cden, A1_0RB1LA_1LC1RD_1RD1LD_1RB0LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  rewrite H2. first [ rewrite <- (app_assoc (rep [S1;S1] j)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapi_0RB1LA_1LC1RD_1RD1LD_1RB0LA : forall p j q0, cview p = (j, Some q0) ->
  exists n, 0 < n /\ csteps tm n (Cc p) = Some (Cc (Pos.succ p)).
Proof.
  intros p j q0 E. exists (4 * j + 4). split; [lia|].
  rewrite (gsi_0RB1LA_1LC1RD_1RD1LD_1RB0LA p j q0 E).
  rewrite (srun_sound tm false true chi_0RB1LA_1LC1RD_1RD1LD_1RB0LA A0_0RB1LA_1LC1RD_1RD1LD_1RB0LA A1_0RB1LA_1LC1RD_1RD1LD_1RB0LA 4 4
             run_int_0RB1LA_1LC1RD_1RD1LD_1RB0LA (Jp q0 ++ [S0]) [] j
             ltac:(discriminate) ltac:(reflexivity)).
  f_equal. exact (gei_0RB1LA_1LC1RD_1RD1LD_1RB0LA p j q0 E).
Qed.

(** The interior closes exactly; the cascade's plumbing runs in [lift]
    space, so restate it there. *)
Lemma lapil_0RB1LA_1LC1RD_1RD1LD_1RB0LA : forall p j q0, cview p = (j, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof.
  intros p j q0 E. destruct (lapi_0RB1LA_1LC1RD_1RD1LD_1RB0LA p j q0 E) as (n & Hn & Hr).
  exists n, (Cc (Pos.succ p)). auto.
Qed.

(** ** The lap *)

Lemma lap_0RB1LA_1LC1RD_1RD1LD_1RB0LA : forall p, exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:E. destruct oq as [q0|].
  - destruct (lapi_0RB1LA_1LC1RD_1RD1LD_1RB0LA p j q0 E) as (n & Hn & Hrun).
    exists n, (Cc (Pos.succ p)).
    split; [exact Hrun | split; [reflexivity | exact Hn]].
  - destruct (cview_pos p j E) as (j' & ->).
    exact (lapo_0RB1LA_1LC1RD_1RD1LD_1RB0LA p j' E).
Qed.

(** ** Bootstrap *)

Lemma boot_0RB1LA_1LC1RD_1RD1LD_1RB0LA : exists t0, stepn tm t0 InitES = Some (lift (Cc 1)).
Proof.
  exists 5.
  assert (H : match csteps tm 5 c0 with
              | Some c => ceqb c (Cc 1) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 5 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** ** Visits

    Every state fires inside the BOOT chain, which runs at the REINDEXED
    anchor -- so the generic witness covers j = S j', and the p = 1 anchor
    (whose overflow has no cascade) gets concrete [visz_] witnesses. *)

Lemma viso_0RB1LA_1LC1RD_1RD1LD_1RB0LA : forall (l : list lstep) (q : St),
  srun_st tm true true l B0_0RB1LA_1LC1RD_1RD1LD_1RB0LA = Some q ->
  forall p j, cview p = (S (S j), None) ->
  exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros l q Hst p j E.
  apply (vis_of_run tm Cc true true l B0_0RB1LA_1LC1RD_1RD1LD_1RB0LA p j [] []);
    [exact Hst | reflexivity | reflexivity | exact (gso_0RB1LA_1LC1RD_1RD1LD_1RB0LA p j E)].
Qed.

(** State StA's visit witness at the reindex's p = 1 case -- concrete. *)
Lemma visz_StA_0RB1LA_1LC1RD_1RD1LD_1RB0LA : exists k c, csteps tm k (Cc 1) = Some c /\ fst c = StA.
Proof. exists 0. eexists. split; [vm_compute; reflexivity | reflexivity]. Qed.

(** State StB's visit witness at the reindex's p = 1 case -- concrete. *)
Lemma visz_StB_0RB1LA_1LC1RD_1RD1LD_1RB0LA : exists k c, csteps tm k (Cc 1) = Some c /\ fst c = StB.
Proof. exists 1. eexists. split; [vm_compute; reflexivity | reflexivity]. Qed.

(** State StC's visit witness at the reindex's p = 1 case -- concrete. *)
Lemma visz_StC_0RB1LA_1LC1RD_1RD1LD_1RB0LA : exists k c, csteps tm k (Cc 1) = Some c /\ fst c = StC.
Proof. exists 4. eexists. split; [vm_compute; reflexivity | reflexivity]. Qed.

(** State StD's visit witness at the reindex's p = 1 case -- concrete. *)
Lemma visz_StD_0RB1LA_1LC1RD_1RD1LD_1RB0LA : exists k c, csteps tm k (Cc 1) = Some c /\ fst c = StD.
Proof. exists 2. eexists. split; [vm_compute; reflexivity | reflexivity]. Qed.

Lemma vis_0RB1LA_1LC1RD_1RD1LD_1RB0LA : forall p q,
  exists k e, stepn tm k (lift (Cc p)) = Some e /\ fst e = q.
Proof.
  intros p q.
  destruct q.
  - (* StA *)
    apply (vis_via_ovf_lift tm Cc lapil_0RB1LA_1LC1RD_1RD1LD_1RB0LA StA).
    intros p1 j1 E1. destruct j1 as [|j1'].
    + rewrite (cview_none_shape p1 0 E1).
      apply (vis_lift_of_csteps tm Cc). exact visz_StA_0RB1LA_1LC1RD_1RD1LD_1RB0LA.
    + apply (vis_lift_of_csteps tm Cc).
      apply (viso_0RB1LA_1LC1RD_1RD1LD_1RB0LA [] StA ltac:(vm_compute; reflexivity)
                   p1 j1' E1).
  - (* StB *)
    apply (vis_via_ovf_lift tm Cc lapil_0RB1LA_1LC1RD_1RD1LD_1RB0LA StB).
    intros p1 j1 E1. destruct j1 as [|j1'].
    + rewrite (cview_none_shape p1 0 E1).
      apply (vis_lift_of_csteps tm Cc). exact visz_StB_0RB1LA_1LC1RD_1RD1LD_1RB0LA.
    + apply (vis_lift_of_csteps tm Cc).
      apply (viso_0RB1LA_1LC1RD_1RD1LD_1RB0LA [SWin 1] StB ltac:(vm_compute; reflexivity)
                   p1 j1' E1).
  - (* StC *)
    apply (vis_via_ovf_lift tm Cc lapil_0RB1LA_1LC1RD_1RD1LD_1RB0LA StC).
    intros p1 j1 E1. destruct j1 as [|j1'].
    + rewrite (cview_none_shape p1 0 E1).
      apply (vis_lift_of_csteps tm Cc). exact visz_StC_0RB1LA_1LC1RD_1RD1LD_1RB0LA.
    + apply (vis_lift_of_csteps tm Cc).
      apply (viso_0RB1LA_1LC1RD_1RD1LD_1RB0LA [SWin 2; SCycL 2 0; SWin 2; SWinL 2] StC ltac:(vm_compute; reflexivity)
                   p1 j1' E1).
  - (* StD *)
    apply (vis_via_ovf_lift tm Cc lapil_0RB1LA_1LC1RD_1RD1LD_1RB0LA StD).
    intros p1 j1 E1. destruct j1 as [|j1'].
    + rewrite (cview_none_shape p1 0 E1).
      apply (vis_lift_of_csteps tm Cc). exact visz_StD_0RB1LA_1LC1RD_1RD1LD_1RB0LA.
    + apply (vis_lift_of_csteps tm Cc).
      apply (viso_0RB1LA_1LC1RD_1RD1LD_1RB0LA [SWin 2] StD ltac:(vm_compute; reflexivity)
                   p1 j1' E1).
Qed.

(** The interior lap closes only up to [lift] (one trailing blank past the
    anchor's far side), so the closer is [LapCertGlueLift.glue_neverqh_lift]:
    [LapGlue.glue_neverqh] with the visit premise in [stepn] space, which is
    what its own proof consumes. *)
Theorem nqhm_0RB1LA_1LC1RD_1RD1LD_1RB0LA : NeverQuasiHaltsSt tm.
Proof. apply (glue_neverqh_lift tm Cc 1). - exact boot_0RB1LA_1LC1RD_1RD1LD_1RB0LA. - intros p _. apply lap_0RB1LA_1LC1RD_1RD1LD_1RB0LA. - intros p q _. apply vis_0RB1LA_1LC1RD_1RD1LD_1RB0LA. Qed.

Theorem nqh_0RB1LA_1LC1RD_1RD1LD_1RB0LA : NeverQuasiHaltsSt tm_0RB1LA_1LC1RD_1RD1LD_1RB0LA.
Proof. apply (mirror_never_qh tm_0RB1LA_1LC1RD_1RD1LD_1RB0LA). rewrite mirror_ok_0RB1LA_1LC1RD_1RD1LD_1RB0LA. exact nqhm_0RB1LA_1LC1RD_1RD1LD_1RB0LA. Qed.

Theorem nonhalt_0RB1LA_1LC1RD_1RD1LD_1RB0LA : NonHalt tm_0RB1LA_1LC1RD_1RD1LD_1RB0LA.
Proof. apply never_qh_nonhalt, nqh_0RB1LA_1LC1RD_1RD1LD_1RB0LA. Qed.
