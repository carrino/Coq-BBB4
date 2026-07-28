(** * CASB_1RB1LD_1LC1RD_0LA1RC_1LA0RC: machine 1RB1LD_1LC1RD_0LA1RC_1LA0RC, boarded by the CASCADE route (octave down).

    Auto-emitted by tools/counters/cascade_emit.py (UNTRUSTED emitter; the Coq
    kernel re-runs the checker on every line below).  Left-growth binary
    counter under the Jp digit alphabet, anchored at

      Cc p = (StC, (Jp p ++ [S0], S0, []))

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
    exact configurations: 192 interior anchors (interior); cascade (octave down): p=1 concrete + 7 overflow phases, j = 2..8 (35 levels, 70 counts, 1941 inner laps).
    Axiom footprint: [functional_extensionality_dep] (via [CTape.lift]). *)
From Coq Require Import Arith Lia Bool List PArith Wellfounded.
From BBB4 Require Import BBB4_Statement CTape Mirror.
From Coq Require Import FunctionalExtensionality.
From BBB4.Counters Require Import WTape MonoCounter JpCounter IXPGadgets
                                  LapCertGlue LapCertGlueLift NestedLap
                                  NestedLapLift NestedLapCascade.
From BBB4.Checkers Require Import LapDecider.
Import ListNotations.

Definition mk_1RB1LD_1LC1RD_0LA1RC_1LA0RC (w : Sym) (d : Dir) (n : St) : option Trans :=
  Some (mkTrans w d n).
Local Notation mk := mk_1RB1LD_1LC1RD_0LA1RC_1LA0RC.

(** 1RB1LD_1LC1RD_0LA1RC_1LA0RC -- the table every lemma below runs on. *)
Definition tm_1RB1LD_1LC1RD_0LA1RC_1LA0RC : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S1 DL StD
  | StB, S0 => mk S1 DL StC | StB, S1 => mk S1 DR StD
  | StC, S0 => mk S0 DL StA | StC, S1 => mk S1 DR StC
  | StD, S0 => mk S1 DL StA | StD, S1 => mk S0 DR StC end.
Local Notation tm := tm_1RB1LD_1LC1RD_0LA1RC_1LA0RC.

Definition Cc_1RB1LD_1LC1RD_0LA1RC_1LA0RC (p : positive) : cconf := (StC, (Jp p ++ [S0], S0, [])).
Local Notation Cc := Cc_1RB1LD_1LC1RD_0LA1RC_1LA0RC.

(** A chain accepted up to [lift] can stop a blank past the anchor -- the
    leniency [NestedLapLift] measured to be the binding one on this bucket --
    and [CTape.lift_side] cannot see it.  Every landing bridge below ends
    here, so it is stated before the first of them. *)
Lemma lbl_1RB1LD_1LC1RD_0LA1RC_1LA0RC : forall q l h r, lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.


(** ** The inner family, at an ARBITRARY tail

    [T] is the cascade's growing region.  The counter's own laps never read
    it, so quantifying over it costs nothing and buys every level. *)
Definition Cin_1RB1LD_1LC1RD_0LA1RC_1LA0RC (T : list Sym) (v : positive) : cconf :=
  (StC, (Jp v ++ T, S0, [])).
Local Notation Cin := Cin_1RB1LD_1LC1RD_0LA1RC_1LA0RC.

Definition Uc_1RB1LD_1LC1RD_0LA1RC_1LA0RC : list Sym := [S1;S1].
Local Notation Uc := Uc_1RB1LD_1LC1RD_0LA1RC_1LA0RC.

(** The two tails a level carries: the count that ENTERS it and the count the
    level's own transition produces.  One unit longer per level down. *)
Definition TB_1RB1LD_1LC1RD_0LA1RC_1LA0RC (m : nat) : list Sym := [S0;S0] ++ rep Uc (m + 0).
Definition TA_1RB1LD_1LC1RD_0LA1RC_1LA0RC (m : nat) : list Sym := [S1;S0] ++ rep Uc (m + 0).
Local Notation TB := TB_1RB1LD_1LC1RD_0LA1RC_1LA0RC.
Local Notation TA := TA_1RB1LD_1LC1RD_0LA1RC_1LA0RC.

(** The level-[l] entry configuration, with [m] units of tail beyond the
    top level's.  Both indices are explicit and both are built by [S]: a
    single index would force [j - l] into an anchor, which is the wave-15
    index-shift trap. *)
Definition Dc_1RB1LD_1LC1RD_0LA1RC_1LA0RC (l m : nat) : cconf := Cin (TB m) (pow2 l).
Local Notation Dc := Dc_1RB1LD_1LC1RD_0LA1RC_1LA0RC.

(** [E (2^n)] and [E (2^(n+1)-1)]: the value each count starts and ends at. *)
Lemma epow2_1RB1LD_1LC1RD_0LA1RC_1LA0RC : forall n, Jp (pow2 n) = rep [S1;S1] n ++ [S1].
Proof. induction n; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.

Lemma efill_1RB1LD_1LC1RD_0LA1RC_1LA0RC : forall n, Jp (fill (pow2 n)) = rep [S1;S0] n ++ [S1].
Proof.
  intro n.
  destruct (JpCounter.cview_none_J (fill (pow2 n)) n (cview_fill_pow2 n)) as (H & _).
  exact H.
Qed.

(** ** The inner family's own interior lap -- ordinary, affine, tail-blind *)

Definition AI0_1RB1LD_1LC1RD_0LA1RC_1LA0RC : sconf := mkC StC (mkS [] [S1;S0] 1 0 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition AI1_1RB1LD_1LC1RD_0LA1RC_1LA0RC : sconf := mkC StC (mkS [] [S1;S1] 1 0 [S1;S0]) S0 (mkS [] [] 0 0 []).
Definition chn_1RB1LD_1LC1RD_0LA1RC_1LA0RC : list lstep := [SRotL 1; SWin 1; SCycL 2 0; SWin 2; SCycR 2; SWin 1; SUnrotL 1].

Lemma run_inner_1RB1LD_1LC1RD_0LA1RC_1LA0RC :
  srun tm false true chn_1RB1LD_1LC1RD_0LA1RC_1LA0RC AI0_1RB1LD_1LC1RD_0LA1RC_1LA0RC = Some (AI1_1RB1LD_1LC1RD_0LA1RC_1LA0RC, 4, 4).
Proof. vm_compute. reflexivity. Qed.

Lemma gsn_1RB1LD_1LC1RD_0LA1RC_1LA0RC : forall T v i q0, cview v = (i, Some q0) ->
  Cin T v = cden (Jp q0 ++ T) [] i AI0_1RB1LD_1LC1RD_0LA1RC_1LA0RC.
Proof.
  intros T v i q0 Ev. destruct (JpCounter.cview_some_J v i q0 Ev) as (H1 & _).
  unfold Cin_1RB1LD_1LC1RD_0LA1RC_1LA0RC, cden, AI0_1RB1LD_1LC1RD_0LA1RC_1LA0RC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia. rewrite H1.
  cbn [rep app]. rewrite <- ?app_assoc. cbn [app]. rewrite ?app_nil_r.
  reflexivity.
Qed.

Lemma gen_1RB1LD_1LC1RD_0LA1RC_1LA0RC : forall T v i q0, cview v = (i, Some q0) ->
  lift (cden (Jp q0 ++ T) [] i AI1_1RB1LD_1LC1RD_0LA1RC_1LA0RC) = lift (Cin T (Pos.succ v)).
Proof.
  intros T v i q0 Ev. destruct (JpCounter.cview_some_J v i q0 Ev) as (_ & H2).
  unfold Cin_1RB1LD_1LC1RD_0LA1RC_1LA0RC, cden, AI1_1RB1LD_1LC1RD_0LA1RC_1LA0RC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia. replace (0 * i + 0) with 0 by lia.
  rewrite H2. cbn [rep app]. rewrite <- ?app_assoc. cbn [app].
  rewrite ?app_nil_r.
  rewrite ?lift_app_blank. reflexivity.
Qed.

(** The lap, up to [lift] and at every tail at once -- this is
    [NestedLapCascade]'s [Hin]. *)
Lemma lapin_1RB1LD_1LC1RD_0LA1RC_1LA0RC : forall T v i q0, cview v = (i, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cin T v) = Some c'
               /\ lift c' = lift (Cin T (Pos.succ v)).
Proof.
  intros T v i q0 Ev.
  exists (4 * i + 4), (cden (Jp q0 ++ T) [] i AI1_1RB1LD_1LC1RD_0LA1RC_1LA0RC).
  split; [lia|]. split; [| exact (gen_1RB1LD_1LC1RD_0LA1RC_1LA0RC T v i q0 Ev)].
  rewrite (gsn_1RB1LD_1LC1RD_0LA1RC_1LA0RC T v i q0 Ev).
  exact (srun_sound tm false true chn_1RB1LD_1LC1RD_0LA1RC_1LA0RC AI0_1RB1LD_1LC1RD_0LA1RC_1LA0RC AI1_1RB1LD_1LC1RD_0LA1RC_1LA0RC 4 4
           run_inner_1RB1LD_1LC1RD_0LA1RC_1LA0RC (Jp q0 ++ T) [] i
           ltac:(discriminate) ltac:(reflexivity)).
Qed.

(** ** The four chains *)

Definition B0_1RB1LD_1LC1RD_0LA1RC_1LA0RC : sconf := mkC StC (mkS [S1;S0] [S1;S0] 1 0 [S1;S0]) S0 (mkS [] [] 0 0 []).
Definition B1_1RB1LD_1LC1RD_0LA1RC_1LA0RC : sconf := mkC StC (mkS [] [S1;S1] 1 1 [S1;S0]) S0 (mkS [] [] 0 0 []).

(** *** boot: the outer overflow anchor -> the level-j count *)
Definition BB1_1RB1LD_1LC1RD_0LA1RC_1LA0RC : sconf := mkC StC (mkS [] [S1;S1] 1 0 [S1;S1;S0;S1;S1]) S0 (mkS [] [] 0 0 []).
Definition chb_1RB1LD_1LC1RD_0LA1RC_1LA0RC : list lstep := [SWin 2; SCycL 2 0; SWin 2; SWinL 4; SCycR 2; SWin 2; SUnrotL 2].

Lemma run_boot_1RB1LD_1LC1RD_0LA1RC_1LA0RC :
  srun tm true true chb_1RB1LD_1LC1RD_0LA1RC_1LA0RC B0_1RB1LD_1LC1RD_0LA1RC_1LA0RC = Some (BB1_1RB1LD_1LC1RD_0LA1RC_1LA0RC, 4, 10).
Proof. vm_compute. reflexivity. Qed.

(** *** B(S l) fill -> A(l) start.  Section 4c of the brief left this one
    open: its turnaround walks back out over cells it has just written and
    runs one short unless a whole unit is PEELED out of the count, and its eat
    reads one cell INTO the growing region -- that misread is what ends the
    eat -- so its opaque split sits one cell deeper than A->B's. *)
Definition BA0_1RB1LD_1LC1RD_0LA1RC_1LA0RC : sconf := mkC StC (mkS [] [S1;S0] 1 0 [S1;S0;S1;S0;S0]) S0 (mkS [] [] 0 0 []).
Definition BA1_1RB1LD_1LC1RD_0LA1RC_1LA0RC : sconf := mkC StC (mkS [] [S1;S1] 1 0 [S1;S1;S0;S1;S1]) S0 (mkS [] [] 0 0 []).
Definition chBA_1RB1LD_1LC1RD_0LA1RC_1LA0RC : list lstep := [SRotL 1; SWin 1; SCycL 2 0; SWin 8; SCycR 2; SWin 1; SUnrotL 1].

Lemma run_BA_1RB1LD_1LC1RD_0LA1RC_1LA0RC :
  srun tm false true chBA_1RB1LD_1LC1RD_0LA1RC_1LA0RC BA0_1RB1LD_1LC1RD_0LA1RC_1LA0RC = Some (BA1_1RB1LD_1LC1RD_0LA1RC_1LA0RC, 4, 10).
Proof. vm_compute. reflexivity. Qed.

(** *** A(l) fill -> B(l) start, the level's second half. *)
Definition AB0_1RB1LD_1LC1RD_0LA1RC_1LA0RC : sconf := mkC StC (mkS [] [S1;S0] 1 0 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition AB1_1RB1LD_1LC1RD_0LA1RC_1LA0RC : sconf := mkC StC (mkS [] [S1;S1] 1 0 [S1;S0]) S0 (mkS [] [] 0 0 []).
Definition chAB_1RB1LD_1LC1RD_0LA1RC_1LA0RC : list lstep := [SRotL 1; SWin 1; SCycL 2 0; SWin 2; SCycR 2; SWin 1; SUnrotL 1].

Lemma run_AB_1RB1LD_1LC1RD_0LA1RC_1LA0RC :
  srun tm false true chAB_1RB1LD_1LC1RD_0LA1RC_1LA0RC AB0_1RB1LD_1LC1RD_0LA1RC_1LA0RC = Some (AB1_1RB1LD_1LC1RD_0LA1RC_1LA0RC, 4, 4).
Proof. vm_compute. reflexivity. Qed.

(** *** the close, octave-down: after level 0 the machine runs ONE MORE
    ASCENDING COUNT at octave j+1 -- the same inner family over the constant
    tail [BT], its exponentially many laps living in [fill_hop] -- framed by
    two affine chains. *)
Definition BT_1RB1LD_1LC1RD_0LA1RC_1LA0RC : list Sym := [S1].
Local Notation BT := BT_1RB1LD_1LC1RD_0LA1RC_1LA0RC.

Definition CLA0_1RB1LD_1LC1RD_0LA1RC_1LA0RC : sconf := mkC StC (mkS [S1;S0;S0] [S1;S1] 1 0 []) S0 (mkS [] [] 0 0 []).
Definition CLA1_1RB1LD_1LC1RD_0LA1RC_1LA0RC : sconf := mkC StC (mkS [] [S1;S1] 1 1 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition chCLA_1RB1LD_1LC1RD_0LA1RC_1LA0RC : list lstep := [SWin 10; SWinR 1; SUnrotL 2; SFoldL 1].

Lemma run_closeA_1RB1LD_1LC1RD_0LA1RC_1LA0RC :
  srun tm true true chCLA_1RB1LD_1LC1RD_0LA1RC_1LA0RC CLA0_1RB1LD_1LC1RD_0LA1RC_1LA0RC = Some (CLA1_1RB1LD_1LC1RD_0LA1RC_1LA0RC, 0, 11).
Proof. vm_compute. reflexivity. Qed.

Definition CLB0_1RB1LD_1LC1RD_0LA1RC_1LA0RC : sconf := mkC StC (mkS [] [S1;S0] 1 0 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition CLB1_1RB1LD_1LC1RD_0LA1RC_1LA0RC : sconf := mkC StC (mkS [] [S1;S1] 1 0 [S1;S0]) S0 (mkS [] [] 0 0 []).
Definition chCLB_1RB1LD_1LC1RD_0LA1RC_1LA0RC : list lstep := [SRotL 1; SWin 1; SCycL 2 0; SWin 2; SCycR 2; SWin 1; SUnrotL 1].

Lemma run_closeB_1RB1LD_1LC1RD_0LA1RC_1LA0RC :
  srun tm true true chCLB_1RB1LD_1LC1RD_0LA1RC_1LA0RC CLB0_1RB1LD_1LC1RD_0LA1RC_1LA0RC = Some (CLB1_1RB1LD_1LC1RD_0LA1RC_1LA0RC, 4, 4).
Proof. vm_compute. reflexivity. Qed.

(** ** The per-level glue

    The opaque region each chain carries, as a function of the level's tail
    length.  Every exponent is built by [S] and [+]; none is a subtraction. *)
Definition XBA_1RB1LD_1LC1RD_0LA1RC_1LA0RC (m : nat) : list Sym := rep Uc m.
Definition XAB_1RB1LD_1LC1RD_0LA1RC_1LA0RC (m : nat) : list Sym := [S0] ++ rep Uc (1 + m).

Lemma gBAs_1RB1LD_1LC1RD_0LA1RC_1LA0RC : forall l m,
  Cin (TB m) (fill (pow2 (S l))) = cden (XBA_1RB1LD_1LC1RD_0LA1RC_1LA0RC m) [] l BA0_1RB1LD_1LC1RD_0LA1RC_1LA0RC.
Proof.
  intros l m.
  unfold Cin_1RB1LD_1LC1RD_0LA1RC_1LA0RC, TB_1RB1LD_1LC1RD_0LA1RC_1LA0RC, XBA_1RB1LD_1LC1RD_0LA1RC_1LA0RC, Uc_1RB1LD_1LC1RD_0LA1RC_1LA0RC, cden, BA0_1RB1LD_1LC1RD_0LA1RC_1LA0RC, sden;
    cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
  rewrite efill_1RB1LD_1LC1RD_0LA1RC_1LA0RC.
  replace (1 * l + 0) with l by lia.
  replace (0 * l + 0) with 0 by lia.
  replace (S l) with (l + 1) by lia.
  replace (m + 0) with (0 + m) by lia.
  rewrite ?rep_add. cbn [rep app]. rewrite <- ?app_assoc.
  cbn [app]. rewrite ?app_nil_r. reflexivity.
Qed.

Lemma gBAd_1RB1LD_1LC1RD_0LA1RC_1LA0RC : forall l m,
  lift (cden (XBA_1RB1LD_1LC1RD_0LA1RC_1LA0RC m) [] l BA1_1RB1LD_1LC1RD_0LA1RC_1LA0RC) = lift (Cin (TA (S m)) (pow2 l)).
Proof.
  intros l m.
  unfold Cin_1RB1LD_1LC1RD_0LA1RC_1LA0RC, TA_1RB1LD_1LC1RD_0LA1RC_1LA0RC, XBA_1RB1LD_1LC1RD_0LA1RC_1LA0RC, Uc_1RB1LD_1LC1RD_0LA1RC_1LA0RC, cden, BA1_1RB1LD_1LC1RD_0LA1RC_1LA0RC, sden;
    cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
  rewrite epow2_1RB1LD_1LC1RD_0LA1RC_1LA0RC.
  replace (1 * l + 0) with l by lia.
  replace (0 * l + 0) with 0 by lia.
  replace (S m + 0) with (1 + m) by lia.
  rewrite ?rep_add. cbn [rep app]. rewrite <- ?app_assoc.
  cbn [app]. rewrite ?app_nil_r.
  rewrite ?lift_app_blank. reflexivity.
Qed.

Lemma gABs_1RB1LD_1LC1RD_0LA1RC_1LA0RC : forall l m,
  Cin (TA (S m)) (fill (pow2 l)) = cden (XAB_1RB1LD_1LC1RD_0LA1RC_1LA0RC m) [] l AB0_1RB1LD_1LC1RD_0LA1RC_1LA0RC.
Proof.
  intros l m.
  unfold Cin_1RB1LD_1LC1RD_0LA1RC_1LA0RC, TA_1RB1LD_1LC1RD_0LA1RC_1LA0RC, XAB_1RB1LD_1LC1RD_0LA1RC_1LA0RC, Uc_1RB1LD_1LC1RD_0LA1RC_1LA0RC, cden, AB0_1RB1LD_1LC1RD_0LA1RC_1LA0RC, sden;
    cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
  rewrite efill_1RB1LD_1LC1RD_0LA1RC_1LA0RC.
  replace (1 * l + 0) with l by lia.
  replace (0 * l + 0) with 0 by lia.
  replace (S m + 0) with (1 + m) by lia.
  rewrite ?rep_add. cbn [rep app]. rewrite <- ?app_assoc.
  cbn [app]. rewrite ?app_nil_r. reflexivity.
Qed.

Lemma gABd_1RB1LD_1LC1RD_0LA1RC_1LA0RC : forall l m,
  lift (cden (XAB_1RB1LD_1LC1RD_0LA1RC_1LA0RC m) [] l AB1_1RB1LD_1LC1RD_0LA1RC_1LA0RC) = lift (Cin (TB (S m)) (pow2 l)).
Proof.
  intros l m.
  unfold Cin_1RB1LD_1LC1RD_0LA1RC_1LA0RC, TB_1RB1LD_1LC1RD_0LA1RC_1LA0RC, XAB_1RB1LD_1LC1RD_0LA1RC_1LA0RC, Uc_1RB1LD_1LC1RD_0LA1RC_1LA0RC, cden, AB1_1RB1LD_1LC1RD_0LA1RC_1LA0RC, sden;
    cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
  rewrite epow2_1RB1LD_1LC1RD_0LA1RC_1LA0RC.
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
Lemma hstep_1RB1LD_1LC1RD_0LA1RC_1LA0RC : forall l m,
  exists n, stepn tm n (lift (Dc (S l) m)) = Some (lift (Dc l (S m))).
Proof.
  intros l m. unfold Dc_1RB1LD_1LC1RD_0LA1RC_1LA0RC.
  apply (level_hop tm Cin lapin_1RB1LD_1LC1RD_0LA1RC_1LA0RC (TB m) (TA (S m))
                   (pow2 (S l)) (pow2 l)).
  - exists (4 * l + 10). rewrite gBAs_1RB1LD_1LC1RD_0LA1RC_1LA0RC, <- gBAd_1RB1LD_1LC1RD_0LA1RC_1LA0RC.
    apply csteps_lift.
    exact (srun_sound tm false true chBA_1RB1LD_1LC1RD_0LA1RC_1LA0RC BA0_1RB1LD_1LC1RD_0LA1RC_1LA0RC BA1_1RB1LD_1LC1RD_0LA1RC_1LA0RC 4 10
             run_BA_1RB1LD_1LC1RD_0LA1RC_1LA0RC (XBA_1RB1LD_1LC1RD_0LA1RC_1LA0RC m) [] l
             ltac:(discriminate) ltac:(reflexivity)).
  - exists (4 * l + 4). rewrite gABs_1RB1LD_1LC1RD_0LA1RC_1LA0RC, <- gABd_1RB1LD_1LC1RD_0LA1RC_1LA0RC.
    apply csteps_lift.
    exact (srun_sound tm false true chAB_1RB1LD_1LC1RD_0LA1RC_1LA0RC AB0_1RB1LD_1LC1RD_0LA1RC_1LA0RC AB1_1RB1LD_1LC1RD_0LA1RC_1LA0RC 4 4
             run_AB_1RB1LD_1LC1RD_0LA1RC_1LA0RC (XAB_1RB1LD_1LC1RD_0LA1RC_1LA0RC m) [] l
             ltac:(discriminate) ltac:(reflexivity)).
Qed.

(** ** The outer glue: boot in, sweep out *)

Lemma gso_1RB1LD_1LC1RD_0LA1RC_1LA0RC : forall p j, cview p = (S (S j), None) ->
  Cc p = cden [] [] j B0_1RB1LD_1LC1RD_0LA1RC_1LA0RC.
Proof.
  intros p j Ev. destruct (JpCounter.cview_none_J p (S j) Ev) as (H1 & _).
  unfold Cc_1RB1LD_1LC1RD_0LA1RC_1LA0RC, cden, B0_1RB1LD_1LC1RD_0LA1RC_1LA0RC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with (j) by lia.
  rewrite H1; cbn [rep app]. rewrite <- ?app_assoc. cbn [app].
  rewrite ?app_nil_r. reflexivity.
Qed.

Lemma geo_1RB1LD_1LC1RD_0LA1RC_1LA0RC : forall p j, cview p = (S j, None) ->
  lift (cden [] [] j B1_1RB1LD_1LC1RD_0LA1RC_1LA0RC) = lift (Cc (Pos.succ p)).
Proof.
  intros p j Ev. destruct (JpCounter.cview_none_J p j Ev) as (_ & H2).
  unfold Cc_1RB1LD_1LC1RD_0LA1RC_1LA0RC, cden, B1_1RB1LD_1LC1RD_0LA1RC_1LA0RC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 1) with (S j) by lia. replace (0 * j + 0) with 0 by lia.
  rewrite H2. cbn [rep app]. rewrite <- ?app_assoc. cbn [app].
  rewrite ?app_nil_r. rewrite ?lift_app_blank. reflexivity.
Qed.

(** The boot chain lands on the TOP level's FIRST count -- A at one level
    BELOW the outer index, tail one unit past the top's -- up to 0/0
    trailing blanks. *)
Lemma gboa_1RB1LD_1LC1RD_0LA1RC_1LA0RC : forall j, lift (cden [] [] j BB1_1RB1LD_1LC1RD_0LA1RC_1LA0RC) = lift (Cin (TA 1) (pow2 j)).
Proof.
  intro j.
  assert (HD : cden [] [] j BB1_1RB1LD_1LC1RD_0LA1RC_1LA0RC = (StC, (rep [S1;S1] j ++ [S1;S1;S0;S1;S1], S0, []))).
  { unfold cden, BB1_1RB1LD_1LC1RD_0LA1RC_1LA0RC, sden;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  replace (0 * j + 0) with 0 by lia.
    rewrite ?rep_add. cbn [rep app]. rewrite <- ?app_assoc.
    cbn [app]. rewrite ?app_nil_r. reflexivity. }
  assert (HC : Cin (TA 1) (pow2 j) = (StC, (rep [S1;S1] j ++ [S1;S1;S0;S1;S1], S0, []))).
  { unfold Cin_1RB1LD_1LC1RD_0LA1RC_1LA0RC, TA_1RB1LD_1LC1RD_0LA1RC_1LA0RC, Uc_1RB1LD_1LC1RD_0LA1RC_1LA0RC. rewrite epow2_1RB1LD_1LC1RD_0LA1RC_1LA0RC.
    replace (1 + 0) with 1 by lia.
    cbn [rep app]. rewrite <- ?app_assoc. cbn [app]. rewrite ?app_nil_r.
    reflexivity. }
  rewrite HD, HC. rewrite ?lbl_1RB1LD_1LC1RD_0LA1RC_1LA0RC. rewrite ?lift_app_blank. reflexivity.
Qed.

(** The level-0 count's tail is [j + 1] units past the top's; the closing
    count starts at [pow2 (S (S j))] over [BT]. *)
Lemma gcla_1RB1LD_1LC1RD_0LA1RC_1LA0RC : forall j, Dc 0 (j + 1) = cden [] [] (S j) CLA0_1RB1LD_1LC1RD_0LA1RC_1LA0RC.
Proof.
  intro j.
  unfold Dc_1RB1LD_1LC1RD_0LA1RC_1LA0RC, Cin_1RB1LD_1LC1RD_0LA1RC_1LA0RC, TB_1RB1LD_1LC1RD_0LA1RC_1LA0RC, Uc_1RB1LD_1LC1RD_0LA1RC_1LA0RC, cden, CLA0_1RB1LD_1LC1RD_0LA1RC_1LA0RC, sden;
    cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
  rewrite (epow2_1RB1LD_1LC1RD_0LA1RC_1LA0RC 0).
  replace (1 * S j + 0) with (j + 1 + 0) by lia.
  replace (0 * S j + 0) with 0 by lia.
  rewrite ?rep_add. cbn [pow2 rep app]. rewrite <- ?app_assoc.
  cbn [app]. rewrite ?app_nil_r. reflexivity.
Qed.

Lemma gclab_1RB1LD_1LC1RD_0LA1RC_1LA0RC : forall j,
  lift (cden [] [] (S j) CLA1_1RB1LD_1LC1RD_0LA1RC_1LA0RC) = lift (Cin BT (pow2 (S (S j)))).
Proof.
  intro j.
  assert (HD : cden [] [] (S j) CLA1_1RB1LD_1LC1RD_0LA1RC_1LA0RC = (StC, (rep [S1;S1] (S (S j)) ++ [S1;S1], S0, []))).
  { unfold cden, CLA1_1RB1LD_1LC1RD_0LA1RC_1LA0RC, sden;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * S j + 1) with (S (S j)) by lia.
    replace (0 * S j + 0) with 0 by lia.
    rewrite ?rep_add. cbn [rep app]. rewrite <- ?app_assoc.
    cbn [app]. rewrite ?app_nil_r. reflexivity. }
  assert (HC : Cin BT (pow2 (S (S j))) = (StC, (rep [S1;S1] (S (S j)) ++ [S1;S1], S0, []))).
  { unfold Cin_1RB1LD_1LC1RD_0LA1RC_1LA0RC, BT_1RB1LD_1LC1RD_0LA1RC_1LA0RC. rewrite epow2_1RB1LD_1LC1RD_0LA1RC_1LA0RC.
    cbn [rep app]. rewrite <- ?app_assoc. cbn [app]. rewrite ?app_nil_r.
    reflexivity. }
  rewrite HD, HC. rewrite ?lbl_1RB1LD_1LC1RD_0LA1RC_1LA0RC. rewrite ?lift_app_blank. reflexivity.
Qed.

Lemma gclb_1RB1LD_1LC1RD_0LA1RC_1LA0RC : forall j,
  Cin BT (fill (pow2 (S (S j)))) = cden [] [] (S (S j)) CLB0_1RB1LD_1LC1RD_0LA1RC_1LA0RC.
Proof.
  intro j.
  unfold Cin_1RB1LD_1LC1RD_0LA1RC_1LA0RC, BT_1RB1LD_1LC1RD_0LA1RC_1LA0RC, cden, CLB0_1RB1LD_1LC1RD_0LA1RC_1LA0RC, sden;
    cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
  rewrite efill_1RB1LD_1LC1RD_0LA1RC_1LA0RC.
  replace (1 * S (S j) + 0) with (S (S j)) by lia.
  replace (0 * S (S j) + 0) with 0 by lia.
  rewrite ?rep_add. cbn [rep app]. rewrite <- ?app_assoc.
  cbn [app]. rewrite ?app_nil_r. reflexivity.
Qed.

(** The closing count lands one index up from [geo_]'s [B1] frame; both
    normalise to the same explicit successor word. *)
Lemma gclbx_1RB1LD_1LC1RD_0LA1RC_1LA0RC : forall j,
  lift (cden [] [] (S (S j)) CLB1_1RB1LD_1LC1RD_0LA1RC_1LA0RC) = lift (cden [] [] (S j) B1_1RB1LD_1LC1RD_0LA1RC_1LA0RC).
Proof.
  intro j.
  assert (HD : cden [] [] (S (S j)) CLB1_1RB1LD_1LC1RD_0LA1RC_1LA0RC = (StC, (rep [S1;S1] (S (S j)) ++ [S1;S0], S0, []))).
  { unfold cden, CLB1_1RB1LD_1LC1RD_0LA1RC_1LA0RC, sden;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * S (S j) + 0) with (S (S j)) by lia.
    replace (0 * S (S j) + 0) with 0 by lia.
    rewrite ?rep_add. cbn [rep app]. rewrite <- ?app_assoc.
    cbn [app]. rewrite ?app_nil_r. reflexivity. }
  assert (HE : cden [] [] (S j) B1_1RB1LD_1LC1RD_0LA1RC_1LA0RC = (StC, (rep [S1;S1] (S (S j)) ++ [S1;S0], S0, []))).
  { unfold cden, B1_1RB1LD_1LC1RD_0LA1RC_1LA0RC, sden;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * S j + 1) with (S (S j)) by lia.
    replace (0 * S j + 0) with 0 by lia.
    rewrite ?rep_add. cbn [rep app]. rewrite <- ?app_assoc.
    cbn [app]. rewrite ?app_nil_r. reflexivity. }
  rewrite HD, HE. rewrite ?lbl_1RB1LD_1LC1RD_0LA1RC_1LA0RC. rewrite ?lift_app_blank. reflexivity.
Qed.

(** ** The overflow branch, reindexed

    The top level sits ONE OCTAVE DOWN, so the generic route runs at
    [j = S j']: boot to A(j'), one A->B hop ([fill_hop] hides that count),
    [j'] level steps down, the closing count, out.  [j = 0] is a concrete
    lap -- the p = 1 overflow has no cascade at all. *)

Lemma gbor_1RB1LD_1LC1RD_0LA1RC_1LA0RC : forall p j, cview p = (S (S j), None) ->
  exists n c, 0 < n /\ csteps tm n (Cc p) = Some c /\ lift c = lift (Dc j 1).
Proof.
  intros p j Ev.
  assert (HAB : exists n, stepn tm n (lift (Cin (TA 1) (fill (pow2 j))))
                = Some (lift (Dc j 1))).
  { exists (4 * j + 4). unfold Dc_1RB1LD_1LC1RD_0LA1RC_1LA0RC.
    rewrite (gABs_1RB1LD_1LC1RD_0LA1RC_1LA0RC j 0), <- (gABd_1RB1LD_1LC1RD_0LA1RC_1LA0RC j 0).
    apply csteps_lift.
    exact (srun_sound tm false true chAB_1RB1LD_1LC1RD_0LA1RC_1LA0RC AB0_1RB1LD_1LC1RD_0LA1RC_1LA0RC AB1_1RB1LD_1LC1RD_0LA1RC_1LA0RC 4 4
             run_AB_1RB1LD_1LC1RD_0LA1RC_1LA0RC (XAB_1RB1LD_1LC1RD_0LA1RC_1LA0RC 0) [] j
             ltac:(discriminate) ltac:(reflexivity)). }
  destruct (fill_hop tm Cin lapin_1RB1LD_1LC1RD_0LA1RC_1LA0RC (TA 1) (pow2 j) _ HAB) as (n2 & H2).
  rewrite <- (gboa_1RB1LD_1LC1RD_0LA1RC_1LA0RC j) in H2.
  destruct (stepn_csteps_at tm n2 (cden [] [] j BB1_1RB1LD_1LC1RD_0LA1RC_1LA0RC) _ H2)
    as (cc & Hcc & Hl).
  exists (4 * j + 10 + n2), cc.
  split; [lia|]. split; [| exact Hl].
  rewrite csteps_add, (gso_1RB1LD_1LC1RD_0LA1RC_1LA0RC p j Ev).
  rewrite (srun_sound tm true true chb_1RB1LD_1LC1RD_0LA1RC_1LA0RC B0_1RB1LD_1LC1RD_0LA1RC_1LA0RC BB1_1RB1LD_1LC1RD_0LA1RC_1LA0RC 4 10
             run_boot_1RB1LD_1LC1RD_0LA1RC_1LA0RC [] [] j ltac:(reflexivity) ltac:(reflexivity)).
  exact Hcc.
Qed.

(** j = 0: the p = 1 overflow, concrete. *)
Lemma lapz_1RB1LD_1LC1RD_0LA1RC_1LA0RC : exists n c', csteps tm n (Cc 1) = Some c'
  /\ lift c' = lift (Cc 2) /\ 0 < n.
Proof.
  exists 23.
  assert (H : match csteps tm 23 (Cc 1) with
              | Some c => ceqb c (Cc 2) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 23 (Cc 1)) as [c|] eqn:E0; [|discriminate].
  exists c. split; [reflexivity|]. split; [apply ceqb_lift; exact H | lia].
Qed.

Lemma lapo_1RB1LD_1LC1RD_0LA1RC_1LA0RC : forall p j, cview p = (S j, None) ->
  exists n c', csteps tm n (Cc p) = Some c'
          /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intros p j Ev.
  destruct j as [|j'].
  - rewrite (cview_none_shape p 0 Ev). exact lapz_1RB1LD_1LC1RD_0LA1RC_1LA0RC.
  - apply (cascade_overflow tm Cc Dc hstep_1RB1LD_1LC1RD_0LA1RC_1LA0RC p j' 1).
    + exact (gbor_1RB1LD_1LC1RD_0LA1RC_1LA0RC p j' Ev).
    + assert (HB : exists n,
        stepn tm n (lift (Cin BT (fill (pow2 (S (S j'))))))
        = Some (lift (Cc (Pos.succ p)))).
      { exists (4 * S (S j') + 4).
        rewrite (gclb_1RB1LD_1LC1RD_0LA1RC_1LA0RC j'), <- (geo_1RB1LD_1LC1RD_0LA1RC_1LA0RC p (S j') Ev), <- (gclbx_1RB1LD_1LC1RD_0LA1RC_1LA0RC j').
        apply csteps_lift.
        exact (srun_sound tm true true chCLB_1RB1LD_1LC1RD_0LA1RC_1LA0RC CLB0_1RB1LD_1LC1RD_0LA1RC_1LA0RC CLB1_1RB1LD_1LC1RD_0LA1RC_1LA0RC
                 4 4 run_closeB_1RB1LD_1LC1RD_0LA1RC_1LA0RC [] [] (S (S j'))
                 ltac:(reflexivity) ltac:(reflexivity)). }
      destruct (fill_hop tm Cin lapin_1RB1LD_1LC1RD_0LA1RC_1LA0RC BT (pow2 (S (S j'))) _ HB)
        as (n2 & H2).
      exists (0 * S j' + 11 + n2).
      rewrite (gcla_1RB1LD_1LC1RD_0LA1RC_1LA0RC j'), stepn_add.
      rewrite (csteps_lift _ _ _ _
        (srun_sound tm true true chCLA_1RB1LD_1LC1RD_0LA1RC_1LA0RC CLA0_1RB1LD_1LC1RD_0LA1RC_1LA0RC CLA1_1RB1LD_1LC1RD_0LA1RC_1LA0RC 0 11
           run_closeA_1RB1LD_1LC1RD_0LA1RC_1LA0RC [] [] (S j')
           ltac:(reflexivity) ltac:(reflexivity))).
      rewrite (gclab_1RB1LD_1LC1RD_0LA1RC_1LA0RC j'). exact H2.
Qed.

(** ** The INTERIOR branch, at the outer anchor *)

Definition A0_1RB1LD_1LC1RD_0LA1RC_1LA0RC : sconf := mkC StC (mkS [] [S1;S0] 1 0 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition A1_1RB1LD_1LC1RD_0LA1RC_1LA0RC : sconf := mkC StC (mkS [] [S1;S1] 1 0 [S1;S0]) S0 (mkS [] [] 0 0 []).
Definition chi_1RB1LD_1LC1RD_0LA1RC_1LA0RC : list lstep := [SRotL 1; SWin 1; SCycL 2 0; SWin 2; SCycR 2; SWin 1; SUnrotL 1].

Lemma run_int_1RB1LD_1LC1RD_0LA1RC_1LA0RC : srun tm false true chi_1RB1LD_1LC1RD_0LA1RC_1LA0RC A0_1RB1LD_1LC1RD_0LA1RC_1LA0RC = Some (A1_1RB1LD_1LC1RD_0LA1RC_1LA0RC, 4, 4).
Proof. vm_compute. reflexivity. Qed.

Lemma gsi_1RB1LD_1LC1RD_0LA1RC_1LA0RC : forall p j q0, cview p = (j, Some q0) ->
  Cc p = cden (Jp q0 ++ [S0]) [] j A0_1RB1LD_1LC1RD_0LA1RC_1LA0RC.
Proof.
  intros p j q0 E. destruct (JpCounter.cview_some_J p j q0 E) as (H1 & _).
  unfold Cc_1RB1LD_1LC1RD_0LA1RC_1LA0RC, cden, A0_1RB1LD_1LC1RD_0LA1RC_1LA0RC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  rewrite H1. first [ rewrite <- (app_assoc (rep [S1;S0] j)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma gei_1RB1LD_1LC1RD_0LA1RC_1LA0RC : forall p j q0, cview p = (j, Some q0) ->
  cden (Jp q0 ++ [S0]) [] j A1_1RB1LD_1LC1RD_0LA1RC_1LA0RC = Cc (Pos.succ p).
Proof.
  intros p j q0 E. destruct (JpCounter.cview_some_J p j q0 E) as (_ & H2).
  unfold Cc_1RB1LD_1LC1RD_0LA1RC_1LA0RC, cden, A1_1RB1LD_1LC1RD_0LA1RC_1LA0RC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  rewrite H2. first [ rewrite <- (app_assoc (rep [S1;S1] j)); reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapi_1RB1LD_1LC1RD_0LA1RC_1LA0RC : forall p j q0, cview p = (j, Some q0) ->
  exists n, 0 < n /\ csteps tm n (Cc p) = Some (Cc (Pos.succ p)).
Proof.
  intros p j q0 E. exists (4 * j + 4). split; [lia|].
  rewrite (gsi_1RB1LD_1LC1RD_0LA1RC_1LA0RC p j q0 E).
  rewrite (srun_sound tm false true chi_1RB1LD_1LC1RD_0LA1RC_1LA0RC A0_1RB1LD_1LC1RD_0LA1RC_1LA0RC A1_1RB1LD_1LC1RD_0LA1RC_1LA0RC 4 4
             run_int_1RB1LD_1LC1RD_0LA1RC_1LA0RC (Jp q0 ++ [S0]) [] j
             ltac:(discriminate) ltac:(reflexivity)).
  f_equal. exact (gei_1RB1LD_1LC1RD_0LA1RC_1LA0RC p j q0 E).
Qed.

(** The interior closes exactly; the cascade's plumbing runs in [lift]
    space, so restate it there. *)
Lemma lapil_1RB1LD_1LC1RD_0LA1RC_1LA0RC : forall p j q0, cview p = (j, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof.
  intros p j q0 E. destruct (lapi_1RB1LD_1LC1RD_0LA1RC_1LA0RC p j q0 E) as (n & Hn & Hr).
  exists n, (Cc (Pos.succ p)). auto.
Qed.

(** ** The lap *)

Lemma lap_1RB1LD_1LC1RD_0LA1RC_1LA0RC : forall p, exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:E. destruct oq as [q0|].
  - destruct (lapi_1RB1LD_1LC1RD_0LA1RC_1LA0RC p j q0 E) as (n & Hn & Hrun).
    exists n, (Cc (Pos.succ p)).
    split; [exact Hrun | split; [reflexivity | exact Hn]].
  - destruct (cview_pos p j E) as (j' & ->).
    exact (lapo_1RB1LD_1LC1RD_0LA1RC_1LA0RC p j' E).
Qed.

(** ** Bootstrap *)

Lemma boot_1RB1LD_1LC1RD_0LA1RC_1LA0RC : exists t0, stepn tm t0 InitES = Some (lift (Cc 1)).
Proof.
  exists 8.
  assert (H : match csteps tm 8 c0 with
              | Some c => ceqb c (Cc 1) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 8 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** ** Visits

    Every state fires inside the BOOT chain, which runs at the REINDEXED
    anchor -- so the generic witness covers j = S j', and the p = 1 anchor
    (whose overflow has no cascade) gets concrete [visz_] witnesses. *)

Lemma viso_1RB1LD_1LC1RD_0LA1RC_1LA0RC : forall (l : list lstep) (q : St),
  srun_st tm true true l B0_1RB1LD_1LC1RD_0LA1RC_1LA0RC = Some q ->
  forall p j, cview p = (S (S j), None) ->
  exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros l q Hst p j E.
  apply (vis_of_run tm Cc true true l B0_1RB1LD_1LC1RD_0LA1RC_1LA0RC p j [] []);
    [exact Hst | reflexivity | reflexivity | exact (gso_1RB1LD_1LC1RD_0LA1RC_1LA0RC p j E)].
Qed.

(** State StA's visit witness at the reindex's p = 1 case -- concrete. *)
Lemma visz_StA_1RB1LD_1LC1RD_0LA1RC_1LA0RC : exists k c, csteps tm k (Cc 1) = Some c /\ fst c = StA.
Proof. exists 1. eexists. split; [vm_compute; reflexivity | reflexivity]. Qed.

(** State StB's visit witness at the reindex's p = 1 case -- concrete. *)
Lemma visz_StB_1RB1LD_1LC1RD_0LA1RC_1LA0RC : exists k c, csteps tm k (Cc 1) = Some c /\ fst c = StB.
Proof. exists 4. eexists. split; [vm_compute; reflexivity | reflexivity]. Qed.

(** State StC's visit witness at the reindex's p = 1 case -- concrete. *)
Lemma visz_StC_1RB1LD_1LC1RD_0LA1RC_1LA0RC : exists k c, csteps tm k (Cc 1) = Some c /\ fst c = StC.
Proof. exists 0. eexists. split; [vm_compute; reflexivity | reflexivity]. Qed.

(** State StD's visit witness at the reindex's p = 1 case -- concrete. *)
Lemma visz_StD_1RB1LD_1LC1RD_0LA1RC_1LA0RC : exists k c, csteps tm k (Cc 1) = Some c /\ fst c = StD.
Proof. exists 2. eexists. split; [vm_compute; reflexivity | reflexivity]. Qed.

Lemma vis_1RB1LD_1LC1RD_0LA1RC_1LA0RC : forall p q,
  exists k e, stepn tm k (lift (Cc p)) = Some e /\ fst e = q.
Proof.
  intros p q.
  destruct q.
  - (* StA *)
    apply (vis_via_ovf_lift tm Cc lapil_1RB1LD_1LC1RD_0LA1RC_1LA0RC StA).
    intros p1 j1 E1. destruct j1 as [|j1'].
    + rewrite (cview_none_shape p1 0 E1).
      apply (vis_lift_of_csteps tm Cc). exact visz_StA_1RB1LD_1LC1RD_0LA1RC_1LA0RC.
    + apply (vis_lift_of_csteps tm Cc).
      apply (viso_1RB1LD_1LC1RD_0LA1RC_1LA0RC [SWin 1] StA ltac:(vm_compute; reflexivity)
                   p1 j1' E1).
  - (* StB *)
    apply (vis_via_ovf_lift tm Cc lapil_1RB1LD_1LC1RD_0LA1RC_1LA0RC StB).
    intros p1 j1 E1. destruct j1 as [|j1'].
    + rewrite (cview_none_shape p1 0 E1).
      apply (vis_lift_of_csteps tm Cc). exact visz_StB_1RB1LD_1LC1RD_0LA1RC_1LA0RC.
    + apply (vis_lift_of_csteps tm Cc).
      apply (viso_1RB1LD_1LC1RD_0LA1RC_1LA0RC [SWin 2; SCycL 2 0; SWin 2; SWinL 2] StB ltac:(vm_compute; reflexivity)
                   p1 j1' E1).
  - (* StC *)
    apply (vis_via_ovf_lift tm Cc lapil_1RB1LD_1LC1RD_0LA1RC_1LA0RC StC).
    intros p1 j1 E1. destruct j1 as [|j1'].
    + rewrite (cview_none_shape p1 0 E1).
      apply (vis_lift_of_csteps tm Cc). exact visz_StC_1RB1LD_1LC1RD_0LA1RC_1LA0RC.
    + apply (vis_lift_of_csteps tm Cc).
      apply (viso_1RB1LD_1LC1RD_0LA1RC_1LA0RC [] StC ltac:(vm_compute; reflexivity)
                   p1 j1' E1).
  - (* StD *)
    apply (vis_via_ovf_lift tm Cc lapil_1RB1LD_1LC1RD_0LA1RC_1LA0RC StD).
    intros p1 j1 E1. destruct j1 as [|j1'].
    + rewrite (cview_none_shape p1 0 E1).
      apply (vis_lift_of_csteps tm Cc). exact visz_StD_1RB1LD_1LC1RD_0LA1RC_1LA0RC.
    + apply (vis_lift_of_csteps tm Cc).
      apply (viso_1RB1LD_1LC1RD_0LA1RC_1LA0RC [SWin 2] StD ltac:(vm_compute; reflexivity)
                   p1 j1' E1).
Qed.

(** The interior lap closes only up to [lift] (one trailing blank past the
    anchor's far side), so the closer is [LapCertGlueLift.glue_neverqh_lift]:
    [LapGlue.glue_neverqh] with the visit premise in [stepn] space, which is
    what its own proof consumes. *)
Theorem nqh_1RB1LD_1LC1RD_0LA1RC_1LA0RC : NeverQuasiHaltsSt tm.
Proof. apply (glue_neverqh_lift tm Cc 1). - exact boot_1RB1LD_1LC1RD_0LA1RC_1LA0RC. - intros p _. apply lap_1RB1LD_1LC1RD_0LA1RC_1LA0RC. - intros p q _. apply vis_1RB1LD_1LC1RD_0LA1RC_1LA0RC. Qed.

Theorem nonhalt_1RB1LD_1LC1RD_0LA1RC_1LA0RC : NonHalt tm.
Proof. apply never_qh_nonhalt, nqh_1RB1LD_1LC1RD_0LA1RC_1LA0RC. Qed.
