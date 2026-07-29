(** * CASB_0RB0LD_1RC1RB_1LD1RC_0RC1LA: machine 0RB0LD_1RC1RB_1LD1RC_0RC1LA, boarded by the SOLO CASCADE route.

    `docs/WAVE29_CASCADE_FINDINGS.md`.  This machine's outer overflow phase is
    a descending-octave cascade carrying ONE count per level, with the
    `2^j` count LAST rather than first:

        level j-1   one count 2^(j-1) .. 2^j-1     tail [] ++ Uc
        level j-2   one count 2^(j-2) .. 2^(j-1)-1 tail one unit longer
        ...
        level 0     the single value 1             tail j units longer
        the MAIN count 2^j .. 2^(j+1)-1, in a SECOND digit alphabet
        -> the outer successor

    which is `CASCADE_EXIT.md` section 3's predicted mirror image of the gated
    route -- a cascade BEFORE the identified count.  WAVE26 section 4 read the
    same phase as TWO counts because an octave SHADOW of the descent spans the
    whole of it and the segment scan's containment rule dropped every level;
    what it called the missing "shift chain" is the descent itself.

    Nothing here is new theory.  [NestedLapCascade]'s level step is a
    hypothesis, so one count per level is [fill_hop] where two are
    [level_hop]; the top level sitting one octave down is the wave-25
    octave-down reindex ([cview_none_shape] + a concrete p = 1 lap); and both
    interior laps are the wave-22b Z/P split, which the LEVEL family needs
    because `rep uS i ++ sS` admits no rotation when `sS` starts with a blank.

    Differential validation before emission: solo cascade: p=1 concrete (20 steps) + 7 overflow phases, j = 2..8 (35 levels, 42 counts, 967 inner laps).

    Axiom footprint: [functional_extensionality_dep] only. *)

From Coq Require Import Arith Lia Bool List PArith Wellfounded.
From BBB4 Require Import BBB4_Statement CTape Mirror.
From Coq Require Import FunctionalExtensionality.
From BBB4.Counters Require Import WTape MonoCounter JpCounter IXPGadgets
                                  LapCertGlue LapCertGlueLift NestedLap
                                  NestedLapLift NestedLapCascade Alph_01_11_011 Alph_10_11_1.
From BBB4.Checkers Require Import LapDecider.
Import ListNotations.

Definition mk_0RB0LD_1RC1RB_1LD1RC_0RC1LA (w : Sym) (d : Dir) (n : St) : option Trans :=
  Some (mkTrans w d n).
Local Notation mk := mk_0RB0LD_1RC1RB_1LD1RC_0RC1LA.

(** 0RB0LD_1RC1RB_1LD1RC_0RC1LA -- the table every lemma below runs on. *)
(** 0RB0LD_1RC1RB_1LD1RC_0RC1LA -- the real machine (its counter grows RIGHT). *)
Definition tm_0RB0LD_1RC1RB_1LD1RC_0RC1LA : TM := fun q s => match q, s with
  | StA, S0 => mk S0 DR StB | StA, S1 => mk S0 DL StD
  | StB, S0 => mk S1 DR StC | StB, S1 => mk S1 DR StB
  | StC, S0 => mk S1 DL StD | StC, S1 => mk S1 DR StC
  | StD, S0 => mk S0 DR StC | StD, S1 => mk S1 DL StA end.

(** Its mirror 0LB0RD_1LC1LB_1RD1LC_0LC1RA: the same counter grown leftward.  Every
    lemma below runs on the MIRRORED table;
    [Mirror.mirror_never_qh] transfers the conclusion back. *)
Definition tmm_0RB0LD_1RC1RB_1LD1RC_0RC1LA : TM := fun q s => match q, s with
  | StA, S0 => mk S0 DL StB | StA, S1 => mk S0 DR StD
  | StB, S0 => mk S1 DL StC | StB, S1 => mk S1 DL StB
  | StC, S0 => mk S1 DR StD | StC, S1 => mk S1 DL StC
  | StD, S0 => mk S0 DL StC | StD, S1 => mk S1 DR StA end.
Local Notation tm := tmm_0RB0LD_1RC1RB_1LD1RC_0RC1LA.

Lemma mirror_ok_0RB0LD_1RC1RB_1LD1RC_0RC1LA : mirror_tm tm_0RB0LD_1RC1RB_1LD1RC_0RC1LA = tmm_0RB0LD_1RC1RB_1LD1RC_0RC1LA.
Proof.
  apply functional_extensionality; intro q;
    apply functional_extensionality; intro b; destruct q, b; reflexivity.
Qed.

Definition Cc_0RB0LD_1RC1RB_1LD1RC_0RC1LA (p : positive) : cconf := (StD, (Ap_Alph_01_11_011 p ++ [S0], S0, [])).
Local Notation Cc := Cc_0RB0LD_1RC1RB_1LD1RC_0RC1LA.

(** A chain accepted up to [lift] can stop a blank past the anchor.  Every
    landing bridge below ends here, so it is stated before the first of them. *)
Lemma lbl_0RB0LD_1RC1RB_1LD1RC_0RC1LA : forall q l h r, lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.


(** ** The LEVEL family, at an ARBITRARY tail

    [T] is the cascade's growing region.  The counter's own laps never read it,
    so quantifying over it costs nothing and buys every level at once. *)
Definition Cin_0RB0LD_1RC1RB_1LD1RC_0RC1LA (T : list Sym) (v : positive) : cconf :=
  (StD, (Ap_Alph_01_11_011 v ++ T, S0, [])).
Local Notation Cin := Cin_0RB0LD_1RC1RB_1LD1RC_0RC1LA.

Definition Uc_0RB0LD_1RC1RB_1LD1RC_0RC1LA : list Sym := [S1;S1].
Local Notation Uc := Uc_0RB0LD_1RC1RB_1LD1RC_0RC1LA.

(** The tail level [l] carries, as a function of [m], the units beyond the top
    level's.  One unit longer per level down. *)
Definition TB_0RB0LD_1RC1RB_1LD1RC_0RC1LA (m : nat) : list Sym := [] ++ rep Uc (m + 1).
Local Notation TB := TB_0RB0LD_1RC1RB_1LD1RC_0RC1LA.

(** The level-[l] entry configuration.  Both indices are explicit and both are
    built by [S]: one index would force [j - l] into an anchor, which is the
    wave-15 index-shift trap. *)
Definition Dc_0RB0LD_1RC1RB_1LD1RC_0RC1LA (l m : nat) : cconf := Cin (TB m) (pow2 l).
Local Notation Dc := Dc_0RB0LD_1RC1RB_1LD1RC_0RC1LA.

Lemma epow2_0RB0LD_1RC1RB_1LD1RC_0RC1LA : forall n, Ap_Alph_01_11_011 (pow2 n) = rep [S0;S1] n ++ [S0;S1;S1].
Proof. induction n; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.

Lemma efill_0RB0LD_1RC1RB_1LD1RC_0RC1LA : forall n, Ap_Alph_01_11_011 (fill (pow2 n)) = rep [S1;S1] n ++ [S0;S1;S1].
Proof.
  intro n.
  destruct (Alph_01_11_011.cview_none_Alph_01_11_011 (fill (pow2 n)) n (cview_fill_pow2 n)) as (H & _).
  exact H.
Qed.

(** ** @WHICH@'s own interior lap, SPLIT

    `rep uS i ++ sS` has no rotation when `sS` starts with a blank, so the
    chain search finds nothing at the plain endpoints: [i = 0] is one concrete
    window and [i = S i'] runs with a unit PEELED into the prefix (count
    i' = i - 1).  The wave-22b interior-lap mirror of the outer j = 0 split. *)
Definition AIZ0_0RB0LD_1RC1RB_1LD1RC_0RC1LA : sconf := mkC StD (mkS [S0;S1] [] 0 0 []) S0 (mkS [] [] 0 0 []).
Definition AIZ1_0RB0LD_1RC1RB_1LD1RC_0RC1LA : sconf := mkC StD (mkS [S1;S1] [] 0 0 []) S0 (mkS [] [] 0 0 []).
Definition AIzc_0RB0LD_1RC1RB_1LD1RC_0RC1LA : list lstep := [SWin 2].

Lemma run_AIz_0RB0LD_1RC1RB_1LD1RC_0RC1LA :
  srun tm false true AIzc_0RB0LD_1RC1RB_1LD1RC_0RC1LA AIZ0_0RB0LD_1RC1RB_1LD1RC_0RC1LA = Some (AIZ1_0RB0LD_1RC1RB_1LD1RC_0RC1LA, 0, 2).
Proof. vm_compute. reflexivity. Qed.

Definition AIP0_0RB0LD_1RC1RB_1LD1RC_0RC1LA : sconf := mkC StD (mkS [S1;S1] [S1;S1] 1 0 [S0;S1]) S0 (mkS [] [] 0 0 []).
Definition AIP1_0RB0LD_1RC1RB_1LD1RC_0RC1LA : sconf := mkC StD (mkS [S0;S1] [S0;S1] 1 0 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition AIpc_0RB0LD_1RC1RB_1LD1RC_0RC1LA : list lstep := [SWin 2; SCycL 2 0; SWin 2; SCycR 2; SWin 2].

Lemma run_AIp_0RB0LD_1RC1RB_1LD1RC_0RC1LA :
  srun tm false true AIpc_0RB0LD_1RC1RB_1LD1RC_0RC1LA AIP0_0RB0LD_1RC1RB_1LD1RC_0RC1LA = Some (AIP1_0RB0LD_1RC1RB_1LD1RC_0RC1LA, 4, 6).
Proof. vm_compute. reflexivity. Qed.

Lemma AIgz0_0RB0LD_1RC1RB_1LD1RC_0RC1LA : forall T v q0, cview v = (0%nat, Some q0) ->
  Cin T v = cden (Ap_Alph_01_11_011 q0 ++ T) [] 0 AIZ0_0RB0LD_1RC1RB_1LD1RC_0RC1LA.
Proof.
  intros T v q0 Ev. destruct (Alph_01_11_011.cview_some_Alph_01_11_011 v 0 q0 Ev) as (H1 & _).
  unfold Cin_0RB0LD_1RC1RB_1LD1RC_0RC1LA, cden, AIZ0_0RB0LD_1RC1RB_1LD1RC_0RC1LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (0 * 0 + 0) with 0 by lia.
  rewrite H1. cbn [rep app]. rewrite ?app_nil_r. rewrite <- ?app_assoc.
  cbn [app]. rewrite ?app_nil_r. reflexivity.
Qed.

Lemma AIgz1_0RB0LD_1RC1RB_1LD1RC_0RC1LA : forall T v q0, cview v = (0%nat, Some q0) ->
  lift (cden (Ap_Alph_01_11_011 q0 ++ T) [] 0 AIZ1_0RB0LD_1RC1RB_1LD1RC_0RC1LA) = lift (Cin T (Pos.succ v)).
Proof.
  intros T v q0 Ev. destruct (Alph_01_11_011.cview_some_Alph_01_11_011 v 0 q0 Ev) as (_ & H2).
  unfold Cin_0RB0LD_1RC1RB_1LD1RC_0RC1LA, cden, AIZ1_0RB0LD_1RC1RB_1LD1RC_0RC1LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (0 * 0 + 0) with 0 by lia.
  rewrite H2. cbn [rep app]. rewrite ?app_nil_r. rewrite <- ?app_assoc.
  cbn [app]. rewrite ?app_nil_r.
  rewrite ?lift_app_blank. rewrite <- ?app_assoc. reflexivity.
Qed.

Lemma AIgp0_0RB0LD_1RC1RB_1LD1RC_0RC1LA : forall T v i q0, cview v = (S i, Some q0) ->
  Cin T v = cden (Ap_Alph_01_11_011 q0 ++ T) [] i AIP0_0RB0LD_1RC1RB_1LD1RC_0RC1LA.
Proof.
  intros T v i q0 Ev. destruct (Alph_01_11_011.cview_some_Alph_01_11_011 v (S i) q0 Ev) as (H1 & _).
  unfold Cin_0RB0LD_1RC1RB_1LD1RC_0RC1LA, cden, AIP0_0RB0LD_1RC1RB_1LD1RC_0RC1LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia. replace (0 * i + 0) with 0 by lia.
  rewrite H1. cbn [rep app]. rewrite ?app_nil_r. rewrite <- ?app_assoc.
  cbn [app]. rewrite ?app_nil_r. reflexivity.
Qed.

Lemma AIgp1_0RB0LD_1RC1RB_1LD1RC_0RC1LA : forall T v i q0, cview v = (S i, Some q0) ->
  lift (cden (Ap_Alph_01_11_011 q0 ++ T) [] i AIP1_0RB0LD_1RC1RB_1LD1RC_0RC1LA) = lift (Cin T (Pos.succ v)).
Proof.
  intros T v i q0 Ev. destruct (Alph_01_11_011.cview_some_Alph_01_11_011 v (S i) q0 Ev) as (_ & H2).
  unfold Cin_0RB0LD_1RC1RB_1LD1RC_0RC1LA, cden, AIP1_0RB0LD_1RC1RB_1LD1RC_0RC1LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia. replace (0 * i + 0) with 0 by lia.
  rewrite H2. cbn [rep app]. rewrite ?app_nil_r. rewrite <- ?app_assoc.
  cbn [app]. rewrite ?app_nil_r.
  rewrite ?lift_app_blank. rewrite <- ?app_assoc. reflexivity.
Qed.

(** The lap, up to [lift] and at every tail at once -- [NestedLapCascade]'s [Hin] for the levels. *)
Lemma AIlap_0RB0LD_1RC1RB_1LD1RC_0RC1LA : forall T v i q0, cview v = (i, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cin T v) = Some c'
               /\ lift c' = lift (Cin T (Pos.succ v)).
Proof.
  intros T v i q0 Ev. destruct i as [|i'].
  - exists (0 * 0 + 2), (cden (Ap_Alph_01_11_011 q0 ++ T) [] 0 AIZ1_0RB0LD_1RC1RB_1LD1RC_0RC1LA).
    split; [lia|]. split; [| exact (AIgz1_0RB0LD_1RC1RB_1LD1RC_0RC1LA T v q0 Ev)].
    rewrite (AIgz0_0RB0LD_1RC1RB_1LD1RC_0RC1LA T v q0 Ev).
    exact (srun_sound tm false true AIzc_0RB0LD_1RC1RB_1LD1RC_0RC1LA AIZ0_0RB0LD_1RC1RB_1LD1RC_0RC1LA AIZ1_0RB0LD_1RC1RB_1LD1RC_0RC1LA
             0 2 run_AIz_0RB0LD_1RC1RB_1LD1RC_0RC1LA (Ap_Alph_01_11_011 q0 ++ T) [] 0
             ltac:(discriminate) ltac:(reflexivity)).
  - exists (4 * i' + 6), (cden (Ap_Alph_01_11_011 q0 ++ T) [] i' AIP1_0RB0LD_1RC1RB_1LD1RC_0RC1LA).
    split; [lia|]. split; [| exact (AIgp1_0RB0LD_1RC1RB_1LD1RC_0RC1LA T v i' q0 Ev)].
    rewrite (AIgp0_0RB0LD_1RC1RB_1LD1RC_0RC1LA T v i' q0 Ev).
    exact (srun_sound tm false true AIpc_0RB0LD_1RC1RB_1LD1RC_0RC1LA AIP0_0RB0LD_1RC1RB_1LD1RC_0RC1LA AIP1_0RB0LD_1RC1RB_1LD1RC_0RC1LA
             4 6 run_AIp_0RB0LD_1RC1RB_1LD1RC_0RC1LA (Ap_Alph_01_11_011 q0 ++ T) [] i'
             ltac:(discriminate) ltac:(reflexivity)).
Qed.

(** ** The MAIN count's family

    The count the phase ends on is in a DIFFERENT digit alphabet from the
    levels', at a different state and a different far side -- the two words are
    genuinely different encodings of the same value, which is why WAVE26 read
    the descent between them as a re-encoding pass over one word.  It is stated
    tail-parametrically too, purely so [fill_hop] applies to it unchanged. *)
Definition CinM_0RB0LD_1RC1RB_1LD1RC_0RC1LA (T : list Sym) (v : positive) : cconf :=
  (StB, (Ap_Alph_10_11_1 v ++ T, S0, [S1])).
Local Notation CinM := CinM_0RB0LD_1RC1RB_1LD1RC_0RC1LA.

Definition MT_0RB0LD_1RC1RB_1LD1RC_0RC1LA : list Sym := [S1].
Local Notation MT := MT_0RB0LD_1RC1RB_1LD1RC_0RC1LA.

Lemma epow2m_0RB0LD_1RC1RB_1LD1RC_0RC1LA : forall n, Ap_Alph_10_11_1 (pow2 n) = rep [S1;S0] n ++ [S1].
Proof. induction n; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.

Lemma efillm_0RB0LD_1RC1RB_1LD1RC_0RC1LA : forall n, Ap_Alph_10_11_1 (fill (pow2 n)) = rep [S1;S1] n ++ [S1].
Proof.
  intro n.
  destruct (Alph_10_11_1.cview_none_Alph_10_11_1 (fill (pow2 n)) n (cview_fill_pow2 n)) as (H & _).
  exact H.
Qed.

(** ** @WHICH@'s own interior lap, SPLIT

    `rep uS i ++ sS` has no rotation when `sS` starts with a blank, so the
    chain search finds nothing at the plain endpoints: [i = 0] is one concrete
    window and [i = S i'] runs with a unit PEELED into the prefix (count
    i' = i - 1).  The wave-22b interior-lap mirror of the outer j = 0 split. *)
Definition AMZ0_0RB0LD_1RC1RB_1LD1RC_0RC1LA : sconf := mkC StB (mkS [S1;S0] [] 0 0 []) S0 (mkS [S1] [] 0 0 []).
Definition AMZ1_0RB0LD_1RC1RB_1LD1RC_0RC1LA : sconf := mkC StB (mkS [S1;S1] [] 0 0 []) S0 (mkS [S1;S0] [] 0 0 []).
Definition AMzc_0RB0LD_1RC1RB_1LD1RC_0RC1LA : list lstep := [SWin 5; SWinR 3].

Lemma run_AMz_0RB0LD_1RC1RB_1LD1RC_0RC1LA :
  srun tm false true AMzc_0RB0LD_1RC1RB_1LD1RC_0RC1LA AMZ0_0RB0LD_1RC1RB_1LD1RC_0RC1LA = Some (AMZ1_0RB0LD_1RC1RB_1LD1RC_0RC1LA, 0, 8).
Proof. vm_compute. reflexivity. Qed.

Definition AMP0_0RB0LD_1RC1RB_1LD1RC_0RC1LA : sconf := mkC StB (mkS [S1;S1] [S1;S1] 1 0 [S1;S0]) S0 (mkS [S1] [] 0 0 []).
Definition AMP1_0RB0LD_1RC1RB_1LD1RC_0RC1LA : sconf := mkC StB (mkS [S1;S0] [S1;S0] 1 0 [S1;S1]) S0 (mkS [S1;S0] [] 0 0 []).
Definition AMpc_0RB0LD_1RC1RB_1LD1RC_0RC1LA : list lstep := [SWin 2; SCycL 2 0; SWin 4; SCycR 2; SWin 3; SWinR 3].

Lemma run_AMp_0RB0LD_1RC1RB_1LD1RC_0RC1LA :
  srun tm false true AMpc_0RB0LD_1RC1RB_1LD1RC_0RC1LA AMP0_0RB0LD_1RC1RB_1LD1RC_0RC1LA = Some (AMP1_0RB0LD_1RC1RB_1LD1RC_0RC1LA, 4, 12).
Proof. vm_compute. reflexivity. Qed.

Lemma AMgz0_0RB0LD_1RC1RB_1LD1RC_0RC1LA : forall T v q0, cview v = (0%nat, Some q0) ->
  CinM T v = cden (Ap_Alph_10_11_1 q0 ++ T) [] 0 AMZ0_0RB0LD_1RC1RB_1LD1RC_0RC1LA.
Proof.
  intros T v q0 Ev. destruct (Alph_10_11_1.cview_some_Alph_10_11_1 v 0 q0 Ev) as (H1 & _).
  unfold CinM_0RB0LD_1RC1RB_1LD1RC_0RC1LA, cden, AMZ0_0RB0LD_1RC1RB_1LD1RC_0RC1LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (0 * 0 + 0) with 0 by lia.
  rewrite H1. cbn [rep app]. rewrite ?app_nil_r. rewrite <- ?app_assoc.
  cbn [app]. rewrite ?app_nil_r. reflexivity.
Qed.

Lemma AMgz1_0RB0LD_1RC1RB_1LD1RC_0RC1LA : forall T v q0, cview v = (0%nat, Some q0) ->
  lift (cden (Ap_Alph_10_11_1 q0 ++ T) [] 0 AMZ1_0RB0LD_1RC1RB_1LD1RC_0RC1LA) = lift (CinM T (Pos.succ v)).
Proof.
  intros T v q0 Ev. destruct (Alph_10_11_1.cview_some_Alph_10_11_1 v 0 q0 Ev) as (_ & H2).
  unfold CinM_0RB0LD_1RC1RB_1LD1RC_0RC1LA, cden, AMZ1_0RB0LD_1RC1RB_1LD1RC_0RC1LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (0 * 0 + 0) with 0 by lia.
  rewrite H2. cbn [rep app]. rewrite ?app_nil_r. rewrite <- ?app_assoc.
  cbn [app]. rewrite ?app_nil_r.
  change ([S1;S0]) with (([S1]) ++ [S0]).
  rewrite ?lift_app_blank. rewrite <- ?app_assoc. reflexivity.
Qed.

Lemma AMgp0_0RB0LD_1RC1RB_1LD1RC_0RC1LA : forall T v i q0, cview v = (S i, Some q0) ->
  CinM T v = cden (Ap_Alph_10_11_1 q0 ++ T) [] i AMP0_0RB0LD_1RC1RB_1LD1RC_0RC1LA.
Proof.
  intros T v i q0 Ev. destruct (Alph_10_11_1.cview_some_Alph_10_11_1 v (S i) q0 Ev) as (H1 & _).
  unfold CinM_0RB0LD_1RC1RB_1LD1RC_0RC1LA, cden, AMP0_0RB0LD_1RC1RB_1LD1RC_0RC1LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia. replace (0 * i + 0) with 0 by lia.
  rewrite H1. cbn [rep app]. rewrite ?app_nil_r. rewrite <- ?app_assoc.
  cbn [app]. rewrite ?app_nil_r. reflexivity.
Qed.

Lemma AMgp1_0RB0LD_1RC1RB_1LD1RC_0RC1LA : forall T v i q0, cview v = (S i, Some q0) ->
  lift (cden (Ap_Alph_10_11_1 q0 ++ T) [] i AMP1_0RB0LD_1RC1RB_1LD1RC_0RC1LA) = lift (CinM T (Pos.succ v)).
Proof.
  intros T v i q0 Ev. destruct (Alph_10_11_1.cview_some_Alph_10_11_1 v (S i) q0 Ev) as (_ & H2).
  unfold CinM_0RB0LD_1RC1RB_1LD1RC_0RC1LA, cden, AMP1_0RB0LD_1RC1RB_1LD1RC_0RC1LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia. replace (0 * i + 0) with 0 by lia.
  rewrite H2. cbn [rep app]. rewrite ?app_nil_r. rewrite <- ?app_assoc.
  cbn [app]. rewrite ?app_nil_r.
  change ([S1;S0]) with (([S1]) ++ [S0]).
  rewrite ?lift_app_blank. rewrite <- ?app_assoc. reflexivity.
Qed.

(** The lap, up to [lift] and at every tail at once -- [fill_hop]'s [Hin] for the closing count. *)
Lemma AMlap_0RB0LD_1RC1RB_1LD1RC_0RC1LA : forall T v i q0, cview v = (i, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (CinM T v) = Some c'
               /\ lift c' = lift (CinM T (Pos.succ v)).
Proof.
  intros T v i q0 Ev. destruct i as [|i'].
  - exists (0 * 0 + 8), (cden (Ap_Alph_10_11_1 q0 ++ T) [] 0 AMZ1_0RB0LD_1RC1RB_1LD1RC_0RC1LA).
    split; [lia|]. split; [| exact (AMgz1_0RB0LD_1RC1RB_1LD1RC_0RC1LA T v q0 Ev)].
    rewrite (AMgz0_0RB0LD_1RC1RB_1LD1RC_0RC1LA T v q0 Ev).
    exact (srun_sound tm false true AMzc_0RB0LD_1RC1RB_1LD1RC_0RC1LA AMZ0_0RB0LD_1RC1RB_1LD1RC_0RC1LA AMZ1_0RB0LD_1RC1RB_1LD1RC_0RC1LA
             0 8 run_AMz_0RB0LD_1RC1RB_1LD1RC_0RC1LA (Ap_Alph_10_11_1 q0 ++ T) [] 0
             ltac:(discriminate) ltac:(reflexivity)).
  - exists (4 * i' + 12), (cden (Ap_Alph_10_11_1 q0 ++ T) [] i' AMP1_0RB0LD_1RC1RB_1LD1RC_0RC1LA).
    split; [lia|]. split; [| exact (AMgp1_0RB0LD_1RC1RB_1LD1RC_0RC1LA T v i' q0 Ev)].
    rewrite (AMgp0_0RB0LD_1RC1RB_1LD1RC_0RC1LA T v i' q0 Ev).
    exact (srun_sound tm false true AMpc_0RB0LD_1RC1RB_1LD1RC_0RC1LA AMP0_0RB0LD_1RC1RB_1LD1RC_0RC1LA AMP1_0RB0LD_1RC1RB_1LD1RC_0RC1LA
             4 12 run_AMp_0RB0LD_1RC1RB_1LD1RC_0RC1LA (Ap_Alph_10_11_1 q0 ++ T) [] i'
             ltac:(discriminate) ltac:(reflexivity)).
Qed.

(** ** The four chains *)

Definition B0_0RB0LD_1RC1RB_1LD1RC_0RC1LA : sconf := mkC StD (mkS [] [S1;S1] 1 0 [S1;S1;S0;S1;S1;S0]) S0 (mkS [] [] 0 0 []).
Definition B1_0RB0LD_1RC1RB_1LD1RC_0RC1LA : sconf := mkC StD (mkS [] [S0;S1] 1 1 [S0;S1;S1;S0]) S0 (mkS [] [] 0 0 []).

(** *** boot: the outer overflow anchor -> the TOP level's count.

    The top level sits one octave DOWN, so this runs at the reindexed anchor
    [S (S j)] and its own source carries one unit PEELED out of the count --
    without the peel there is no chain at any split, the standing lesson of
    waves 24-26 applied once more. *)
Definition BB1_0RB0LD_1RC1RB_1LD1RC_0RC1LA : sconf := mkC StD (mkS [] [S0;S1] 1 0 [S0;S1;S1;S1;S1;S0]) S0 (mkS [] [] 0 0 []).
Definition chb_0RB0LD_1RC1RB_1LD1RC_0RC1LA : list lstep := [SRotL 1; SWin 1; SCycL 2 0; SWin 4; SCycR 2; SWin 1; SUnrotL 1].

Lemma run_boot_0RB0LD_1RC1RB_1LD1RC_0RC1LA :
  srun tm true true chb_0RB0LD_1RC1RB_1LD1RC_0RC1LA B0_0RB0LD_1RC1RB_1LD1RC_0RC1LA = Some (BB1_0RB0LD_1RC1RB_1LD1RC_0RC1LA, 4, 6).
Proof. vm_compute. reflexivity. Qed.

(** *** level (S l) fill -> level l start.  THE level step -- one count per
    level, so the whole of [NestedLapCascade.Hstep] is this chain behind a
    [fill_hop], where the gated route needs [level_hop] and two. *)
Definition DW0_0RB0LD_1RC1RB_1LD1RC_0RC1LA : sconf := mkC StD (mkS [] [S1;S1] 1 0 [S1;S1;S0]) S0 (mkS [] [] 0 0 []).
Definition DW1_0RB0LD_1RC1RB_1LD1RC_0RC1LA : sconf := mkC StD (mkS [] [S0;S1] 1 0 [S0;S1;S1]) S0 (mkS [] [] 0 0 []).
Definition chDW_0RB0LD_1RC1RB_1LD1RC_0RC1LA : list lstep := [SRotL 1; SWin 1; SCycL 2 0; SWin 4; SCycR 2; SWin 1; SUnrotL 1].

Lemma run_down_0RB0LD_1RC1RB_1LD1RC_0RC1LA :
  srun tm false true chDW_0RB0LD_1RC1RB_1LD1RC_0RC1LA DW0_0RB0LD_1RC1RB_1LD1RC_0RC1LA = Some (DW1_0RB0LD_1RC1RB_1LD1RC_0RC1LA, 4, 6).
Proof. vm_compute. reflexivity. Qed.

(** *** the close, in two halves: level 0's fill into the MAIN count's start,
    and the main count's fill out to the outer successor.  Its exponentially
    many laps live in [fill_hop] between them, so neither chain sees them. *)
Definition CLA0_0RB0LD_1RC1RB_1LD1RC_0RC1LA : sconf := mkC StD (mkS [S0;S1;S1] [S1;S1] 1 0 []) S0 (mkS [] [] 0 0 []).
Definition CLA1_0RB0LD_1RC1RB_1LD1RC_0RC1LA : sconf := mkC StB (mkS [] [S1;S0] 1 0 [S1;S1]) S0 (mkS [S1;S0] [] 0 0 []).
Definition chCLA_0RB0LD_1RC1RB_1LD1RC_0RC1LA : list lstep := [SWin 5; SCycL 2 0; SWinL 2; SCycR 2; SWin 5; SUnrotL 1].

Lemma run_closeA_0RB0LD_1RC1RB_1LD1RC_0RC1LA :
  srun tm true true chCLA_0RB0LD_1RC1RB_1LD1RC_0RC1LA CLA0_0RB0LD_1RC1RB_1LD1RC_0RC1LA = Some (CLA1_0RB0LD_1RC1RB_1LD1RC_0RC1LA, 4, 12).
Proof. vm_compute. reflexivity. Qed.

Definition CLB0_0RB0LD_1RC1RB_1LD1RC_0RC1LA : sconf := mkC StB (mkS [] [S1;S1] 1 0 [S1;S1]) S0 (mkS [S1] [] 0 0 []).
Definition CLB1_0RB0LD_1RC1RB_1LD1RC_0RC1LA : sconf := mkC StD (mkS [] [S0;S1] 1 1 [S0;S1;S1]) S0 (mkS [] [] 0 0 []).
Definition chCLB_0RB0LD_1RC1RB_1LD1RC_0RC1LA : list lstep := [SRotL 1; SWin 1; SCycL 2 0; SWin 1; SWinL 3; SCycR 2; SWin 2; SWinR 1; SUnrotL 1; SFoldL 1].

Lemma run_closeB_0RB0LD_1RC1RB_1LD1RC_0RC1LA :
  srun tm true true chCLB_0RB0LD_1RC1RB_1LD1RC_0RC1LA CLB0_0RB0LD_1RC1RB_1LD1RC_0RC1LA = Some (CLB1_0RB0LD_1RC1RB_1LD1RC_0RC1LA, 4, 8).
Proof. vm_compute. reflexivity. Qed.

(** ** The per-level glue

    The opaque region the level chain carries, as a function of the level's
    tail length.  Every exponent is built by [S] and [+]; none is a
    subtraction. *)
Definition XDW_0RB0LD_1RC1RB_1LD1RC_0RC1LA (m : nat) : list Sym := rep Uc (2 + m).

Lemma gDWs_0RB0LD_1RC1RB_1LD1RC_0RC1LA : forall l m,
  Cin (TB m) (fill (pow2 (S l))) = cden (XDW_0RB0LD_1RC1RB_1LD1RC_0RC1LA m) [] l DW0_0RB0LD_1RC1RB_1LD1RC_0RC1LA.
Proof.
  intros l m.
  unfold Cin_0RB0LD_1RC1RB_1LD1RC_0RC1LA, TB_0RB0LD_1RC1RB_1LD1RC_0RC1LA, XDW_0RB0LD_1RC1RB_1LD1RC_0RC1LA, Uc_0RB0LD_1RC1RB_1LD1RC_0RC1LA, cden, DW0_0RB0LD_1RC1RB_1LD1RC_0RC1LA, sden;
    cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
  rewrite efill_0RB0LD_1RC1RB_1LD1RC_0RC1LA.
  replace (1 * l + 0) with (l) by lia.
  replace (0 * l + 0) with 0 by lia.
  replace (S l) with (l + 1) by lia.
  replace (m + 1) with (1 + m) by lia.
  rewrite ?rep_add. cbn [rep app]. rewrite <- ?app_assoc.
  cbn [app]. rewrite ?app_nil_r. reflexivity.
Qed.

Lemma gDWd_0RB0LD_1RC1RB_1LD1RC_0RC1LA : forall l m,
  lift (cden (XDW_0RB0LD_1RC1RB_1LD1RC_0RC1LA m) [] l DW1_0RB0LD_1RC1RB_1LD1RC_0RC1LA) = lift (Cin (TB (S m)) (pow2 l)).
Proof.
  intros l m.
  unfold Cin_0RB0LD_1RC1RB_1LD1RC_0RC1LA, TB_0RB0LD_1RC1RB_1LD1RC_0RC1LA, XDW_0RB0LD_1RC1RB_1LD1RC_0RC1LA, Uc_0RB0LD_1RC1RB_1LD1RC_0RC1LA, cden, DW1_0RB0LD_1RC1RB_1LD1RC_0RC1LA, sden;
    cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
  rewrite epow2_0RB0LD_1RC1RB_1LD1RC_0RC1LA.
  replace (1 * l + 0) with (l) by lia.
  replace (0 * l + 0) with 0 by lia.
  replace (S m + 1) with (2 + m) by lia.
  rewrite ?rep_add. cbn [rep app]. rewrite <- ?app_assoc.
  cbn [app]. rewrite ?app_nil_r.
  rewrite ?lift_app_blank. reflexivity.
Qed.

(** ONE LEVEL: one count -- an [exists n] hiding a [Theta(2^l)] -- and the
    chain out of its fill.  The SAME step at every level, which is the whole
    content of the cascade. *)
Lemma hstep_0RB0LD_1RC1RB_1LD1RC_0RC1LA : forall l m,
  exists n, stepn tm n (lift (Dc (S l) m)) = Some (lift (Dc l (S m))).
Proof.
  intros l m. unfold Dc_0RB0LD_1RC1RB_1LD1RC_0RC1LA.
  apply (fill_hop tm Cin AIlap_0RB0LD_1RC1RB_1LD1RC_0RC1LA (TB m) (pow2 (S l))).
  exists (4 * l + 6). rewrite gDWs_0RB0LD_1RC1RB_1LD1RC_0RC1LA, <- gDWd_0RB0LD_1RC1RB_1LD1RC_0RC1LA.
  apply csteps_lift.
  exact (srun_sound tm false true chDW_0RB0LD_1RC1RB_1LD1RC_0RC1LA DW0_0RB0LD_1RC1RB_1LD1RC_0RC1LA DW1_0RB0LD_1RC1RB_1LD1RC_0RC1LA 4 6
           run_down_0RB0LD_1RC1RB_1LD1RC_0RC1LA (XDW_0RB0LD_1RC1RB_1LD1RC_0RC1LA m) [] l
           ltac:(discriminate) ltac:(reflexivity)).
Qed.

(** ** The outer glue: boot in, close out.

    [gso_] is stated at the REINDEXED anchor [S (S j)]: the top level is one
    octave below the outer index, so the generic route runs at [j = S j'] and
    the boot's source carries the peeled unit that shift leaves behind. *)
Lemma gso_0RB0LD_1RC1RB_1LD1RC_0RC1LA : forall p j, cview p = (S (S j), None) ->
  Cc p = cden [] [] j B0_0RB0LD_1RC1RB_1LD1RC_0RC1LA.
Proof.
  intros p j Ev. destruct (Alph_01_11_011.cview_none_Alph_01_11_011 p (S j) Ev) as (H1 & _).
  unfold Cc_0RB0LD_1RC1RB_1LD1RC_0RC1LA, cden, B0_0RB0LD_1RC1RB_1LD1RC_0RC1LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia. replace (0 * j + 0) with 0 by lia.
  rewrite H1. replace (S j) with (j + 1) by lia.
  rewrite rep_add. cbn [rep app]. rewrite <- ?app_assoc. cbn [app].
  rewrite ?app_nil_r. reflexivity.
Qed.

Lemma geo_0RB0LD_1RC1RB_1LD1RC_0RC1LA : forall p j, cview p = (S j, None) ->
  lift (cden [] [] j B1_0RB0LD_1RC1RB_1LD1RC_0RC1LA) = lift (Cc (Pos.succ p)).
Proof.
  intros p j Ev. destruct (Alph_01_11_011.cview_none_Alph_01_11_011 p j Ev) as (_ & H2).
  unfold Cc_0RB0LD_1RC1RB_1LD1RC_0RC1LA, cden, B1_0RB0LD_1RC1RB_1LD1RC_0RC1LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 1) with (S j) by lia. replace (0 * j + 0) with 0 by lia.
  rewrite H2. cbn [rep app]. rewrite <- ?app_assoc. cbn [app].
  rewrite ?app_nil_r. rewrite ?lift_app_blank. reflexivity.
Qed.

(** The boot lands on the top level's count, up to 1/0 trailing
    blanks -- the [lift] leniency [NestedLapLift] measured to be the binding
    one on this whole bucket. *)
Lemma gbo_0RB0LD_1RC1RB_1LD1RC_0RC1LA : forall j, lift (cden [] [] j BB1_0RB0LD_1RC1RB_1LD1RC_0RC1LA) = lift (Dc j 0).
Proof.
  intro j.
  assert (HD : cden [] [] j BB1_0RB0LD_1RC1RB_1LD1RC_0RC1LA = (StD, ((rep [S0;S1] j ++ [S0;S1;S1;S1;S1]) ++ [S0], S0, []))).
  { unfold cden, BB1_0RB0LD_1RC1RB_1LD1RC_0RC1LA, sden;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with (j) by lia.
  replace (0 * j + 0) with 0 by lia.
    rewrite ?rep_add. cbn [rep app]. rewrite <- ?app_assoc.
    cbn [app]. rewrite ?app_nil_r. reflexivity. }
  assert (HC : Dc j 0 = (StD, (rep [S0;S1] j ++ [S0;S1;S1;S1;S1], S0, []))).
  { unfold Dc_0RB0LD_1RC1RB_1LD1RC_0RC1LA, Cin_0RB0LD_1RC1RB_1LD1RC_0RC1LA, TB_0RB0LD_1RC1RB_1LD1RC_0RC1LA, Uc_0RB0LD_1RC1RB_1LD1RC_0RC1LA. rewrite epow2_0RB0LD_1RC1RB_1LD1RC_0RC1LA.
    replace (0 + 1) with 1 by lia.
    cbn [rep app]. rewrite <- ?app_assoc. cbn [app]. rewrite ?app_nil_r.
    reflexivity. }
  rewrite HD, HC. rewrite ?lbl_0RB0LD_1RC1RB_1LD1RC_0RC1LA. rewrite ?lift_app_blank. reflexivity.
Qed.

(** The close starts from level 0, whose tail is by then [j] units past the top
    level's -- so unlike the level chain it is indexed by the OUTER index. *)
Lemma gcla_0RB0LD_1RC1RB_1LD1RC_0RC1LA : forall j, Dc 0 (j + 0) = cden [] [] (S j) CLA0_0RB0LD_1RC1RB_1LD1RC_0RC1LA.
Proof.
  intro j.
  unfold Dc_0RB0LD_1RC1RB_1LD1RC_0RC1LA, Cin_0RB0LD_1RC1RB_1LD1RC_0RC1LA, TB_0RB0LD_1RC1RB_1LD1RC_0RC1LA, Uc_0RB0LD_1RC1RB_1LD1RC_0RC1LA, cden, CLA0_0RB0LD_1RC1RB_1LD1RC_0RC1LA, sden;
    cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
  rewrite (epow2_0RB0LD_1RC1RB_1LD1RC_0RC1LA 0).
  replace (1 * S j + 0) with (S j) by lia.
  replace (0 * S j + 0) with 0 by lia.
  replace (j + 0 + 1) with (S j) by lia.
  rewrite ?rep_add. cbn [pow2 rep app]. rewrite <- ?app_assoc.
  cbn [app]. rewrite ?app_nil_r. reflexivity.
Qed.

Lemma gclab_0RB0LD_1RC1RB_1LD1RC_0RC1LA : forall j,
  lift (cden [] [] (S j) CLA1_0RB0LD_1RC1RB_1LD1RC_0RC1LA) = lift (CinM MT (pow2 (S j))).
Proof.
  intro j.
  assert (HD : cden [] [] (S j) CLA1_0RB0LD_1RC1RB_1LD1RC_0RC1LA = (StB, (rep [S1;S0] (S j) ++ [S1;S1], S0, ([S1]) ++ [S0]))).
  { unfold cden, CLA1_0RB0LD_1RC1RB_1LD1RC_0RC1LA, sden;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * S j + 0) with (S j) by lia.
    replace (0 * S j + 0) with 0 by lia.
    rewrite ?rep_add. cbn [rep app]. rewrite <- ?app_assoc.
    cbn [app]. rewrite ?app_nil_r. reflexivity. }
  assert (HC : CinM MT (pow2 (S j)) = (StB, (rep [S1;S0] (S j) ++ [S1;S1], S0, [S1]))).
  { unfold CinM_0RB0LD_1RC1RB_1LD1RC_0RC1LA, MT_0RB0LD_1RC1RB_1LD1RC_0RC1LA. rewrite epow2m_0RB0LD_1RC1RB_1LD1RC_0RC1LA.
    cbn [rep app]. rewrite <- ?app_assoc. cbn [app]. rewrite ?app_nil_r.
    reflexivity. }
  rewrite HD, HC. rewrite ?lbl_0RB0LD_1RC1RB_1LD1RC_0RC1LA. rewrite ?lift_app_blank. reflexivity.
Qed.

Lemma gclb_0RB0LD_1RC1RB_1LD1RC_0RC1LA : forall j,
  CinM MT (fill (pow2 (S j))) = cden [] [] (S j) CLB0_0RB0LD_1RC1RB_1LD1RC_0RC1LA.
Proof.
  intro j.
  unfold CinM_0RB0LD_1RC1RB_1LD1RC_0RC1LA, MT_0RB0LD_1RC1RB_1LD1RC_0RC1LA, cden, CLB0_0RB0LD_1RC1RB_1LD1RC_0RC1LA, sden;
    cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
  rewrite efillm_0RB0LD_1RC1RB_1LD1RC_0RC1LA.
  replace (1 * S j + 0) with (S j) by lia.
  replace (0 * S j + 0) with 0 by lia.
  rewrite ?rep_add. cbn [rep app]. rewrite <- ?app_assoc.
  cbn [app]. rewrite ?app_nil_r. reflexivity.
Qed.

(** The main count's chain out lands on the outer successor up to trailing
    blanks; both sides normalise to the same explicit word. *)
Lemma gclbx_0RB0LD_1RC1RB_1LD1RC_0RC1LA : forall j,
  lift (cden [] [] (S j) CLB1_0RB0LD_1RC1RB_1LD1RC_0RC1LA) = lift (cden [] [] (S j) B1_0RB0LD_1RC1RB_1LD1RC_0RC1LA).
Proof.
  intro j.
  assert (HD : cden [] [] (S j) CLB1_0RB0LD_1RC1RB_1LD1RC_0RC1LA = (StD, (rep [S0;S1] (S (S j)) ++ [S0;S1;S1], S0, []))).
  { unfold cden, CLB1_0RB0LD_1RC1RB_1LD1RC_0RC1LA, sden;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * S j + 1) with (1 + S j) by lia.
    replace (0 * S j + 0) with 0 by lia.
    rewrite ?rep_add. cbn [rep app]. rewrite <- ?app_assoc.
    cbn [app]. rewrite ?app_nil_r. reflexivity. }
  assert (HE : cden [] [] (S j) B1_0RB0LD_1RC1RB_1LD1RC_0RC1LA = (StD, ((rep [S0;S1] (S (S j)) ++ [S0;S1;S1]) ++ [S0], S0, []))).
  { unfold cden, B1_0RB0LD_1RC1RB_1LD1RC_0RC1LA, sden;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * S j + 1) with (1 + S j) by lia.
    replace (0 * S j + 0) with 0 by lia.
    rewrite ?rep_add. cbn [rep app]. rewrite <- ?app_assoc.
    cbn [app]. rewrite ?app_nil_r. reflexivity. }
  rewrite HD, HE. rewrite ?lbl_0RB0LD_1RC1RB_1LD1RC_0RC1LA. rewrite ?lift_app_blank. reflexivity.
Qed.

(** ** The overflow branch, reindexed

    j = 0 is the p = 1 overflow and has no cascade at all: a concrete lap, the
    octave-down route's exact device. *)
Lemma lapz_0RB0LD_1RC1RB_1LD1RC_0RC1LA : exists n c', csteps tm n (Cc 1) = Some c'
  /\ lift c' = lift (Cc 2) /\ 0 < n.
Proof.
  exists 20.
  assert (H : match csteps tm 20 (Cc 1) with
              | Some c => ceqb c (Cc 2) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 20 (Cc 1)) as [c|] eqn:E0; [|discriminate].
  exists c. split; [reflexivity|]. split; [apply ceqb_lift; exact H | lia].
Qed.

Lemma lapo_0RB0LD_1RC1RB_1LD1RC_0RC1LA : forall p j, cview p = (S j, None) ->
  exists n c', csteps tm n (Cc p) = Some c'
          /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intros p j Ev.
  destruct j as [|j'].
  - rewrite (cview_none_shape p 0 Ev). exact lapz_0RB0LD_1RC1RB_1LD1RC_0RC1LA.
  - apply (cascade_overflow tm Cc Dc hstep_0RB0LD_1RC1RB_1LD1RC_0RC1LA p j' 0).
    + exists (4 * j' + 6), (cden [] [] j' BB1_0RB0LD_1RC1RB_1LD1RC_0RC1LA).
      split; [lia|]. split; [| exact (gbo_0RB0LD_1RC1RB_1LD1RC_0RC1LA j')].
      rewrite (gso_0RB0LD_1RC1RB_1LD1RC_0RC1LA p j' Ev).
      exact (srun_sound tm true true chb_0RB0LD_1RC1RB_1LD1RC_0RC1LA B0_0RB0LD_1RC1RB_1LD1RC_0RC1LA BB1_0RB0LD_1RC1RB_1LD1RC_0RC1LA 4 6
               run_boot_0RB0LD_1RC1RB_1LD1RC_0RC1LA [] [] j' ltac:(reflexivity) ltac:(reflexivity)).
    + assert (HB : exists n, stepn tm n (lift (CinM MT (fill (pow2 (S j')))))
                   = Some (lift (Cc (Pos.succ p)))).
      { exists (4 * S j' + 8).
        rewrite (gclb_0RB0LD_1RC1RB_1LD1RC_0RC1LA j'), <- (geo_0RB0LD_1RC1RB_1LD1RC_0RC1LA p (S j') Ev), <- (gclbx_0RB0LD_1RC1RB_1LD1RC_0RC1LA j').
        apply csteps_lift.
        exact (srun_sound tm true true chCLB_0RB0LD_1RC1RB_1LD1RC_0RC1LA CLB0_0RB0LD_1RC1RB_1LD1RC_0RC1LA CLB1_0RB0LD_1RC1RB_1LD1RC_0RC1LA
                 4 8 run_closeB_0RB0LD_1RC1RB_1LD1RC_0RC1LA [] [] (S j')
                 ltac:(reflexivity) ltac:(reflexivity)). }
      destruct (fill_hop tm CinM AMlap_0RB0LD_1RC1RB_1LD1RC_0RC1LA MT (pow2 (S j')) _ HB) as (n2 & H2).
      exists (4 * S j' + 12 + n2).
      rewrite (gcla_0RB0LD_1RC1RB_1LD1RC_0RC1LA j'), stepn_add.
      rewrite (csteps_lift _ _ _ _
        (srun_sound tm true true chCLA_0RB0LD_1RC1RB_1LD1RC_0RC1LA CLA0_0RB0LD_1RC1RB_1LD1RC_0RC1LA CLA1_0RB0LD_1RC1RB_1LD1RC_0RC1LA 4 12
           run_closeA_0RB0LD_1RC1RB_1LD1RC_0RC1LA [] [] (S j')
           ltac:(reflexivity) ltac:(reflexivity))).
      rewrite (gclab_0RB0LD_1RC1RB_1LD1RC_0RC1LA j'). exact H2.
Qed.

(** ** The INTERIOR branch, at the outer anchor *)

(** j = 0: the repeated block is absent, so the whole lap is concrete. *)
Definition Z0_0RB0LD_1RC1RB_1LD1RC_0RC1LA : sconf := mkC StD (mkS [S0;S1] [] 0 0 []) S0 (mkS [] [] 0 0 []).
Definition Z1_0RB0LD_1RC1RB_1LD1RC_0RC1LA : sconf := mkC StD (mkS [S1;S1] [] 0 0 []) S0 (mkS [] [] 0 0 []).
Definition chz_0RB0LD_1RC1RB_1LD1RC_0RC1LA : list lstep := [SWin 2].

Lemma run_z_0RB0LD_1RC1RB_1LD1RC_0RC1LA : srun tm false true chz_0RB0LD_1RC1RB_1LD1RC_0RC1LA Z0_0RB0LD_1RC1RB_1LD1RC_0RC1LA = Some (Z1_0RB0LD_1RC1RB_1LD1RC_0RC1LA, 0, 2).
Proof. vm_compute. reflexivity. Qed.

(** j = S j': one copy of the unit sits in the PREFIX, so the head always has
    a concrete cell to step onto. *)
Definition P0_0RB0LD_1RC1RB_1LD1RC_0RC1LA : sconf := mkC StD (mkS [S1;S1] [S1;S1] 1 0 [S0;S1]) S0 (mkS [] [] 0 0 []).
Definition P1_0RB0LD_1RC1RB_1LD1RC_0RC1LA : sconf := mkC StD (mkS [S0;S1] [S0;S1] 1 0 [S1;S1]) S0 (mkS [] [] 0 0 []).
Definition chp_0RB0LD_1RC1RB_1LD1RC_0RC1LA : list lstep := [SWin 2; SCycL 2 0; SWin 2; SCycR 2; SWin 2].

Lemma run_p_0RB0LD_1RC1RB_1LD1RC_0RC1LA : srun tm false true chp_0RB0LD_1RC1RB_1LD1RC_0RC1LA P0_0RB0LD_1RC1RB_1LD1RC_0RC1LA = Some (P1_0RB0LD_1RC1RB_1LD1RC_0RC1LA, 4, 6).
Proof. vm_compute. reflexivity. Qed.

Lemma gz_0RB0LD_1RC1RB_1LD1RC_0RC1LA : forall p q0, cview p = (0, Some q0) ->
  Cc p = cden (Ap_Alph_01_11_011 q0 ++ [S0]) [] 0 Z0_0RB0LD_1RC1RB_1LD1RC_0RC1LA /\
  cden (Ap_Alph_01_11_011 q0 ++ [S0]) [] 0 Z1_0RB0LD_1RC1RB_1LD1RC_0RC1LA = Cc (Pos.succ p).
Proof.
  intros p q0 E. destruct (Alph_01_11_011.cview_some_Alph_01_11_011 p 0 q0 E) as (H1 & H2).
  unfold Cc_0RB0LD_1RC1RB_1LD1RC_0RC1LA, cden, Z0_0RB0LD_1RC1RB_1LD1RC_0RC1LA, Z1_0RB0LD_1RC1RB_1LD1RC_0RC1LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  split.
  - rewrite H1; cbn [rep app]. first [ rewrite <- app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
  - rewrite H2; cbn [rep app]. first [ rewrite <- app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma gp_0RB0LD_1RC1RB_1LD1RC_0RC1LA : forall p j q0, cview p = (S j, Some q0) ->
  Cc p = cden (Ap_Alph_01_11_011 q0 ++ [S0]) [] j P0_0RB0LD_1RC1RB_1LD1RC_0RC1LA /\
  cden (Ap_Alph_01_11_011 q0 ++ [S0]) [] j P1_0RB0LD_1RC1RB_1LD1RC_0RC1LA = Cc (Pos.succ p).
Proof.
  intros p j q0 E. destruct (Alph_01_11_011.cview_some_Alph_01_11_011 p (S j) q0 E) as (H1 & H2).
  unfold Cc_0RB0LD_1RC1RB_1LD1RC_0RC1LA, cden, P0_0RB0LD_1RC1RB_1LD1RC_0RC1LA, P1_0RB0LD_1RC1RB_1LD1RC_0RC1LA; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  split.
  - rewrite H1; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
  - rewrite H2; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapi_0RB0LD_1RC1RB_1LD1RC_0RC1LA : forall p j q0, cview p = (j, Some q0) ->
  exists n, 0 < n /\ csteps tm n (Cc p) = Some (Cc (Pos.succ p)).
Proof.
  intros p j q0 E. destruct j as [|j'].
  - destruct (gz_0RB0LD_1RC1RB_1LD1RC_0RC1LA p q0 E) as (HA & HB).
    exists (0 * 0 + 2). split; [lia|].
    rewrite HA.
    rewrite (srun_sound tm false true chz_0RB0LD_1RC1RB_1LD1RC_0RC1LA Z0_0RB0LD_1RC1RB_1LD1RC_0RC1LA Z1_0RB0LD_1RC1RB_1LD1RC_0RC1LA 0 2
               run_z_0RB0LD_1RC1RB_1LD1RC_0RC1LA (Ap_Alph_01_11_011 q0 ++ [S0]) [] 0
               ltac:(discriminate) ltac:(reflexivity)).
    f_equal. exact HB.
  - destruct (gp_0RB0LD_1RC1RB_1LD1RC_0RC1LA p j' q0 E) as (HA & HB).
    exists (4 * j' + 6). split; [lia|].
    rewrite HA.
    rewrite (srun_sound tm false true chp_0RB0LD_1RC1RB_1LD1RC_0RC1LA P0_0RB0LD_1RC1RB_1LD1RC_0RC1LA P1_0RB0LD_1RC1RB_1LD1RC_0RC1LA 4 6
               run_p_0RB0LD_1RC1RB_1LD1RC_0RC1LA (Ap_Alph_01_11_011 q0 ++ [S0]) [] j'
               ltac:(discriminate) ltac:(reflexivity)).
    f_equal. exact HB.
Qed.

(** The interior closes exactly; the cascade's plumbing runs in [lift]
    space, so restate it there. *)
Lemma lapil_0RB0LD_1RC1RB_1LD1RC_0RC1LA : forall p j q0, cview p = (j, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof.
  intros p j q0 E. destruct (lapi_0RB0LD_1RC1RB_1LD1RC_0RC1LA p j q0 E) as (n & Hn & Hr).
  exists n, (Cc (Pos.succ p)). auto.
Qed.

(** ** The lap *)

Lemma lap_0RB0LD_1RC1RB_1LD1RC_0RC1LA : forall p, exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:E. destruct oq as [q0|].
  - destruct (lapi_0RB0LD_1RC1RB_1LD1RC_0RC1LA p j q0 E) as (n & Hn & Hrun).
    exists n, (Cc (Pos.succ p)).
    split; [exact Hrun | split; [reflexivity | exact Hn]].
  - destruct (cview_pos p j E) as (j' & ->).
    exact (lapo_0RB0LD_1RC1RB_1LD1RC_0RC1LA p j' E).
Qed.

(** ** Bootstrap *)

Lemma boot_0RB0LD_1RC1RB_1LD1RC_0RC1LA : exists t0, stepn tm t0 InitES = Some (lift (Cc 2)).
Proof.
  exists 22.
  assert (H : match csteps tm 22 c0 with
              | Some c => ceqb c (Cc 2) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 22 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** ** Visits

    Both hosts run at the REINDEXED anchor, so each covers j = S j' and the
    p = 1 anchor (whose overflow has no cascade) gets a concrete [visz_].
    Three states fire in the BOOT chain; the fourth fires only in the CLOSE,
    which is reached from the boot through the whole descent -- exponentially
    many counts across every level -- by [cascade_vis].  The per-level chain is
    not a host: at j' = 0 the descent is empty, so a witness inside it would
    not be universal. *)

Lemma viso_0RB0LD_1RC1RB_1LD1RC_0RC1LA : forall (l : list lstep) (q : St),
  srun_st tm true true l B0_0RB0LD_1RC1RB_1LD1RC_0RC1LA = Some q ->
  forall p j, cview p = (S (S j), None) ->
  exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros l q Hst p j E.
  apply (vis_of_run tm Cc true true l B0_0RB0LD_1RC1RB_1LD1RC_0RC1LA p j [] []);
    [exact Hst | reflexivity | reflexivity | exact (gso_0RB0LD_1RC1RB_1LD1RC_0RC1LA p j E)].
Qed.

Lemma visc_0RB0LD_1RC1RB_1LD1RC_0RC1LA : forall (l : list lstep) (q : St),
  srun_st tm true true l CLA0_0RB0LD_1RC1RB_1LD1RC_0RC1LA = Some q ->
  forall p j, cview p = (S (S j), None) ->
  exists k e, stepn tm k (lift (Cc p)) = Some e /\ fst e = q.
Proof.
  intros l q Hst p j Ev.
  apply (cascade_vis tm Cc Dc hstep_0RB0LD_1RC1RB_1LD1RC_0RC1LA q p j 0).
  - exists (4 * j + 6), (cden [] [] j BB1_0RB0LD_1RC1RB_1LD1RC_0RC1LA).
    split; [| exact (gbo_0RB0LD_1RC1RB_1LD1RC_0RC1LA j)].
    rewrite (gso_0RB0LD_1RC1RB_1LD1RC_0RC1LA p j Ev).
    exact (srun_sound tm true true chb_0RB0LD_1RC1RB_1LD1RC_0RC1LA B0_0RB0LD_1RC1RB_1LD1RC_0RC1LA BB1_0RB0LD_1RC1RB_1LD1RC_0RC1LA 4 6
             run_boot_0RB0LD_1RC1RB_1LD1RC_0RC1LA [] [] j ltac:(reflexivity) ltac:(reflexivity)).
  - rewrite gcla_0RB0LD_1RC1RB_1LD1RC_0RC1LA.
    destruct (vis_of_run tm (fun _ => cden [] [] (S j) CLA0_0RB0LD_1RC1RB_1LD1RC_0RC1LA) true true l
                CLA0_0RB0LD_1RC1RB_1LD1RC_0RC1LA 1%positive (S j) [] [] q Hst
                ltac:(reflexivity) ltac:(reflexivity) eq_refl)
      as (k & c & Hk & Hq).
    exists k, (lift c).
    split; [apply csteps_lift; exact Hk | rewrite lift_state; exact Hq].
Qed.

(** State StA's visit witness at the reindex's p = 1 case -- concrete. *)
Lemma visz_StA_0RB0LD_1RC1RB_1LD1RC_0RC1LA : exists k c, csteps tm k (Cc 1) = Some c /\ fst c = StA.
Proof. exists 8. eexists. split; [vm_compute; reflexivity | reflexivity]. Qed.

(** State StB's visit witness at the reindex's p = 1 case -- concrete. *)
Lemma visz_StB_0RB0LD_1RC1RB_1LD1RC_0RC1LA : exists k c, csteps tm k (Cc 1) = Some c /\ fst c = StB.
Proof. exists 11. eexists. split; [vm_compute; reflexivity | reflexivity]. Qed.

(** State StC's visit witness at the reindex's p = 1 case -- concrete. *)
Lemma visz_StC_0RB0LD_1RC1RB_1LD1RC_0RC1LA : exists k c, csteps tm k (Cc 1) = Some c /\ fst c = StC.
Proof. exists 1. eexists. split; [vm_compute; reflexivity | reflexivity]. Qed.

(** State StD's visit witness at the reindex's p = 1 case -- concrete. *)
Lemma visz_StD_0RB0LD_1RC1RB_1LD1RC_0RC1LA : exists k c, csteps tm k (Cc 1) = Some c /\ fst c = StD.
Proof. exists 0. eexists. split; [vm_compute; reflexivity | reflexivity]. Qed.

Lemma vis_0RB0LD_1RC1RB_1LD1RC_0RC1LA : forall p q,
  exists k e, stepn tm k (lift (Cc p)) = Some e /\ fst e = q.
Proof.
  intros p q.
  destruct q.
  - (* StA: fires in the boot chain *)
    apply (vis_via_ovf_lift tm Cc lapil_0RB0LD_1RC1RB_1LD1RC_0RC1LA StA).
    intros p1 j1 E1. destruct j1 as [|j1'].
    + rewrite (cview_none_shape p1 0 E1).
      apply (vis_lift_of_csteps tm Cc). exact visz_StA_0RB0LD_1RC1RB_1LD1RC_0RC1LA.
    + apply (vis_lift_of_csteps tm Cc).
      apply (viso_0RB0LD_1RC1RB_1LD1RC_0RC1LA [SRotL 1; SWin 1; SCycL 2 0; SWin 4] StA ltac:(vm_compute; reflexivity)
                   p1 j1' E1).
  - (* StB: fires only in the close, reached through the whole descent *)
    apply (vis_via_ovf_lift tm Cc lapil_0RB0LD_1RC1RB_1LD1RC_0RC1LA StB).
    intros p1 j1 E1. destruct j1 as [|j1'].
    + rewrite (cview_none_shape p1 0 E1).
      apply (vis_lift_of_csteps tm Cc). exact visz_StB_0RB0LD_1RC1RB_1LD1RC_0RC1LA.
    + apply (visc_0RB0LD_1RC1RB_1LD1RC_0RC1LA [SWin 5; SCycL 2 0; SWinL 2; SCycR 2; SWin 4] StB ltac:(vm_compute; reflexivity)
                 p1 j1' E1).
  - (* StC: fires in the boot chain *)
    apply (vis_via_ovf_lift tm Cc lapil_0RB0LD_1RC1RB_1LD1RC_0RC1LA StC).
    intros p1 j1 E1. destruct j1 as [|j1'].
    + rewrite (cview_none_shape p1 0 E1).
      apply (vis_lift_of_csteps tm Cc). exact visz_StC_0RB0LD_1RC1RB_1LD1RC_0RC1LA.
    + apply (vis_lift_of_csteps tm Cc).
      apply (viso_0RB0LD_1RC1RB_1LD1RC_0RC1LA [SRotL 1; SWin 1] StC ltac:(vm_compute; reflexivity)
                   p1 j1' E1).
  - (* StD: fires in the boot chain *)
    apply (vis_via_ovf_lift tm Cc lapil_0RB0LD_1RC1RB_1LD1RC_0RC1LA StD).
    intros p1 j1 E1. destruct j1 as [|j1'].
    + rewrite (cview_none_shape p1 0 E1).
      apply (vis_lift_of_csteps tm Cc). exact visz_StD_0RB0LD_1RC1RB_1LD1RC_0RC1LA.
    + apply (vis_lift_of_csteps tm Cc).
      apply (viso_0RB0LD_1RC1RB_1LD1RC_0RC1LA [] StD ltac:(vm_compute; reflexivity)
                   p1 j1' E1).
Qed.

(** The interior lap closes only up to [lift] (one trailing blank past the
    anchor's far side), so the closer is [LapCertGlueLift.glue_neverqh_lift]:
    [LapGlue.glue_neverqh] with the visit premise in [stepn] space, which is
    what its own proof consumes. *)
Theorem nqhm_0RB0LD_1RC1RB_1LD1RC_0RC1LA : NeverQuasiHaltsSt tm.
Proof. apply (glue_neverqh_lift tm Cc 2). - exact boot_0RB0LD_1RC1RB_1LD1RC_0RC1LA. - intros p _. apply lap_0RB0LD_1RC1RB_1LD1RC_0RC1LA. - intros p q _. apply vis_0RB0LD_1RC1RB_1LD1RC_0RC1LA. Qed.

Theorem nqh_0RB0LD_1RC1RB_1LD1RC_0RC1LA : NeverQuasiHaltsSt tm_0RB0LD_1RC1RB_1LD1RC_0RC1LA.
Proof. apply (mirror_never_qh tm_0RB0LD_1RC1RB_1LD1RC_0RC1LA). rewrite mirror_ok_0RB0LD_1RC1RB_1LD1RC_0RC1LA. exact nqhm_0RB0LD_1RC1RB_1LD1RC_0RC1LA. Qed.

Theorem nonhalt_0RB0LD_1RC1RB_1LD1RC_0RC1LA : NonHalt tm_0RB0LD_1RC1RB_1LD1RC_0RC1LA.
Proof. apply never_qh_nonhalt, nqh_0RB0LD_1RC1RB_1LD1RC_0RC1LA. Qed.
