(** * CASB_1RB1RC_0RC1LD_1LB1RC_0RA0LB: machine 1RB1RC_0RC1LD_1LB1RC_0RA0LB, boarded by the SOLO CASCADE route.

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

    Differential validation before emission: solo cascade: p=1 concrete (24 steps) + 7 overflow phases, j = 2..8 (35 levels, 42 counts, 1475 inner laps).

    Axiom footprint: [functional_extensionality_dep] only. *)

From Coq Require Import Arith Lia Bool List PArith Wellfounded.
From BBB4 Require Import BBB4_Statement CTape Mirror.
From Coq Require Import FunctionalExtensionality.
From BBB4.Counters Require Import WTape MonoCounter JpCounter IXPGadgets
                                  LapCertGlue LapCertGlueLift NestedLap
                                  NestedLapLift NestedLapCascade Alph_01_11_011 Alph_10_11_1.
From BBB4.Checkers Require Import LapDecider.
Import ListNotations.

Definition mk_1RB1RC_0RC1LD_1LB1RC_0RA0LB (w : Sym) (d : Dir) (n : St) : option Trans :=
  Some (mkTrans w d n).
Local Notation mk := mk_1RB1RC_0RC1LD_1LB1RC_0RA0LB.

(** 1RB1RC_0RC1LD_1LB1RC_0RA0LB -- the table every lemma below runs on. *)
(** 1RB1RC_0RC1LD_1LB1RC_0RA0LB -- the real machine (its counter grows RIGHT). *)
Definition tm_1RB1RC_0RC1LD_1LB1RC_0RA0LB : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S1 DR StC
  | StB, S0 => mk S0 DR StC | StB, S1 => mk S1 DL StD
  | StC, S0 => mk S1 DL StB | StC, S1 => mk S1 DR StC
  | StD, S0 => mk S0 DR StA | StD, S1 => mk S0 DL StB end.

(** Its mirror 1LB1LC_0LC1RD_1RB1LC_0LA0RB: the same counter grown leftward.  Every
    lemma below runs on the MIRRORED table;
    [Mirror.mirror_never_qh] transfers the conclusion back. *)
Definition tmm_1RB1RC_0RC1LD_1LB1RC_0RA0LB : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DL StB | StA, S1 => mk S1 DL StC
  | StB, S0 => mk S0 DL StC | StB, S1 => mk S1 DR StD
  | StC, S0 => mk S1 DR StB | StC, S1 => mk S1 DL StC
  | StD, S0 => mk S0 DL StA | StD, S1 => mk S0 DR StB end.
Local Notation tm := tmm_1RB1RC_0RC1LD_1LB1RC_0RA0LB.

Lemma mirror_ok_1RB1RC_0RC1LD_1LB1RC_0RA0LB : mirror_tm tm_1RB1RC_0RC1LD_1LB1RC_0RA0LB = tmm_1RB1RC_0RC1LD_1LB1RC_0RA0LB.
Proof.
  apply functional_extensionality; intro q;
    apply functional_extensionality; intro b; destruct q, b; reflexivity.
Qed.

Definition Cc_1RB1RC_0RC1LD_1LB1RC_0RA0LB (p : positive) : cconf := (StB, (Ap_Alph_01_11_011 p ++ [S0], S0, [S1])).
Local Notation Cc := Cc_1RB1RC_0RC1LD_1LB1RC_0RA0LB.

(** A chain accepted up to [lift] can stop a blank past the anchor.  Every
    landing bridge below ends here, so it is stated before the first of them. *)
Lemma lbl_1RB1RC_0RC1LD_1LB1RC_0RA0LB : forall q l h r, lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.


(** ** The LEVEL family, at an ARBITRARY tail

    [T] is the cascade's growing region.  The counter's own laps never read it,
    so quantifying over it costs nothing and buys every level at once. *)
Definition Cin_1RB1RC_0RC1LD_1LB1RC_0RA0LB (T : list Sym) (v : positive) : cconf :=
  (StB, (Ap_Alph_01_11_011 v ++ T, S0, [S1])).
Local Notation Cin := Cin_1RB1RC_0RC1LD_1LB1RC_0RA0LB.

Definition Uc_1RB1RC_0RC1LD_1LB1RC_0RA0LB : list Sym := [S1;S1].
Local Notation Uc := Uc_1RB1RC_0RC1LD_1LB1RC_0RA0LB.

(** The tail level [l] carries, as a function of [m], the units beyond the top
    level's.  One unit longer per level down. *)
Definition TB_1RB1RC_0RC1LD_1LB1RC_0RA0LB (m : nat) : list Sym := [] ++ rep Uc (m + 1).
Local Notation TB := TB_1RB1RC_0RC1LD_1LB1RC_0RA0LB.

(** The level-[l] entry configuration.  Both indices are explicit and both are
    built by [S]: one index would force [j - l] into an anchor, which is the
    wave-15 index-shift trap. *)
Definition Dc_1RB1RC_0RC1LD_1LB1RC_0RA0LB (l m : nat) : cconf := Cin (TB m) (pow2 l).
Local Notation Dc := Dc_1RB1RC_0RC1LD_1LB1RC_0RA0LB.

Lemma epow2_1RB1RC_0RC1LD_1LB1RC_0RA0LB : forall n, Ap_Alph_01_11_011 (pow2 n) = rep [S0;S1] n ++ [S0;S1;S1].
Proof. induction n; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.

Lemma efill_1RB1RC_0RC1LD_1LB1RC_0RA0LB : forall n, Ap_Alph_01_11_011 (fill (pow2 n)) = rep [S1;S1] n ++ [S0;S1;S1].
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
Definition AIZ0_1RB1RC_0RC1LD_1LB1RC_0RA0LB : sconf := mkC StB (mkS [S0;S1] [] 0 0 []) S0 (mkS [S1] [] 0 0 []).
Definition AIZ1_1RB1RC_0RC1LD_1LB1RC_0RA0LB : sconf := mkC StB (mkS [S1;S1] [] 0 0 []) S0 (mkS [S1] [] 0 0 []).
Definition AIzc_1RB1RC_0RC1LD_1LB1RC_0RA0LB : list lstep := [SWin 2].

Lemma run_AIz_1RB1RC_0RC1LD_1LB1RC_0RA0LB :
  srun tm false true AIzc_1RB1RC_0RC1LD_1LB1RC_0RA0LB AIZ0_1RB1RC_0RC1LD_1LB1RC_0RA0LB = Some (AIZ1_1RB1RC_0RC1LD_1LB1RC_0RA0LB, 0, 2).
Proof. vm_compute. reflexivity. Qed.

Definition AIP0_1RB1RC_0RC1LD_1LB1RC_0RA0LB : sconf := mkC StB (mkS [S1;S1] [S1;S1] 1 0 [S0;S1]) S0 (mkS [S1] [] 0 0 []).
Definition AIP1_1RB1RC_0RC1LD_1LB1RC_0RA0LB : sconf := mkC StB (mkS [S0;S1] [S0;S1] 1 0 [S1;S1]) S0 (mkS [S1] [] 0 0 []).
Definition AIpc_1RB1RC_0RC1LD_1LB1RC_0RA0LB : list lstep := [SWin 2; SCycL 2 0; SWin 2; SCycR 2; SWin 2].

Lemma run_AIp_1RB1RC_0RC1LD_1LB1RC_0RA0LB :
  srun tm false true AIpc_1RB1RC_0RC1LD_1LB1RC_0RA0LB AIP0_1RB1RC_0RC1LD_1LB1RC_0RA0LB = Some (AIP1_1RB1RC_0RC1LD_1LB1RC_0RA0LB, 4, 6).
Proof. vm_compute. reflexivity. Qed.

Lemma AIgz0_1RB1RC_0RC1LD_1LB1RC_0RA0LB : forall T v q0, cview v = (0%nat, Some q0) ->
  Cin T v = cden (Ap_Alph_01_11_011 q0 ++ T) [] 0 AIZ0_1RB1RC_0RC1LD_1LB1RC_0RA0LB.
Proof.
  intros T v q0 Ev. destruct (Alph_01_11_011.cview_some_Alph_01_11_011 v 0 q0 Ev) as (H1 & _).
  unfold Cin_1RB1RC_0RC1LD_1LB1RC_0RA0LB, cden, AIZ0_1RB1RC_0RC1LD_1LB1RC_0RA0LB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (0 * 0 + 0) with 0 by lia.
  rewrite H1. cbn [rep app]. rewrite ?app_nil_r. rewrite <- ?app_assoc.
  cbn [app]. rewrite ?app_nil_r. reflexivity.
Qed.

Lemma AIgz1_1RB1RC_0RC1LD_1LB1RC_0RA0LB : forall T v q0, cview v = (0%nat, Some q0) ->
  lift (cden (Ap_Alph_01_11_011 q0 ++ T) [] 0 AIZ1_1RB1RC_0RC1LD_1LB1RC_0RA0LB) = lift (Cin T (Pos.succ v)).
Proof.
  intros T v q0 Ev. destruct (Alph_01_11_011.cview_some_Alph_01_11_011 v 0 q0 Ev) as (_ & H2).
  unfold Cin_1RB1RC_0RC1LD_1LB1RC_0RA0LB, cden, AIZ1_1RB1RC_0RC1LD_1LB1RC_0RA0LB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (0 * 0 + 0) with 0 by lia.
  rewrite H2. cbn [rep app]. rewrite ?app_nil_r. rewrite <- ?app_assoc.
  cbn [app]. rewrite ?app_nil_r.
  rewrite ?lift_app_blank. rewrite <- ?app_assoc. reflexivity.
Qed.

Lemma AIgp0_1RB1RC_0RC1LD_1LB1RC_0RA0LB : forall T v i q0, cview v = (S i, Some q0) ->
  Cin T v = cden (Ap_Alph_01_11_011 q0 ++ T) [] i AIP0_1RB1RC_0RC1LD_1LB1RC_0RA0LB.
Proof.
  intros T v i q0 Ev. destruct (Alph_01_11_011.cview_some_Alph_01_11_011 v (S i) q0 Ev) as (H1 & _).
  unfold Cin_1RB1RC_0RC1LD_1LB1RC_0RA0LB, cden, AIP0_1RB1RC_0RC1LD_1LB1RC_0RA0LB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia. replace (0 * i + 0) with 0 by lia.
  rewrite H1. cbn [rep app]. rewrite ?app_nil_r. rewrite <- ?app_assoc.
  cbn [app]. rewrite ?app_nil_r. reflexivity.
Qed.

Lemma AIgp1_1RB1RC_0RC1LD_1LB1RC_0RA0LB : forall T v i q0, cview v = (S i, Some q0) ->
  lift (cden (Ap_Alph_01_11_011 q0 ++ T) [] i AIP1_1RB1RC_0RC1LD_1LB1RC_0RA0LB) = lift (Cin T (Pos.succ v)).
Proof.
  intros T v i q0 Ev. destruct (Alph_01_11_011.cview_some_Alph_01_11_011 v (S i) q0 Ev) as (_ & H2).
  unfold Cin_1RB1RC_0RC1LD_1LB1RC_0RA0LB, cden, AIP1_1RB1RC_0RC1LD_1LB1RC_0RA0LB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia. replace (0 * i + 0) with 0 by lia.
  rewrite H2. cbn [rep app]. rewrite ?app_nil_r. rewrite <- ?app_assoc.
  cbn [app]. rewrite ?app_nil_r.
  rewrite ?lift_app_blank. rewrite <- ?app_assoc. reflexivity.
Qed.

(** The lap, up to [lift] and at every tail at once -- [NestedLapCascade]'s [Hin] for the levels. *)
Lemma AIlap_1RB1RC_0RC1LD_1LB1RC_0RA0LB : forall T v i q0, cview v = (i, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cin T v) = Some c'
               /\ lift c' = lift (Cin T (Pos.succ v)).
Proof.
  intros T v i q0 Ev. destruct i as [|i'].
  - exists (0 * 0 + 2), (cden (Ap_Alph_01_11_011 q0 ++ T) [] 0 AIZ1_1RB1RC_0RC1LD_1LB1RC_0RA0LB).
    split; [lia|]. split; [| exact (AIgz1_1RB1RC_0RC1LD_1LB1RC_0RA0LB T v q0 Ev)].
    rewrite (AIgz0_1RB1RC_0RC1LD_1LB1RC_0RA0LB T v q0 Ev).
    exact (srun_sound tm false true AIzc_1RB1RC_0RC1LD_1LB1RC_0RA0LB AIZ0_1RB1RC_0RC1LD_1LB1RC_0RA0LB AIZ1_1RB1RC_0RC1LD_1LB1RC_0RA0LB
             0 2 run_AIz_1RB1RC_0RC1LD_1LB1RC_0RA0LB (Ap_Alph_01_11_011 q0 ++ T) [] 0
             ltac:(discriminate) ltac:(reflexivity)).
  - exists (4 * i' + 6), (cden (Ap_Alph_01_11_011 q0 ++ T) [] i' AIP1_1RB1RC_0RC1LD_1LB1RC_0RA0LB).
    split; [lia|]. split; [| exact (AIgp1_1RB1RC_0RC1LD_1LB1RC_0RA0LB T v i' q0 Ev)].
    rewrite (AIgp0_1RB1RC_0RC1LD_1LB1RC_0RA0LB T v i' q0 Ev).
    exact (srun_sound tm false true AIpc_1RB1RC_0RC1LD_1LB1RC_0RA0LB AIP0_1RB1RC_0RC1LD_1LB1RC_0RA0LB AIP1_1RB1RC_0RC1LD_1LB1RC_0RA0LB
             4 6 run_AIp_1RB1RC_0RC1LD_1LB1RC_0RA0LB (Ap_Alph_01_11_011 q0 ++ T) [] i'
             ltac:(discriminate) ltac:(reflexivity)).
Qed.

(** ** The MAIN count's family

    The count the phase ends on is in a DIFFERENT digit alphabet from the
    levels', at a different state and a different far side -- the two words are
    genuinely different encodings of the same value, which is why WAVE26 read
    the descent between them as a re-encoding pass over one word.  It is stated
    tail-parametrically too, purely so [fill_hop] applies to it unchanged. *)
Definition CinM_1RB1RC_0RC1LD_1LB1RC_0RA0LB (T : list Sym) (v : positive) : cconf :=
  (StD, (Ap_Alph_10_11_1 v ++ T, S0, [S1])).
Local Notation CinM := CinM_1RB1RC_0RC1LD_1LB1RC_0RA0LB.

Definition MT_1RB1RC_0RC1LD_1LB1RC_0RA0LB : list Sym := [S1].
Local Notation MT := MT_1RB1RC_0RC1LD_1LB1RC_0RA0LB.

Lemma epow2m_1RB1RC_0RC1LD_1LB1RC_0RA0LB : forall n, Ap_Alph_10_11_1 (pow2 n) = rep [S1;S0] n ++ [S1].
Proof. induction n; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.

Lemma efillm_1RB1RC_0RC1LD_1LB1RC_0RA0LB : forall n, Ap_Alph_10_11_1 (fill (pow2 n)) = rep [S1;S1] n ++ [S1].
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
Definition AMZ0_1RB1RC_0RC1LD_1LB1RC_0RA0LB : sconf := mkC StD (mkS [S1;S0] [] 0 0 []) S0 (mkS [S1] [] 0 0 []).
Definition AMZ1_1RB1RC_0RC1LD_1LB1RC_0RA0LB : sconf := mkC StD (mkS [S1;S1] [] 0 0 []) S0 (mkS [S1] [] 0 0 []).
Definition AMzc_1RB1RC_0RC1LD_1LB1RC_0RA0LB : list lstep := [SWin 4].

Lemma run_AMz_1RB1RC_0RC1LD_1LB1RC_0RA0LB :
  srun tm false true AMzc_1RB1RC_0RC1LD_1LB1RC_0RA0LB AMZ0_1RB1RC_0RC1LD_1LB1RC_0RA0LB = Some (AMZ1_1RB1RC_0RC1LD_1LB1RC_0RA0LB, 0, 4).
Proof. vm_compute. reflexivity. Qed.

Definition AMP0_1RB1RC_0RC1LD_1LB1RC_0RA0LB : sconf := mkC StD (mkS [S1;S1] [S1;S1] 1 0 [S1;S0]) S0 (mkS [S1] [] 0 0 []).
Definition AMP1_1RB1RC_0RC1LD_1LB1RC_0RA0LB : sconf := mkC StD (mkS [S1;S0] [S1;S0] 1 0 [S1;S1]) S0 (mkS [S1] [] 0 0 []).
Definition AMpc_1RB1RC_0RC1LD_1LB1RC_0RA0LB : list lstep := [SWin 2; SCycL 2 0; SWin 4; SCycR 2; SWin 2].

Lemma run_AMp_1RB1RC_0RC1LD_1LB1RC_0RA0LB :
  srun tm false true AMpc_1RB1RC_0RC1LD_1LB1RC_0RA0LB AMP0_1RB1RC_0RC1LD_1LB1RC_0RA0LB = Some (AMP1_1RB1RC_0RC1LD_1LB1RC_0RA0LB, 4, 8).
Proof. vm_compute. reflexivity. Qed.

Lemma AMgz0_1RB1RC_0RC1LD_1LB1RC_0RA0LB : forall T v q0, cview v = (0%nat, Some q0) ->
  CinM T v = cden (Ap_Alph_10_11_1 q0 ++ T) [] 0 AMZ0_1RB1RC_0RC1LD_1LB1RC_0RA0LB.
Proof.
  intros T v q0 Ev. destruct (Alph_10_11_1.cview_some_Alph_10_11_1 v 0 q0 Ev) as (H1 & _).
  unfold CinM_1RB1RC_0RC1LD_1LB1RC_0RA0LB, cden, AMZ0_1RB1RC_0RC1LD_1LB1RC_0RA0LB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (0 * 0 + 0) with 0 by lia.
  rewrite H1. cbn [rep app]. rewrite ?app_nil_r. rewrite <- ?app_assoc.
  cbn [app]. rewrite ?app_nil_r. reflexivity.
Qed.

Lemma AMgz1_1RB1RC_0RC1LD_1LB1RC_0RA0LB : forall T v q0, cview v = (0%nat, Some q0) ->
  lift (cden (Ap_Alph_10_11_1 q0 ++ T) [] 0 AMZ1_1RB1RC_0RC1LD_1LB1RC_0RA0LB) = lift (CinM T (Pos.succ v)).
Proof.
  intros T v q0 Ev. destruct (Alph_10_11_1.cview_some_Alph_10_11_1 v 0 q0 Ev) as (_ & H2).
  unfold CinM_1RB1RC_0RC1LD_1LB1RC_0RA0LB, cden, AMZ1_1RB1RC_0RC1LD_1LB1RC_0RA0LB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (0 * 0 + 0) with 0 by lia.
  rewrite H2. cbn [rep app]. rewrite ?app_nil_r. rewrite <- ?app_assoc.
  cbn [app]. rewrite ?app_nil_r.
  rewrite ?lift_app_blank. rewrite <- ?app_assoc. reflexivity.
Qed.

Lemma AMgp0_1RB1RC_0RC1LD_1LB1RC_0RA0LB : forall T v i q0, cview v = (S i, Some q0) ->
  CinM T v = cden (Ap_Alph_10_11_1 q0 ++ T) [] i AMP0_1RB1RC_0RC1LD_1LB1RC_0RA0LB.
Proof.
  intros T v i q0 Ev. destruct (Alph_10_11_1.cview_some_Alph_10_11_1 v (S i) q0 Ev) as (H1 & _).
  unfold CinM_1RB1RC_0RC1LD_1LB1RC_0RA0LB, cden, AMP0_1RB1RC_0RC1LD_1LB1RC_0RA0LB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia. replace (0 * i + 0) with 0 by lia.
  rewrite H1. cbn [rep app]. rewrite ?app_nil_r. rewrite <- ?app_assoc.
  cbn [app]. rewrite ?app_nil_r. reflexivity.
Qed.

Lemma AMgp1_1RB1RC_0RC1LD_1LB1RC_0RA0LB : forall T v i q0, cview v = (S i, Some q0) ->
  lift (cden (Ap_Alph_10_11_1 q0 ++ T) [] i AMP1_1RB1RC_0RC1LD_1LB1RC_0RA0LB) = lift (CinM T (Pos.succ v)).
Proof.
  intros T v i q0 Ev. destruct (Alph_10_11_1.cview_some_Alph_10_11_1 v (S i) q0 Ev) as (_ & H2).
  unfold CinM_1RB1RC_0RC1LD_1LB1RC_0RA0LB, cden, AMP1_1RB1RC_0RC1LD_1LB1RC_0RA0LB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia. replace (0 * i + 0) with 0 by lia.
  rewrite H2. cbn [rep app]. rewrite ?app_nil_r. rewrite <- ?app_assoc.
  cbn [app]. rewrite ?app_nil_r.
  rewrite ?lift_app_blank. rewrite <- ?app_assoc. reflexivity.
Qed.

(** The lap, up to [lift] and at every tail at once -- [fill_hop]'s [Hin] for the closing count. *)
Lemma AMlap_1RB1RC_0RC1LD_1LB1RC_0RA0LB : forall T v i q0, cview v = (i, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (CinM T v) = Some c'
               /\ lift c' = lift (CinM T (Pos.succ v)).
Proof.
  intros T v i q0 Ev. destruct i as [|i'].
  - exists (0 * 0 + 4), (cden (Ap_Alph_10_11_1 q0 ++ T) [] 0 AMZ1_1RB1RC_0RC1LD_1LB1RC_0RA0LB).
    split; [lia|]. split; [| exact (AMgz1_1RB1RC_0RC1LD_1LB1RC_0RA0LB T v q0 Ev)].
    rewrite (AMgz0_1RB1RC_0RC1LD_1LB1RC_0RA0LB T v q0 Ev).
    exact (srun_sound tm false true AMzc_1RB1RC_0RC1LD_1LB1RC_0RA0LB AMZ0_1RB1RC_0RC1LD_1LB1RC_0RA0LB AMZ1_1RB1RC_0RC1LD_1LB1RC_0RA0LB
             0 4 run_AMz_1RB1RC_0RC1LD_1LB1RC_0RA0LB (Ap_Alph_10_11_1 q0 ++ T) [] 0
             ltac:(discriminate) ltac:(reflexivity)).
  - exists (4 * i' + 8), (cden (Ap_Alph_10_11_1 q0 ++ T) [] i' AMP1_1RB1RC_0RC1LD_1LB1RC_0RA0LB).
    split; [lia|]. split; [| exact (AMgp1_1RB1RC_0RC1LD_1LB1RC_0RA0LB T v i' q0 Ev)].
    rewrite (AMgp0_1RB1RC_0RC1LD_1LB1RC_0RA0LB T v i' q0 Ev).
    exact (srun_sound tm false true AMpc_1RB1RC_0RC1LD_1LB1RC_0RA0LB AMP0_1RB1RC_0RC1LD_1LB1RC_0RA0LB AMP1_1RB1RC_0RC1LD_1LB1RC_0RA0LB
             4 8 run_AMp_1RB1RC_0RC1LD_1LB1RC_0RA0LB (Ap_Alph_10_11_1 q0 ++ T) [] i'
             ltac:(discriminate) ltac:(reflexivity)).
Qed.

(** ** The four chains *)

Definition B0_1RB1RC_0RC1LD_1LB1RC_0RA0LB : sconf := mkC StB (mkS [] [S1;S1] 1 0 [S1;S1;S0;S1;S1;S0]) S0 (mkS [S1] [] 0 0 []).
Definition B1_1RB1RC_0RC1LD_1LB1RC_0RA0LB : sconf := mkC StB (mkS [] [S0;S1] 1 1 [S0;S1;S1;S0]) S0 (mkS [S1] [] 0 0 []).

(** *** boot: the outer overflow anchor -> the TOP level's count.

    The top level sits one octave DOWN, so this runs at the reindexed anchor
    [S (S j)] and its own source carries one unit PEELED out of the count --
    without the peel there is no chain at any split, the standing lesson of
    waves 24-26 applied once more. *)
Definition BB1_1RB1RC_0RC1LD_1LB1RC_0RA0LB : sconf := mkC StB (mkS [] [S0;S1] 1 0 [S0;S1;S1;S1;S1;S0]) S0 (mkS [S1] [] 0 0 []).
Definition chb_1RB1RC_0RC1LD_1LB1RC_0RA0LB : list lstep := [SRotL 1; SWin 1; SCycL 2 0; SWin 4; SCycR 2; SWin 1; SUnrotL 1].

Lemma run_boot_1RB1RC_0RC1LD_1LB1RC_0RA0LB :
  srun tm true true chb_1RB1RC_0RC1LD_1LB1RC_0RA0LB B0_1RB1RC_0RC1LD_1LB1RC_0RA0LB = Some (BB1_1RB1RC_0RC1LD_1LB1RC_0RA0LB, 4, 6).
Proof. vm_compute. reflexivity. Qed.

(** *** level (S l) fill -> level l start.  THE level step -- one count per
    level, so the whole of [NestedLapCascade.Hstep] is this chain behind a
    [fill_hop], where the gated route needs [level_hop] and two. *)
Definition DW0_1RB1RC_0RC1LD_1LB1RC_0RA0LB : sconf := mkC StB (mkS [] [S1;S1] 1 0 [S1;S1;S0]) S0 (mkS [S1] [] 0 0 []).
Definition DW1_1RB1RC_0RC1LD_1LB1RC_0RA0LB : sconf := mkC StB (mkS [] [S0;S1] 1 0 [S0;S1;S1]) S0 (mkS [S1] [] 0 0 []).
Definition chDW_1RB1RC_0RC1LD_1LB1RC_0RA0LB : list lstep := [SRotL 1; SWin 1; SCycL 2 0; SWin 4; SCycR 2; SWin 1; SUnrotL 1].

Lemma run_down_1RB1RC_0RC1LD_1LB1RC_0RA0LB :
  srun tm false true chDW_1RB1RC_0RC1LD_1LB1RC_0RA0LB DW0_1RB1RC_0RC1LD_1LB1RC_0RA0LB = Some (DW1_1RB1RC_0RC1LD_1LB1RC_0RA0LB, 4, 6).
Proof. vm_compute. reflexivity. Qed.

(** *** the close, in two halves: level 0's fill into the MAIN count's start,
    and the main count's fill out to the outer successor.  Its exponentially
    many laps live in [fill_hop] between them, so neither chain sees them. *)
Definition CLA0_1RB1RC_0RC1LD_1LB1RC_0RA0LB : sconf := mkC StB (mkS [S0;S1;S1] [S1;S1] 1 0 []) S0 (mkS [S1] [] 0 0 []).
Definition CLA1_1RB1RC_0RC1LD_1LB1RC_0RA0LB : sconf := mkC StD (mkS [] [S1;S0] 1 1 [S1;S1]) S0 (mkS [S1] [] 0 0 []).
Definition chCLA_1RB1RC_0RC1LD_1LB1RC_0RA0LB : list lstep := [SWin 5; SCycL 2 0; SWinL 2; SCycR 2; SWin 3; SUnrotL 1; SFoldL 1].

Lemma run_closeA_1RB1RC_0RC1LD_1LB1RC_0RA0LB :
  srun tm true true chCLA_1RB1RC_0RC1LD_1LB1RC_0RA0LB CLA0_1RB1RC_0RC1LD_1LB1RC_0RA0LB = Some (CLA1_1RB1RC_0RC1LD_1LB1RC_0RA0LB, 4, 10).
Proof. vm_compute. reflexivity. Qed.

Definition CLB0_1RB1RC_0RC1LD_1LB1RC_0RA0LB : sconf := mkC StD (mkS [] [S1;S1] 1 0 [S1;S1]) S0 (mkS [S1] [] 0 0 []).
Definition CLB1_1RB1RC_0RC1LD_1LB1RC_0RA0LB : sconf := mkC StB (mkS [] [S0;S1] 1 0 [S0;S1;S1]) S0 (mkS [S1] [] 0 0 []).
Definition chCLB_1RB1RC_0RC1LD_1LB1RC_0RA0LB : list lstep := [SRotL 1; SWin 1; SRotL 1; SWin 1; SCycL 2 0; SWinL 2; SCycR 2; SWin 2; SUnrotL 2].

Lemma run_closeB_1RB1RC_0RC1LD_1LB1RC_0RA0LB :
  srun tm true true chCLB_1RB1RC_0RC1LD_1LB1RC_0RA0LB CLB0_1RB1RC_0RC1LD_1LB1RC_0RA0LB = Some (CLB1_1RB1RC_0RC1LD_1LB1RC_0RA0LB, 4, 6).
Proof. vm_compute. reflexivity. Qed.

(** ** The per-level glue

    The opaque region the level chain carries, as a function of the level's
    tail length.  Every exponent is built by [S] and [+]; none is a
    subtraction. *)
Definition XDW_1RB1RC_0RC1LD_1LB1RC_0RA0LB (m : nat) : list Sym := rep Uc (2 + m).

Lemma gDWs_1RB1RC_0RC1LD_1LB1RC_0RA0LB : forall l m,
  Cin (TB m) (fill (pow2 (S l))) = cden (XDW_1RB1RC_0RC1LD_1LB1RC_0RA0LB m) [] l DW0_1RB1RC_0RC1LD_1LB1RC_0RA0LB.
Proof.
  intros l m.
  unfold Cin_1RB1RC_0RC1LD_1LB1RC_0RA0LB, TB_1RB1RC_0RC1LD_1LB1RC_0RA0LB, XDW_1RB1RC_0RC1LD_1LB1RC_0RA0LB, Uc_1RB1RC_0RC1LD_1LB1RC_0RA0LB, cden, DW0_1RB1RC_0RC1LD_1LB1RC_0RA0LB, sden;
    cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
  rewrite efill_1RB1RC_0RC1LD_1LB1RC_0RA0LB.
  replace (1 * l + 0) with (l) by lia.
  replace (0 * l + 0) with 0 by lia.
  replace (S l) with (l + 1) by lia.
  replace (m + 1) with (1 + m) by lia.
  rewrite ?rep_add. cbn [rep app]. rewrite <- ?app_assoc.
  cbn [app]. rewrite ?app_nil_r. reflexivity.
Qed.

Lemma gDWd_1RB1RC_0RC1LD_1LB1RC_0RA0LB : forall l m,
  lift (cden (XDW_1RB1RC_0RC1LD_1LB1RC_0RA0LB m) [] l DW1_1RB1RC_0RC1LD_1LB1RC_0RA0LB) = lift (Cin (TB (S m)) (pow2 l)).
Proof.
  intros l m.
  unfold Cin_1RB1RC_0RC1LD_1LB1RC_0RA0LB, TB_1RB1RC_0RC1LD_1LB1RC_0RA0LB, XDW_1RB1RC_0RC1LD_1LB1RC_0RA0LB, Uc_1RB1RC_0RC1LD_1LB1RC_0RA0LB, cden, DW1_1RB1RC_0RC1LD_1LB1RC_0RA0LB, sden;
    cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
  rewrite epow2_1RB1RC_0RC1LD_1LB1RC_0RA0LB.
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
Lemma hstep_1RB1RC_0RC1LD_1LB1RC_0RA0LB : forall l m,
  exists n, stepn tm n (lift (Dc (S l) m)) = Some (lift (Dc l (S m))).
Proof.
  intros l m. unfold Dc_1RB1RC_0RC1LD_1LB1RC_0RA0LB.
  apply (fill_hop tm Cin AIlap_1RB1RC_0RC1LD_1LB1RC_0RA0LB (TB m) (pow2 (S l))).
  exists (4 * l + 6). rewrite gDWs_1RB1RC_0RC1LD_1LB1RC_0RA0LB, <- gDWd_1RB1RC_0RC1LD_1LB1RC_0RA0LB.
  apply csteps_lift.
  exact (srun_sound tm false true chDW_1RB1RC_0RC1LD_1LB1RC_0RA0LB DW0_1RB1RC_0RC1LD_1LB1RC_0RA0LB DW1_1RB1RC_0RC1LD_1LB1RC_0RA0LB 4 6
           run_down_1RB1RC_0RC1LD_1LB1RC_0RA0LB (XDW_1RB1RC_0RC1LD_1LB1RC_0RA0LB m) [] l
           ltac:(discriminate) ltac:(reflexivity)).
Qed.

(** ** The outer glue: boot in, close out.

    [gso_] is stated at the REINDEXED anchor [S (S j)]: the top level is one
    octave below the outer index, so the generic route runs at [j = S j'] and
    the boot's source carries the peeled unit that shift leaves behind. *)
Lemma gso_1RB1RC_0RC1LD_1LB1RC_0RA0LB : forall p j, cview p = (S (S j), None) ->
  Cc p = cden [] [] j B0_1RB1RC_0RC1LD_1LB1RC_0RA0LB.
Proof.
  intros p j Ev. destruct (Alph_01_11_011.cview_none_Alph_01_11_011 p (S j) Ev) as (H1 & _).
  unfold Cc_1RB1RC_0RC1LD_1LB1RC_0RA0LB, cden, B0_1RB1RC_0RC1LD_1LB1RC_0RA0LB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia. replace (0 * j + 0) with 0 by lia.
  rewrite H1. replace (S j) with (j + 1) by lia.
  rewrite rep_add. cbn [rep app]. rewrite <- ?app_assoc. cbn [app].
  rewrite ?app_nil_r. reflexivity.
Qed.

Lemma geo_1RB1RC_0RC1LD_1LB1RC_0RA0LB : forall p j, cview p = (S j, None) ->
  lift (cden [] [] j B1_1RB1RC_0RC1LD_1LB1RC_0RA0LB) = lift (Cc (Pos.succ p)).
Proof.
  intros p j Ev. destruct (Alph_01_11_011.cview_none_Alph_01_11_011 p j Ev) as (_ & H2).
  unfold Cc_1RB1RC_0RC1LD_1LB1RC_0RA0LB, cden, B1_1RB1RC_0RC1LD_1LB1RC_0RA0LB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 1) with (S j) by lia. replace (0 * j + 0) with 0 by lia.
  rewrite H2. cbn [rep app]. rewrite <- ?app_assoc. cbn [app].
  rewrite ?app_nil_r. rewrite ?lift_app_blank. reflexivity.
Qed.

(** The boot lands on the top level's count, up to 1/0 trailing
    blanks -- the [lift] leniency [NestedLapLift] measured to be the binding
    one on this whole bucket. *)
Lemma gbo_1RB1RC_0RC1LD_1LB1RC_0RA0LB : forall j, lift (cden [] [] j BB1_1RB1RC_0RC1LD_1LB1RC_0RA0LB) = lift (Dc j 0).
Proof.
  intro j.
  assert (HD : cden [] [] j BB1_1RB1RC_0RC1LD_1LB1RC_0RA0LB = (StB, ((rep [S0;S1] j ++ [S0;S1;S1;S1;S1]) ++ [S0], S0, [S1]))).
  { unfold cden, BB1_1RB1RC_0RC1LD_1LB1RC_0RA0LB, sden;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with (j) by lia.
  replace (0 * j + 0) with 0 by lia.
    rewrite ?rep_add. cbn [rep app]. rewrite <- ?app_assoc.
    cbn [app]. rewrite ?app_nil_r. reflexivity. }
  assert (HC : Dc j 0 = (StB, (rep [S0;S1] j ++ [S0;S1;S1;S1;S1], S0, [S1]))).
  { unfold Dc_1RB1RC_0RC1LD_1LB1RC_0RA0LB, Cin_1RB1RC_0RC1LD_1LB1RC_0RA0LB, TB_1RB1RC_0RC1LD_1LB1RC_0RA0LB, Uc_1RB1RC_0RC1LD_1LB1RC_0RA0LB. rewrite epow2_1RB1RC_0RC1LD_1LB1RC_0RA0LB.
    replace (0 + 1) with 1 by lia.
    cbn [rep app]. rewrite <- ?app_assoc. cbn [app]. rewrite ?app_nil_r.
    reflexivity. }
  rewrite HD, HC. rewrite ?lbl_1RB1RC_0RC1LD_1LB1RC_0RA0LB. rewrite ?lift_app_blank. reflexivity.
Qed.

(** The close starts from level 0, whose tail is by then [j] units past the top
    level's -- so unlike the level chain it is indexed by the OUTER index. *)
Lemma gcla_1RB1RC_0RC1LD_1LB1RC_0RA0LB : forall j, Dc 0 (j + 0) = cden [] [] (S j) CLA0_1RB1RC_0RC1LD_1LB1RC_0RA0LB.
Proof.
  intro j.
  unfold Dc_1RB1RC_0RC1LD_1LB1RC_0RA0LB, Cin_1RB1RC_0RC1LD_1LB1RC_0RA0LB, TB_1RB1RC_0RC1LD_1LB1RC_0RA0LB, Uc_1RB1RC_0RC1LD_1LB1RC_0RA0LB, cden, CLA0_1RB1RC_0RC1LD_1LB1RC_0RA0LB, sden;
    cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
  rewrite (epow2_1RB1RC_0RC1LD_1LB1RC_0RA0LB 0).
  replace (1 * S j + 0) with (S j) by lia.
  replace (0 * S j + 0) with 0 by lia.
  replace (j + 0 + 1) with (S j) by lia.
  rewrite ?rep_add. cbn [pow2 rep app]. rewrite <- ?app_assoc.
  cbn [app]. rewrite ?app_nil_r. reflexivity.
Qed.

Lemma gclab_1RB1RC_0RC1LD_1LB1RC_0RA0LB : forall j,
  lift (cden [] [] (S j) CLA1_1RB1RC_0RC1LD_1LB1RC_0RA0LB) = lift (CinM MT (pow2 (S (S j)))).
Proof.
  intro j.
  assert (HD : cden [] [] (S j) CLA1_1RB1RC_0RC1LD_1LB1RC_0RA0LB = (StD, (rep [S1;S0] (S (S j)) ++ [S1;S1], S0, [S1]))).
  { unfold cden, CLA1_1RB1RC_0RC1LD_1LB1RC_0RA0LB, sden;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * S j + 1) with (1 + S j) by lia.
    replace (0 * S j + 0) with 0 by lia.
    rewrite ?rep_add. cbn [rep app]. rewrite <- ?app_assoc.
    cbn [app]. rewrite ?app_nil_r. reflexivity. }
  assert (HC : CinM MT (pow2 (S (S j))) = (StD, (rep [S1;S0] (S (S j)) ++ [S1;S1], S0, [S1]))).
  { unfold CinM_1RB1RC_0RC1LD_1LB1RC_0RA0LB, MT_1RB1RC_0RC1LD_1LB1RC_0RA0LB. rewrite epow2m_1RB1RC_0RC1LD_1LB1RC_0RA0LB.
    cbn [rep app]. rewrite <- ?app_assoc. cbn [app]. rewrite ?app_nil_r.
    reflexivity. }
  rewrite HD, HC. rewrite ?lbl_1RB1RC_0RC1LD_1LB1RC_0RA0LB. rewrite ?lift_app_blank. reflexivity.
Qed.

Lemma gclb_1RB1RC_0RC1LD_1LB1RC_0RA0LB : forall j,
  CinM MT (fill (pow2 (S (S j)))) = cden [] [] (S (S j)) CLB0_1RB1RC_0RC1LD_1LB1RC_0RA0LB.
Proof.
  intro j.
  unfold CinM_1RB1RC_0RC1LD_1LB1RC_0RA0LB, MT_1RB1RC_0RC1LD_1LB1RC_0RA0LB, cden, CLB0_1RB1RC_0RC1LD_1LB1RC_0RA0LB, sden;
    cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
  rewrite efillm_1RB1RC_0RC1LD_1LB1RC_0RA0LB.
  replace (1 * S (S j) + 0) with (S (S j)) by lia.
  replace (0 * S (S j) + 0) with 0 by lia.
  rewrite ?rep_add. cbn [rep app]. rewrite <- ?app_assoc.
  cbn [app]. rewrite ?app_nil_r. reflexivity.
Qed.

(** The main count's chain out lands on the outer successor up to trailing
    blanks; both sides normalise to the same explicit word. *)
Lemma gclbx_1RB1RC_0RC1LD_1LB1RC_0RA0LB : forall j,
  lift (cden [] [] (S (S j)) CLB1_1RB1RC_0RC1LD_1LB1RC_0RA0LB) = lift (cden [] [] (S j) B1_1RB1RC_0RC1LD_1LB1RC_0RA0LB).
Proof.
  intro j.
  assert (HD : cden [] [] (S (S j)) CLB1_1RB1RC_0RC1LD_1LB1RC_0RA0LB = (StB, (rep [S0;S1] (S (S j)) ++ [S0;S1;S1], S0, [S1]))).
  { unfold cden, CLB1_1RB1RC_0RC1LD_1LB1RC_0RA0LB, sden;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * S (S j) + 0) with (S (S j)) by lia.
    replace (0 * S (S j) + 0) with 0 by lia.
    rewrite ?rep_add. cbn [rep app]. rewrite <- ?app_assoc.
    cbn [app]. rewrite ?app_nil_r. reflexivity. }
  assert (HE : cden [] [] (S j) B1_1RB1RC_0RC1LD_1LB1RC_0RA0LB = (StB, ((rep [S0;S1] (S (S j)) ++ [S0;S1;S1]) ++ [S0], S0, [S1]))).
  { unfold cden, B1_1RB1RC_0RC1LD_1LB1RC_0RA0LB, sden;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * S j + 1) with (1 + S j) by lia.
    replace (0 * S j + 0) with 0 by lia.
    rewrite ?rep_add. cbn [rep app]. rewrite <- ?app_assoc.
    cbn [app]. rewrite ?app_nil_r. reflexivity. }
  rewrite HD, HE. rewrite ?lbl_1RB1RC_0RC1LD_1LB1RC_0RA0LB. rewrite ?lift_app_blank. reflexivity.
Qed.

(** ** The overflow branch, reindexed

    j = 0 is the p = 1 overflow and has no cascade at all: a concrete lap, the
    octave-down route's exact device. *)
Lemma lapz_1RB1RC_0RC1LD_1LB1RC_0RA0LB : exists n c', csteps tm n (Cc 1) = Some c'
  /\ lift c' = lift (Cc 2) /\ 0 < n.
Proof.
  exists 24.
  assert (H : match csteps tm 24 (Cc 1) with
              | Some c => ceqb c (Cc 2) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 24 (Cc 1)) as [c|] eqn:E0; [|discriminate].
  exists c. split; [reflexivity|]. split; [apply ceqb_lift; exact H | lia].
Qed.

Lemma lapo_1RB1RC_0RC1LD_1LB1RC_0RA0LB : forall p j, cview p = (S j, None) ->
  exists n c', csteps tm n (Cc p) = Some c'
          /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intros p j Ev.
  destruct j as [|j'].
  - rewrite (cview_none_shape p 0 Ev). exact lapz_1RB1RC_0RC1LD_1LB1RC_0RA0LB.
  - apply (cascade_overflow tm Cc Dc hstep_1RB1RC_0RC1LD_1LB1RC_0RA0LB p j' 0).
    + exists (4 * j' + 6), (cden [] [] j' BB1_1RB1RC_0RC1LD_1LB1RC_0RA0LB).
      split; [lia|]. split; [| exact (gbo_1RB1RC_0RC1LD_1LB1RC_0RA0LB j')].
      rewrite (gso_1RB1RC_0RC1LD_1LB1RC_0RA0LB p j' Ev).
      exact (srun_sound tm true true chb_1RB1RC_0RC1LD_1LB1RC_0RA0LB B0_1RB1RC_0RC1LD_1LB1RC_0RA0LB BB1_1RB1RC_0RC1LD_1LB1RC_0RA0LB 4 6
               run_boot_1RB1RC_0RC1LD_1LB1RC_0RA0LB [] [] j' ltac:(reflexivity) ltac:(reflexivity)).
    + assert (HB : exists n, stepn tm n (lift (CinM MT (fill (pow2 (S (S j'))))))
                   = Some (lift (Cc (Pos.succ p)))).
      { exists (4 * (S (S j')) + 6).
        rewrite (gclb_1RB1RC_0RC1LD_1LB1RC_0RA0LB j'), <- (geo_1RB1RC_0RC1LD_1LB1RC_0RA0LB p (S j') Ev), <- (gclbx_1RB1RC_0RC1LD_1LB1RC_0RA0LB j').
        apply csteps_lift.
        exact (srun_sound tm true true chCLB_1RB1RC_0RC1LD_1LB1RC_0RA0LB CLB0_1RB1RC_0RC1LD_1LB1RC_0RA0LB CLB1_1RB1RC_0RC1LD_1LB1RC_0RA0LB
                 4 6 run_closeB_1RB1RC_0RC1LD_1LB1RC_0RA0LB [] [] (S (S j'))
                 ltac:(reflexivity) ltac:(reflexivity)). }
      destruct (fill_hop tm CinM AMlap_1RB1RC_0RC1LD_1LB1RC_0RA0LB MT (pow2 (S (S j'))) _ HB) as (n2 & H2).
      exists (4 * S j' + 10 + n2).
      rewrite (gcla_1RB1RC_0RC1LD_1LB1RC_0RA0LB j'), stepn_add.
      rewrite (csteps_lift _ _ _ _
        (srun_sound tm true true chCLA_1RB1RC_0RC1LD_1LB1RC_0RA0LB CLA0_1RB1RC_0RC1LD_1LB1RC_0RA0LB CLA1_1RB1RC_0RC1LD_1LB1RC_0RA0LB 4 10
           run_closeA_1RB1RC_0RC1LD_1LB1RC_0RA0LB [] [] (S j')
           ltac:(reflexivity) ltac:(reflexivity))).
      rewrite (gclab_1RB1RC_0RC1LD_1LB1RC_0RA0LB j'). exact H2.
Qed.

(** ** The INTERIOR branch, at the outer anchor *)

(** j = 0: the repeated block is absent, so the whole lap is concrete. *)
Definition Z0_1RB1RC_0RC1LD_1LB1RC_0RA0LB : sconf := mkC StB (mkS [S0;S1] [] 0 0 []) S0 (mkS [S1] [] 0 0 []).
Definition Z1_1RB1RC_0RC1LD_1LB1RC_0RA0LB : sconf := mkC StB (mkS [S1;S1] [] 0 0 []) S0 (mkS [S1] [] 0 0 []).
Definition chz_1RB1RC_0RC1LD_1LB1RC_0RA0LB : list lstep := [SWin 2].

Lemma run_z_1RB1RC_0RC1LD_1LB1RC_0RA0LB : srun tm false true chz_1RB1RC_0RC1LD_1LB1RC_0RA0LB Z0_1RB1RC_0RC1LD_1LB1RC_0RA0LB = Some (Z1_1RB1RC_0RC1LD_1LB1RC_0RA0LB, 0, 2).
Proof. vm_compute. reflexivity. Qed.

(** j = S j': one copy of the unit sits in the PREFIX, so the head always has
    a concrete cell to step onto. *)
Definition P0_1RB1RC_0RC1LD_1LB1RC_0RA0LB : sconf := mkC StB (mkS [S1;S1] [S1;S1] 1 0 [S0;S1]) S0 (mkS [S1] [] 0 0 []).
Definition P1_1RB1RC_0RC1LD_1LB1RC_0RA0LB : sconf := mkC StB (mkS [S0;S1] [S0;S1] 1 0 [S1;S1]) S0 (mkS [S1] [] 0 0 []).
Definition chp_1RB1RC_0RC1LD_1LB1RC_0RA0LB : list lstep := [SWin 2; SCycL 2 0; SWin 2; SCycR 2; SWin 2].

Lemma run_p_1RB1RC_0RC1LD_1LB1RC_0RA0LB : srun tm false true chp_1RB1RC_0RC1LD_1LB1RC_0RA0LB P0_1RB1RC_0RC1LD_1LB1RC_0RA0LB = Some (P1_1RB1RC_0RC1LD_1LB1RC_0RA0LB, 4, 6).
Proof. vm_compute. reflexivity. Qed.

Lemma gz_1RB1RC_0RC1LD_1LB1RC_0RA0LB : forall p q0, cview p = (0, Some q0) ->
  Cc p = cden (Ap_Alph_01_11_011 q0 ++ [S0]) [] 0 Z0_1RB1RC_0RC1LD_1LB1RC_0RA0LB /\
  cden (Ap_Alph_01_11_011 q0 ++ [S0]) [] 0 Z1_1RB1RC_0RC1LD_1LB1RC_0RA0LB = Cc (Pos.succ p).
Proof.
  intros p q0 E. destruct (Alph_01_11_011.cview_some_Alph_01_11_011 p 0 q0 E) as (H1 & H2).
  unfold Cc_1RB1RC_0RC1LD_1LB1RC_0RA0LB, cden, Z0_1RB1RC_0RC1LD_1LB1RC_0RA0LB, Z1_1RB1RC_0RC1LD_1LB1RC_0RA0LB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  split.
  - rewrite H1; cbn [rep app]. first [ rewrite <- app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
  - rewrite H2; cbn [rep app]. first [ rewrite <- app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma gp_1RB1RC_0RC1LD_1LB1RC_0RA0LB : forall p j q0, cview p = (S j, Some q0) ->
  Cc p = cden (Ap_Alph_01_11_011 q0 ++ [S0]) [] j P0_1RB1RC_0RC1LD_1LB1RC_0RA0LB /\
  cden (Ap_Alph_01_11_011 q0 ++ [S0]) [] j P1_1RB1RC_0RC1LD_1LB1RC_0RA0LB = Cc (Pos.succ p).
Proof.
  intros p j q0 E. destruct (Alph_01_11_011.cview_some_Alph_01_11_011 p (S j) q0 E) as (H1 & H2).
  unfold Cc_1RB1RC_0RC1LD_1LB1RC_0RA0LB, cden, P0_1RB1RC_0RC1LD_1LB1RC_0RA0LB, P1_1RB1RC_0RC1LD_1LB1RC_0RA0LB; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  split.
  - rewrite H1; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
  - rewrite H2; cbn [rep app]. first [ rewrite <- !app_assoc; reflexivity
        | cbn [app]; rewrite <- ?app_assoc; cbn [app]; rewrite ?app_nil_r; reflexivity ].
Qed.

Lemma lapi_1RB1RC_0RC1LD_1LB1RC_0RA0LB : forall p j q0, cview p = (j, Some q0) ->
  exists n, 0 < n /\ csteps tm n (Cc p) = Some (Cc (Pos.succ p)).
Proof.
  intros p j q0 E. destruct j as [|j'].
  - destruct (gz_1RB1RC_0RC1LD_1LB1RC_0RA0LB p q0 E) as (HA & HB).
    exists (0 * 0 + 2). split; [lia|].
    rewrite HA.
    rewrite (srun_sound tm false true chz_1RB1RC_0RC1LD_1LB1RC_0RA0LB Z0_1RB1RC_0RC1LD_1LB1RC_0RA0LB Z1_1RB1RC_0RC1LD_1LB1RC_0RA0LB 0 2
               run_z_1RB1RC_0RC1LD_1LB1RC_0RA0LB (Ap_Alph_01_11_011 q0 ++ [S0]) [] 0
               ltac:(discriminate) ltac:(reflexivity)).
    f_equal. exact HB.
  - destruct (gp_1RB1RC_0RC1LD_1LB1RC_0RA0LB p j' q0 E) as (HA & HB).
    exists (4 * j' + 6). split; [lia|].
    rewrite HA.
    rewrite (srun_sound tm false true chp_1RB1RC_0RC1LD_1LB1RC_0RA0LB P0_1RB1RC_0RC1LD_1LB1RC_0RA0LB P1_1RB1RC_0RC1LD_1LB1RC_0RA0LB 4 6
               run_p_1RB1RC_0RC1LD_1LB1RC_0RA0LB (Ap_Alph_01_11_011 q0 ++ [S0]) [] j'
               ltac:(discriminate) ltac:(reflexivity)).
    f_equal. exact HB.
Qed.

(** The interior closes exactly; the cascade's plumbing runs in [lift]
    space, so restate it there. *)
Lemma lapil_1RB1RC_0RC1LD_1LB1RC_0RA0LB : forall p j q0, cview p = (j, Some q0) ->
  exists n c', 0 < n /\ csteps tm n (Cc p) = Some c'
               /\ lift c' = lift (Cc (Pos.succ p)).
Proof.
  intros p j q0 E. destruct (lapi_1RB1RC_0RC1LD_1LB1RC_0RA0LB p j q0 E) as (n & Hn & Hr).
  exists n, (Cc (Pos.succ p)). auto.
Qed.

(** ** The lap *)

Lemma lap_1RB1RC_0RC1LD_1LB1RC_0RA0LB : forall p, exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:E. destruct oq as [q0|].
  - destruct (lapi_1RB1RC_0RC1LD_1LB1RC_0RA0LB p j q0 E) as (n & Hn & Hrun).
    exists n, (Cc (Pos.succ p)).
    split; [exact Hrun | split; [reflexivity | exact Hn]].
  - destruct (cview_pos p j E) as (j' & ->).
    exact (lapo_1RB1RC_0RC1LD_1LB1RC_0RA0LB p j' E).
Qed.

(** ** Bootstrap *)

Lemma boot_1RB1RC_0RC1LD_1LB1RC_0RA0LB : exists t0, stepn tm t0 InitES = Some (lift (Cc 1)).
Proof.
  exists 13.
  assert (H : match csteps tm 13 c0 with
              | Some c => ceqb c (Cc 1) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 13 c0) as [c|] eqn:E; [|discriminate].
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

Lemma viso_1RB1RC_0RC1LD_1LB1RC_0RA0LB : forall (l : list lstep) (q : St),
  srun_st tm true true l B0_1RB1RC_0RC1LD_1LB1RC_0RA0LB = Some q ->
  forall p j, cview p = (S (S j), None) ->
  exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros l q Hst p j E.
  apply (vis_of_run tm Cc true true l B0_1RB1RC_0RC1LD_1LB1RC_0RA0LB p j [] []);
    [exact Hst | reflexivity | reflexivity | exact (gso_1RB1RC_0RC1LD_1LB1RC_0RA0LB p j E)].
Qed.

Lemma visc_1RB1RC_0RC1LD_1LB1RC_0RA0LB : forall (l : list lstep) (q : St),
  srun_st tm true true l CLA0_1RB1RC_0RC1LD_1LB1RC_0RA0LB = Some q ->
  forall p j, cview p = (S (S j), None) ->
  exists k e, stepn tm k (lift (Cc p)) = Some e /\ fst e = q.
Proof.
  intros l q Hst p j Ev.
  apply (cascade_vis tm Cc Dc hstep_1RB1RC_0RC1LD_1LB1RC_0RA0LB q p j 0).
  - exists (4 * j + 6), (cden [] [] j BB1_1RB1RC_0RC1LD_1LB1RC_0RA0LB).
    split; [| exact (gbo_1RB1RC_0RC1LD_1LB1RC_0RA0LB j)].
    rewrite (gso_1RB1RC_0RC1LD_1LB1RC_0RA0LB p j Ev).
    exact (srun_sound tm true true chb_1RB1RC_0RC1LD_1LB1RC_0RA0LB B0_1RB1RC_0RC1LD_1LB1RC_0RA0LB BB1_1RB1RC_0RC1LD_1LB1RC_0RA0LB 4 6
             run_boot_1RB1RC_0RC1LD_1LB1RC_0RA0LB [] [] j ltac:(reflexivity) ltac:(reflexivity)).
  - rewrite gcla_1RB1RC_0RC1LD_1LB1RC_0RA0LB.
    destruct (vis_of_run tm (fun _ => cden [] [] (S j) CLA0_1RB1RC_0RC1LD_1LB1RC_0RA0LB) true true l
                CLA0_1RB1RC_0RC1LD_1LB1RC_0RA0LB 1%positive (S j) [] [] q Hst
                ltac:(reflexivity) ltac:(reflexivity) eq_refl)
      as (k & c & Hk & Hq).
    exists k, (lift c).
    split; [apply csteps_lift; exact Hk | rewrite lift_state; exact Hq].
Qed.

(** State StA's visit witness at the reindex's p = 1 case -- concrete. *)
Lemma visz_StA_1RB1RC_0RC1LD_1LB1RC_0RA0LB : exists k c, csteps tm k (Cc 1) = Some c /\ fst c = StA.
Proof. exists 11. eexists. split; [vm_compute; reflexivity | reflexivity]. Qed.

(** State StB's visit witness at the reindex's p = 1 case -- concrete. *)
Lemma visz_StB_1RB1RC_0RC1LD_1LB1RC_0RA0LB : exists k c, csteps tm k (Cc 1) = Some c /\ fst c = StB.
Proof. exists 0. eexists. split; [vm_compute; reflexivity | reflexivity]. Qed.

(** State StC's visit witness at the reindex's p = 1 case -- concrete. *)
Lemma visz_StC_1RB1RC_0RC1LD_1LB1RC_0RA0LB : exists k c, csteps tm k (Cc 1) = Some c /\ fst c = StC.
Proof. exists 1. eexists. split; [vm_compute; reflexivity | reflexivity]. Qed.

(** State StD's visit witness at the reindex's p = 1 case -- concrete. *)
Lemma visz_StD_1RB1RC_0RC1LD_1LB1RC_0RA0LB : exists k c, csteps tm k (Cc 1) = Some c /\ fst c = StD.
Proof. exists 8. eexists. split; [vm_compute; reflexivity | reflexivity]. Qed.

Lemma vis_1RB1RC_0RC1LD_1LB1RC_0RA0LB : forall p q,
  exists k e, stepn tm k (lift (Cc p)) = Some e /\ fst e = q.
Proof.
  intros p q.
  destruct q.
  - (* StA: fires only in the close, reached through the whole descent *)
    apply (vis_via_ovf_lift tm Cc lapil_1RB1RC_0RC1LD_1LB1RC_0RA0LB StA).
    intros p1 j1 E1. destruct j1 as [|j1'].
    + rewrite (cview_none_shape p1 0 E1).
      apply (vis_lift_of_csteps tm Cc). exact visz_StA_1RB1RC_0RC1LD_1LB1RC_0RA0LB.
    + apply (visc_1RB1RC_0RC1LD_1LB1RC_0RA0LB [SWin 5; SCycL 2 0; SWinL 2; SCycR 2; SWin 3; SUnrotL 1; SFoldL 1; SRotL 1; SWin 1] StA ltac:(vm_compute; reflexivity)
                 p1 j1' E1).
  - (* StB: fires in the boot chain *)
    apply (vis_via_ovf_lift tm Cc lapil_1RB1RC_0RC1LD_1LB1RC_0RA0LB StB).
    intros p1 j1 E1. destruct j1 as [|j1'].
    + rewrite (cview_none_shape p1 0 E1).
      apply (vis_lift_of_csteps tm Cc). exact visz_StB_1RB1RC_0RC1LD_1LB1RC_0RA0LB.
    + apply (vis_lift_of_csteps tm Cc).
      apply (viso_1RB1RC_0RC1LD_1LB1RC_0RA0LB [] StB ltac:(vm_compute; reflexivity)
                   p1 j1' E1).
  - (* StC: fires in the boot chain *)
    apply (vis_via_ovf_lift tm Cc lapil_1RB1RC_0RC1LD_1LB1RC_0RA0LB StC).
    intros p1 j1 E1. destruct j1 as [|j1'].
    + rewrite (cview_none_shape p1 0 E1).
      apply (vis_lift_of_csteps tm Cc). exact visz_StC_1RB1RC_0RC1LD_1LB1RC_0RA0LB.
    + apply (vis_lift_of_csteps tm Cc).
      apply (viso_1RB1RC_0RC1LD_1LB1RC_0RA0LB [SRotL 1; SWin 1] StC ltac:(vm_compute; reflexivity)
                   p1 j1' E1).
  - (* StD: fires in the boot chain *)
    apply (vis_via_ovf_lift tm Cc lapil_1RB1RC_0RC1LD_1LB1RC_0RA0LB StD).
    intros p1 j1 E1. destruct j1 as [|j1'].
    + rewrite (cview_none_shape p1 0 E1).
      apply (vis_lift_of_csteps tm Cc). exact visz_StD_1RB1RC_0RC1LD_1LB1RC_0RA0LB.
    + apply (vis_lift_of_csteps tm Cc).
      apply (viso_1RB1RC_0RC1LD_1LB1RC_0RA0LB [SRotL 1; SWin 1; SCycL 2 0; SWin 4] StD ltac:(vm_compute; reflexivity)
                   p1 j1' E1).
Qed.

(** The interior lap closes only up to [lift] (one trailing blank past the
    anchor's far side), so the closer is [LapCertGlueLift.glue_neverqh_lift]:
    [LapGlue.glue_neverqh] with the visit premise in [stepn] space, which is
    what its own proof consumes. *)
Theorem nqhm_1RB1RC_0RC1LD_1LB1RC_0RA0LB : NeverQuasiHaltsSt tm.
Proof. apply (glue_neverqh_lift tm Cc 1). - exact boot_1RB1RC_0RC1LD_1LB1RC_0RA0LB. - intros p _. apply lap_1RB1RC_0RC1LD_1LB1RC_0RA0LB. - intros p q _. apply vis_1RB1RC_0RC1LD_1LB1RC_0RA0LB. Qed.

Theorem nqh_1RB1RC_0RC1LD_1LB1RC_0RA0LB : NeverQuasiHaltsSt tm_1RB1RC_0RC1LD_1LB1RC_0RA0LB.
Proof. apply (mirror_never_qh tm_1RB1RC_0RC1LD_1LB1RC_0RA0LB). rewrite mirror_ok_1RB1RC_0RC1LD_1LB1RC_0RA0LB. exact nqhm_1RB1RC_0RC1LD_1LB1RC_0RA0LB. Qed.

Theorem nonhalt_1RB1RC_0RC1LD_1LB1RC_0RA0LB : NonHalt tm_1RB1RC_0RC1LD_1LB1RC_0RA0LB.
Proof. apply never_qh_nonhalt, nqh_1RB1RC_0RC1LD_1LB1RC_0RA0LB. Qed.
