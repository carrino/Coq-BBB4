(** * NLAP_1RB____1RC1LB_0LB1RD_0RA0RC: machine 1RB---_1RC1LB_0LB1RD_0RA0RC,
    boarded by a NESTED certificate.

    This is the one row of the 24 three-state core rows (docs/CORE_3STATE.md)
    that TARGETS [StA], and the only one of them that does NOT quasihalt: its
    conclusion is [NeverQuasiHaltsSt], closed by [LapGlue.glue_neverqh].

    WHAT THE MACHINE IS.  A binary counter with one marker [S1] beside every
    bit, MSB to the LEFT, growing rightward from a blank tape.  Read at the
    moment the head sits on the counter's low end with nothing written to its
    right, the anchor is

      Cin v = (StB, (S1 :: Rw v, S0, [S0]))        Rw = Alph_01_11_1

    -- digit words [A = 01] (clear), [B = 11] (set), terminator [C = 1], with
    the leading [S1] the stop digit's own marker.  The interior increment is
    an ordinary carry: [SWin]-bump, sweep left over the run of set digits,
    then an alternating [StC]/[StD] sweep back out clearing every second cell.
    Lap [4*j + 8] at carry length [j], EXACT.

    WHY IT IS NESTED, AND WHY EVERY FLAT SEARCH MISSED IT.  The counter is
    FIXED-WIDTH: [Cin v] is visited only for [v] in [[2^(2i), 2^(2i+1) - 1]],
    and when [v] fills to all ones the machine WIDENS -- it re-spreads the
    solid run of ones into marker/bit pairs, and that is the one path on which
    [StD]'s [0RA] fires, once per epoch (measured at configuration indices
    19, 66, 257, 1024, 4095, 16382, ... to t = 2*10^6).  So the anchor value
    JUMPS, [2^(2i+1) - 1 -> 2^(2i+2)], and no [Cf p -> Cf (p+1)] counter
    family over all of [positive] exists at this anchor.  What does exist is
    the two-level split [Counters/NestedLap.v] was written for:

      outer   Cc p := Cin (pow2 (2 * Pos.to_nat p))
      boot    one interior lap                          (affine, 8 steps)
      inner   Cin v0 -> Cin (fill v0)   (INDUCTION; the cost is exponential
                                         and stays inside the existential)
      exit    Cin (fill (pow2 (2*j))) -> Cc (Pos.succ p) (affine, 8*j + 11)

    The exit chain is the widening itself: sweep the solid run left, turn, and
    re-lay it as [rep [S0;S1] (2*j+2)] on the way out -- which is where [StA]
    fires, and therefore where the [StA] visit witness comes from.

    Both laps are DATA for [Checkers/LapDecider.v], run by the kernel through
    [vm_compute] and discharged by [srun_sound].  The machine is used
    UNMIRRORED: its counter word already lies to the left of the anchor head.

    Differentially validated against the raw simulator before this file was
    written: 3,988 interior laps exact ([v] = 2..3999), 11 exit laps
    lift-exact ([j] = 1..11), and the rails (boot -> inner laps -> exit ->
    next epoch) walked forward through six epochs of the real trajectory.

    Axiom footprint: [functional_extensionality_dep] (via [CTape.lift]). *)
From Coq Require Import Arith Lia Bool List PArith Wellfounded.
From BBB4 Require Import BBB4_Statement CTape.
From Coq Require Import FunctionalExtensionality.
From BBB4.Counters Require Import WTape LapGlue MonoCounter IXPGadgets
                                  Alph_01_11_1 NestedLap.
From BBB4.Checkers Require Import LapDecider.
Import ListNotations.

Definition mk_1RB____1RC1LB_0LB1RD_0RA0RC (w : Sym) (d : Dir) (n : St)
  : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_1RB____1RC1LB_0LB1RD_0RA0RC.

(** 1RB---_1RC1LB_0LB1RD_0RA0RC *)
Definition tm_1RB____1RC1LB_0LB1RD_0RA0RC : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => None
  | StB, S0 => mk S1 DR StC | StB, S1 => mk S1 DL StB
  | StC, S0 => mk S0 DL StB | StC, S1 => mk S1 DR StD
  | StD, S0 => mk S0 DR StA | StD, S1 => mk S0 DR StC end.
Local Notation tm := tm_1RB____1RC1LB_0LB1RD_0RA0RC.

Local Notation Rw := Ap_Alph_01_11_1.

(** ** The two anchor families *)

(** The INNER anchor: head on the counter's low end, word to the left, one
    blank cell to the right (which is what makes the interior lap close
    exactly rather than up to [lift]). *)
Definition Cin_1RB____1RC1LB_0LB1RD_0RA0RC (v : positive) : cconf :=
  (StB, (S1 :: Rw v, S0, [S0])).
Local Notation Cin := Cin_1RB____1RC1LB_0LB1RD_0RA0RC.

(** The OUTER anchor: the first inner value of each epoch. *)
Definition Cc_1RB____1RC1LB_0LB1RD_0RA0RC (p : positive) : cconf :=
  Cin (pow2 (2 * Pos.to_nat p)).
Local Notation Cc := Cc_1RB____1RC1LB_0LB1RD_0RA0RC.

Lemma Cc_succ_1RB____1RC1LB_0LB1RD_0RA0RC : forall p,
  Cc (Pos.succ p) = Cin (pow2 (2 * Pos.to_nat p + 2)).
Proof.
  intro p. unfold Cc_1RB____1RC1LB_0LB1RD_0RA0RC.
  rewrite Pos2Nat.inj_succ. f_equal. f_equal. lia.
Qed.

(** ** Word shapes at the two ends of an epoch *)

Lemma rep11_snoc_1RB____1RC1LB_0LB1RD_0RA0RC : forall n,
  rep [S1; S1] n ++ [S1] = S1 :: rep [S1; S1] n.
Proof. induction n; cbn [rep app]; [reflexivity | now rewrite IHn]. Qed.

(** The epoch's LAST word: all ones. *)
Lemma Rw_fill_pow2_1RB____1RC1LB_0LB1RD_0RA0RC : forall n,
  Rw (fill (pow2 n)) = rep [S1; S1] n ++ [S1].
Proof.
  induction n as [|n IH]; cbn [pow2 fill Ap_Alph_01_11_1 rep app];
    [reflexivity | now rewrite IH].
Qed.

(** The epoch's FIRST word: one set digit over clear ones. *)
Lemma Rw_pow2_1RB____1RC1LB_0LB1RD_0RA0RC : forall n,
  Rw (pow2 n) = rep [S0; S1] n ++ [S1].
Proof.
  induction n as [|n IH]; cbn [pow2 Ap_Alph_01_11_1 rep app];
    [reflexivity | now rewrite IH].
Qed.

Lemma cview_pow2_1RB____1RC1LB_0LB1RD_0RA0RC : forall n,
  cview (pow2 (S n)) = (0, Some (pow2 n)).
Proof. reflexivity. Qed.

(** ** The INTERIOR certificate -- one carry of the inner counter *)

Definition A0_1RB____1RC1LB_0LB1RD_0RA0RC : sconf :=
  mkC StB (mkS [S1] [S1;S1] 1 0 [S0;S1]) S0 (mkS [S0] [] 0 0 []).
Definition A1_1RB____1RC1LB_0LB1RD_0RA0RC : sconf :=
  mkC StB (mkS [S1] [S0;S1] 1 0 [S1;S1]) S0 (mkS [S0] [] 0 0 []).
Definition chi_1RB____1RC1LB_0LB1RD_0RA0RC : list lstep :=
  [SWin 2; SWin 1; SCycL 2 0; SWin 1; SWin 1; SCycR 2; SWin 3].

Lemma run_int_1RB____1RC1LB_0LB1RD_0RA0RC :
  srun tm false true chi_1RB____1RC1LB_0LB1RD_0RA0RC
       A0_1RB____1RC1LB_0LB1RD_0RA0RC
  = Some (A1_1RB____1RC1LB_0LB1RD_0RA0RC, 4, 8).
Proof. vm_compute. reflexivity. Qed.

Lemma gsi_1RB____1RC1LB_0LB1RD_0RA0RC : forall v j q0, cview v = (j, Some q0) ->
  Cin v = cden (Rw q0) [] j A0_1RB____1RC1LB_0LB1RD_0RA0RC.
Proof.
  intros v j q0 E. destruct (cview_some_Alph_01_11_1 v j q0 E) as (H1 & _).
  unfold Cin_1RB____1RC1LB_0LB1RD_0RA0RC, cden,
         A0_1RB____1RC1LB_0LB1RD_0RA0RC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  rewrite H1. cbn [rep app].
  first [ reflexivity
        | rewrite <- !app_assoc; reflexivity
        | rewrite <- ?app_assoc, ?app_nil_r; reflexivity ].
Qed.

Lemma gei_1RB____1RC1LB_0LB1RD_0RA0RC : forall v j q0, cview v = (j, Some q0) ->
  cden (Rw q0) [] j A1_1RB____1RC1LB_0LB1RD_0RA0RC = Cin (Pos.succ v).
Proof.
  intros v j q0 E. destruct (cview_some_Alph_01_11_1 v j q0 E) as (_ & H2).
  unfold Cin_1RB____1RC1LB_0LB1RD_0RA0RC, cden,
         A1_1RB____1RC1LB_0LB1RD_0RA0RC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  rewrite H2. cbn [rep app].
  first [ reflexivity
        | rewrite <- !app_assoc; reflexivity
        | rewrite <- ?app_assoc, ?app_nil_r; reflexivity ].
Qed.

(** The inner family's interior lap: [Hin] of [NestedLap], EXACT. *)
Lemma lapi_1RB____1RC1LB_0LB1RD_0RA0RC : forall v j q0, cview v = (j, Some q0) ->
  exists n, 0 < n /\ csteps tm n (Cin v) = Some (Cin (Pos.succ v)).
Proof.
  intros v j q0 E. exists (4 * j + 8). split; [lia|].
  rewrite (gsi_1RB____1RC1LB_0LB1RD_0RA0RC v j q0 E).
  rewrite (srun_sound tm false true chi_1RB____1RC1LB_0LB1RD_0RA0RC
             A0_1RB____1RC1LB_0LB1RD_0RA0RC A1_1RB____1RC1LB_0LB1RD_0RA0RC 4 8
             run_int_1RB____1RC1LB_0LB1RD_0RA0RC (Rw q0) [] j
             ltac:(discriminate) ltac:(reflexivity)).
  f_equal. exact (gei_1RB____1RC1LB_0LB1RD_0RA0RC v j q0 E).
Qed.

(** ** The EXIT certificate -- the widening that ends an epoch *)

Definition B0_1RB____1RC1LB_0LB1RD_0RA0RC : sconf :=
  mkC StB (mkS [] [S1;S1] 2 1 []) S0 (mkS [S0] [] 0 0 []).
Definition B1_1RB____1RC1LB_0LB1RD_0RA0RC : sconf :=
  mkC StB (mkS [S1] [S0;S1] 2 2 [S1]) S0 (mkS [] [] 0 0 []).
Definition cho_1RB____1RC1LB_0LB1RD_0RA0RC : list lstep :=
  [SWin 2; SCycL 2 0; SWinL 1; SWin 1; SCycR 2; SWinR 3; SFoldL 1].

Lemma run_ovf_1RB____1RC1LB_0LB1RD_0RA0RC :
  srun tm true true cho_1RB____1RC1LB_0LB1RD_0RA0RC
       B0_1RB____1RC1LB_0LB1RD_0RA0RC
  = Some (B1_1RB____1RC1LB_0LB1RD_0RA0RC, 8, 11).
Proof. vm_compute. reflexivity. Qed.

Lemma gso_1RB____1RC1LB_0LB1RD_0RA0RC : forall j,
  Cin (fill (pow2 (2 * j))) = cden [] [] j B0_1RB____1RC1LB_0LB1RD_0RA0RC.
Proof.
  intro j.
  unfold Cin_1RB____1RC1LB_0LB1RD_0RA0RC, cden,
         B0_1RB____1RC1LB_0LB1RD_0RA0RC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  rewrite Rw_fill_pow2_1RB____1RC1LB_0LB1RD_0RA0RC,
          rep11_snoc_1RB____1RC1LB_0LB1RD_0RA0RC.
  replace (2 * j + 1) with (S (2 * j)) by lia.
  cbn [rep app]. rewrite ?app_nil_r. reflexivity.
Qed.

Lemma geo_1RB____1RC1LB_0LB1RD_0RA0RC : forall j,
  lift (cden [] [] j B1_1RB____1RC1LB_0LB1RD_0RA0RC)
  = lift (Cin (pow2 (2 * j + 2))).
Proof.
  intro j.
  unfold Cin_1RB____1RC1LB_0LB1RD_0RA0RC, cden,
         B1_1RB____1RC1LB_0LB1RD_0RA0RC; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  rewrite Rw_pow2_1RB____1RC1LB_0LB1RD_0RA0RC.
  cbn [rep app]. rewrite ?app_nil_r.
  exact (eq_sym (lift_app_blank StB (S1 :: rep [S0;S1] (2 * j + 2) ++ [S1]) S0 [])).
Qed.

(** ** The two bridges the nesting needs, at an EVEN exponent *)

Lemma boot_lap_1RB____1RC1LB_0LB1RD_0RA0RC : forall j, 0 < j ->
  exists n, 0 < n /\ csteps tm n (Cin (pow2 (2 * j)))
                   = Some (Cin (Pos.succ (pow2 (2 * j)))).
Proof.
  intros j Hj. destruct j as [|j']; [lia|].
  replace (2 * S j') with (S (S (2 * j'))) by lia.
  exact (lapi_1RB____1RC1LB_0LB1RD_0RA0RC _ 0 _
           (cview_pow2_1RB____1RC1LB_0LB1RD_0RA0RC (S (2 * j')))).
Qed.

Lemma fill_boot_1RB____1RC1LB_0LB1RD_0RA0RC : forall j, 0 < j ->
  fill (Pos.succ (pow2 (2 * j))) = fill (pow2 (2 * j)).
Proof.
  intros j Hj. destruct j as [|j']; [lia|].
  replace (2 * S j') with (S (S (2 * j'))) by lia.
  exact (fill_succ _ 0 _
           (cview_pow2_1RB____1RC1LB_0LB1RD_0RA0RC (S (2 * j')))).
Qed.

(** ** The outer lap *)

Lemma lap_1RB____1RC1LB_0LB1RD_0RA0RC : forall p, exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. assert (Hp : 0 < Pos.to_nat p) by apply Pos2Nat.is_pos.
  apply (nested_overflow tm Cc Cin lapi_1RB____1RC1LB_0LB1RD_0RA0RC p
           (Pos.succ (pow2 (2 * Pos.to_nat p)))).
  - exact (boot_lap_1RB____1RC1LB_0LB1RD_0RA0RC _ Hp).
  - exists (8 * Pos.to_nat p + 11),
           (cden [] [] (Pos.to_nat p) B1_1RB____1RC1LB_0LB1RD_0RA0RC).
    split.
    + rewrite (fill_boot_1RB____1RC1LB_0LB1RD_0RA0RC _ Hp),
              (gso_1RB____1RC1LB_0LB1RD_0RA0RC (Pos.to_nat p)).
      exact (srun_sound tm true true cho_1RB____1RC1LB_0LB1RD_0RA0RC
               B0_1RB____1RC1LB_0LB1RD_0RA0RC B1_1RB____1RC1LB_0LB1RD_0RA0RC
               8 11 run_ovf_1RB____1RC1LB_0LB1RD_0RA0RC [] [] (Pos.to_nat p)
               ltac:(reflexivity) ltac:(reflexivity)).
    + rewrite Cc_succ_1RB____1RC1LB_0LB1RD_0RA0RC.
      exact (geo_1RB____1RC1LB_0LB1RD_0RA0RC (Pos.to_nat p)).
Qed.

(** ** Bootstrap *)

Lemma boot_1RB____1RC1LB_0LB1RD_0RA0RC :
  exists t0, stepn tm t0 InitES = Some (lift (Cc 1)).
Proof.
  exists 20.
  assert (H : match csteps tm 20 c0 with
              | Some c => ceqb c (Cc 1) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 20 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** ** Visits

    [StB]/[StC]/[StD] all fire inside the very first interior lap, so a prefix
    chain at the OUTER anchor (which is an interior anchor, [j = 0]) suffices.
    [StA] fires only on the widening, so its witness runs the whole epoch --
    boot lap, then [inner_to_fill], then a prefix of the exit chain. *)

Lemma Cc_interior_1RB____1RC1LB_0LB1RD_0RA0RC : forall p,
  exists q0, Cc p = cden (Rw q0) [] 0 A0_1RB____1RC1LB_0LB1RD_0RA0RC.
Proof.
  intro p. assert (Hp : 0 < Pos.to_nat p) by apply Pos2Nat.is_pos.
  unfold Cc_1RB____1RC1LB_0LB1RD_0RA0RC.
  destruct (Pos.to_nat p) as [|k]; [lia|].
  replace (2 * S k) with (S (S (2 * k))) by lia.
  exists (pow2 (S (2 * k))).
  exact (gsi_1RB____1RC1LB_0LB1RD_0RA0RC _ 0 _
           (cview_pow2_1RB____1RC1LB_0LB1RD_0RA0RC (S (2 * k)))).
Qed.

Lemma visi_1RB____1RC1LB_0LB1RD_0RA0RC : forall (l : list lstep) (q : St),
  srun_st tm false true l A0_1RB____1RC1LB_0LB1RD_0RA0RC = Some q ->
  forall p, exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros l q Hst p.
  destruct (Cc_interior_1RB____1RC1LB_0LB1RD_0RA0RC p) as (q0 & Hq).
  exact (vis_of_run tm Cc false true l A0_1RB____1RC1LB_0LB1RD_0RA0RC p 0
           (Rw q0) [] q Hst ltac:(discriminate) ltac:(reflexivity) Hq).
Qed.

Lemma reach_fill_1RB____1RC1LB_0LB1RD_0RA0RC : forall p, exists n,
  csteps tm n (Cc p) = Some (Cin (fill (pow2 (2 * Pos.to_nat p)))).
Proof.
  intro p. assert (Hp : 0 < Pos.to_nat p) by apply Pos2Nat.is_pos.
  destruct (boot_lap_1RB____1RC1LB_0LB1RD_0RA0RC _ Hp) as (nb & _ & Hb).
  destruct (inner_to_fill tm Cin lapi_1RB____1RC1LB_0LB1RD_0RA0RC
              (Pos.succ (pow2 (2 * Pos.to_nat p)))) as (ni & Hi).
  exists (nb + ni). unfold Cc_1RB____1RC1LB_0LB1RD_0RA0RC.
  rewrite csteps_add, Hb, Hi, (fill_boot_1RB____1RC1LB_0LB1RD_0RA0RC _ Hp).
  reflexivity.
Qed.

Lemma visA_1RB____1RC1LB_0LB1RD_0RA0RC : forall p,
  exists k c, csteps tm k (Cc p) = Some c /\ fst c = StA.
Proof.
  intro p.
  destruct (reach_fill_1RB____1RC1LB_0LB1RD_0RA0RC p) as (n1 & H1).
  destruct (vis_of_run tm (fun _ => Cin (fill (pow2 (2 * Pos.to_nat p))))
              true true [SWin 2; SCycL 2 0; SWinL 1; SWin 1; SCycR 2; SWinR 2]
              B0_1RB____1RC1LB_0LB1RD_0RA0RC xH (Pos.to_nat p) [] [] StA
              ltac:(vm_compute; reflexivity)
              ltac:(reflexivity) ltac:(reflexivity)
              (gso_1RB____1RC1LB_0LB1RD_0RA0RC (Pos.to_nat p)))
    as (n2 & c & H2 & H3).
  exists (n1 + n2), c. rewrite csteps_add, H1. split; [exact H2 | exact H3].
Qed.

Lemma vis_1RB____1RC1LB_0LB1RD_0RA0RC : forall p q,
  exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros p q. destruct q.
  - exact (visA_1RB____1RC1LB_0LB1RD_0RA0RC p).
  - exists 0. eexists. split; reflexivity.
  - exact (visi_1RB____1RC1LB_0LB1RD_0RA0RC [SWin 1] StC
             ltac:(vm_compute; reflexivity) p).
  - exact (visi_1RB____1RC1LB_0LB1RD_0RA0RC
             [SWin 2; SWin 1; SCycL 2 0; SWin 1; SWin 1; SCycR 2; SWin 1] StD
             ltac:(vm_compute; reflexivity) p).
Qed.

(** ** The closer *)

Theorem nqh_1RB____1RC1LB_0LB1RD_0RA0RC : NeverQuasiHaltsSt tm.
Proof.
  apply (glue_neverqh tm Cc 1).
  - exact boot_1RB____1RC1LB_0LB1RD_0RA0RC.
  - intros p _. apply lap_1RB____1RC1LB_0LB1RD_0RA0RC.
  - intros p q _. apply vis_1RB____1RC1LB_0LB1RD_0RA0RC.
Qed.

Theorem nonhalt_1RB____1RC1LB_0LB1RD_0RA0RC : NonHalt tm.
Proof. apply never_qh_nonhalt, nqh_1RB____1RC1LB_0LB1RD_0RA0RC. Qed.
