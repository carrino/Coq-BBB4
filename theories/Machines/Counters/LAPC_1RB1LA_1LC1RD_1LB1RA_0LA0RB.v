(** * LAPC_1RB1LA_1LC1RD_1LB1RA_0LA0RB: the same board as
    [ILS4_1RB1LA_1LC1RD_1LB1RA_0LA0RB], re-derived as a CERTIFICATE.

    This is the architecture proof for [Checkers/LapDecider.v].  The hand
    emitted board (tools/counters/emit_shape4.py) spent nine hand-authored
    window lemmas, nine transported phase lemmas and two hand-assembled lap
    proofs on this machine.  Here the entire lap is DATA —

      interior:  [SRotL 1; SWin 1; SCycL 2 0; SWin 1; SWin 1; SCycR 2;
                  SWin 1; SUnrotL 1]
      overflow:  [SRotL 1; SWin 1; SCycL 2 0; SWin 3; SUnrotR 1; SCycR 2;
                  SWinR 7; SUnrotL 1]

    — and every step of it is discharged by ONE theorem, [srun_sound], via a
    [vm_compute].  What is left per machine is only the ANCHOR GLUE: the two
    [cview] decompositions relating [Cc p] to the symbolic start, which are
    [ILCounter.cview_some_I] / [cview_none_I] plus [app_assoc].

    Nothing here is trusted: [srun] is a Coq function, the kernel runs it, and
    a wrong certificate makes it return [None] rather than a wrong theorem.

    Axiom footprint: [functional_extensionality_dep] (via [CTape.lift]). *)

From Coq Require Import Arith Lia Bool List PArith Wellfounded.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape LapGlue MonoCounter ILCounter JpCounter
                                  LapCertGlue.
From BBB4.Checkers Require Import LapDecider.
Import ListNotations.

Definition mk_1RB1LA_1LC1RD_1LB1RA_0LA0RB (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_1RB1LA_1LC1RD_1LB1RA_0LA0RB.

(** 1RB1LA_1LC1RD_1LB1RA_0LA0RB *)
Definition tm_1RB1LA_1LC1RD_1LB1RA_0LA0RB : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S1 DL StA
  | StB, S0 => mk S1 DL StC | StB, S1 => mk S1 DR StD
  | StC, S0 => mk S1 DL StB | StC, S1 => mk S1 DR StA
  | StD, S0 => mk S0 DL StA | StD, S1 => mk S0 DR StB end.
Local Notation tm := tm_1RB1LA_1LC1RD_1LB1RA_0LA0RB.

Definition Cc_1RB1LA_1LC1RD_1LB1RA_0LA0RB (p : positive) : cconf :=
  (StD, (Ip p ++ [S1;S0], S0, [])).
Local Notation Cc := Cc_1RB1LA_1LC1RD_1LB1RA_0LA0RB.

(** ** The certificate

    Interior branch ([cview p = (j, Some q0)]): the anchor's left side is
    [rep [S1;S1] j ++ [S1;S0] ++ XL] with the opaque tail [XL = Ip q0 ++ [S1;S0]]
    — the high bits above the carry, which the lap never reaches.  Both tails
    are arbitrary, so the run is checked with [el = er = false]. *)

Definition A0_int : sconf := mkC StD (mkS [] [S1;S1] 1 0 [S1;S0]) S0 (sflat []).
Definition A1_int : sconf := mkC StD (mkS [] [S1;S0] 1 0 [S1;S1]) S0 (sflat []).
Definition ch_int : list lstep :=
  [SRotL 1; SWin 1; SCycL 2 0; SWin 1; SWin 1; SCycR 2; SWin 1; SUnrotL 1].

Lemma run_int_1RB1LA_1LC1RD_1LB1RA_0LA0RB :
  srun tm false false ch_int A0_int = Some (A1_int, 4, 4).
Proof. vm_compute. reflexivity. Qed.

(** Overflow branch ([cview p = (S j', None)], i.e. [p = 2^(j'+1) - 1]): the
    counter is all ones and nothing is written above it, so BOTH tails are
    empty and the chain may use the open-right window [SWinR] to grow the
    frontier past the old tape edge. *)

Definition A0_ovf : sconf := mkC StD (mkS [] [S1;S1] 1 0 [S1;S1;S0]) S0 (sflat []).
Definition A1_ovf : sconf := mkC StD (mkS [S1;S0] [S1;S0] 1 0 [S1;S1]) S0 (sflat []).
Definition ch_ovf : list lstep :=
  [SRotL 1; SWin 1; SCycL 2 0; SWin 3; SUnrotR 1; SCycR 2; SWinR 7; SUnrotL 1].

Lemma run_ovf_1RB1LA_1LC1RD_1LB1RA_0LA0RB :
  srun tm true true ch_ovf A0_ovf = Some (A1_ovf, 4, 11).
Proof. vm_compute. reflexivity. Qed.

(** ** Anchor glue

    The only per-machine mathematics: read the anchor through [cview]. *)

Lemma gs_int_1RB1LA_1LC1RD_1LB1RA_0LA0RB : forall p j q0, cview p = (j, Some q0) ->
  Cc p = cden (Ip q0 ++ [S1;S0]) [] j A0_int.
Proof.
  intros p j q0 E. destruct (cview_some_I p j q0 E) as (HIp & _).
  unfold Cc_1RB1LA_1LC1RD_1LB1RA_0LA0RB, cden, A0_int; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  rewrite HIp, <- (app_assoc (rep [S1;S1] j)).
  reflexivity.
Qed.

Lemma ge_int_1RB1LA_1LC1RD_1LB1RA_0LA0RB : forall p j q0, cview p = (j, Some q0) ->
  cden (Ip q0 ++ [S1;S0]) [] j A1_int = Cc (Pos.succ p).
Proof.
  intros p j q0 E. destruct (cview_some_I p j q0 E) as (_ & HIs).
  unfold Cc_1RB1LA_1LC1RD_1LB1RA_0LA0RB, cden, A1_int; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  rewrite HIs, <- (app_assoc (rep [S1;S0] j)).
  reflexivity.
Qed.

Lemma gs_ovf_1RB1LA_1LC1RD_1LB1RA_0LA0RB : forall p j, cview p = (S j, None) ->
  Cc p = cden [] [] j A0_ovf.
Proof.
  intros p j E. destruct (cview_none_I p j E) as (HIp & _).
  unfold Cc_1RB1LA_1LC1RD_1LB1RA_0LA0RB, cden, A0_ovf; cbn [c_st c_l c_h c_r].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  replace (1 * j + 0) with j by lia.
  rewrite HIp, <- (app_assoc (rep [S1;S1] j)).
  reflexivity.
Qed.

(** A trailing blank on the LEFT half-tape is denotationally invisible: the
    overflow rebuilds the wall one cell deeper and consumes the anchor's
    synthetic deep blank, so the two agree under [lift]. *)
Lemma lblank_1RB1LA_1LC1RD_1LB1RA_0LA0RB : forall q l h r,
  lift (q,(l ++ [S0],h,r)) = lift (q,(l,h,r)).
Proof. intros. unfold lift; simpl. rewrite lift_side_app_blank. reflexivity. Qed.

Lemma ge_ovf_1RB1LA_1LC1RD_1LB1RA_0LA0RB : forall p j, cview p = (S j, None) ->
  lift (cden [] [] j A1_ovf) = lift (Cc (Pos.succ p)).
Proof.
  intros p j E. destruct (cview_none_I p j E) as (_ & HIs).
  assert (HD : cden [] [] j A1_ovf
             = (StD, ([S1;S0] ++ rep [S1;S0] j ++ [S1;S1], S0, []))).
  { unfold cden, A1_ovf, sden, sflat;
      cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    replace (1 * j + 0) with j by lia.
    replace (0 * j + 0) with 0 by lia.
    cbn [rep app]. reflexivity. }
  assert (HC : Cc (Pos.succ p)
             = (StD, (([S1;S0] ++ rep [S1;S0] j ++ [S1;S1]) ++ [S0], S0, []))).
  { unfold Cc_1RB1LA_1LC1RD_1LB1RA_0LA0RB. rewrite HIs.
    cbn [rep app]. rewrite <- !app_assoc. reflexivity. }
  rewrite HD, HC. symmetry.
  apply (lblank_1RB1LA_1LC1RD_1LB1RA_0LA0RB StD
           ([S1;S0] ++ rep [S1;S0] j ++ [S1;S1]) S0 []).
Qed.

(** ** The lap *)

Lemma lap_int_1RB1LA_1LC1RD_1LB1RA_0LA0RB : forall p j q0, cview p = (j, Some q0) ->
  exists n, 0 < n /\ csteps tm n (Cc p) = Some (Cc (Pos.succ p)).
Proof.
  intros p j q0 E. exists (4 * j + 4). split; [lia|].
  rewrite (gs_int_1RB1LA_1LC1RD_1LB1RA_0LA0RB p j q0 E).
  rewrite (srun_sound tm false false ch_int A0_int A1_int 4 4
             run_int_1RB1LA_1LC1RD_1LB1RA_0LA0RB
             (Ip q0 ++ [S1;S0]) [] j
             ltac:(discriminate) ltac:(discriminate)).
  f_equal. exact (ge_int_1RB1LA_1LC1RD_1LB1RA_0LA0RB p j q0 E).
Qed.

Lemma lap_1RB1LA_1LC1RD_1LB1RA_0LA0RB : forall p,
  exists n c', csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:E. destruct oq as [q0|].
  - destruct (lap_int_1RB1LA_1LC1RD_1LB1RA_0LA0RB p j q0 E) as (n & Hn & Hrun).
    exists n, (Cc (Pos.succ p)). split; [exact Hrun | split; [reflexivity | exact Hn]].
  - destruct (cview_pos p j E) as (j' & ->).
    apply (lap_of_run tm Cc true true ch_ovf A0_ovf A1_ovf 4 11 p j' [] []).
    + exact run_ovf_1RB1LA_1LC1RD_1LB1RA_0LA0RB.
    + reflexivity.
    + reflexivity.
    + exact (gs_ovf_1RB1LA_1LC1RD_1LB1RA_0LA0RB p j' E).
    + exact (ge_ovf_1RB1LA_1LC1RD_1LB1RA_0LA0RB p j' E).
    + lia.
Qed.

(** ** Bootstrap *)

Lemma boot_1RB1LA_1LC1RD_1LB1RA_0LA0RB : exists t0, stepn tm t0 InitES = Some (lift (Cc 2)).
Proof.
  exists 13.
  assert (H : match csteps tm 13 c0 with Some c => ceqb c (Cc 2) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 13 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** ** Visits

    Every state fires inside the OVERFLOW lap, so one prefix chain per state
    plus [LapCertGlue.vis_via_ovf] (run interior laps until the counter
    overflows) covers every anchor.  [StD] is the anchor state itself. *)

Lemma vis_ovf_1RB1LA_1LC1RD_1LB1RA_0LA0RB :
  forall (l : list lstep) (q : St), srun_st tm true true l A0_ovf = Some q ->
  forall p j, cview p = (S j, None) ->
  exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros l q Hst p j E.
  apply (vis_of_run tm Cc true true l A0_ovf p j [] []);
    [exact Hst | reflexivity | reflexivity
     | exact (gs_ovf_1RB1LA_1LC1RD_1LB1RA_0LA0RB p j E)].
Qed.

Lemma vis_1RB1LA_1LC1RD_1LB1RA_0LA0RB : forall p q,
  exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros p q.
  assert (Hi : forall p0 j q0, cview p0 = (j, Some q0) ->
            exists n, 0 < n /\ csteps tm n (Cc p0) = Some (Cc (Pos.succ p0)))
    by exact lap_int_1RB1LA_1LC1RD_1LB1RA_0LA0RB.
  destruct q.
  - (* StA *)
    apply (vis_via_ovf tm Cc Hi StA), vis_ovf_1RB1LA_1LC1RD_1LB1RA_0LA0RB
      with (l := [SRotL 1; SWin 1]).
    vm_compute; reflexivity.
  - (* StB *)
    apply (vis_via_ovf tm Cc Hi StB), vis_ovf_1RB1LA_1LC1RD_1LB1RA_0LA0RB
      with (l := [SRotL 1; SWin 1; SCycL 2 0; SWin 3]).
    vm_compute; reflexivity.
  - (* StC: fires only inside the overflow close *)
    apply (vis_via_ovf tm Cc Hi StC), vis_ovf_1RB1LA_1LC1RD_1LB1RA_0LA0RB
      with (l := [SRotL 1; SWin 1; SCycL 2 0; SWin 3; SUnrotR 1; SCycR 2; SWinR 3]).
    vm_compute; reflexivity.
  - (* StD: the anchor state *)
    exists 0. eexists. split; reflexivity.
Qed.

Theorem nqh_1RB1LA_1LC1RD_1LB1RA_0LA0RB : NeverQuasiHaltsSt tm.
Proof.
  apply (glue_neverqh tm Cc 2).
  - exact boot_1RB1LA_1LC1RD_1LB1RA_0LA0RB.
  - intros p _. apply lap_1RB1LA_1LC1RD_1LB1RA_0LA0RB.
  - intros p q _. apply vis_1RB1LA_1LC1RD_1LB1RA_0LA0RB.
Qed.

Theorem nonhalt_1RB1LA_1LC1RD_1LB1RA_0LA0RB : NonHalt tm.
Proof. apply never_qh_nonhalt, nqh_1RB1LA_1LC1RD_1LB1RA_0LA0RB. Qed.
