(** * KC3_1RB1RC_1LA1RA_0RC1LD_1LB0LD: the KCOPY3 core row, boarded by CERTIFICATE.

    Machine `1RB1RC_1LA1RA_0RC1LD_1LB0LD` -- one of the four undecided (4,2)
    core rows, filed `AFFINE` / `EXP2` / `Alph_000_111_111` /
    `no inner family at pow2 j` in `tools/closeout/residue_map.tsv`.

    A leftward-growing binary counter against a RIGHT wall, three cells a
    digit, anchored at

      Cc p = (StC, (Wk p, S1, []))

    with [Wk] the PACKED-FRONTIER numeral of [Counters/Kc3Num.v] -- NOT
    [Alph_000_111_111.Ap], which mismatches at every one of 250,013 anchor
    visits (`tools/counters/kc3lap.py`).  Values are 1, 2, 3, ... with no
    offset, and the right side of the anchor is literally empty.

    The lap is DATA: five [Checkers/LapDecider.v] chains run by [vm_compute].

      interior, j = 0     (cview p = (0,   Some q0), q0 <> xH):        6 steps
      interior, j = S j'  (cview p = (S j', Some q0), q0 <> xH):  6*j' + 12
      frontier, j = 0     (cview p = (0,   Some xH)):                  4 steps
      frontier, j = S j'  (cview p = (S j', Some xH)):            6*j' + 10
      overflow            (cview p = (S j', None)):                6*j' +  8

    THREE [cview] branches, not two, and the split is the packed frontier's:
    a carry that lands ON the top digit rewrites one cell where an interior
    carry rewrites three.  Overflow has its OWN cost rather than sharing an
    interior branch's -- `docs/LADDER_PLAN.md` §4y's outcome, not §4z's --
    and the frontier adds a third branch neither of them had.

    Each interior/frontier branch is stated twice because the anchor's head
    sits FLUSH against the repeated block: with an empty [s_pre] no window
    step can move, so the [j = 0] lap is concrete and the [j = S j'] lap
    carries one peeled digit in the prefix.  Only the overflow branch escapes
    it, because its [s_post] is a single [S1] that [SRotL] can rotate out.

    All five branches close EXACTLY -- there is no [lift] slack anywhere in
    this file, so [LapCertGlue.reach_ovf] takes both interior branches
    directly.  All four states occur in every one of 250,012 measured laps,
    so the theorem is [NeverQuasiHaltsSt] and the closer is the plain
    [LapGlue.glue_neverqh].

    Differentially validated against the raw simulator before any proof:
    every rule run in single cells over an UNKNOWN context, aborting on the
    first unknown read (`tools/counters/kc3lem.py`).
    Axiom footprint: [functional_extensionality_dep] (via [CTape.lift]). *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape LapGlue MonoCounter Kc3Num LapCertGlue.
From BBB4.Census Require Import TNF_QH.
From BBB4.Checkers Require Import LapDecider.
Import ListNotations.

Definition mk_kc3 (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
Local Notation mk := mk_kc3.

(** 1RB1RC_1LA1RA_0RC1LD_1LB0LD -- the counter grows LEFT, so no mirror. *)
Definition tm_1RB1RC_1LA1RA_0RC1LD_1LB0LD : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S1 DR StC
  | StB, S0 => mk S1 DL StA | StB, S1 => mk S1 DR StA
  | StC, S0 => mk S0 DR StC | StC, S1 => mk S1 DL StD
  | StD, S0 => mk S1 DL StB | StD, S1 => mk S0 DL StD end.
Local Notation tm := tm_1RB1RC_1LA1RA_0RC1LD_1LB0LD.

Definition Cc_kc3 (p : positive) : cconf := (StC, (Wk p, S1, [])).
Local Notation Cc := Cc_kc3.

(** ** The certificates *)

Definition I0a : sconf := mkC StC (mkS [S0;S0;S0] [] 0 0 []) S1 (mkS [] [] 0 0 []).
Definition I0b : sconf := mkC StC (mkS [S1;S1;S1] [] 0 0 []) S1 (mkS [] [] 0 0 []).
Definition chI0 : list lstep := [SWin 6].

Lemma run_int0 : srun tm false true chI0 I0a = Some (I0b, 0, 6).
Proof. vm_compute. reflexivity. Qed.

Definition ISa : sconf := mkC StC (mkS [S1;S1;S1] [S1;S1;S1] 1 0 [S0;S0;S0]) S1 (mkS [] [] 0 0 []).
Definition ISb : sconf := mkC StC (mkS [S0;S0;S0] [S0;S0;S0] 1 0 [S1;S1;S1]) S1 (mkS [] [] 0 0 []).
Definition chIS : list lstep := [SWin 3; SCycL 3 0; SWin 6; SCycR 3; SWin 3].

Lemma run_intS : srun tm false true chIS ISa = Some (ISb, 6, 12).
Proof. vm_compute. reflexivity. Qed.

Definition F0a : sconf := mkC StC (mkS [S0;S1;S1;S1] [] 0 0 []) S1 (mkS [] [] 0 0 []).
Definition F0b : sconf := mkC StC (mkS [S1;S1;S1;S1] [] 0 0 []) S1 (mkS [] [] 0 0 []).
Definition chF0 : list lstep := [SWin 4].

Lemma run_frt0 : srun tm true true chF0 F0a = Some (F0b, 0, 4).
Proof. vm_compute. reflexivity. Qed.

Definition FSa : sconf := mkC StC (mkS [S1;S1;S1] [S1;S1;S1] 1 0 [S0;S1;S1;S1]) S1 (mkS [] [] 0 0 []).
Definition FSb : sconf := mkC StC (mkS [S0;S0;S0] [S0;S0;S0] 1 0 [S1;S1;S1;S1]) S1 (mkS [] [] 0 0 []).
Definition chFS : list lstep := [SWin 3; SCycL 3 0; SWin 4; SCycR 3; SWin 3].

Lemma run_frtS : srun tm true true chFS FSa = Some (FSb, 6, 10).
Proof. vm_compute. reflexivity. Qed.

Definition Va : sconf := mkC StC (mkS [] [S1;S1;S1] 1 0 [S1]) S1 (mkS [] [] 0 0 []).
Definition Vb : sconf := mkC StC (mkS [] [S0;S0;S0] 1 0 [S0;S1;S1;S1]) S1 (mkS [] [] 0 0 []).
Definition chV : list lstep :=
  [SRotL 1; SWin 1; SCycL 3 0; SWinL 6; SCycR 3; SWin 1; SUnrotL 1].

Lemma run_ovf : srun tm true true chV Va = Some (Vb, 6, 8).
Proof. vm_compute. reflexivity. Qed.

(** ** Anchor glue -- the only per-machine mathematics

    Each is one [Kc3Num] rewrite plus [app_assoc].  The right side of every
    anchor is empty, so its [sden] collapses to [[]]. *)

Ltac kc3_glue A H :=
  unfold Cc_kc3, cden, sden; unfold A;
  cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post];
  repeat (match goal with
          | |- context [ 0 * ?j + 0 ] => replace (0 * j + 0) with 0 by lia
          | |- context [ 1 * ?j + 0 ] => replace (1 * j + 0) with j by lia
          end);
  rewrite H; cbn [rep app]; rewrite <- ?app_assoc; cbn [app];
  rewrite ?app_nil_r; reflexivity.

Lemma gs_int0 : forall p q0, cview p = (0, Some q0) -> q0 <> xH ->
  Cc p = cden (Wk q0) [] 0 I0a.
Proof.
  intros p q0 E Hq. destruct (cview_some_Wk p 0 q0 E Hq) as (H1 & _).
  kc3_glue I0a H1.
Qed.

Lemma ge_int0 : forall p q0, cview p = (0, Some q0) -> q0 <> xH ->
  cden (Wk q0) [] 0 I0b = Cc (Pos.succ p).
Proof.
  intros p q0 E Hq. destruct (cview_some_Wk p 0 q0 E Hq) as (_ & H2).
  symmetry. kc3_glue I0b H2.
Qed.

Lemma gs_intS : forall p j q0, cview p = (S j, Some q0) -> q0 <> xH ->
  Cc p = cden (Wk q0) [] j ISa.
Proof.
  intros p j q0 E Hq. destruct (cview_some_Wk p (S j) q0 E Hq) as (H1 & _).
  kc3_glue ISa H1.
Qed.

Lemma ge_intS : forall p j q0, cview p = (S j, Some q0) -> q0 <> xH ->
  cden (Wk q0) [] j ISb = Cc (Pos.succ p).
Proof.
  intros p j q0 E Hq. destruct (cview_some_Wk p (S j) q0 E Hq) as (_ & H2).
  symmetry. kc3_glue ISb H2.
Qed.

Lemma gs_frt0 : forall p, cview p = (0, Some xH) -> Cc p = cden [] [] 0 F0a.
Proof.
  intros p E. destruct (cview_one_Wk p 0 E) as (H1 & _). kc3_glue F0a H1.
Qed.

Lemma ge_frt0 : forall p, cview p = (0, Some xH) -> cden [] [] 0 F0b = Cc (Pos.succ p).
Proof.
  intros p E. destruct (cview_one_Wk p 0 E) as (_ & H2). symmetry. kc3_glue F0b H2.
Qed.

Lemma gs_frtS : forall p j, cview p = (S j, Some xH) -> Cc p = cden [] [] j FSa.
Proof.
  intros p j E. destruct (cview_one_Wk p (S j) E) as (H1 & _). kc3_glue FSa H1.
Qed.

Lemma ge_frtS : forall p j, cview p = (S j, Some xH) ->
  cden [] [] j FSb = Cc (Pos.succ p).
Proof.
  intros p j E. destruct (cview_one_Wk p (S j) E) as (_ & H2). symmetry. kc3_glue FSb H2.
Qed.

Lemma gs_ovf : forall p j, cview p = (S j, None) -> Cc p = cden [] [] j Va.
Proof.
  intros p j E. destruct (cview_none_Wk p j E) as (H1 & _). kc3_glue Va H1.
Qed.

Lemma ge_ovf : forall p j, cview p = (S j, None) ->
  cden [] [] j Vb = Cc (Pos.succ p).
Proof.
  intros p j E. destruct (cview_none_Wk p j E) as (_ & H2). symmetry. kc3_glue Vb H2.
Qed.

(** ** The interior lap, exactly

    Both [Some] branches close on the nose, which is what
    [LapCertGlue.reach_ovf] consumes. *)

Lemma lapi : forall p j q0, cview p = (j, Some q0) ->
  exists n, 0 < n /\ csteps tm n (Cc p) = Some (Cc (Pos.succ p)).
Proof.
  intros p j q0 E.
  destruct (Pos.eq_dec q0 xH) as [Hq | Hq]; subst.
  - (* frontier *)
    destruct j as [ | j].
    + exists (0 * 0 + 4). split; [lia|].
      rewrite (gs_frt0 p E).
      rewrite (srun_sound tm true true chF0 F0a F0b 0 4 run_frt0 [] [] 0
                 ltac:(reflexivity) ltac:(reflexivity)).
      f_equal. exact (ge_frt0 p E).
    + exists (6 * j + 10). split; [lia|].
      rewrite (gs_frtS p j E).
      rewrite (srun_sound tm true true chFS FSa FSb 6 10 run_frtS [] [] j
                 ltac:(reflexivity) ltac:(reflexivity)).
      f_equal. exact (ge_frtS p j E).
  - (* interior *)
    destruct j as [ | j].
    + exists (0 * 0 + 6). split; [lia|].
      rewrite (gs_int0 p q0 E Hq).
      rewrite (srun_sound tm false true chI0 I0a I0b 0 6 run_int0 (Wk q0) [] 0
                 ltac:(discriminate) ltac:(reflexivity)).
      f_equal. exact (ge_int0 p q0 E Hq).
    + exists (6 * j + 12). split; [lia|].
      rewrite (gs_intS p j q0 E Hq).
      rewrite (srun_sound tm false true chIS ISa ISb 6 12 run_intS (Wk q0) [] j
                 ltac:(discriminate) ltac:(reflexivity)).
      f_equal. exact (ge_intS p j q0 E Hq).
Qed.

(** ** The lap *)

Lemma lap : forall p, exists n c',
  csteps tm n (Cc p) = Some c' /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intro p. destruct (cview p) as [j oq] eqn:E. destruct oq as [q0|].
  - destruct (lapi p j q0 E) as (n & Hn & Hrun).
    exists n, (Cc (Pos.succ p)).
    split; [exact Hrun | split; [reflexivity | exact Hn]].
  - destruct (cview_pos p j E) as (j' & ->).
    apply (lap_of_run tm Cc true true chV Va Vb 6 8 p j' [] []).
    + exact run_ovf.
    + reflexivity.
    + reflexivity.
    + exact (gs_ovf p j' E).
    + rewrite (ge_ovf p j' E). reflexivity.
    + lia.
Qed.

(** ** Bootstrap: the blank tape reaches [Cc 1 = (StC, ([S1], S1, []))] at
    step 3 -- the counter starts at 1 with no offset. *)

Lemma boot : exists t0, stepn tm t0 InitES = Some (lift (Cc 1)).
Proof.
  exists 3.
  assert (H : match csteps tm 3 c0 with
              | Some c => ceqb c (Cc 1) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 3 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

(** ** Visits

    Measured: all four states occur in every lap.  Reading them off the
    OVERFLOW branch plus [LapCertGlue.vis_via_ovf] (run interior laps until
    the counter overflows -- they close exactly) covers every anchor. *)

Lemma viso : forall (l : list lstep) (q : St),
  srun_st tm true true l Va = Some q ->
  forall p j, cview p = (S j, None) ->
  exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros l q Hst p j E.
  apply (vis_of_run tm Cc true true l Va p j [] []);
    [exact Hst | reflexivity | reflexivity | exact (gs_ovf p j E)].
Qed.

Lemma vis : forall p q, exists k c, csteps tm k (Cc p) = Some c /\ fst c = q.
Proof.
  intros p q.
  assert (Hi : forall p0 j q0, cview p0 = (j, Some q0) ->
            exists n, 0 < n /\ csteps tm n (Cc p0) = Some (Cc (Pos.succ p0)))
    by exact lapi.
  destruct q.
  - (* StA *)
    apply (vis_via_ovf tm Cc Hi StA), viso
      with (l := [SRotL 1; SWin 1; SCycL 3 0; SWinL 3]).
    vm_compute; reflexivity.
  - (* StB *)
    apply (vis_via_ovf tm Cc Hi StB), viso
      with (l := [SRotL 1; SWin 1; SCycL 3 0; SWinL 2]).
    vm_compute; reflexivity.
  - (* StC: the anchor state *)
    exists 0. eexists. split; reflexivity.
  - (* StD *)
    apply (vis_via_ovf tm Cc Hi StD), viso with (l := [SRotL 1; SWin 1]).
    vm_compute; reflexivity.
Qed.

Theorem nqh_1RB1RC_1LA1RA_0RC1LD_1LB0LD : NeverQuasiHaltsSt tm.
Proof.
  apply (glue_neverqh tm Cc 1).
  - exact boot.
  - intros p _. apply lap.
  - intros p q _. apply vis.
Qed.

Theorem nonhalt_1RB1RC_1LA1RA_0RC1LD_1LB0LD : NonHalt tm.
Proof. apply never_qh_nonhalt, nqh_1RB1RC_1LA1RA_0RC1LD_1LB0LD. Qed.
