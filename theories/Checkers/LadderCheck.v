(** * Checkers.LadderCheck: from the kernel's RULES to a MACHINE theorem.

    LADDER_PLAN.md 4h states exactly what Stage B did not close: the boards
    prove every RULE the certificate carries, but no [NeverQuasiHaltsSt].
    Three things were missing, and this file is the first two of them --
    (b) LIVENESS, and (a) the COVERAGE reduction for positional step 1 --
    plus the SELECTION check 4f settled.

    The shape of the argument, in the order the pieces are built:

    - **Liveness** ([GlueN]).  [LapGlue.glue_neverqh] asks that every state
      be reachable from EVERY anchor.  That is too strong for one lap: the
      fill arm is the only arm that sees the end of the counter, and it
      fires once per width, not once per anchor.  [glue_neverqhN] below is
      the same theorem with the same proof and a weaker visit premise --
      "for every [N] there is an anchor past [N] from which [q] is
      reachable" -- which the fill arm discharges.  That the fill arm fires
      unboundedly often is [tops_cofinal], and it is a THEOREM here rather
      than the certificate's measurement: within a width the value
      increases by [fm_step] and is bounded by [b^k - 1] ([fam_next_wf] is
      that invariant), so every width tops out, and the fill widens.

    - **Coverage**.  The prover checks coverage by ENUMERATING every digit
      string to [kmax = 9]; a kernel cannot.  The reduction is in two
      halves, and the split is the point:

      * the GENERIC half, [digs_decomp] and [fam_cells_class]: every digit
        string is [t^n ++ w ++ rest] or [t^k], and the cells of such a
        string are exactly one [sside] -- [s_pre ++ rep u (a*j+b) ++
        s_post ++ X] -- with [rest] in the opaque tail.  The class shape
        IS the engine's side shape, which is why an arm proved for an
        arbitrary tail covers a whole class at once.  Parametric in [t],
        and it is the bridge [flat_map_repeat] that makes it so.
      * the NON-GENERIC half, [ClassSucc] and [pos1_class]: what the
        successor of a class IS.  [fam_next] is stated on the VALUE (4g),
        which is what makes it right for Gray and for step 2, and the arms
        are patterns on CELLS; the class law is what bridges them, and it
        is one lemma per (code, step) PAIR -- per parameter value, not per
        machine and not per row.  [ClassSucc] is the interface; this file
        gives the [(Binary, 1)] instance only.  See LADDER_PLAN 4i for the
        measurement of whether [(Gray, 2)] is a second instance.

    - **Selection**.  First-applicable in the arm list, with the order a
      linearization of pattern subsumption (4f).  [order_ok] re-derives
      that property from the arms AS DATA by [vm_compute], so the kernel
      never trusts the order the search emitted and never has to decide
      membership.

    Nothing here is trusted beyond the engine it reuses: every hypothesis a
    board supplies is either a [RuleSound] discharged by [LadderKernel], or
    an equation between two concrete terms closed by [vm_compute].

    Axiom footprint: [functional_extensionality_dep], via [CTape.lift] --
    and only in the final assembly.  The class lemmas and the lap are on
    [csteps]/[cden] and are Closed under the global context. *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Census Require Import TNF_QH.
From BBB4.Counters Require Import WTape LapGlueQuiet.
From BBB4.Checkers Require Import LapDecider LapAvoid LadderKernel LadderFam.
Import ListNotations.

(** ** 1. Liveness: the glue, with the visit premise one lap can carry

    [LapGlue.glue_neverqh] verbatim, except that [Hvis] no longer ranges
    over every anchor.  The counter is indexed by [nat] here rather than
    [positive] because the premise below needs to COMPARE an anchor index
    with the bound [N], and the [k]-th anchor's global step index is at
    least [k] precisely because each lap takes at least one step. *)

Section GlueN.

Variable tm : TM.
Variable Cf : nat -> cconf.

Hypothesis Hboot : exists t0, stepn tm t0 InitES = Some (lift (Cf 0)).
Hypothesis Hlap : forall n, exists m c',
  csteps tm m (Cf n) = Some c' /\ lift c' = lift (Cf (S n)) /\ 0 < m.

(** The [n]-th anchor is reached at a global index of at least [n]. *)
Lemma glue_reachN : forall n,
  exists T, n <= T /\ stepn tm T InitES = Some (lift (Cf n)).
Proof.
  induction n as [|n IH].
  - destruct Hboot as [t0 H0]. exists t0. split; [lia | exact H0].
  - destruct IH as (T & HT & Hstep).
    destruct (Hlap n) as (m & c' & Hrun & Hlift & Hm).
    exists (T + m). split; [lia|].
    rewrite stepn_add, Hstep, (csteps_lift _ _ _ _ Hrun), Hlift. reflexivity.
Qed.

(** The weak visit premise: not "every state from every anchor", but "for
    every state and every bound, SOME anchor past the bound reaches it".
    That is what a fill arm gives -- it fires once per width, and the
    widths are cofinal. *)
Hypothesis Hvis : forall q N, exists n k c,
  N <= n /\ csteps tm k (Cf n) = Some c /\ fst c = q.

Theorem glue_neverqhN : NeverQuasiHaltsSt tm.
Proof.
  intros q _ N.
  destruct (Hvis q N) as (n & k & c & Hn & Hc & Hq).
  destruct (glue_reachN n) as (T & HT & Hstep).
  exists (T + k). split; [lia|].
  exists (lift c). split.
  - rewrite stepn_add, Hstep. apply csteps_lift; exact Hc.
  - rewrite lift_state. exact Hq.
Qed.

End GlueN.

(** ** 1b. Liveness for a QUASIHALTER: the same port, of the same premise

    Eleven of the live core's binary/step-1 rows have liveness [BCD] rather
    than [ABCD] (4i): one state stops firing after the bootstrap, so
    [board_neverqh] proves the wrong theorem for them by construction.
    [LapGlueQuiet.glue_qh_quiet] already ends in exactly the triple
    [CloseoutKit.covers_iqh_at] consumes, and its [Hvis] is the same
    too-strong premise [glue_neverqhN] weakened above.  This is that port:
    [nat]-indexed, and "for every [N] some anchor past [N] reaches [q]" for
    every [q <> qa].

    The one genuinely new obligation is [AvoidRun tm qa m (Cf n)] on the lap
    -- the lap must never enter the quiet state.  [Checkers/LapAvoid.v]
    computes it from the arm's own chain; [arm_avoid] below is the bridge. *)

Section GlueQuietN.

Variable tm : TM.
Variable Cf : nat -> cconf.
Variable qa : St.
Variable t0 sq : nat.

(** The bootstrap, at a CONCRETE index: the bound depends on it, and so does
    the window in which [qa]'s last visit is looked for. *)
Hypothesis Hboot : stepn tm t0 InitES = Some (lift (Cf 0)).

(** The lap, strengthened with avoidance of [qa]. *)
Hypothesis Hlap : forall n, exists m c',
  csteps tm m (Cf n) = Some c' /\ lift c' = lift (Cf (S n)) /\ 0 < m
  /\ AvoidRun tm qa m (Cf n).

(** The weak visit premise, for every RECURRING state. *)
Hypothesis Hvis : forall q N, q <> qa -> exists n k c,
  N <= n /\ csteps tm k (Cf n) = Some c /\ fst c = q.

(** [qa]'s last visit, and the checked [qa]-free window up to the anchor. *)
Hypothesis Hqvis : VisitsAt tm qa sq.
Hypothesis Hqwin : forall n c, sq < n < t0 ->
  stepn tm n InitES = Some c -> fst c <> qa.

Lemma gqn_lap_plain : forall n, exists m c',
  csteps tm m (Cf n) = Some c' /\ lift c' = lift (Cf (S n)) /\ 0 < m.
Proof.
  intros n. destruct (Hlap n) as (m & c' & H1 & H2 & H3 & _).
  exists m, c'. auto.
Qed.

(** The anchors march, and everything since [t0] is [qa]-free: every global
    index in [[T, T+m)] projects into the lap from [Cf n] by [csteps_prefix]
    and [csteps_lift], where [AvoidRun] speaks. *)
Lemma gqn_anchors : forall k, exists T n, k <= T /\ t0 <= T
  /\ stepn tm T InitES = Some (lift (Cf n))
  /\ (forall N c, t0 <= N < T -> stepn tm N InitES = Some c -> fst c <> qa).
Proof.
  induction k as [|k IH].
  - exists t0, 0. split; [lia|]. split; [lia|]. split; [exact Hboot|].
    intros N c HN. lia.
  - destruct IH as (T & n & HkT & Ht0T & Hstep & Hcov).
    destruct (Hlap n) as (m & c' & Hrun & Hlift & Hm & Hav).
    exists (T + m), (S n). split; [lia|]. split; [lia|]. split.
    { rewrite stepn_add, Hstep, (csteps_lift _ _ _ _ Hrun), Hlift.
      reflexivity. }
    intros N c HN HstepN.
    destruct (Nat.lt_ge_cases N T) as [HNT | HTN].
    + exact (Hcov N c ltac:(lia) HstepN).
    + replace N with (T + (N - T)) in HstepN by lia.
      rewrite stepn_add, Hstep in HstepN.
      destruct (csteps_prefix tm (N - T) m (Cf n) c' ltac:(lia) Hrun)
        as (cm & Hcm & _).
      rewrite (csteps_lift _ _ _ _ Hcm) in HstepN.
      injection HstepN as <-.
      rewrite lift_state.
      exact (Hav (N - T) cm ltac:(lia) Hcm).
Qed.

Lemma gqn_noqa : forall N c, t0 <= N ->
  stepn tm N InitES = Some c -> fst c <> qa.
Proof.
  intros N c HN Hstep.
  destruct (gqn_anchors (S N)) as (T & n & HkT & Ht0T & _ & Hcov).
  exact (Hcov N c ltac:(lia) Hstep).
Qed.

Lemma gqn_quiet : QuietAfter tm qa sq.
Proof.
  split; [exact Hqvis|].
  intros n Hn (c & Hc & Hqc).
  destruct (Nat.lt_ge_cases n t0) as [Hlt | Hge].
  - exact (Hqwin n c ltac:(lia) Hc Hqc).
  - exact (gqn_noqa n c Hge Hc Hqc).
Qed.

Lemma gqn_recurs : forall q, q <> qa ->
  forall N, exists n, N <= n /\ VisitsAt tm q n.
Proof.
  intros q Hq N.
  destruct (Hvis q N Hq) as (n & k & c & Hn & Hc & Hqc).
  destruct (glue_reachN tm Cf (ex_intro _ t0 Hboot) gqn_lap_plain n)
    as (T & HT & Hstep).
  exists (T + k). split; [lia|].
  exists (lift c). split.
  - rewrite stepn_add, Hstep. apply csteps_lift; exact Hc.
  - rewrite lift_state. exact Hqc.
Qed.

Lemma gqn_nonhalt : NonHalt tm.
Proof.
  intros n Hnone.
  destruct (glue_reachN tm Cf (ex_intro _ t0 Hboot) gqn_lap_plain n)
    as (T & HT & Hstep).
  replace T with (n + (T - n)) in Hstep by lia.
  rewrite stepn_add, Hnone in Hstep. discriminate.
Qed.

Lemma gqn_qhbound : QHBound (S sq) tm.
Proof.
  intros q s Hq.
  destruct (st_eqb q qa) eqn:Eq.
  - apply st_eqb_spec in Eq. subst q.
    destruct Hq as (HvisS & _).
    destruct (Nat.le_gt_cases s sq) as [Hle | Hgt]; [lia|].
    exfalso. destruct gqn_quiet as (_ & Hq0). exact (Hq0 s Hgt HvisS).
  - assert (Hne : q <> qa).
    { intro E. rewrite E in Eq.
      rewrite (proj2 (st_eqb_spec qa qa) eq_refl) in Eq. discriminate. }
    exfalso.
    destruct Hq as (_ & Hafter).
    destruct (gqn_recurs q Hne (S s)) as (n & Hn & Hvn).
    exact (Hafter n ltac:(lia) Hvn).
Qed.

Theorem glue_qh_quietN : NonHalt tm /\ QHBound (S sq) tm /\ QuasiHaltsSt tm.
Proof.
  split; [exact gqn_nonhalt | split; [exact gqn_qhbound |]].
  exact (quiet_after_qh tm qa sq gqn_quiet).
Qed.

End GlueQuietN.

(** ** 1c. An arm that avoids a state

    [LapAvoid.srun_avoid_sound] is stated on [srun] over [list lstep]; an
    arm's derivation is a [list rstep], which may invoke a ladder rule with
    [RU].  Every class arm the emitter builds is all-[RB] today -- the ladder
    remains one level deep in practice (4h(c)) -- so the bridge is a partial
    projection and one lemma saying [rrun] on an all-[RB] chain IS [srun].
    A chain that does invoke a rule simply projects to [None] and the arm is
    refused, which is a checkable restriction and not an assumption. *)

Fixpoint base_chain (l : list rstep) : option (list lstep) :=
  match l with
  | [] => Some []
  | RB b :: t => option_map (cons b) (base_chain t)
  | RU _ :: _ => None
  end.

Lemma base_chain_run : forall tm el er rs l lb c,
  base_chain l = Some lb -> rrun tm el er rs l c = srun tm el er lb c.
Proof.
  intros tm el er rs l; induction l as [|[b|i] l IH]; intros lb c H; cbn in H.
  - injection H as <-. reflexivity.
  - destruct (base_chain l) as [t|] eqn:E; cbn in H; [|discriminate].
    injection H as <-. cbn.
    destruct (sstep tm el er b c) as [[[c1 a1] b1]|]; [|reflexivity].
    rewrite (IH t c1 eq_refl). reflexivity.
  - discriminate.
Qed.

(** The avoidance twin of [RuleSound]: from the rule's left-hand side, at any
    carry index and against any tails the flags permit, the concrete run of
    [ca*j + cb] steps never enters [qa]. *)
Definition RuleAvoid (tm : TM) (el er : bool) (qa : St) (r : LRule) : Prop :=
  forall XL XR j,
    (el = true -> XL = []) -> (er = true -> XR = []) ->
    AvoidRun tm qa (lr_ca r * j + lr_cb r) (cden XL XR j (lr_lhs r)).

Definition check_avoid (tm : TM) (el er : bool) (qa : St) (a : LRule)
    (l : list rstep) : bool :=
  match base_chain l with
  | Some lb => srun_avoid tm el er qa lb (lr_lhs a)
  | None => false
  end.

(** No new certificate data: the avoidance is recomputed from the SAME chain
    the kernel already replays, and a chain whose trace touches [qa]
    evaluates to [false]. *)
Lemma arm_avoid : forall tm el er qa rs a l,
  check_arm tm el er rs a l = true ->
  check_avoid tm el er qa a l = true ->
  RuleAvoid tm el er qa a.
Proof.
  intros tm el er qa rs a l Hc Hav XL XR j HL HR.
  unfold check_arm, check_rule in Hc.
  destruct (rrun tm el er rs l (lr_lhs a)) as [[[c ca] cb]|] eqn:E;
    [|discriminate].
  apply andb_prop in Hc as [Hc Hcb]. apply andb_prop in Hc as [_ Hca].
  apply Nat.eqb_eq in Hca. apply Nat.eqb_eq in Hcb.
  unfold check_avoid in Hav.
  destruct (base_chain l) as [lb|] eqn:Eb; [|discriminate].
  rewrite (base_chain_run tm el er rs l lb (lr_lhs a) Eb) in E.
  rewrite <- Hca, <- Hcb.
  exact (srun_avoid_sound tm el er qa lb (lr_lhs a) c ca cb E Hav XL XR j HL HR).
Qed.

(** ** 2. The generic half of coverage: strings, classes and cells *)

Definition dig (F : Fam) (d : nat) : list Sym := nth d (fm_digs F) [].

(** [fam_cells] with its digit map named.  Definitional (eta), and it is
    what lets the rewrites below fire. *)
Lemma fam_cells_eq : forall F ds ph,
  fam_cells F ds ph
    = fm_pre F ++ flat_map (dig F) ds ++ nth ph (fm_tails F) [].
Proof. reflexivity. Qed.

(** The bridge to [sside]: a run of one digit is a run of its WORD. *)
Lemma flat_map_repeat : forall F t n rest,
  flat_map (dig F) (repeat t n ++ rest)
    = rep (dig F t) n ++ flat_map (dig F) rest.
Proof.
  intros F t n rest. induction n as [|n IH]; simpl; [reflexivity|].
  rewrite IH, app_assoc. reflexivity.
Qed.

Lemma flat_map_repeat_nil : forall F t n,
  flat_map (dig F) (repeat t n) = rep (dig F t) n.
Proof.
  intros F t n.
  rewrite <- (app_nil_r (repeat t n)), flat_map_repeat. simpl.
  apply app_nil_r.
Qed.

(** Every digit string is a run of [t] followed by a digit that is not
    [t], or a run of [t] outright.  Generic, cheap, and parametric in
    [t] -- this is the half that does not depend on the code or the step. *)
Lemma digs_decomp : forall (t : nat) (ds : list nat),
  ds = repeat t (length ds) \/
  (exists n d rest, ds = repeat t n ++ d :: rest /\ d <> t).
Proof.
  induction ds as [|x ds IH]; [left; reflexivity|].
  destruct (Nat.eq_dec x t) as [->|Hne].
  - destruct IH as [H | (n & d & rest & -> & Hd)].
    + left. simpl. f_equal. exact H.
    + right. exists (S n), d, rest. split; [reflexivity | exact Hd].
  - right. exists 0, x, ds. split; [reflexivity | exact Hne].
Qed.

(** ** 2b. The arm index: ONE scheme, and both class arms use it

    A class arm covers a run of length [n].  Which arm serves it, and at what
    block count, is the single thing LADDER_PLAN 4k found BOTH arms wanting
    and neither had.  The scheme is: [n] itself while [n] is below a
    THRESHOLD [N0] -- a flat arm, stride [0], the whole run concrete in
    [s_pre] -- and [N0 + (n - N0) mod st] at or above it, with the block
    taken [(n - N0) / st] times.

    One threshold, one stride, one offset, and [arm_index] is the one lemma
    about [n = k + s*j] that both arms use; the interior arm and the fill arm
    instantiate it at their own [(N0, st)].  That the SCHEME is shared is
    4k's gate: two parallel indexing schemes is how [fm_pre] became a fixed
    list in the first place.

    4i's [off = n mod st] is this scheme at [N0 = 0], and that is exactly why
    it stopped four rows short.  A materialisation offset of [off >= st]
    cannot be a residue, so under the old scheme the small [n] such an arm
    does not reach had no arm at all -- measured, in
    [tools/ladder/core61_armshapes.txt], as interior offsets of 2 at stride
    2.  Here they are [N0 = 1], [st = 2]: arms at [r = 0] (flat, the run
    empty), [r = 1] (odd [n]) and [r = 2] (even [n >= 2]). *)

Definition astride (N0 st r : nat) : nat := if r <? N0 then 0 else st.
Definition aoff (N0 st n : nat) : nat :=
  if n <? N0 then n else N0 + (n - N0) mod st.
Definition acnt (N0 st n : nat) : nat :=
  if n <? N0 then 0 else (n - N0) / st.

(** The whole of the arithmetic: [Nat.div_mod_eq] and [lia]. *)
Lemma arm_index : forall N0 st n, 0 < st ->
  aoff N0 st n + astride N0 st (aoff N0 st n) * acnt N0 st n = n.
Proof.
  intros N0 st n Hst. unfold aoff, acnt, astride.
  destruct (n <? N0) eqn:E.
  - lia.
  - apply Nat.ltb_ge in E.
    assert (Hc : (N0 + (n - N0) mod st <? N0) = false)
      by (apply Nat.ltb_ge; lia).
    rewrite Hc.
    pose proof (Nat.div_mod_eq (n - N0) st). lia.
Qed.

Lemma arm_index_lt : forall N0 st n, 0 < st -> aoff N0 st n < N0 + st.
Proof.
  intros N0 st n Hst. unfold aoff.
  destruct (n <? N0) eqn:E.
  - apply Nat.ltb_lt in E. lia.
  - pose proof (Nat.mod_upper_bound (n - N0) st ltac:(lia)). lia.
Qed.

(** The fill arm never sees width [0], so its own threshold being positive is
    what keeps [r = 0] out of its index range. *)
Lemma arm_index_pos : forall N0 st n, 0 < N0 -> 0 < n -> 0 < aoff N0 st n.
Proof.
  intros N0 st n HN Hn. unfold aoff.
  destruct (n <? N0) eqn:E; lia.
Qed.

(** The gray fill arm is indexed by the WIDTH and its left-hand side spells a
    fixed word at each end, so its index range starts at 2 rather than at 1.
    [2 <= N0] is what keeps [r = 0] and [r = 1] out of it. *)
Lemma arm_index_ge2 : forall N0 st n, 2 <= N0 -> 2 <= n -> 2 <= aoff N0 st n.
Proof. intros N0 st n HN Hn. unfold aoff. destruct (n <? N0); lia. Qed.

Lemma rep_rep : forall (u : list Sym) s m, rep (rep u s) m = rep u (s * m).
Proof.
  intros u s. induction m as [|m IH]; simpl.
  - rewrite Nat.mul_0_r. reflexivity.
  - rewrite IH, <- rep_add. f_equal. lia.
Qed.

Lemma rep_nil_mul : forall (u : list Sym) s n, rep u s = [] -> rep u (s * n) = [].
Proof.
  intros u s n H. destruct u as [|x u]; [apply rep_nil|].
  destruct s as [|s]; simpl in H; [|discriminate].
  rewrite Nat.mul_0_l. reflexivity.
Qed.

(** A symbolic side whose repeated block may be EMPTY.

    [stride = 0] is one end of the arm scheme above, and it needs exactly one
    thing the strided end does not: with no block there is nothing for the
    engine's window steps to walk AROUND.  [SWin] moves inside [s_pre] and no
    step carries a cell from [s_post] across the block boundary into it, so a
    side with an empty block and a non-empty [s_post] has no chain at all --
    a flat arm has to be stated with everything concrete in [s_pre].

    [blk] is that normalisation and [blk_den] says the denotation is the
    same either way, which is what keeps it a normalisation of the SHAPE
    rather than a second indexing scheme.  Both class sides below take their
    block through it. *)
Definition blk (P u : list Sym) (s : nat) (W : list Sym) : sside :=
  match rep u s with
  | [] => sflat (P ++ W)
  | v => mkS P v 1 0 W
  end.

Lemma blk_den : forall P u s W X n,
  sden X n (blk P u s W) = P ++ rep u (s * n) ++ W ++ X.
Proof.
  intros P u s W X n. unfold blk. destruct (rep u s) eqn:E.
  - rewrite sden_flat, (rep_nil_mul u s n E), <- app_assoc. reflexivity.
  - unfold sden; cbn [s_pre s_u s_a s_b s_post].
    rewrite <- E, rep_rep, Nat.mul_1_l, Nat.add_0_r. reflexivity.
Qed.

Section Cells.

Variable F : Fam.

(** The opaque tail an arm sees: everything the class does not name. *)
Definition cls_tail (rest : list nat) (ph : nat) : list Sym :=
  flat_map (dig F) rest ++ nth ph (fm_tails F) [].

(** The class [u ++ t^(r + s*m) ++ w ++ rest] IS one [sside], with [rest]
    opaque.

    The STRIDE [s] is there because the cost of a carry ripple need not be
    affine in the run length: measured (LADDER_PLAN 4i), four live-core rows
    walk the run at one cost on even lengths and another on odd, so their
    class splits into one arm per residue and each arm's block is [s] copies
    of the digit word.  [s = 1], [r = 0] is the ordinary case; [s = 0] is a
    flat arm, and [blk] is what makes that shape derivable.

    The FIXED WORD [u] before the run is [Class]'s [cs_u] and it rides in
    [s_pre] exactly as [run_side]'s [w1] does.  [(Binary, 1)]'s classes have
    [cs_u = []], which is why this side never carried one; three of
    [(Gray, 2)]'s four do (LADDER_PLAN 4i, 4n). *)
Definition cls_side (u : list nat) (t r s : nat) (w : list nat) : sside :=
  blk (fm_pre F ++ flat_map (dig F) u ++ rep (dig F t) r) (dig F t) s
      (flat_map (dig F) w).

Lemma fam_cells_class : forall u t r s m w rest ph,
  fam_cells F (u ++ repeat t (r + s * m) ++ w ++ rest) ph
    = sden (cls_tail rest ph) m (cls_side u t r s w).
Proof.
  intros u t r s m w rest ph.
  rewrite fam_cells_eq. unfold cls_side, cls_tail.
  rewrite blk_den, !flat_map_app, flat_map_repeat_nil.
  rewrite rep_add, !app_assoc. reflexivity.
Qed.

(** The class [t^(m1 + s*n + m2)] with NOTHING opaque -- the shape the fill
    arm needs, because it must see the end of the counter.  The guaranteed
    copies are materialised into [s_pre] and [s_post] (4h: without that the
    fill arm has no chain at all, since a symbolic block count cannot have
    one copy peeled off its front).

    The STRIDE [s] is the second of 4k's two knobs and it is the same knob
    [cls_side] carries: measured, six of the eleven quasihalters and four of
    the ten never-QH rows have no fill chain without it, for the same reason
    the interior arm needs one -- the cost of the widening alternates with
    the parity of the width. *)
Definition run_side (t m1 s m2 ph : nat) (w1 w2 : list nat) : sside :=
  blk (fm_pre F ++ flat_map (dig F) w1 ++ rep (dig F t) m1) (dig F t) s
      (rep (dig F t) m2 ++ flat_map (dig F) w2 ++ nth ph (fm_tails F) []).

Lemma fam_cells_run : forall t m1 s n m2 ph w1 w2,
  fam_cells F (w1 ++ repeat t (m1 + s * n + m2) ++ w2) ph
    = sden [] n (run_side t m1 s m2 ph w1 w2).
Proof.
  intros t m1 s n m2 ph w1 w2.
  rewrite fam_cells_eq. unfold run_side.
  rewrite blk_den, !flat_map_app, (flat_map_repeat_nil F t (m1 + s * n + m2)).
  rewrite !rep_add, app_nil_r, !app_assoc. reflexivity.
Qed.

(** The configuration of a class, on whichever side the counter is. *)
Definition cls_conf (sd : sside) : sconf :=
  if fm_left F
  then mkC (fm_st F) sd (fm_hs F) (sflat (fm_other F))
  else mkC (fm_st F) (sflat (fm_other F)) (fm_hs F) sd.

Definition tailL (X : list Sym) : list Sym := if fm_left F then X else [].
Definition tailR (X : list Sym) : list Sym := if fm_left F then [] else X.

Lemma cden_cls_conf : forall sd X n ds p ph,
  fam_cells F ds ph = sden X n sd ->
  cden (tailL X) (tailR X) n (cls_conf sd) = fam_cfg F (ds, p, ph).
Proof.
  intros sd X n ds p ph H.
  unfold cden, cls_conf, fam_cfg, tailL, tailR.
  destruct (fm_left F); simpl; rewrite sden_flat, app_nil_r, <- H; reflexivity.
Qed.

End Cells.

(** ** 3. The non-generic half: what a class's successor IS

    [fam_next] is stated on the VALUE.  The arms are patterns on CELLS with
    one symbolic run length.  A CLASS LAW is what bridges the two, and it
    is the one thing "the successor is a parameter" does not buy for free:
    it is a lemma per (code, step) pair.

    The interface is stated on the shape the [sside] can carry -- a fixed
    word, a run, a fixed word, an untouched tail -- because that is exactly
    the shape an arm proved for an arbitrary tail covers.  The run digit
    may CHANGE across the step ([cs_t] to [cs_t']), and both fixed words
    may, which is what a code other than positional needs. *)

Record Class : Set := mkCls {
  cs_u  : list nat;   (** the fixed word nearest the head, before the run *)
  cs_t  : nat;        (** the run digit *)
  cs_w  : list nat;   (** the fixed word after the run *)
  cs_u' : list nat;   (** and the same three, after the step *)
  cs_t' : nat;
  cs_w' : list nat
}.

Definition cls_lhs (c : Class) (n : nat) (rest : list nat) : list nat :=
  cs_u c ++ repeat (cs_t c) n ++ cs_w c ++ rest.
Definition cls_rhs (c : Class) (n : nat) (rest : list nat) : list nat :=
  cs_u' c ++ repeat (cs_t' c) n ++ cs_w' c ++ rest.

(** A class law holds of [F] when [fam_next] agrees with it on every
    instance of the class whose digits are in range AND which satisfies the
    family's own membership predicate [P].

    [P] is the one thing this interface needed that the [(Binary, 1)] case
    does not use ([fun _ => True] below).  It is there because a family
    whose step is not 1 has only PART of each width as a member (4g), and
    the discriminator can be GLOBAL rather than a local pattern: for
    [(Gray, 2)] it is the parity of the whole digit string -- which is the
    value's low bit, and [+2] preserves it.  Measured, in LADDER_PLAN 4i:
    with the parities mixed the classes contradict each other, and split by
    parity four classes OF THIS RECORD's SHAPE cover every interior string
    of every width.  So [(Gray, 2)] is a second instance of [ClassSucc] and
    not a rewrite of it -- but only once [P] is here. *)
Definition ClassSucc (F : Fam) (P : list nat -> Prop) (c : Class) : Prop :=
  forall n rest ph,
    Forall (fun x => x < fm_b F) rest -> P (cls_lhs c n rest) ->
    fam_next F (cls_lhs c n rest) ph = Some (cls_rhs c n rest).

(** *** Positional arithmetic, and the [(Binary, 1)] instance *)

Lemma val_pos_lt : forall b ds,
  1 < b -> Forall (fun d => d < b) ds -> val_pos b ds < Nat.pow b (length ds).
Proof.
  induction ds as [|d t IH]; intros Hb HF; simpl; [lia|].
  inversion HF as [|? ? Hd Ht]; subst.
  specialize (IH Hb Ht). nia.
Qed.

Lemma pos_of_val_pos : forall b ds,
  1 < b -> Forall (fun d => d < b) ds ->
  pos_of b (length ds) (val_pos b ds) = ds.
Proof.
  induction ds as [|d t IH]; intros Hb HF; simpl; [reflexivity|].
  inversion HF as [|? ? Hd Ht]; subst.
  replace (d + b * val_pos b t) with (d + val_pos b t * b) by lia.
  rewrite Nat.mod_add by lia. rewrite Nat.mod_small by lia.
  rewrite Nat.div_add by lia. rewrite Nat.div_small by lia. simpl.
  rewrite IH by assumption. reflexivity.
Qed.

Lemma pow_pos : forall b n, 0 < b -> 0 < Nat.pow b n.
Proof. induction n; intros; simpl; [lia | nia]. Qed.

Lemma val_pos_repeat_max : forall b n,
  1 < b -> val_pos b (repeat (b - 1) n) = Nat.pow b n - 1.
Proof.
  induction n as [|n IH]; intros Hb; simpl; [reflexivity|].
  rewrite IH by assumption. pose proof (pow_pos b n ltac:(lia)). nia.
Qed.

Lemma val_pos_repeat0 : forall b n l,
  val_pos b (repeat 0 n ++ l) = Nat.pow b n * val_pos b l.
Proof.
  induction n as [|n IH]; intros l; simpl; [lia|].
  rewrite IH. lia.
Qed.

Lemma val_pos_class : forall b n d rest,
  1 < b ->
  val_pos b (repeat (b - 1) n ++ d :: rest)
    = Nat.pow b n - 1 + Nat.pow b n * (d + b * val_pos b rest).
Proof.
  induction n as [|n IH]; intros d rest Hb; simpl; [lia|].
  rewrite IH by assumption. pose proof (pow_pos b n ltac:(lia)). nia.
Qed.

(** The class law for a POSITIONAL base-[b] counter stepping by 1: the
    top run ripples to zeros and the first non-top digit goes up by one.
    Elementary arithmetic on [val_pos], as 4h says -- and note that it is
    stated through [fam_next], hence through the VALUE, so that a code
    other than positional is a different proof of the same interface and
    not a different interface. *)
Definition pos1_class (F : Fam) (d : nat) : Class :=
  mkCls [] (fm_b F - 1) [d] [] 0 [S d].

Lemma pos1_class_succ : forall F d,
  1 < fm_b F -> fm_code F = Binary -> fm_step F = 1 ->
  d < fm_b F - 1 ->
  ClassSucc F (fun _ => True) (pos1_class F d).
Proof.
  intros F d Hb Hcode Hstep Hd n rest ph Hrest _.
  unfold ClassSucc, cls_lhs, cls_rhs, pos1_class; simpl.
  pose proof (pow_pos (fm_b F) n ltac:(lia)) as Hpn.
  assert (Hv : fam_value F (repeat (fm_b F - 1) n ++ d :: rest)
               = Nat.pow (fm_b F) n - 1
                 + Nat.pow (fm_b F) n * (d + fm_b F * val_pos (fm_b F) rest)).
  { unfold fam_value. rewrite Hcode. apply val_pos_class; lia. }
  assert (Hv' : fam_value F (repeat 0 n ++ S d :: rest)
                = Nat.pow (fm_b F) n * (S d + fm_b F * val_pos (fm_b F) rest)).
  { unfold fam_value. rewrite Hcode. apply val_pos_repeat0. }
  (* the successor's value is exactly one more *)
  assert (Hsucc : fam_value F (repeat 0 n ++ S d :: rest)
                  = fam_value F (repeat (fm_b F - 1) n ++ d :: rest) + fm_step F).
  { rewrite Hv, Hv', Hstep. nia. }
  assert (Hlen : length (repeat 0 n ++ S d :: rest)
                 = length (repeat (fm_b F - 1) n ++ d :: rest)).
  { rewrite !app_length, !repeat_length. reflexivity. }
  assert (Hbnd : Forall (fun x => x < fm_b F) (repeat 0 n ++ S d :: rest)).
  { apply Forall_app. split.
    - apply Forall_forall. intros x Hx. apply repeat_spec in Hx. lia.
    - constructor; [lia | exact Hrest]. }
  (* and it is still inside the width, so this is an INTERIOR step *)
  assert (Hlt : fam_value F (repeat 0 n ++ S d :: rest)
                < Nat.pow (fm_b F) (length (repeat (fm_b F - 1) n ++ d :: rest))).
  { rewrite <- Hlen. unfold fam_value. rewrite Hcode.
    apply val_pos_lt; [lia | exact Hbnd]. }
  assert (Htop : fam_is_top F (repeat (fm_b F - 1) n ++ d :: rest) = false).
  { unfold fam_is_top. rewrite (fam_lim_bin F _ Hcode).
    apply Nat.ltb_ge. lia. }
  unfold fam_next. rewrite Htop.
  rewrite <- Hsucc. unfold fam_of_value.
  rewrite (fam_lim_bin F _ Hcode), Hcode.
  destruct (Nat.ltb_spec (fam_value F (repeat 0 n ++ S d :: rest))
              (Nat.pow (fm_b F)
                 (length (repeat (fm_b F - 1) n ++ d :: rest)))); [|lia].
  f_equal. rewrite <- Hlen.
  unfold fam_value. rewrite Hcode.
  apply pos_of_val_pos; [lia | exact Hbnd].
Qed.

(** The other half of the split: a run of the top digit IS the top, and
    there the phase's FILL LAW applies instead. *)
Lemma pos1_is_top : forall F k,
  1 < fm_b F -> fm_code F = Binary -> fm_step F = 1 ->
  fam_is_top F (repeat (fm_b F - 1) k) = true.
Proof.
  intros F k Hb Hcode Hstep. unfold fam_is_top, fam_value.
  rewrite (fam_lim_bin F _ Hcode).
  rewrite Hcode, repeat_length, val_pos_repeat_max by lia.
  rewrite Hstep. pose proof (pow_pos (fm_b F) k ltac:(lia)). apply Nat.ltb_lt. lia.
Qed.

Lemma pos1_fill : forall F k ph,
  1 < fm_b F -> fm_code F = Binary -> fm_step F = 1 ->
  fam_next F (repeat (fm_b F - 1) k) ph = fill_apply (fam_fill F ph) k.
Proof.
  intros F k ph Hb Hcode Hstep. unfold fam_next.
  rewrite (pos1_is_top F k Hb Hcode Hstep), repeat_length. reflexivity.
Qed.

(** The top of a width IS the all-max run, for a positional counter: the
    only string of width [k] whose value is [b^k - 1].  This is the half of
    the case split the fill arm serves. *)
Lemma pos_of_max : forall b k,
  1 < b -> pos_of b k (Nat.pow b k - 1) = repeat (b - 1) k.
Proof.
  induction k as [|k IH]; intros Hb; simpl; [reflexivity|].
  pose proof (pow_pos b k ltac:(lia)).
  replace (b * Nat.pow b k - 1) with ((b - 1) + (Nat.pow b k - 1) * b) by nia.
  rewrite Nat.mod_add by lia. rewrite Nat.mod_small by lia.
  rewrite Nat.div_add by lia. rewrite Nat.div_small by lia. simpl.
  rewrite IH by assumption. reflexivity.
Qed.

Lemma pos1_top_shape : forall F ds,
  1 < fm_b F -> fm_code F = Binary -> fm_step F = 1 ->
  Forall (fun d => d < fm_b F) ds ->
  fam_is_top F ds = true ->
  ds = repeat (fm_b F - 1) (length ds).
Proof.
  intros F ds Hb Hcode Hstep Hbnd Htop.
  assert (Hlt : fam_value F ds < Nat.pow (fm_b F) (length ds))
    by (unfold fam_value; rewrite Hcode; apply val_pos_lt; [lia | exact Hbnd]).
  unfold fam_is_top in Htop. rewrite (fam_lim_bin F _ Hcode) in Htop.
  apply Nat.ltb_lt in Htop. rewrite Hstep in Htop.
  assert (Hv : fam_value F ds = Nat.pow (fm_b F) (length ds) - 1) by lia.
  unfold fam_value in Hv. rewrite Hcode in Hv.
  transitivity (pos_of (fm_b F) (length ds) (val_pos (fm_b F) ds)).
  - symmetry. apply pos_of_val_pos; assumption.
  - rewrite Hv. apply pos_of_max; lia.
Qed.

(** ** 3b. The non-generic half again, at [(Gray, 2)]

    LADDER_PLAN 4i asked whether the class-successor lemma can be stated so
    that [(Gray, 2)] is a second INSTANCE rather than a rewrite, and measured
    that it can: four classes OF [Class]'s OWN SHAPE cover every interior
    string of every width, and what has to widen is the PREMISE -- the
    predicate [P], because with a step other than 1 only PART of each width is
    a member and the discriminator is the parity of the whole digit string.
    4n's probe re-derived the same four from the machines themselves.  This is
    that instance, and the record does not widen.

    Everything below is about base 2 and the reflected code, so it is written
    on [gval], the value [fam_value] computes there.  The one structural fact
    the arithmetic needs is that [gdec]'s entry at [i] is the parity of the
    digit sum from [i] up -- hence [gval_cons], hence [gval_app], which splits
    the value at any point into a bounded PREFIX contribution [gpre] and the
    suffix's own value.  A class's two sides differ only in their fixed words,
    so the run never has to be evaluated: only [gpre] does.

    The parity is a PARAMETER [p] and not a constant.  Five of the six gray
    core rows are even and one is odd, and the odd family's classes are the
    even family's with the two sides exchanged -- which written out is the
    same table with [p] where [0] stood:

      [p;p]     0^n              -> [1-p;1-p] 0^n
      [p;1-p]   1^n              -> [1-p;p]   1^n
      [1-p]     0^n ++ [1;p]     -> [p]       0^n ++ [1;1-p]
      [1-p]     0^n ++ [1;1-p]   -> [p]       0^n ++ [1;p]

    At [p = 0] those are 4i's four verbatim.  [tools/ladder/gray2check.py] is
    the oracle: it checks the table, the split and the top shape by
    enumerating every bounded string of widths 2..13 for all six rows. *)

Fixpoint dsum (ds : list nat) : nat :=
  match ds with
  | [] => 0
  | d :: t => d + dsum t
  end.

Lemma dsum_cons : forall d t, dsum (d :: t) = d + dsum t.
Proof. reflexivity. Qed.

Lemma dsum_app : forall l r, dsum (l ++ r) = dsum l + dsum r.
Proof.
  induction l as [|x l IH]; intros r; [reflexivity|].
  cbn [app]. rewrite !dsum_cons, IH. lia.
Qed.

Lemma dsum_repeat : forall t n, dsum (repeat t n) = n * t.
Proof.
  induction n as [|n IH]; [reflexivity|].
  cbn [repeat]. rewrite dsum_cons, IH. lia.
Qed.

Definition gval (ds : list nat) : nat := val_pos 2 (gdec 2 ds).

Lemma gdec_hd : forall ds, hd 0 (gdec 2 ds) = dsum ds mod 2.
Proof.
  induction ds as [|d t IH]; [reflexivity|].
  cbn [gdec hd]. rewrite IH, dsum_cons.
  rewrite Nat.add_mod_idemp_r by lia. reflexivity.
Qed.

Lemma gval_cons : forall d t, gval (d :: t) = (d + dsum t) mod 2 + 2 * gval t.
Proof.
  intros d t. unfold gval. cbn [gdec val_pos].
  rewrite gdec_hd, Nat.add_mod_idemp_r by lia. reflexivity.
Qed.

Lemma gval_nil : gval [] = 0.
Proof. reflexivity. Qed.

Lemma dsum_nil : dsum [] = 0.
Proof. reflexivity. Qed.

Fixpoint gpre (a : list nat) (p : nat) : nat :=
  match a with
  | [] => 0
  | d :: t => (d + dsum t + p) mod 2 + 2 * gpre t p
  end.

Lemma gval_app : forall a l,
  gval (a ++ l) = gpre a (dsum l) + Nat.pow 2 (length a) * gval l.
Proof.
  induction a as [|d a IH]; intros l; simpl (_ ++ _).
  - simpl. lia.
  - rewrite gval_cons, IH, dsum_app.
    cbn [gpre length]. rewrite Nat.pow_succ_r by lia.
    rewrite Nat.add_assoc. lia.
Qed.

Lemma gpre_repeat0 : forall n l p,
  gpre (repeat 0 n ++ l) p
  = ((dsum l + p) mod 2) * (Nat.pow 2 n - 1) + Nat.pow 2 n * gpre l p.
Proof.
  induction n as [|n IH]; intros l p; simpl (repeat _ _ ++ _).
  - simpl. lia.
  - cbn [gpre]. rewrite IH, dsum_app, dsum_repeat.
    replace (0 + (n * 0 + dsum l) + p) with (dsum l + p) by lia.
    pose proof (pow_pos 2 n ltac:(lia)).
    rewrite Nat.pow_succ_r by lia. nia.
Qed.

Lemma gpre_repeat0_nil : forall n p,
  gpre (repeat 0 n) p = (p mod 2) * (Nat.pow 2 n - 1).
Proof.
  intros n p. rewrite <- (app_nil_r (repeat 0 n)), gpre_repeat0.
  rewrite dsum_nil. cbn [gpre]. rewrite Nat.add_0_l. lia.
Qed.

Lemma gval_mod2 : forall ds, gval ds mod 2 = dsum ds mod 2.
Proof.
  destruct ds as [|d t]; [reflexivity|].
  rewrite gval_cons, dsum_cons.
  replace (2 * gval t) with (gval t * 2) by lia.
  rewrite Nat.mod_add by lia. rewrite Nat.mod_mod by lia. reflexivity.
Qed.

Lemma gval_shift : forall A B C,
  length A = length B ->
  gpre B (dsum C) = gpre A (dsum C) + 2 ->
  gval (B ++ C) = gval (A ++ C) + 2.
Proof. intros A B C HL HG. rewrite !gval_app, HL, HG. lia. Qed.

(* ---------------------------------------------------------- the codec -- *)

Lemma gdec_lt : forall b ds, 0 < b -> Forall (fun x => x < b) (gdec b ds).
Proof.
  induction ds as [|d t IH]; intros Hb; simpl; constructor;
    [apply Nat.mod_upper_bound; lia | apply IH; exact Hb].
Qed.

Lemma gdec_hd_lt : forall b ds, 0 < b -> hd 0 (gdec b ds) < b.
Proof.
  intros b ds Hb. destruct ds as [|d t]; simpl; [lia|].
  apply Nat.mod_upper_bound; lia.
Qed.

Lemma genc_lt : forall b ns, 0 < b -> Forall (fun x => x < b) (genc b ns).
Proof.
  induction ns as [|n t IH]; intros Hb; simpl; constructor;
    [apply Nat.mod_upper_bound; lia | apply IH; exact Hb].
Qed.

Lemma modb_sub_add : forall b n m, 1 < b -> n < b -> m < b ->
  ((n + m) mod b + (b - m)) mod b = n.
Proof.
  intros b n m Hb Hn Hm.
  destruct (Nat.le_gt_cases b (n + m)) as [H|H].
  - assert (E : (n + m) mod b = n + m - b).
    { transitivity ((n + m - b + 1 * b) mod b).
      - f_equal. lia.
      - rewrite Nat.mod_add by lia. apply Nat.mod_small; lia. }
    rewrite E. replace (n + m - b + (b - m)) with n by lia.
    apply Nat.mod_small; lia.
  - assert (E : (n + m) mod b = n + m) by (apply Nat.mod_small; lia).
    rewrite E. replace (n + m + (b - m)) with (n + 1 * b) by lia.
    rewrite Nat.mod_add by lia. apply Nat.mod_small; lia.
Qed.

Lemma genc_gdec : forall b ds, 1 < b -> Forall (fun d => d < b) ds ->
  genc b (gdec b ds) = ds.
Proof.
  induction ds as [|d t IH]; intros Hb HF; [reflexivity|].
  inversion HF as [|? ? Hd Ht]; subst.
  cbn [gdec genc]. rewrite IH by assumption. f_equal.
  pose proof (gdec_hd_lt b t ltac:(lia)) as Hh.
  rewrite (Nat.mod_small (hd 0 (gdec b t)) b) by exact Hh.
  rewrite Nat.mod_mod by lia.
  apply modb_sub_add; assumption.
Qed.

Lemma mod2_add : forall c s e, s mod 2 = e -> (c + s) mod 2 = (c + e) mod 2.
Proof. intros c s e H. rewrite <- H, Nat.add_mod_idemp_r by lia. reflexivity. Qed.

Lemma mod2_cases : forall s, s mod 2 = 0 \/ s mod 2 = 1.
Proof. intros s. pose proof (Nat.mod_upper_bound s 2 ltac:(lia)). lia. Qed.

Lemma gpre1 : forall a s, gpre [a] s = (a + s) mod 2.
Proof.
  intros a s. cbn [gpre]. rewrite dsum_nil.
  replace (a + 0 + s) with (a + s) by lia. lia.
Qed.

Lemma gpre2 : forall a b s,
  gpre [a; b] s = (a + b + s) mod 2 + 2 * ((b + s) mod 2).
Proof.
  intros a b s. cbn [gpre]. rewrite !dsum_cons, dsum_nil.
  replace (b + 0) with b by lia. replace (b + 0 + s) with (b + s) by lia. lia.
Qed.

Lemma gpre_run : forall a c n s,
  gpre (a :: (repeat 0 n ++ [1; c])) s
  = (a + (1 + c) + s) mod 2
    + 2 * (((1 + c + s) mod 2) * (Nat.pow 2 n - 1)
           + Nat.pow 2 n * ((1 + c + s) mod 2 + 2 * ((c + s) mod 2))).
Proof.
  intros a c n s. cbn [gpre]. rewrite gpre_repeat0, gpre2, dsum_app, dsum_repeat.
  rewrite !dsum_cons, dsum_nil.
  replace (n * 0 + (1 + (c + 0))) with (1 + c) by lia.
  replace (1 + (c + 0)) with (1 + c) by lia.
  reflexivity.
Qed.

Definition g2c (p i : nat) : Class :=
  match i with
  | 0 => mkCls [p; p] 0 [] [1 - p; 1 - p] 0 []
  | 1 => mkCls [p; 1 - p] 1 [] [1 - p; p] 1 []
  | 2 => mkCls [1 - p] 0 [1; p] [p] 0 [1; 1 - p]
  | _ => mkCls [1 - p] 0 [1; 1 - p] [p] 0 [1; p]
  end.

Definition g2par (p : nat) (ds : list nat) : Prop := dsum ds mod 2 = p.

Lemma g2c_step01 : forall p p' u u' t n rest,
  p + p' = 1 -> u + u' = 1 ->
  dsum ([p; u] ++ repeat t n ++ rest) mod 2 = p ->
  gval ([p'; u'] ++ repeat t n ++ rest)
  = gval ([p; u] ++ repeat t n ++ rest) + 2.
Proof.
  intros p p' u u' t n rest Hp Hu H.
  apply (gval_shift [p; u] [p'; u'] (repeat t n ++ rest)); [reflexivity|].
  rewrite !gpre2.
  rewrite dsum_app in H. cbn [dsum] in H.
  set (S := dsum (repeat t n ++ rest)) in *.
  destruct (mod2_cases S) as [HS|HS];
    rewrite !(mod2_add _ _ _ HS) in H; rewrite !(mod2_add _ _ _ HS);
    assert (Hc : p = 0 /\ p' = 1 \/ p = 1 /\ p' = 0) by lia;
    assert (Hd : u = 0 /\ u' = 1 \/ u = 1 /\ u' = 0) by lia;
    destruct Hc as [[-> ->]|[-> ->]]; destruct Hd as [[-> ->]|[-> ->]];
    cbn in H |- *; lia.
Qed.

Lemma g2c_step23 : forall a a' c c' n rest,
  a + a' = 1 -> c + c' = 1 ->
  dsum ([a] ++ repeat 0 n ++ [1; c] ++ rest) mod 2 = a' ->
  gval ([a'] ++ repeat 0 n ++ [1; c'] ++ rest)
  = gval ([a] ++ repeat 0 n ++ [1; c] ++ rest) + 2.
Proof.
  intros a a' c c' n rest Ha Hc H.
  assert (Hd : dsum ([a] ++ repeat 0 n ++ [1; c] ++ rest)
               = a + (1 + c) + dsum rest)
    by (rewrite !dsum_app, dsum_repeat; cbn [dsum]; lia).
  rewrite Hd in H.
  rewrite (app_assoc (repeat 0 n) [1; c] rest),
          (app_assoc (repeat 0 n) [1; c'] rest).
  apply (gval_shift (a :: (repeat 0 n ++ [1; c]))
                    (a' :: (repeat 0 n ++ [1; c'])) rest).
  - cbn [length]. rewrite !app_length, !repeat_length. reflexivity.
  - rewrite !gpre_run.
    pose proof (pow_pos 2 n ltac:(lia)).
    set (S := dsum rest) in *.
    destruct (mod2_cases S) as [HS|HS];
      rewrite !(mod2_add _ _ _ HS) in H; rewrite !(mod2_add _ _ _ HS);
      assert (Hx : a = 0 /\ a' = 1 \/ a = 1 /\ a' = 0) by lia;
      assert (Hy : c = 0 /\ c' = 1 \/ c = 1 /\ c' = 0) by lia;
      destruct Hx as [[-> ->]|[-> ->]]; destruct Hy as [[-> ->]|[-> ->]];
      cbn in H |- *; nia.
Qed.

Definition g2top (p k : nat) : list nat := (1 - p) :: repeat 0 (k - 2) ++ [1].

Lemma g2top_length : forall p k, 2 <= k -> length (g2top p k) = k.
Proof.
  intros p k Hk. unfold g2top. cbn [length].
  rewrite app_length, repeat_length. cbn [length]. lia.
Qed.

Lemma g2top_bnd : forall p k, p < 2 -> Forall (fun d : nat => d < 2) (g2top p k).
Proof.
  intros p k Hp. unfold g2top. apply Forall_cons; [lia|].
  apply Forall_app. split.
  - apply Forall_forall. intros x Hx. apply repeat_spec in Hx. lia.
  - apply Forall_cons; [lia | apply Forall_nil].
Qed.

Lemma g2top_dsum : forall p k, p < 2 -> dsum (g2top p k) mod 2 = p.
Proof.
  intros p k Hp. unfold g2top. cbn [dsum].
  rewrite dsum_app, dsum_repeat. cbn [dsum].
  replace (1 - p + ((k - 2) * 0 + (1 + 0))) with (2 - p) by lia.
  destruct p as [|[|p]]; try lia; reflexivity.
Qed.

Lemma g2top_gval : forall p k, p < 2 -> 2 <= k ->
  gval (g2top p k) = Nat.pow 2 k - 2 + p.
Proof.
  intros p k Hp Hk. unfold g2top.
  change ((1 - p) :: (repeat 0 (k - 2) ++ [1]))
    with ([1 - p] ++ (repeat 0 (k - 2) ++ [1])).
  rewrite gval_app. cbn [length]. rewrite gpre1.
  rewrite dsum_app, dsum_repeat. cbn [dsum].
  rewrite gval_app, gpre_repeat0_nil. cbn [dsum].
  rewrite gval_cons. cbn [dsum]. rewrite gval_nil, repeat_length.
  pose proof (pow_pos 2 (k - 2) ltac:(lia)).
  assert (Hpw : Nat.pow 2 k = 4 * Nat.pow 2 (k - 2)).
  { replace k with (S (S (k - 2))) at 1 by lia.
    rewrite !Nat.pow_succ_r by lia. lia. }
  replace (1 - p + ((k - 2) * 0 + (1 + 0))) with (2 - p) by lia.
  replace ((1 + 0) mod 2) with 1 by reflexivity.
  replace (Nat.pow 2 1) with 2 by reflexivity.
  destruct p as [|[|p]]; try lia;
    [ replace ((2 - 0) mod 2) with 0 by reflexivity
    | replace ((2 - 1) mod 2) with 1 by reflexivity ]; lia.
Qed.

Lemma gray_split : forall p ds, p < 2 ->
  Forall (fun d : nat => d < 2) ds -> dsum ds mod 2 = p -> 2 <= length ds ->
  ds = g2top p (length ds)
  \/ exists i n rest, i < 4 /\ Forall (fun d : nat => d < 2) rest
                      /\ ds = cls_lhs (g2c p i) n rest.
Proof.
  intros p ds Hp Hbnd Hpar Hk.
  destruct ds as [|d0 ds1]; [cbn [length] in Hk; lia|].
  assert (Hd0 : d0 < 2) by exact (Forall_inv Hbnd).
  pose proof (Forall_inv_tail Hbnd) as Hbnd1.
  destruct (Nat.eq_dec d0 p) as [Hd0p|Hne].
  - (* the first digit is the parity: the class fires at run length 0, and the
       second digit picks which *)
    destruct ds1 as [|d1 ds2]; [cbn [length] in Hk; lia|].
    assert (Hd1 : d1 < 2) by exact (Forall_inv Hbnd1).
    pose proof (Forall_inv_tail Hbnd1) as Hbnd2.
    right. destruct (Nat.eq_dec d1 p) as [Hd1p|Hne1].
    + exists 0, 0, ds2. split; [lia|]. split; [exact Hbnd2|].
      unfold cls_lhs. cbn [g2c cs_u cs_t cs_w repeat app].
      rewrite Hd0p, Hd1p. reflexivity.
    + exists 1, 0, ds2. split; [lia|]. split; [exact Hbnd2|].
      unfold cls_lhs. cbn [g2c cs_u cs_t cs_w repeat app].
      rewrite Hd0p. f_equal. f_equal. lia.
  - (* the first digit is the other one.  Walk the zeros after it: there IS a
       1 past them, because [(1-p) ++ 0^m] has digit sum [1-p] and the parity
       says [p].  If it is the LAST digit the string is the top. *)
    assert (Hd0' : d0 = 1 - p) by lia.
    destruct (digs_decomp 0 ds1) as [Hall | (n & d & rest & Hds1 & Hd)].
    + exfalso.
      assert (Hs : dsum ds1 = 0)
        by (rewrite Hall at 1; rewrite dsum_repeat; lia).
      cbn [dsum] in Hpar. rewrite Hs, Hd0' in Hpar.
      destruct p as [|[|p]]; try lia; cbn in Hpar; lia.
    + assert (Hd1 : d = 1).
      { rewrite Hds1 in Hbnd1. apply Forall_app in Hbnd1 as [_ Hb2].
        assert (Hx : d < 2) by exact (Forall_inv Hb2). lia. }
      assert (Hbr : Forall (fun d : nat => d < 2) rest).
      { rewrite Hds1 in Hbnd1. apply Forall_app in Hbnd1 as [_ Hb2].
        exact (Forall_inv_tail Hb2). }
      subst d. destruct rest as [|c rest'].
      * left. unfold g2top. rewrite Hd0', Hds1. repeat f_equal.
        cbn [length]. rewrite app_length, repeat_length. cbn [length]. lia.
      * right. assert (Hc : c < 2) by exact (Forall_inv Hbr).
        pose proof (Forall_inv_tail Hbr) as Hbr'.
        destruct (Nat.eq_dec c p) as [Hcp|Hcn].
        -- exists 2, n, rest'. split; [lia|]. split; [exact Hbr'|].
           unfold cls_lhs. cbn [g2c cs_u cs_t cs_w].
           rewrite Hd0', Hds1, Hcp. reflexivity.
        -- exists 3, n, rest'. split; [lia|]. split; [exact Hbr'|].
           unfold cls_lhs. cbn [g2c cs_u cs_t cs_w].
           rewrite Hd0', Hds1. cbn [app]. repeat f_equal. lia.
Qed.


Section Gray2.

Variable F : Fam.
Hypothesis HbF : fm_b F = 2.
Hypothesis HcF : fm_code F = Gray.
Hypothesis HsF : fm_step F = 2.

Lemma gray_value : forall ds, fam_value F ds = gval ds.
Proof. intros ds. unfold fam_value, gval. rewrite HcF, HbF. reflexivity. Qed.

Lemma gray_val_lt : forall ds, fam_value F ds < Nat.pow 2 (length ds).
Proof.
  intros ds. rewrite gray_value. unfold gval.
  rewrite <- (gdec_length 2 ds).
  apply val_pos_lt; [lia | apply gdec_lt; lia].
Qed.

Lemma gray_roundtrip : forall ds, Forall (fun d => d < 2) ds ->
  fam_of_value F (fam_value F ds) (length ds) = Some ds.
Proof.
  intros ds Hbnd. pose proof (gray_val_lt ds) as Hlt.
  unfold fam_of_value. rewrite (fam_lim_gray F _ HcF), HbF, HcF.
  destruct (Nat.ltb_spec (fam_value F ds) (Nat.pow 2 (length ds))); [|lia].
  f_equal. rewrite gray_value. unfold gval.
  rewrite <- (gdec_length 2 ds).
  rewrite (pos_of_val_pos 2 (gdec 2 ds) ltac:(lia) (gdec_lt 2 ds ltac:(lia))).
  apply genc_gdec; [lia | exact Hbnd].
Qed.

Lemma gray_inj : forall a c,
  Forall (fun d => d < 2) a -> Forall (fun d => d < 2) c ->
  length a = length c -> fam_value F a = fam_value F c -> a = c.
Proof.
  intros a c Ha Hc HL HV.
  assert (E : Some a = Some c).
  { rewrite <- (gray_roundtrip a Ha), <- (gray_roundtrip c Hc), HL, HV.
    reflexivity. }
  injection E; auto.
Qed.

Lemma gray_next_of : forall ds nd ph,
  Forall (fun d => d < 2) nd ->
  length nd = length ds ->
  fam_value F nd = fam_value F ds + 2 ->
  fam_is_top F ds = false /\ fam_next F ds ph = Some nd.
Proof.
  intros ds nd ph Hnd HL HV.
  pose proof (gray_val_lt nd) as Hlt. rewrite HL in Hlt.
  pose proof (pow_pos 2 (length ds) ltac:(lia)).
  assert (Htop : fam_is_top F ds = false).
  { unfold fam_is_top. rewrite (fam_lim_gray F _ HcF), HbF, HsF.
    apply Nat.ltb_ge. lia. }
  split; [exact Htop|].
  unfold fam_next. rewrite Htop, HsF, <- HV, <- HL.
  apply gray_roundtrip; exact Hnd.
Qed.

Lemma g2c_len : forall p i n rest,
  length (cls_rhs (g2c p i) n rest) = length (cls_lhs (g2c p i) n rest).
Proof.
  intros p i n rest. unfold cls_lhs, cls_rhs.
  destruct i as [|[|[|i]]]; cbn [g2c cs_u cs_t cs_w cs_u' cs_t' cs_w'];
    rewrite !app_length, !repeat_length; reflexivity.
Qed.

Lemma g2c_bnd : forall p i n rest, p < 2 -> Forall (fun d => d < 2) rest ->
  Forall (fun d => d < 2) (cls_rhs (g2c p i) n rest).
Proof.
  intros p i n rest Hp Hr. unfold cls_rhs.
  assert (Hrep : forall t m, t < 2 -> Forall (fun d : nat => d < 2) (repeat t m)).
  { intros t m Ht. apply Forall_forall. intros x Hx.
    apply repeat_spec in Hx. lia. }
  destruct i as [|[|[|i]]]; cbn [g2c cs_u' cs_t' cs_w'];
    repeat (apply Forall_app; split);
    first [ assumption
          | (apply Hrep; lia)
          | (repeat (apply Forall_cons; [lia|]); apply Forall_nil) ].
Qed.

Lemma gray2_class : forall p i n rest, p < 2 ->
  Forall (fun d => d < 2) rest -> g2par p (cls_lhs (g2c p i) n rest) ->
  fam_is_top F (cls_lhs (g2c p i) n rest) = false
  /\ (forall ph, fam_next F (cls_lhs (g2c p i) n rest) ph
                 = Some (cls_rhs (g2c p i) n rest))
  /\ g2par p (cls_rhs (g2c p i) n rest).
Proof.
  intros p i n rest Hp Hrest Hpar.
  assert (Hv : fam_value F (cls_rhs (g2c p i) n rest)
               = fam_value F (cls_lhs (g2c p i) n rest) + 2).
  { rewrite !gray_value. unfold g2par in Hpar.
    destruct i as [|[|[|i]]]; unfold cls_lhs, cls_rhs in *;
      cbn [g2c cs_u cs_t cs_w cs_u' cs_t' cs_w'] in *.
    - exact (g2c_step01 p (1 - p) p (1 - p) 0 n rest
               ltac:(lia) ltac:(lia) Hpar).
    - exact (g2c_step01 p (1 - p) (1 - p) p 1 n rest
               ltac:(lia) ltac:(lia) Hpar).
    - exact (g2c_step23 (1 - p) p p (1 - p) n rest
               ltac:(lia) ltac:(lia) Hpar).
    - exact (g2c_step23 (1 - p) p (1 - p) p n rest
               ltac:(lia) ltac:(lia) Hpar). }
  destruct (gray_next_of (cls_lhs (g2c p i) n rest) (cls_rhs (g2c p i) n rest) 0
              (g2c_bnd p i n rest Hp Hrest) (g2c_len p i n rest) Hv)
    as (Htop & _).
  split; [exact Htop | split].
  - intros ph.
    exact (proj2 (gray_next_of (cls_lhs (g2c p i) n rest)
                    (cls_rhs (g2c p i) n rest) ph
                    (g2c_bnd p i n rest Hp Hrest) (g2c_len p i n rest) Hv)).
  - unfold g2par in *.
    rewrite <- gval_mod2 in Hpar. rewrite <- gval_mod2.
    rewrite <- gray_value in Hpar. rewrite <- gray_value. rewrite Hv.
    replace (fam_value F (cls_lhs (g2c p i) n rest) + 2)
      with (fam_value F (cls_lhs (g2c p i) n rest) + 1 * 2) by lia.
    rewrite Nat.mod_add by lia. exact Hpar.
Qed.

Lemma gray2_class_succ : forall p i, p < 2 -> ClassSucc F (g2par p) (g2c p i).
Proof.
  intros p i Hp n rest ph Hrest Hpar. rewrite HbF in Hrest.
  exact (proj1 (proj2 (gray2_class p i n rest Hp Hrest Hpar)) ph).
Qed.

Lemma g2top_value : forall p k, p < 2 -> 2 <= k ->
  fam_value F (g2top p k) = Nat.pow 2 k - 2 + p.
Proof.
  intros p k Hp Hk. rewrite gray_value. apply g2top_gval; assumption.
Qed.

Lemma g2top_is_top : forall p k, p < 2 -> 2 <= k ->
  fam_is_top F (g2top p k) = true.
Proof.
  intros p k Hp Hk. unfold fam_is_top.
  rewrite (fam_lim_gray F _ HcF), HbF, HsF.
  rewrite (g2top_length p k Hk), (g2top_value p k Hp Hk).
  pose proof (pow_pos 2 k ltac:(lia)). apply Nat.ltb_lt. lia.
Qed.

Lemma gray_top_shape : forall p ds, p < 2 ->
  Forall (fun d : nat => d < 2) ds -> dsum ds mod 2 = p -> 2 <= length ds ->
  fam_is_top F ds = true -> ds = g2top p (length ds).
Proof.
  intros p ds Hp Hbnd Hpar Hk Htop.
  apply gray_inj;
    [exact Hbnd | apply g2top_bnd; lia
     | rewrite g2top_length by lia; reflexivity |].
  rewrite (g2top_value p (length ds) Hp Hk).
  pose proof (gray_val_lt ds) as Hlt.
  unfold fam_is_top in Htop.
  rewrite (fam_lim_gray F _ HcF), HbF, HsF in Htop.
  apply Nat.ltb_lt in Htop.
  assert (Hm : fam_value F ds mod 2 = p)
    by (rewrite gray_value, gval_mod2; exact Hpar).
  remember (Nat.pow 2 (length ds - 1)) as q eqn:Eq.
  assert (Hq1 : 1 <= q) by (subst q; apply pow_pos; lia).
  assert (Hpw : Nat.pow 2 (length ds) = 2 * q).
  { subst q. replace (length ds) with (S (length ds - 1)) at 1 by lia.
    rewrite Nat.pow_succ_r by lia. reflexivity. }
  rewrite Hpw in Hlt, Htop |- *.
  assert (Hv : fam_value F ds = 2 * q - 2 \/ fam_value F ds = 2 * q - 1) by lia.
  destruct Hv as [Hv|Hv]; rewrite Hv in Hm |- *.
  - replace (2 * q - 2) with ((q - 1) * 2) in Hm by lia.
    rewrite Nat.mod_mul in Hm by lia. lia.
  - replace (2 * q - 1) with (1 + (q - 1) * 2) in Hm by lia.
    rewrite Nat.mod_add in Hm by lia. cbn in Hm. lia.
Qed.

End Gray2.

(** ** 3c. The non-generic half a third time, at [(Fib, 1)]

    LADDER_PLAN 4p measured five core rows whose counter is WEIGHTED: the
    digit at index [i] carries [1, 1, 2, 3, 5, 8, ...] and the widths spell
    2, 3, 5, 8, 13, 21 members rather than [2^k].  [LadderFam]'s [Fib] is
    that arithmetic; this is the THIRD instance of [ClassSucc] over it, and
    the record does not widen -- 4i's result, held for [(Gray, 2)] by 4o and
    held again here.

    What is different from both earlier instances is that the numeration is
    REDUNDANT.  [fibw 0 = fibw 1 = 1], so [1;0;0] and [0;1;0] have the same
    value, and "which string of a width the counter stands on" is not
    determined by the value alone.  [ClassSucc]'s predicate [P] -- which
    [(Binary, 1)] takes as [True] and [(Gray, 2)] as a parity -- is here a
    MEMBERSHIP predicate on the digit string, and the risky lemma is that
    the value is injective ON IT, so that [fam_of_value] is a genuine
    inverse.

    Membership, LSB-first (4p, checked against the orbit read off all five
    machines by [tools/ladder/fibmem.py]): an optional leading [1], then a
    concatenation of the blocks [[0]] and [[1;1]].  Equivalently, every
    maximal run of [1]s has EVEN length except the one that reaches index 0.
    Equivalently again, and this is [fibokb]: at every [0] the number of
    [1]s ABOVE it is even.

    The last form is a two-state automaton read from the most significant
    digit DOWN, and [o] is its state: [E] (no run open) accepts a [0], [O]
    (a run open with an odd count) does not, and a [1] flips the two.  Both
    states accept at the end, which is the "optional leading [1]".
    [LadderFam]'s [fibdec] is that automaton's decode, and the two facts
    that make it an inverse are [fib_ub] and [fib_lb]: each state's
    reachable values are an INTERVAL, and the top digit splits [E]'s at
    exactly [fibw k], because [fibsum (k-1) + 1 = fibw k]. *)

Fixpoint fibokb (o : bool) (ds : list nat) : bool :=
  match ds with
  | [] => true
  | d :: t => (match d with
               | O => Bool.eqb (Nat.odd (dsum t)) o
               | _ => true
               end) && fibokb o t
  end.

Lemma andb_swap3 : forall a b c : bool, a && (b && c) = b && (a && c).
Proof. intros [] [] []; reflexivity. Qed.

Lemma dsum_snoc : forall l d, dsum (l ++ [d]) = dsum l + d.
Proof. intros l d. rewrite dsum_app. cbn [dsum]. lia. Qed.

(** The two ways into the string.  From the HEAD they are definitional --
    that is the side the class laws pattern on, and it is why the increment
    class costs one line.  From the TAIL they are the automaton's own step,
    and that is the side the decode's induction on the WIDTH needs. *)
Lemma fibokb_snoc0 : forall o l, fibokb o (l ++ [0]) = negb o && fibokb o l.
Proof.
  intros o. induction l as [|x l IH]; cbn [app].
  - destruct o; reflexivity.
  - cbn [fibokb]. rewrite IH, dsum_snoc, Nat.add_0_r. apply andb_swap3.
Qed.

Lemma fibokb_snoc1 : forall o l, fibokb o (l ++ [1]) = fibokb (negb o) l.
Proof.
  intros o. induction l as [|x l IH]; cbn [app].
  - destruct o; reflexivity.
  - cbn [fibokb]. rewrite IH, dsum_snoc.
    f_equal. destruct x as [|x]; [|reflexivity].
    replace (dsum l + 1) with (S (dsum l)) by lia.
    rewrite Nat.odd_succ, <- Nat.negb_odd.
    destruct (Nat.odd (dsum l)); destruct o; reflexivity.
Qed.

(** Both states' values are bounded by the width's own [fibsum]: "the value
    is below the ceiling" for a weighted numeration, which is what
    [val_pos_lt] is for a positional one. *)
Lemma fib_ub : forall ds, Forall (fun d => d < 2) ds ->
  forall o, fibokb o ds = true -> fibval ds <= fibsum (length ds).
Proof.
  intros ds. induction ds as [|x ds IH] using rev_ind; intros Hbnd o Hok.
  - cbn [length fibsum]. unfold fibval. cbn [fibvl]. lia.
  - apply Forall_app in Hbnd as [Hb1 Hb2].
    assert (Hx : x < 2) by exact (Forall_inv Hb2).
    rewrite fibval_snoc, app_length. cbn [length]. rewrite Nat.add_1_r.
    cbn [fibsum].
    destruct x as [|[|x]]; [| |lia].
    + rewrite fibokb_snoc0 in Hok. apply andb_true_iff in Hok as [_ Hok].
      specialize (IH Hb1 o Hok). lia.
    + rewrite fibokb_snoc1 in Hok. specialize (IH Hb1 (negb o) Hok). lia.
Qed.

(** State [O] cannot spell a small value: its top digit is FORCED to be a
    [1], so its value is at least that digit's weight.  This is the half
    that makes the decode's test at [fibw k] the right test. *)
Lemma fib_lb : forall ds, Forall (fun d => d < 2) ds ->
  fibokb true ds = true -> fiblo true (length ds) <= fibval ds.
Proof.
  intros ds. induction ds as [|x ds IH] using rev_ind; intros Hbnd Hok.
  - cbn [length fiblo]. lia.
  - clear IH. apply Forall_app in Hbnd as [Hb1 Hb2].
    assert (Hx : x < 2) by exact (Forall_inv Hb2).
    rewrite app_length. cbn [length]. rewrite Nat.add_1_r.
    rewrite fibval_snoc.
    destruct x as [|[|x]]; [| |lia].
    + rewrite fibokb_snoc0 in Hok. cbn [negb andb] in Hok. discriminate.
    + cbn [fiblo]. lia.
Qed.

(** THE ROUND TRIP, and it is the canonicity theorem the redundancy makes
    necessary: the decode of a MEMBER's value is that member back.  With it,
    two members of one width with one value are one string ([fib_inj]),
    which is what turns "the top has value [fibsum k]" into "the top IS
    [1^k]".

    The induction is on the WIDTH and it strips the top digit.  A [0] there
    forces the state to [E] and puts the value below [fibw k] ([fib_ub] on
    the shorter string); a [1] flips the state and puts it at or above
    ([fib_lb] with [fiblo_fibw]).  Those two bounds ARE the decode's test,
    which is why there is no third case and no arithmetic left over. *)
Lemma fibdec_round : forall k o ds,
  length ds = k -> Forall (fun d => d < 2) ds -> fibokb o ds = true ->
  fibdec k o (fibval ds) = ds.
Proof.
  induction k as [|k IH]; intros o ds Hlen Hbnd Hok.
  - destruct ds; [reflexivity | cbn [length] in Hlen; lia].
  - assert (Hne : ds <> []) by (intros ->; cbn [length] in Hlen; lia).
    destruct (exists_last Hne) as (t & x & ->).
    rewrite app_length in Hlen. cbn [length] in Hlen.
    assert (Hlt : length t = k) by lia.
    apply Forall_app in Hbnd as [Hbt Hbx].
    assert (Hx : x < 2) by exact (Forall_inv Hbx).
    pose proof (fibsum_S k) as Hss.
    destruct x as [|[|x]]; [| |lia].
    + (* the top digit is 0: state [E], and the value is inside width [k] *)
      rewrite fibokb_snoc0 in Hok. apply andb_true_iff in Hok as [Ho Hok].
      destruct o; [cbn [negb] in Ho; discriminate|].
      rewrite fibval_snoc, Hlt, Nat.mul_0_l, Nat.add_0_r.
      pose proof (fib_ub t Hbt false Hok) as Hub. rewrite Hlt in Hub.
      cbn [fibdec orb].
      replace (fibw (S k) <=? fibval t) with false
        by (symmetry; apply Nat.leb_gt; lia).
      rewrite (IH false t Hlt Hbt Hok). reflexivity.
    + (* the top digit is 1: the state flips and the weight comes off *)
      rewrite fibokb_snoc1 in Hok.
      rewrite fibval_snoc, Hlt.
      assert (Hb : o || (fibw (S k) <=? fibval t + 1 * fibw k) = true).
      { destruct o; [reflexivity|]. cbn [orb]. apply Nat.leb_le.
        cbn [negb] in Hok. pose proof (fib_lb t Hbt Hok) as Hlb.
        rewrite Hlt in Hlb. pose proof (fiblo_fibw k). lia. }
      cbn [fibdec]. rewrite Hb.
      replace (fibval t + 1 * fibw k - fibw k) with (fibval t) by lia.
      rewrite (IH (negb o) t Hlt Hbt Hok). reflexivity.
Qed.

(** *** The runs the two classes are made of *)

Lemma fibvl_rep0 : forall n j, fibvl j (repeat 0 n) = 0.
Proof.
  induction n as [|n IH]; intros j; cbn [repeat fibvl]; [reflexivity|].
  rewrite IH. lia.
Qed.

Lemma fibval_rep0 : forall n, fibval (repeat 0 n) = 0.
Proof. intros n. unfold fibval. apply fibvl_rep0. Qed.

Lemma repeat_snoc : forall (A : Type) (a : A) n,
  repeat a (S n) = repeat a n ++ [a].
Proof.
  intros A a n. replace (S n) with (n + 1) by lia.
  rewrite repeat_app. reflexivity.
Qed.

(** The top of a width is the ALL-ONES string and its value is [fibsum k] --
    the width's whole ceiling, which is what [maxval] is here.  Simpler than
    [(Gray, 2)]'s top and simpler than [b^k - 1]: no [fam_of_value] is
    needed to compute it. *)
Lemma fibval_rep1 : forall n, fibval (repeat 1 n) = fibsum n.
Proof.
  induction n as [|n IH]; [reflexivity|].
  cbn [fibsum]. rewrite (repeat_snoc nat 1 n), fibval_snoc, repeat_length, IH.
  lia.
Qed.

Lemma fibokb_rep1 : forall o n X, fibokb o (repeat 1 n ++ X) = fibokb o X.
Proof.
  intros o. induction n as [|n IH]; intros X; [reflexivity|].
  cbn [repeat app fibokb]. apply IH.
Qed.

Lemma dsum_rep0 : forall n X, dsum (repeat 0 n ++ X) = dsum X.
Proof. intros n X. rewrite dsum_app, dsum_repeat. lia. Qed.

Lemma fibokb_rep0 : forall o n X,
  Bool.eqb (Nat.odd (dsum X)) o = true ->
  fibokb o (repeat 0 n ++ X) = fibokb o X.
Proof.
  intros o n X H. induction n as [|n IH]; [reflexivity|].
  cbn [repeat app fibokb]. rewrite dsum_rep0, H. cbn [andb]. exact IH.
Qed.

Lemma fib_rep1_bnd : forall n, Forall (fun d => d < 2) (repeat 1 n).
Proof.
  intros n. apply Forall_forall. intros x Hx. apply repeat_spec in Hx. lia.
Qed.

Lemma fib_rep0_bnd : forall n, Forall (fun d => d < 2) (repeat 0 n).
Proof.
  intros n. apply Forall_forall. intros x Hx. apply repeat_spec in Hx. lia.
Qed.

Lemma fib_top_mem : forall k, fibokb false (repeat 1 k) = true.
Proof.
  intros k. rewrite <- (app_nil_r (repeat 1 k)), fibokb_rep1. reflexivity.
Qed.

(** *** The two classes, and they split on the LOW DIGIT

    4p measured them over all 2,284 interior members of the five rows --
    overlap 0, uncovered 0, wrong successor 0.  The increment carries a
    fixed word BEFORE the run, which is [cls_side]'s [u]: the widening 4n
    specified for [(Gray, 2)] and 4o built, needed again here and already
    in place. *)
Definition f1c (i : nat) : Class :=
  match i with
  | 0 => mkCls [0] 0 [] [1] 0 []       (** low digit 0: the increment *)
  | _ => mkCls [] 1 [1;0] [] 0 [1;1]   (** low digit 1: the carry *)
  end.

(** The increment adds the weight of index 0, which is 1. *)
Lemma fibval_cons01 : forall X, fibval (1 :: X) = fibval (0 :: X) + 1.
Proof. intros X. unfold fibval. cbn [fibvl fibw]. lia. Qed.

(** The carry adds 1 too, and THAT is [fibsum_S]: the run of ones it
    collapses is worth exactly one less than the weight two places up.  The
    ripple is affine here -- 4p measured it on the machines, and
    LADDER_PLAN 5's sentence is simply false for these five. *)
Lemma fibval_carry : forall n rest,
  fibval (repeat 0 n ++ [1;1] ++ rest)
  = fibval (repeat 1 n ++ [1;0] ++ rest) + 1.
Proof.
  intros n rest.
  rewrite !fibval_app, !repeat_length, fibval_rep1, fibval_rep0.
  cbn [app fibvl]. pose proof (fibsum_S n) as Hss. lia.
Qed.

Lemma f1c_len : forall i n rest,
  length (cls_rhs (f1c i) n rest) = length (cls_lhs (f1c i) n rest).
Proof.
  intros i n rest. unfold cls_lhs, cls_rhs.
  destruct i as [|i]; cbn [f1c cs_u cs_t cs_w cs_u' cs_t' cs_w'];
    rewrite !app_length, !repeat_length; reflexivity.
Qed.

Lemma f1c_bnd : forall i n rest, Forall (fun d => d < 2) rest ->
  Forall (fun d => d < 2) (cls_rhs (f1c i) n rest).
Proof.
  intros i n rest Hr. unfold cls_rhs.
  destruct i as [|i]; cbn [f1c cs_u' cs_t' cs_w'];
    repeat (apply Forall_app; split);
    first [ exact Hr
          | apply fib_rep0_bnd
          | apply fib_rep1_bnd
          | (repeat (apply Forall_cons; [lia|]); apply Forall_nil) ].
Qed.

(** The step and MEMBERSHIP together: the right-hand side of either class is
    a member whose value is one more.  Membership is the only one of the two
    that is not arithmetic, and it is where the classes differ -- the
    increment's is a conjunct dropped, the carry's is that collapsing a run
    of ones into [1;1] two places up does not move the parity ABOVE any of
    the zeros it leaves behind. *)
Lemma f1c_step : forall i n rest, Forall (fun d => d < 2) rest ->
  fibokb false (cls_lhs (f1c i) n rest) = true ->
  fibval (cls_rhs (f1c i) n rest) = fibval (cls_lhs (f1c i) n rest) + 1
  /\ fibokb false (cls_rhs (f1c i) n rest) = true.
Proof.
  intros i n rest Hrest Hok. unfold cls_lhs, cls_rhs in *.
  destruct i as [|i]; cbn [f1c cs_u cs_t cs_w cs_u' cs_t' cs_w'] in *;
    cbn [app] in *.
  - (* the increment: [0 :: X -> 1 :: X], and [X] carries the whole
       membership because a leading [1] constrains nothing *)
    cbn [fibokb] in Hok. apply andb_true_iff in Hok as [_ Hok].
    split; [apply fibval_cons01 | cbn [fibokb]; rewrite Hok; reflexivity].
  - (* the carry *)
    rewrite fibokb_rep1 in Hok. cbn [fibokb andb] in Hok.
    apply andb_true_iff in Hok as [Hpar Hok].
    apply Bool.eqb_prop in Hpar.
    split; [apply fibval_carry|].
    rewrite (fibokb_rep0 false n (1 :: 1 :: rest)).
    + cbn [fibokb]. rewrite Hok. reflexivity.
    + cbn [dsum].
      replace (1 + (1 + dsum rest)) with (S (S (dsum rest))) by lia.
      rewrite Nat.odd_succ, Nat.even_succ, Hpar. reflexivity.
Qed.

(** Coverage: a member of a width is the top, or an instance of exactly one
    of the two classes.  This is [digs_decomp]'s analogue, and where
    [(Gray, 2)] needed a four-way split this is a [destruct] on the LOW
    DIGIT: a [0] is the increment at run length 0, a [1] walks its own run
    to the [0] that ends it -- or there is none, and the string is [1^k]. *)
Lemma fib_split : forall ds,
  Forall (fun d => d < 2) ds -> fibokb false ds = true -> 0 < length ds ->
  ds = repeat 1 (length ds)
  \/ exists i n rest, i < 2 /\ Forall (fun d => d < 2) rest
                      /\ ds = cls_lhs (f1c i) n rest.
Proof.
  intros ds Hbnd Hok Hk.
  destruct ds as [|d0 t]; [cbn [length] in Hk; lia|].
  assert (Hd0 : d0 < 2) by exact (Forall_inv Hbnd).
  pose proof (Forall_inv_tail Hbnd) as Hbt.
  destruct d0 as [|d0].
  - right. exists 0, 0, t. split; [lia|]. split; [exact Hbt|].
    unfold cls_lhs. cbn [f1c cs_u cs_t cs_w repeat app]. reflexivity.
  - assert (Hd1 : d0 = 0) by lia. subst d0.
    destruct (digs_decomp 1 (1 :: t)) as [Hall | (n & d & rest & Hds & Hd)].
    + left. exact Hall.
    + destruct n as [|n]; [cbn [repeat app] in Hds; congruence|].
      assert (Hbnd' : Forall (fun x => x < 2) (repeat 1 (S n) ++ d :: rest))
        by (rewrite <- Hds; exact Hbnd).
      apply Forall_app in Hbnd' as [_ Hb2].
      assert (Hdlt : d < 2) by exact (Forall_inv Hb2).
      assert (Hd0' : d = 0) by lia. subst d.
      right. exists 1, n, rest. split; [lia|].
      split; [exact (Forall_inv_tail Hb2)|].
      rewrite Hds. unfold cls_lhs. cbn [f1c cs_u cs_t cs_w app].
      rewrite (repeat_snoc nat 1 n), <- app_assoc. cbn [app]. reflexivity.
Qed.

(** *** The instance

    Every lemma below is stated at an ARBITRARY family whose code is [Fib]
    and whose step is 1, exactly as section 3 states [(Binary, 1)].  Nothing
    here is a hypothesis about a particular row. *)

Lemma fib_value : forall F, fm_code F = Fib ->
  forall ds, fam_value F ds = fibval ds.
Proof. intros F Hc ds. unfold fam_value. rewrite Hc. reflexivity. Qed.

Lemma fib_roundtrip : forall F, fm_code F = Fib ->
  forall ds, Forall (fun d => d < 2) ds -> fibokb false ds = true ->
  fam_of_value F (fam_value F ds) (length ds) = Some ds.
Proof.
  intros F Hc ds Hbnd Hok.
  pose proof (fib_ub ds Hbnd false Hok) as Hub.
  unfold fam_of_value. rewrite (fam_lim_fib F _ Hc), Hc, (fib_value F Hc).
  destruct (Nat.ltb_spec (fibval ds) (S (fibsum (length ds)))); [|lia].
  f_equal. apply fibdec_round; [reflexivity | exact Hbnd | exact Hok].
Qed.

Lemma fib_inj : forall F, fm_code F = Fib ->
  forall a c, Forall (fun d => d < 2) a -> fibokb false a = true ->
  Forall (fun d => d < 2) c -> fibokb false c = true ->
  length a = length c -> fam_value F a = fam_value F c -> a = c.
Proof.
  intros F Hc a c Ha Hoka Hcc Hokc HL HV.
  assert (E : Some a = Some c).
  { rewrite <- (fib_roundtrip F Hc a Ha Hoka),
            <- (fib_roundtrip F Hc c Hcc Hokc), HL, HV. reflexivity. }
  injection E; auto.
Qed.

Lemma fib_next_of : forall F, fm_code F = Fib -> fm_step F = 1 ->
  forall ds nd ph,
  Forall (fun d => d < 2) nd -> fibokb false nd = true ->
  length nd = length ds ->
  fam_value F nd = fam_value F ds + 1 ->
  fam_is_top F ds = false /\ fam_next F ds ph = Some nd.
Proof.
  intros F Hc Hs ds nd ph Hbnd Hok HL HV.
  pose proof (fib_ub nd Hbnd false Hok) as Hub.
  rewrite <- (fib_value F Hc), HL in Hub.
  assert (Htop : fam_is_top F ds = false).
  { unfold fam_is_top. rewrite (fam_lim_fib F _ Hc), Hs.
    apply Nat.ltb_ge. lia. }
  split; [exact Htop|].
  unfold fam_next. rewrite Htop, Hs, <- HV, <- HL.
  apply fib_roundtrip; assumption.
Qed.

Lemma fib_class : forall F, fm_code F = Fib -> fm_step F = 1 ->
  forall i n rest, Forall (fun d => d < 2) rest ->
  fibokb false (cls_lhs (f1c i) n rest) = true ->
  fam_is_top F (cls_lhs (f1c i) n rest) = false
  /\ (forall ph, fam_next F (cls_lhs (f1c i) n rest) ph
                 = Some (cls_rhs (f1c i) n rest))
  /\ fibokb false (cls_rhs (f1c i) n rest) = true.
Proof.
  intros F Hc Hs i n rest Hrest Hok.
  destruct (f1c_step i n rest Hrest Hok) as (Hval & Hmem).
  assert (HV : fam_value F (cls_rhs (f1c i) n rest)
               = fam_value F (cls_lhs (f1c i) n rest) + 1)
    by (rewrite !(fib_value F Hc); exact Hval).
  destruct (fib_next_of F Hc Hs (cls_lhs (f1c i) n rest)
              (cls_rhs (f1c i) n rest) 0
              (f1c_bnd i n rest Hrest) Hmem (f1c_len i n rest) HV)
    as (Htop & _).
  split; [exact Htop | split; [|exact Hmem]].
  intros ph.
  exact (proj2 (fib_next_of F Hc Hs (cls_lhs (f1c i) n rest)
                  (cls_rhs (f1c i) n rest) ph
                  (f1c_bnd i n rest Hrest) Hmem (f1c_len i n rest) HV)).
Qed.

(** THE THIRD [ClassSucc] INSTANCE, and the record did not widen.  [P] is
    the membership predicate; [Class] is untouched, [ClassSucc] is not
    weakened, and there is no second class record. *)
Lemma fib_class_succ : forall F i,
  fm_b F = 2 -> fm_code F = Fib -> fm_step F = 1 ->
  ClassSucc F (fun ds => fibokb false ds = true) (f1c i).
Proof.
  intros F i Hb Hc Hs n rest ph Hrest Hok. rewrite Hb in Hrest.
  exact (proj1 (proj2 (fib_class F Hc Hs i n rest Hrest Hok)) ph).
Qed.

Lemma fib_top_value : forall F, fm_code F = Fib ->
  forall k, fam_value F (repeat 1 k) = fibsum k.
Proof. intros F Hc k. rewrite (fib_value F Hc). apply fibval_rep1. Qed.

Lemma fib_is_top : forall F, fm_code F = Fib -> fm_step F = 1 ->
  forall k, fam_is_top F (repeat 1 k) = true.
Proof.
  intros F Hc Hs k. unfold fam_is_top.
  rewrite (fam_lim_fib F _ Hc), Hs, repeat_length, (fib_top_value F Hc).
  apply Nat.ltb_lt. lia.
Qed.

(** The top of a width IS the all-ones string: the only MEMBER of the width
    whose value is [fibsum k].  Uniqueness is [fib_inj], hence the round
    trip -- the only place the canonicity is used, exactly as [gray_inj] is
    for [(Gray, 2)]. *)
Lemma fib_top_shape : forall F, fm_code F = Fib -> fm_step F = 1 ->
  forall ds, Forall (fun d => d < 2) ds -> fibokb false ds = true ->
  fam_is_top F ds = true -> ds = repeat 1 (length ds).
Proof.
  intros F Hc Hs ds Hbnd Hok Htop.
  apply (fib_inj F Hc); try assumption.
  - apply fib_rep1_bnd.
  - apply fib_top_mem.
  - rewrite repeat_length. reflexivity.
  - rewrite (fib_top_value F Hc), (fib_value F Hc).
    pose proof (fib_ub ds Hbnd false Hok) as Hub.
    unfold fam_is_top in Htop.
    rewrite (fam_lim_fib F _ Hc), Hs, (fib_value F Hc) in Htop.
    apply Nat.ltb_lt in Htop. lia.
Qed.


(** ** 4. The lap: one arm, one class, one anchor step

    An arm is a rule over an ARBITRARY tail.  A class is a digit-string
    shape whose cells are one [sside] with the untouched remainder in that
    tail.  Putting the two together is the whole of the lap: no search, no
    membership test, and the instantiation of the arm's variable [j] is the
    class's run length.  [board_arm] below states it once and hands the two
    [cden] equations to whichever closer asked, which is what lets one case
    split serve both. *)

Lemma tailL_nil : forall F, tailL F [] = [].
Proof. intros F; unfold tailL; destruct (fm_left F); reflexivity. Qed.

Lemma tailR_nil : forall F, tailR F [] = [].
Proof. intros F; unfold tailR; destruct (fm_left F); reflexivity. Qed.

(** A class instance is never the top of its width: its successor has the
    same width, which is what lets the interior arm leave the PHASE alone.
    Extracted from [pos1_class_succ]'s own arithmetic, where it was a local
    assertion -- the phase cycle needs it as a lemma, because with more than
    one phase "not the top" and "the phase does not move" are the same
    fact. *)
Lemma pos1_class_not_top : forall F d n rest,
  1 < fm_b F -> fm_code F = Binary -> fm_step F = 1 ->
  d < fm_b F - 1 -> Forall (fun x => x < fm_b F) rest ->
  fam_is_top F (repeat (fm_b F - 1) n ++ d :: rest) = false.
Proof.
  intros F d n rest Hb Hcode Hstep Hd Hrest.
  pose proof (pow_pos (fm_b F) n ltac:(lia)) as Hpn.
  assert (Hv : fam_value F (repeat (fm_b F - 1) n ++ d :: rest)
               = Nat.pow (fm_b F) n - 1
                 + Nat.pow (fm_b F) n * (d + fm_b F * val_pos (fm_b F) rest)).
  { unfold fam_value. rewrite Hcode. apply val_pos_class; lia. }
  assert (Hv' : fam_value F (repeat 0 n ++ S d :: rest)
                = Nat.pow (fm_b F) n * (S d + fm_b F * val_pos (fm_b F) rest)).
  { unfold fam_value. rewrite Hcode. apply val_pos_repeat0. }
  assert (Hbnd : Forall (fun x => x < fm_b F) (repeat 0 n ++ S d :: rest)).
  { apply Forall_app. split.
    - apply Forall_forall. intros x Hx. apply repeat_spec in Hx. lia.
    - constructor; [lia | exact Hrest]. }
  assert (Hlen : length (repeat 0 n ++ S d :: rest)
                 = length (repeat (fm_b F - 1) n ++ d :: rest)).
  { rewrite !app_length, !repeat_length. reflexivity. }
  assert (Hlt : fam_value F (repeat 0 n ++ S d :: rest)
                < Nat.pow (fm_b F) (length (repeat (fm_b F - 1) n ++ d :: rest))).
  { rewrite <- Hlen. unfold fam_value. rewrite Hcode.
    apply val_pos_lt; [lia | exact Hbnd]. }
  unfold fam_is_top. rewrite (fam_lim_bin F _ Hcode).
  apply Nat.ltb_ge. rewrite Hstep. nia.
Qed.

(** ** 5. The widths are cofinal, hence the fill arm fires forever

    4h(b): "the value strictly increases by [fm_step] within a width and is
    bounded by [b^k - 1], so the top of every width is reached and the fill
    fires there, and the width grows without bound."  That is
    [top_reached] and [tops_cofinal], and it is what turns the
    certificate's MEASUREMENT [arms_infinitely_often] into a theorem.

    All of it is stated over a family of [NPH] PHASES.  4i said the phase
    cycle is "a change to this predicate and to nothing above it", and that
    is exactly what it is: [Inv] carries [ph < NPH] instead of [ph = 0], the
    fill law is read at the state's own phase, and the interior step leaves
    the phase where it found it.  Nothing about the value, the width or the
    measure changes, because the phase does not enter any of them.  A
    one-phase family is [NPH = 1] and every phase-indexed object collapses
    ([board_neverqh] below is that instance, with the interface it had
    before this section was generalised). *)

Definition ct_ds (s : CtrSt) : list nat := let '(ds, _, _) := s in ds.
Definition ct_ph (s : CtrSt) : nat := let '(_, _, ph) := s in ph.

(** Where the phase is after [k] fills.  The interior steps do not move it,
    so this IS the phase cycle: [f_to] iterated. *)
Fixpoint phto (F : Fam) (k ph : nat) : nat :=
  match k with
  | 0 => ph
  | S k' => phto F k' (f_to (fam_fill F ph))
  end.

(** What a reachable counter state carries.  The phase is bounded rather
    than pinned: a one-phase family's fill lands back in phase 0, a
    multi-phase counter laps once per terminator and comes back. *)
Definition Inv (F : Fam) (NPH : nat) (s : CtrSt) : Prop :=
  let '(ds, _, ph) := s in
  Forall (fun d => d < fm_b F) ds /\ 0 < length ds /\ ph < NPH.

(** The fill at the top of width [k], in phase [ph]. *)
Definition filled (F : Fam) (ph k : nat) : list nat :=
  f_pre (fam_fill F ph)
  ++ repeat (f_mid (fam_fill F ph))
       (k + f_s (fam_fill F ph)
        - (length (f_pre (fam_fill F ph)) + length (f_suf (fam_fill F ph))))
  ++ f_suf (fam_fill F ph).

Section Iter.

Variable F : Fam.
Variable NPH : nat.
Hypothesis Hb    : 1 < fm_b F.
Hypothesis Hcode : fm_code F = Binary.
Hypothesis Hstep : fm_step F = 1.
Hypothesis Hfpre : forall ph, ph < NPH ->
  Forall (fun d => d < fm_b F) (f_pre (fam_fill F ph)).
Hypothesis Hfsuf : forall ph, ph < NPH ->
  Forall (fun d => d < fm_b F) (f_suf (fam_fill F ph)).
Hypothesis Hfmid : forall ph, ph < NPH -> f_mid (fam_fill F ph) < fm_b F.
Hypothesis Hfs   : forall ph, ph < NPH ->
  length (f_pre (fam_fill F ph)) + length (f_suf (fam_fill F ph))
  <= 1 + f_s (fam_fill F ph).
(** The phase CYCLE: every phase's fill lands in a phase of the same family.
    At [NPH = 1] this is [f_to (fam_fill F 0) = 0], which is what it was. *)
Hypothesis Hfto  : forall ph, ph < NPH -> f_to (fam_fill F ph) < NPH.

Lemma inv_value_lt : forall s,
  Inv F NPH s -> fam_value F (ct_ds s) < Nat.pow (fm_b F) (length (ct_ds s)).
Proof.
  intros [[ds p] ph] (Hbnd & _ & _); simpl.
  unfold fam_value. rewrite Hcode. apply val_pos_lt; [lia | exact Hbnd].
Qed.

Lemma fill_at_top : forall ds ph, ph < NPH ->
  0 < length ds -> fam_is_top F ds = true ->
  fam_next F ds ph = Some (filled F ph (length ds)).
Proof.
  intros ds ph Hph Hk Htop. unfold fam_next, filled. rewrite Htop.
  unfold fill_apply. pose proof (Hfs ph Hph).
  destruct (Nat.leb_spec (length (f_pre (fam_fill F ph))
                          + length (f_suf (fam_fill F ph)))
              (length ds + f_s (fam_fill F ph))); [reflexivity | lia].
Qed.

Lemma filled_length : forall ph k, ph < NPH -> 0 < k ->
  length (filled F ph k) = k + f_s (fam_fill F ph).
Proof.
  intros ph k Hph Hk. unfold filled. pose proof (Hfs ph Hph).
  rewrite !app_length, repeat_length. lia.
Qed.

Lemma filled_bnd : forall ph k, ph < NPH ->
  Forall (fun d => d < fm_b F) (filled F ph k).
Proof.
  intros ph k Hph. unfold filled. apply Forall_app.
  split; [apply (Hfpre ph Hph)|].
  apply Forall_app. split; [|apply (Hfsuf ph Hph)].
  apply Forall_forall. intros x Hx. apply repeat_spec in Hx.
  pose proof (Hfmid ph Hph). lia.
Qed.

Lemma fam_succ_total : forall s,
  Inv F NPH s -> exists s', fam_succ F s = Some s' /\ Inv F NPH s'.
Proof.
  intros [[ds p] ph] Hi. destruct Hi as (Hbnd & Hlen & Hph).
  destruct (fam_is_top F ds) eqn:Htop.
  - (* the fill: the phase moves to the one the law lands in *)
    eexists. unfold fam_succ.
    rewrite (fill_at_top ds ph Hph Hlen Htop), Htop.
    split; [reflexivity|]. simpl. repeat split.
    + apply filled_bnd; exact Hph.
    + rewrite filled_length by assumption. pose proof (Hfs ph Hph). lia.
    + apply Hfto; exact Hph.
  - (* an interior step: the phase stays *)
    assert (Hlt : fam_value F ds + fm_step F < Nat.pow (fm_b F) (length ds)).
    { unfold fam_is_top in Htop. rewrite (fam_lim_bin F _ Hcode) in Htop.
      apply Nat.ltb_ge in Htop.
      pose proof (pow_pos (fm_b F) (length ds) ltac:(lia)). lia. }
    unfold fam_succ, fam_next. rewrite Htop.
    unfold fam_of_value. rewrite (fam_lim_bin F _ Hcode), Hcode.
    destruct (Nat.ltb_spec (fam_value F ds + fm_step F)
                (Nat.pow (fm_b F) (length ds))); [|lia].
    eexists. split; [reflexivity|]. simpl. repeat split.
    + apply pos_of_lt; lia.
    + rewrite pos_of_length. exact Hlen.
    + exact Hph.
Qed.

Lemma fam_iter_total : forall N s,
  Inv F NPH s -> exists s', fam_iter F s N = Some s' /\ Inv F NPH s'.
Proof.
  induction N as [|N IH]; intros s Hi; [exists s; split; [reflexivity|exact Hi]|].
  destruct (fam_succ_total s Hi) as (s1 & H1 & Hi1).
  destruct (IH s1 Hi1) as (s' & H' & Hi').
  exists s'. split; [|exact Hi']. simpl. rewrite H1. exact H'.
Qed.

(** Within a width the measure [b^k - value] strictly decreases, so the top
    of the width is reached in finitely many anchor visits. *)
Lemma top_reached_aux : forall m s,
  Inv F NPH s ->
  Nat.pow (fm_b F) (length (ct_ds s)) - fam_value F (ct_ds s) <= m ->
  exists n s', fam_iter F s n = Some s' /\ fam_is_top F (ct_ds s') = true
               /\ Inv F NPH s' /\ ct_ph s' = ct_ph s.
Proof.
  induction m as [|m IH]; intros s Hi Hm.
  - exfalso. pose proof (inv_value_lt s Hi). lia.
  - destruct (fam_is_top F (ct_ds s)) eqn:Htop.
    + exists 0, s.
      split; [reflexivity | split; [exact Htop | split; [exact Hi|reflexivity]]].
    + destruct s as [[ds p] ph]. simpl in Htop.
      destruct Hi as (Hbnd & Hlen & Hph).
      assert (Hi : Inv F NPH (ds, p, ph)) by (simpl; repeat split; assumption).
      destruct (fam_succ_total _ Hi) as (s1 & H1 & Hi1).
      (* the interior step: value up by [fm_step], width and PHASE unchanged *)
      unfold fam_succ in H1. rewrite Htop in H1.
      destruct (fam_next F ds ph) as [nd|] eqn:Hnd; [|discriminate].
      injection H1 as <-.
      destruct (fam_next_interior F ds ph nd Hb Htop Hnd) as (Hval & Hlen').
      destruct (IH (nd, p, ph) Hi1) as (n & s' & Hit & Htop' & Hi' & Hph').
      { simpl. simpl in Hm. rewrite Hval, Hlen'. lia. }
      exists (S n), s'.
      split; [|split; [exact Htop' | split; [exact Hi' | exact Hph']]].
      simpl. unfold fam_succ. rewrite Htop, Hnd. exact Hit.
Qed.

Lemma top_reached : forall s,
  Inv F NPH s ->
  exists n s', fam_iter F s n = Some s' /\ fam_is_top F (ct_ds s') = true
               /\ Inv F NPH s' /\ ct_ph s' = ct_ph s.
Proof.
  intros s Hi.
  apply (top_reached_aux
           (Nat.pow (fm_b F) (length (ct_ds s)) - fam_value F (ct_ds s)) s Hi).
  lia.
Qed.

(** One fill moves the phase one step along the cycle, and the top of the
    NEXT phase is reached from there.  Iterated: a top in whatever phase the
    cycle is in [k] fills from here.

    This is what a multi-phase counter needs that a one-phase one does not.
    A fill arm's anchor does not have to reach every state -- what has to
    hold is that for each state SOME anchor past every bound reaches it, and
    when the short phase of the cycle cannot (measured: a fill that laps into
    the next terminator without widening is six machine steps long and passes
    through two states), the tops of the OTHER phase carry the whole visit
    premise, because they are cofinal too. *)
Lemma top_after : forall k s, Inv F NPH s ->
  exists n s', fam_iter F s n = Some s' /\ fam_is_top F (ct_ds s') = true
               /\ Inv F NPH s' /\ ct_ph s' = phto F k (ct_ph s).
Proof.
  induction k as [|k IH]; intros s Hi.
  - destruct (top_reached s Hi) as (n & s' & Hit & Htop & Hi' & Hph).
    exists n, s'.
    split; [exact Hit | split; [exact Htop | split; [exact Hi' | exact Hph]]].
  - destruct (top_reached s Hi) as (n & s1 & Hit & Htop & Hi1 & Hph).
    destruct (fam_succ_total s1 Hi1) as (s2 & Hs2 & Hi2).
    assert (Hph2 : ct_ph s2 = f_to (fam_fill F (ct_ph s1))).
    { destruct s1 as [[ds1 p1] ph1]. simpl in Htop |- *.
      unfold fam_succ in Hs2. rewrite Htop in Hs2.
      destruct (fam_next F ds1 ph1) as [nd|]; [|discriminate].
      injection Hs2 as <-. reflexivity. }
    destruct (IH s2 Hi2) as (m & s' & Hit2 & Htop' & Hi' & Hph').
    exists (n + (1 + m)), s'.
    split; [| split; [exact Htop' | split; [exact Hi' |]]].
    + rewrite fam_iter_add, Hit. simpl. rewrite Hs2. exact Hit2.
    + rewrite Hph', Hph2, Hph. reflexivity.
Qed.

(** ...and since a fill widens, tops keep coming: for every bound there is
    a later anchor at the top of its width.  This is the premise
    [glue_neverqhN] needs, and the reason it needs only the weak one.

    Note what this does NOT need: that the fill widens.  A multi-phase
    counter's phase-0 fill can widen by nothing at all (it re-enters the
    same width in the next phase, which is what a terminator cycle IS), and
    the argument is unchanged -- what it needs is that a top RECURS, and
    [top_reached] gives that from any state whatever the phase. *)
Theorem tops_cofinal : forall s N,
  Inv F NPH s ->
  exists n s', N <= n /\ fam_iter F s n = Some s'
               /\ fam_is_top F (ct_ds s') = true /\ Inv F NPH s'.
Proof.
  intros s N Hi.
  destruct (fam_iter_total N s Hi) as (sN & HN & HiN).
  destruct (top_reached sN HiN) as (m & s' & Hm & Htop & Hi' & _).
  exists (N + m), s'.
  split; [lia | split; [| split; [exact Htop | exact Hi']]].
  rewrite fam_iter_add, HN. exact Hm.
Qed.

(** ...and cofinal IN A CHOSEN PHASE, provided the cycle reaches it from
    every phase.  [pv] is a phase whose fill anchors witness every recurring
    state; the hypothesis is that the cycle gets there, which for a concrete
    family is a case split over [NPH] phases and a [vm_compute]. *)
Theorem tops_cofinal_at : forall pv s N,
  (forall ph, ph < NPH -> exists k, phto F k ph = pv) ->
  Inv F NPH s ->
  exists n s', N <= n /\ fam_iter F s n = Some s'
               /\ fam_is_top F (ct_ds s') = true /\ Inv F NPH s'
               /\ ct_ph s' = pv.
Proof.
  intros pv s N Hcyc Hi.
  destruct (fam_iter_total N s Hi) as (sN & HN & HiN).
  assert (HphN : ct_ph sN < NPH)
    by (destruct sN as [[? ?] ?]; destruct HiN as (_ & _ & H); exact H).
  destruct (Hcyc (ct_ph sN) HphN) as (k & Hk).
  destruct (top_after k sN HiN) as (m & s' & Hm & Htop & Hi' & Hph).
  exists (N + m), s'.
  split; [lia | split; [| split; [exact Htop | split; [exact Hi' |]]]].
  - rewrite fam_iter_add, HN. exact Hm.
  - rewrite Hph. exact Hk.
Qed.

End Iter.

(** ** 5b. The same, at [(Gray, 2)]: the parity is an invariant, and the
    measure falls by two

    [fam_value] at [Gray] is a fold from the most significant digit DOWN
    ([gdec] before [val_pos]), so no lemma about [val_pos] transfers and
    section 5 is restated rather than instantiated.  What actually differs is
    small and is all here:

    * the invariant carries the PARITY -- section 3b's [P], which is what
      makes "member of this width" a predicate at all when the step is not 1
      -- and it is preserved because [+2] does not move the value's low bit
      and the fill target's digit sum is fixed ([Hfpar]);
    * it carries [2 <= length ds] rather than [0 < length ds], because the top
      of a width is [1-p] ++ 0^(k-2) ++ [1] and that needs two digits to
      spell;
    * the measure [2^k - value] falls by 2 rather than by 1, which changes one
      [lia];
    * the family is ONE PHASE.  All six gray core rows are (measured, 4n), so
      the phase cycle section 5 carries has nothing to do here and [ph] is
      pinned at [0]. *)

Section IterG.

Variable F : Fam.
Variable p : nat.                   (** the family's own parity *)
Hypothesis HbF   : fm_b F = 2.
Hypothesis HcF   : fm_code F = Gray.
Hypothesis HsF   : fm_step F = 2.
Hypothesis Hp    : p < 2.
Hypothesis Hfpre : Forall (fun d => d < 2) (f_pre (fam_fill F 0)).
Hypothesis Hfsuf : Forall (fun d => d < 2) (f_suf (fam_fill F 0)).
Hypothesis Hfmid : f_mid (fam_fill F 0) < 2.
Hypothesis Hfs   : length (f_pre (fam_fill F 0))
                   + length (f_suf (fam_fill F 0))
                   <= 2 + f_s (fam_fill F 0).
Hypothesis Hfto  : f_to (fam_fill F 0) = 0.
(** The fill target is a MEMBER: its digit sum has the family's parity.  For a
    fill whose digit is [0] this is a fact about [f_pre] and [f_suf] alone and
    [filled_parity] below discharges it; a fill digit of [1] would make the
    parity alternate with the width and there would be no family at all. *)
Hypothesis Hfpar : forall k, 2 <= k -> dsum (filled F 0 k) mod 2 = p.

Definition InvG (s : CtrSt) : Prop :=
  let '(ds, _, ph) := s in
  Forall (fun d => d < 2) ds /\ 2 <= length ds /\ ph = 0
  /\ dsum ds mod 2 = p.

Lemma fillG_at_top : forall ds, 2 <= length ds -> fam_is_top F ds = true ->
  fam_next F ds 0 = Some (filled F 0 (length ds)).
Proof.
  intros ds Hk Htop. unfold fam_next, filled. rewrite Htop. unfold fill_apply.
  destruct (Nat.leb_spec (length (f_pre (fam_fill F 0))
                          + length (f_suf (fam_fill F 0)))
              (length ds + f_s (fam_fill F 0))); [reflexivity | lia].
Qed.

Lemma filledG_length : forall k, 2 <= k ->
  length (filled F 0 k) = k + f_s (fam_fill F 0).
Proof.
  intros k Hk. unfold filled. rewrite !app_length, repeat_length. lia.
Qed.

Lemma filledG_bnd : forall k, Forall (fun d => d < 2) (filled F 0 k).
Proof.
  intros k. unfold filled. apply Forall_app. split; [exact Hfpre|].
  apply Forall_app. split; [|exact Hfsuf].
  apply Forall_forall. intros x Hx. apply repeat_spec in Hx. lia.
Qed.

Lemma invG_value_lt : forall ds,
  fam_value F ds < Nat.pow 2 (length ds).
Proof. intros ds. apply gray_val_lt; assumption. Qed.

Lemma famG_succ_total : forall s,
  InvG s -> exists s', fam_succ F s = Some s' /\ InvG s'.
Proof.
  intros [[ds q] ph] (Hbnd & Hk & -> & Hpar).
  destruct (fam_is_top F ds) eqn:Htop.
  - (* the fill, and it lands back in phase 0 *)
    exists (filled F 0 (length ds), q, 0).
    unfold fam_succ. rewrite (fillG_at_top ds Hk Htop), Htop, Hfto.
    split; [reflexivity|]. unfold InvG.
    split; [apply filledG_bnd|].
    split; [rewrite filledG_length by exact Hk; lia|].
    split; [reflexivity | apply Hfpar; exact Hk].
  - (* an interior step: the value goes up by two, so its low bit does not
       move and neither does the digit sum's parity *)
    assert (Hlt : fam_value F ds + fm_step F < Nat.pow (fm_b F) (length ds)).
    { unfold fam_is_top in Htop. rewrite (fam_lim_gray F _ HcF) in Htop.
      apply Nat.ltb_ge in Htop.
      pose proof (pow_pos (fm_b F) (length ds) ltac:(lia)). lia. }
    assert (Hex : exists nd, fam_next F ds 0 = Some nd).
    { unfold fam_next. rewrite Htop. unfold fam_of_value.
      rewrite (fam_lim_gray F _ HcF).
      destruct (Nat.ltb_spec (fam_value F ds + fm_step F)
                  (Nat.pow (fm_b F) (length ds))); [|lia].
      eexists; reflexivity. }
    destruct Hex as (nd & Hnd).
    exists (nd, q, 0).
    split; [unfold fam_succ; rewrite Hnd, Htop; reflexivity|].
    destruct (fam_next_interior F ds 0 nd ltac:(lia) Htop Hnd) as (Hval & Hlen).
    assert (Hbnd' : Forall (fun d => d < 2) nd).
    { unfold fam_next in Hnd. rewrite Htop in Hnd. unfold fam_of_value in Hnd.
      rewrite (fam_lim_gray F _ HcF) in Hnd.
      destruct (_ <? _); [|discriminate]. rewrite HcF in Hnd.
      injection Hnd as <-. rewrite HbF. apply genc_lt. lia. }
    unfold InvG.
    split; [exact Hbnd'|].
    split; [rewrite Hlen; exact Hk|].
    split; [reflexivity|].
    assert (Hm : fam_value F nd mod 2 = fam_value F ds mod 2).
    { rewrite Hval, HsF.
      replace (fam_value F ds + 2) with (fam_value F ds + 1 * 2) by lia.
      apply Nat.mod_add. lia. }
    rewrite <- gval_mod2, <- (gray_value F HbF HcF), Hm.
    rewrite (gray_value F HbF HcF), gval_mod2. exact Hpar.
Qed.

Lemma famG_iter_total : forall N s,
  InvG s -> exists s', fam_iter F s N = Some s' /\ InvG s'.
Proof.
  induction N as [|N IH]; intros s Hi;
    [exists s; split; [reflexivity | exact Hi]|].
  destruct (famG_succ_total s Hi) as (s1 & H1 & Hi1).
  destruct (IH s1 Hi1) as (s' & H' & Hi').
  exists s'. split; [|exact Hi']. simpl. rewrite H1. exact H'.
Qed.

(** Within a width the measure [2^k - value] falls by [fm_step = 2], so the
    top of the width is reached in finitely many anchor visits.  This is
    section 5's [top_reached_aux] with the two in place of the one. *)
Lemma topG_reached_aux : forall m s,
  InvG s ->
  Nat.pow 2 (length (ct_ds s)) - fam_value F (ct_ds s) <= m ->
  exists n s', fam_iter F s n = Some s' /\ fam_is_top F (ct_ds s') = true
               /\ InvG s'.
Proof.
  induction m as [|m IH]; intros s Hi Hm.
  - exfalso. pose proof (invG_value_lt (ct_ds s)). lia.
  - destruct (fam_is_top F (ct_ds s)) eqn:Htop.
    + exists 0, s. split; [reflexivity | split; [exact Htop | exact Hi]].
    + destruct s as [[ds q] ph]. simpl in Htop.
      destruct (famG_succ_total _ Hi) as (s1 & H1 & Hi1).
      unfold fam_succ in H1. rewrite Htop in H1.
      destruct (fam_next F ds ph) as [nd|] eqn:Hnd; [|discriminate].
      injection H1 as <-.
      destruct (fam_next_interior F ds ph nd ltac:(lia) Htop Hnd)
        as (Hval & Hlen).
      destruct (IH _ Hi1) as (n & s' & Hit & Htop' & Hi').
      { simpl. simpl in Hm. rewrite Hval, Hlen, HsF. lia. }
      exists (S n), s'. split; [|split; [exact Htop' | exact Hi']].
      simpl. unfold fam_succ. rewrite Htop, Hnd. exact Hit.
Qed.

Lemma topG_reached : forall s,
  InvG s ->
  exists n s', fam_iter F s n = Some s' /\ fam_is_top F (ct_ds s') = true
               /\ InvG s'.
Proof.
  intros s Hi.
  apply (topG_reached_aux
           (Nat.pow 2 (length (ct_ds s)) - fam_value F (ct_ds s)) s Hi). lia.
Qed.

Theorem topsG_cofinal : forall s N,
  InvG s ->
  exists n s', N <= n /\ fam_iter F s n = Some s'
               /\ fam_is_top F (ct_ds s') = true /\ InvG s'.
Proof.
  intros s N Hi.
  destruct (famG_iter_total N s Hi) as (sN & HN & HiN).
  destruct (topG_reached sN HiN) as (m & s' & Hm & Htop & Hi').
  exists (N + m), s'.
  split; [lia | split; [| split; [exact Htop | exact Hi']]].
  rewrite fam_iter_add, HN. exact Hm.
Qed.

End IterG.

(** The fill target's parity, for a fill whose digit is [0]: it does not
    depend on the width at all, so [Hfpar] above is two [vm_compute]s on the
    emitted board rather than an induction. *)
Lemma filled_parity : forall F ph k,
  f_mid (fam_fill F ph) = 0 ->
  dsum (filled F ph k)
  = dsum (f_pre (fam_fill F ph)) + dsum (f_suf (fam_fill F ph)).
Proof.
  intros F ph k Hm. unfold filled.
  rewrite !dsum_app, dsum_repeat, Hm. lia.
Qed.

(** ** 6. Selection: which arm serves which class, from the arms as DATA

    4f settled the semantics -- first applicable in the listed order, the
    order a linearization of pattern subsumption, most specific first --
    and settled it so that the kernel "never trusts the order it is handed
    and never has to decide membership".  Under a PROVED case split that
    obligation collapses to a lookup: [sel] finds the first arm in the list
    whose left-hand side is the class's, [sel_sound] says the arm found is
    in the list and has that left-hand side, and both are closed by
    [vm_compute] on the arm list.  Nothing selects on emission order and
    nothing decides membership; the two classes are disjoint because
    [digs_decomp] says so, not because an ordering check said so. *)

Fixpoint sel (l : list LRule) (lhs : sconf) : option LRule :=
  match l with
  | [] => None
  | a :: t => if sconf_eqb (lr_lhs a) lhs then Some a else sel t lhs
  end.

Lemma sel_sound : forall l lhs a,
  sel l lhs = Some a -> In a l /\ lr_lhs a = lhs.
Proof.
  induction l as [|x t IH]; intros lhs a H; simpl in H; [discriminate|].
  destruct (sconf_eqb (lr_lhs x) lhs) eqn:E.
  - injection H as <-. split; [left; reflexivity | apply sconf_eqb_eq; exact E].
  - destruct (IH lhs a H) as [Hin Hl]. split; [right; exact Hin | exact Hl].
Qed.

(** ** 7. The closure: what a board supplies, and what it gets

    Everything a board hands in is either a [RuleSound] the Stage-B kernel
    already discharged ([LadderKernel.arm_sound]), or an equation between
    two CONCRETE terms that [vm_compute] closes.  The counter's four
    parameters -- code, step, fill law, terminator -- are read off the
    [Fam] record, so a family with a different successor is a different
    record and not a different theorem.

    Two CLASSES carry the whole lap: the interior digits, and the top of a
    width.  That is not a coincidence of any row -- it is the case split of
    [digs_decomp], and the emitted certificate's dozen arms are
    specialisations of the two at pinned run lengths.  Each class is served
    by one arm per ARM INDEX (section 2b), which is where 4k's two knobs
    live: [N0i]/[sti] for the interior, [N0f]/[stf] for the fill.

    The section is indexed by the PHASE as well as the arm index, because a
    counter with more than one terminator laps through them: the fill arm
    sees the terminator of its own phase and lands on the terminator of the
    phase the law names.  The INTERIOR arm is not phase-indexed and does not
    need to be -- its terminator is inside the opaque tail [cls_tail], which
    is the same reason an arm proved for an arbitrary tail covers a whole
    class.  [board_neverqh] and [board_iqh] at the end of the file are this
    section at [NPH = 1], with the interface they had before. *)

Section BoardPh.

Variable tm    : TM.
Variable F     : Fam.
Variable NPH   : nat.               (** how many phases the family laps through *)
Variable Aint  : nat -> nat -> LRule.  (** the interior arm for digit [d] at
                                           arm index [r] *)
Variable N0i sti : nat.             (** its threshold and its stride *)
Variable Afill : nat -> nat -> LRule.  (** the arm that sees the counter's end,
                                           at arm index [r] and PHASE [ph] *)
Variable N0f stf : nat.             (** and ITS threshold and stride -- the
                                        same scheme, its own two knobs *)
Variable fm1 fm2 : nat -> nat -> nat.  (** how the fill's guaranteed copies
                                           split, per arm index and phase *)
Variable pv    : nat.               (** the phase whose fill anchors witness
                                        every recurring state *)
Variable vis   : nat -> St -> list lstep.  (** a chain to each state, from
                                               each fill arm's anchor in
                                               phase [pv] *)
Variable ds0   : list nat.          (** the boot digit string *)
Variable ph0   : nat.               (** and the phase it is read in *)
Variable t0    : nat.               (** and how many steps reach it *)

(** And, for a row that QUASIHALTS rather than never quasihalting (section 8
    below), the quiet state, its last visit, and the visit chains for the
    other three.  [boardph_neverqh] does not use them, so it does not carry
    them: a never-quasihalting board supplies [vis] and a quasihalting one
    supplies [visq]. *)
Variable qa   : St.
Variable sq   : nat.
Variable visq : nat -> St -> list lstep.

(** *** The family's parameters *)
Hypothesis Hb    : 1 < fm_b F.
Hypothesis Hcode : fm_code F = Binary.
Hypothesis Hstep : fm_step F = 1.
Hypothesis Hfpre : forall ph, ph < NPH ->
  Forall (fun d => d < fm_b F) (f_pre (fam_fill F ph)).
Hypothesis Hfsuf : forall ph, ph < NPH ->
  Forall (fun d => d < fm_b F) (f_suf (fam_fill F ph)).
Hypothesis Hfmid : forall ph, ph < NPH -> f_mid (fam_fill F ph) < fm_b F.
Hypothesis Hfs   : forall ph, ph < NPH ->
  length (f_pre (fam_fill F ph)) + length (f_suf (fam_fill F ph))
  <= 1 + f_s (fam_fill F ph).
Hypothesis Hfto  : forall ph, ph < NPH -> f_to (fam_fill F ph) < NPH.

(** The visit phase, and that the cycle reaches it from every phase.  A fill
    arm's anchor does NOT have to witness every recurring state: measured
    (LADDER_PLAN 4n), the phase of a two-phase counter whose fill laps into
    the next terminator without widening is six machine steps long and its
    anchor reaches two of the four states, while the other phase's reaches
    all four.  What the liveness needs is that the anchors which DO witness a
    state keep coming, and [tops_cofinal_at] says the tops of one phase are
    cofinal exactly when the cycle returns to it. *)
Hypothesis Hpv   : pv < NPH.
Hypothesis Hcyc  : forall ph, ph < NPH -> exists k, phto F k ph = pv.

(** How many of the fill target's guaranteed digit copies sit before the
    symbolic run and how many after.  The emitter picks the split the chain
    search normalises to; the kernel only asks that they add up -- and what
    they add up to depends on the arm AND the phase, because an arm at
    offset [r] has [r] copies of the run on its left-hand side and each
    phase has its own fill law. *)
Hypothesis Hfm12 : forall r ph, 0 < r -> r < N0f + stf -> ph < NPH ->
  fm1 r ph + fm2 r ph
  + (length (f_pre (fam_fill F ph)) + length (f_suf (fam_fill F ph)))
  = r + f_s (fam_fill F ph).

(** *** The boot *)
Hypothesis Hbnd0 : Forall (fun d => d < fm_b F) ds0.
Hypothesis Hlen0 : 0 < length ds0.
Hypothesis Hph0  : ph0 < NPH.
Hypothesis Hboot : csteps tm t0 CTape.c0 = Some (fam_cfg F (ds0, 0, ph0)).

(** *** The interior arms, one per digit below the top and per arm index *)
Hypothesis Hsti : 0 < sti.
Hypothesis HAiS : forall d r, d < fm_b F - 1 -> r < N0i + sti ->
  RuleSound tm (negb (fm_left F)) (fm_left F) (Aint d r).
Hypothesis HAiL : forall d r, d < fm_b F - 1 -> r < N0i + sti ->
  lr_lhs (Aint d r)
    = cls_conf F (cls_side F [] (fm_b F - 1) r (astride N0i sti r) [d]).
Hypothesis HAiR : forall d r, d < fm_b F - 1 -> r < N0i + sti ->
  lr_rhs (Aint d r)
    = cls_conf F (cls_side F [] 0 r (astride N0i sti r) [S d]).
Hypothesis HAiC : forall d r, d < fm_b F - 1 -> r < N0i + sti ->
  0 < lr_cb (Aint d r).

(** *** The fill arms, at both tails known empty, one per index and phase.
    [0 < N0f] is what keeps [r = 0] out of the index range: no width is [0],
    so no fill arm is. *)
Hypothesis Hstf : 0 < stf.
Hypothesis HN0f : 0 < N0f.
Hypothesis HAfS : forall r ph, 0 < r -> r < N0f + stf -> ph < NPH ->
  RuleSound tm true true (Afill r ph).
Hypothesis HAfL : forall r ph, 0 < r -> r < N0f + stf -> ph < NPH ->
  lr_lhs (Afill r ph)
    = cls_conf F (run_side F (fm_b F - 1) r (astride N0f stf r) 0 ph [] []).
Hypothesis HAfR : forall r ph, 0 < r -> r < N0f + stf -> ph < NPH ->
  lr_rhs (Afill r ph)
    = cls_conf F (run_side F (f_mid (fam_fill F ph)) (fm1 r ph)
                    (astride N0f stf r) (fm2 r ph) (f_to (fam_fill F ph))
                    (f_pre (fam_fill F ph)) (f_suf (fam_fill F ph))).
Hypothesis HAfC : forall r ph, 0 < r -> r < N0f + stf -> ph < NPH ->
  0 < lr_cb (Afill r ph).

(** *** Liveness: every state is reached from every fill arm's anchor IN
    PHASE [pv] *)
Hypothesis Hvisit : forall r q, 0 < r -> r < N0f + stf ->
  srun_st tm true true (vis r q) (lr_lhs (Afill r pv)) = Some q.

Let s0 : CtrSt := (ds0, 0, ph0).

Definition CfB (n : nat) : cconf :=
  match fam_iter F s0 n with
  | Some s => fam_cfg F s
  | None => CTape.c0
  end.

Lemma inv0 : Inv F NPH s0.
Proof. simpl. repeat split; assumption. Qed.

(** The two facts section 5 exports, at this section's own parameters. *)
Lemma iter_total : forall N s,
  Inv F NPH s -> exists s', fam_iter F s N = Some s' /\ Inv F NPH s'.
Proof. intros N s Hi. eapply fam_iter_total; eassumption. Qed.

Lemma tops_cof : forall s N,
  Inv F NPH s ->
  exists n s', N <= n /\ fam_iter F s n = Some s'
               /\ fam_is_top F (ct_ds s') = true /\ Inv F NPH s'.
Proof. intros s N Hi. eapply tops_cofinal; eassumption. Qed.

(** The tops of the visit phase are cofinal -- section 5's [tops_cofinal_at]
    at this section's own parameters. *)
Lemma tops_cof_pv : forall s N,
  Inv F NPH s ->
  exists n s', N <= n /\ fam_iter F s n = Some s'
               /\ fam_is_top F (ct_ds s') = true /\ Inv F NPH s'
               /\ ct_ph s' = pv.
Proof. intros s N Hi. eapply tops_cofinal_at; eassumption. Qed.

Lemma fill_top : forall ds ph, ph < NPH ->
  0 < length ds -> fam_is_top F ds = true ->
  fam_next F ds ph = Some (filled F ph (length ds)).
Proof. intros ds ph Hph Hk Ht. eapply fill_at_top; eassumption. Qed.

(** The cells of a top-of-width string, as the fill arm's left-hand side.
    The arm is the one at index [m1], and it walks the width in blocks of
    [s]: [m1 + s*n = k] is [arm_index] and nothing else. *)
Lemma cells_top : forall k m1 s n ph, m1 + s * n = k ->
  fam_cells F (repeat (fm_b F - 1) k) ph
    = sden [] n (run_side F (fm_b F - 1) m1 s 0 ph [] []).
Proof.
  intros k m1 s n ph Hk.
  transitivity
    (fam_cells F ([] ++ repeat (fm_b F - 1) (m1 + s * n + 0) ++ []) ph).
  - f_equal. rewrite Nat.add_0_r, Hk, app_nil_r. reflexivity.
  - apply fam_cells_run.
Qed.

(** ...and of what the fill law puts there, as its right-hand side.  The
    law's own prefix and suffix ride along as the fixed words either side of
    the run, which is what lets a family whose fill is not a bare widening
    use the same arm shape.  The tail is the one of the phase the law LANDS
    in, which is the only place the phase cycle reaches the cells. *)
Lemma cells_filled : forall k a s n c ph,
  a + s * n + c
    = k + f_s (fam_fill F ph)
      - (length (f_pre (fam_fill F ph)) + length (f_suf (fam_fill F ph))) ->
  fam_cells F (filled F ph k) (f_to (fam_fill F ph))
    = sden [] n
        (run_side F (f_mid (fam_fill F ph)) a s c (f_to (fam_fill F ph))
           (f_pre (fam_fill F ph)) (f_suf (fam_fill F ph))).
Proof.
  intros k a s n c ph Hk.
  transitivity (fam_cells F
    (f_pre (fam_fill F ph)
     ++ repeat (f_mid (fam_fill F ph)) (a + s * n + c)
     ++ f_suf (fam_fill F ph)) (f_to (fam_fill F ph))).
  - f_equal. unfold filled. rewrite Hk. reflexivity.
  - apply fam_cells_run.
Qed.

(** The lap, by the case split: a state is at the top of its width, where a
    fill arm applies, or it is not, where an interior arm does.

    Stated ONCE, for both closers.  What a closer wants OF the arm it lands
    on is the parameter [P]: [board_neverqh] wants [RuleSound], and the
    quasihalt board wants [RuleSound] and [RuleAvoid] of the same arm.
    Everything else -- which arm serves the state, at what index and block
    count, and that the configurations either side of the lap are that arm's
    two [cden]s -- is common, and duplicating it is how two closers drift
    apart. *)
Lemma board_arm : forall (P : bool -> bool -> LRule -> Prop),
  (forall d r, d < fm_b F - 1 -> r < N0i + sti ->
     P (negb (fm_left F)) (fm_left F) (Aint d r)) ->
  (forall r ph, 0 < r -> r < N0f + stf -> ph < NPH -> P true true (Afill r ph)) ->
  forall s, Inv F NPH s ->
  exists s' A el er X n,
    fam_succ F s = Some s'
    /\ P el er A
    /\ (el = true -> tailL F X = []) /\ (er = true -> tailR F X = [])
    /\ fam_cfg F s  = cden (tailL F X) (tailR F X) n (lr_lhs A)
    /\ fam_cfg F s' = cden (tailL F X) (tailR F X) n (lr_rhs A)
    /\ 0 < lr_cb A.
Proof.
  intros P HPi HPf [[ds p] ph] Hi. destruct Hi as (Hbnd & Hlen & Hph).
  destruct (digs_decomp (fm_b F - 1) ds) as [Htop | (n & d & rest & -> & Hd)].
  - (* the top of a width: the FILL arm at index [aoff N0f stf (length ds)],
       in this state's OWN phase *)
    remember (aoff N0f stf (length ds)) as r eqn:Er.
    assert (Hr0 : 0 < r) by (subst r; apply arm_index_pos; assumption).
    assert (Hrlt : r < N0f + stf) by (subst r; apply arm_index_lt; assumption).
    assert (Hk : r + astride N0f stf r * acnt N0f stf (length ds) = length ds)
      by (subst r; apply arm_index; assumption).
    assert (Hist : fam_is_top F ds = true).
    { rewrite Htop at 1. apply pos1_is_top; assumption. }
    exists (filled F ph (length ds), p, f_to (fam_fill F ph)), (Afill r ph).
    exists true, true, [].
    exists (acnt N0f stf (length ds)).
    split; [|split; [|split; [|split; [|split; [|split]]]]].
    + unfold fam_succ.
      rewrite (fill_top ds ph Hph Hlen Hist), Hist. reflexivity.
    + exact (HPf r ph Hr0 Hrlt Hph).
    + intros _; apply tailL_nil.
    + intros _; apply tailR_nil.
    + rewrite (HAfL r ph Hr0 Hrlt Hph). symmetry.
      apply cden_cls_conf. rewrite Htop at 1. apply cells_top. exact Hk.
    + rewrite (HAfR r ph Hr0 Hrlt Hph). symmetry.
      apply cden_cls_conf. apply cells_filled.
      pose proof (Hfm12 r ph Hr0 Hrlt Hph). lia.
    + exact (HAfC r ph Hr0 Hrlt Hph).
  - (* not the top: an INTERIOR arm, for the digit that is not the top one.
       The phase is carried across untouched -- [pos1_class_not_top] is what
       says the fill does not fire here, and with more than one phase that
       is the same fact as "the phase does not move". *)
    apply Forall_app in Hbnd as [Hrun Hrest'].
    inversion Hrest' as [|? ? Hdb Hrest]; subst.
    assert (Hdlt : d < fm_b F - 1) by lia.
    remember (aoff N0i sti n) as r eqn:Er.
    assert (Hrlt : r < N0i + sti) by (subst r; apply arm_index_lt; assumption).
    assert (Hn : r + astride N0i sti r * acnt N0i sti n = n)
      by (subst r; apply arm_index; assumption).
    exists (repeat 0 n ++ S d :: rest, p, ph), (Aint d r).
    exists (negb (fm_left F)), (fm_left F), (cls_tail F rest ph).
    exists (acnt N0i sti n).
    split; [|split; [|split; [|split; [|split; [|split]]]]].
    + assert (Hns : fam_next F (repeat (fm_b F - 1) n ++ d :: rest) ph
                    = Some (repeat 0 n ++ S d :: rest))
        by exact (pos1_class_succ F d Hb Hcode Hstep Hdlt n rest ph Hrest I).
      unfold fam_succ. rewrite Hns.
      rewrite (pos1_class_not_top F d n rest Hb Hcode Hstep Hdlt Hrest).
      reflexivity.
    + exact (HPi d r Hdlt Hrlt).
    + intros He. unfold tailL. destruct (fm_left F); [discriminate|reflexivity].
    + intros He. unfold tailR. rewrite He. reflexivity.
    + rewrite (HAiL d r Hdlt Hrlt). symmetry. apply cden_cls_conf.
      rewrite <- Hn at 1.
      apply (fam_cells_class F [] (fm_b F - 1) r (astride N0i sti r)
               (acnt N0i sti n) [d] rest ph).
    + rewrite (HAiR d r Hdlt Hrlt). symmetry. apply cden_cls_conf.
      rewrite <- Hn at 1.
      apply (fam_cells_class F [] 0 r (astride N0i sti r)
               (acnt N0i sti n) [S d] rest ph).
    + exact (HAiC d r Hdlt Hrlt).
Qed.

Lemma board_lap : forall s, Inv F NPH s ->
  exists s' m, fam_succ F s = Some s' /\ 0 < m /\
               csteps tm m (fam_cfg F s) = Some (fam_cfg F s').
Proof.
  intros s Hi.
  destruct (board_arm (RuleSound tm) HAiS HAfS s Hi)
    as (s' & A & el & er & X & n & Hsucc & HA & HL & HR & Hl & Hr & Hcb).
  exists s', (lr_ca A * n + lr_cb A).
  split; [exact Hsucc | split; [nia|]].
  rewrite Hl, Hr. exact (HA _ _ n HL HR).
Qed.

(** The visit premise, at a top of whatever phase the counter is in when it
    gets there.  Both closers need exactly this and they differ only in
    which chains they are handed, so it is proved once over the chain. *)
Lemma board_visit : forall (V : nat -> St -> list lstep) q N,
  (forall r, 0 < r -> r < N0f + stf ->
     srun_st tm true true (V r q) (lr_lhs (Afill r pv)) = Some q) ->
  exists n k c, N <= n /\ csteps tm k (CfB n) = Some c /\ fst c = q.
Proof.
  intros V q N HV.
  destruct (tops_cof_pv s0 N inv0)
    as (n & s' & HN & Hit & Htop & Hi' & Hph).
  exists n.
  destruct s' as [[ds' p'] ph']. simpl in Htop. simpl in Hph. subst ph'.
  destruct Hi' as (Hbnd' & Hlen' & _).
  assert (Hsh : ds' = repeat (fm_b F - 1) (length ds'))
    by (apply pos1_top_shape; assumption).
  remember (aoff N0f stf (length ds')) as r eqn:Er.
  assert (Hr0 : 0 < r) by (subst r; apply arm_index_pos; assumption).
  assert (Hrlt : r < N0f + stf) by (subst r; apply arm_index_lt; assumption).
  assert (Hk : r + astride N0f stf r * acnt N0f stf (length ds') = length ds')
    by (subst r; apply arm_index; assumption).
  assert (Hden : CfB n
                 = cden [] [] (acnt N0f stf (length ds')) (lr_lhs (Afill r pv))).
  { unfold CfB. rewrite Hit, (HAfL r pv Hr0 Hrlt Hpv).
    rewrite <- (cden_cls_conf F
                  (run_side F (fm_b F - 1) r (astride N0f stf r) 0 pv [] [])
                  [] (acnt N0f stf (length ds')) ds' p' pv).
    - unfold tailL, tailR; destruct (fm_left F); reflexivity.
    - rewrite Hsh at 1. apply cells_top. exact Hk. }
  destruct (vis_of_run tm (fun _ => CfB n) true true (V r q)
              (lr_lhs (Afill r pv)) 1%positive (acnt N0f stf (length ds'))
              [] [] q (HV r Hr0 Hrlt)
              (fun _ => eq_refl) (fun _ => eq_refl) Hden) as (k & c & Hc & Hq).
  exists k, c. split; [exact HN | split; [exact Hc | exact Hq]].
Qed.

Theorem boardph_neverqh : NeverQuasiHaltsSt tm.
Proof.
  apply (glue_neverqhN tm CfB).
  - (* boot *)
    exists t0. unfold CfB; simpl.
    rewrite <- lift_c0. apply csteps_lift. exact Hboot.
  - (* lap *)
    intros n.
    destruct (iter_total n s0 inv0) as (s & Hit & Hi).
    destruct (board_lap s Hi) as (s' & m & Hsucc & Hm & Hrun).
    exists m, (fam_cfg F s'). unfold CfB. rewrite Hit.
    split; [exact Hrun | split; [|exact Hm]].
    replace (S n) with (n + 1) by lia.
    rewrite fam_iter_add, Hit. simpl. rewrite Hsucc. reflexivity.
  - (* visits: at every top, and the tops are cofinal *)
    intros q N.
    exact (board_visit vis q N (fun r H0 Hr => Hvisit r q H0 Hr)).
Qed.

(** ** 8. The same board, for a row that QUASIHALTS

    4i: eleven of the live core's binary/step-1 rows read [BCD] rather than
    [ABCD].  Everything above is unchanged and is reused verbatim -- the same
    family, the same arms, the same [board_arm] case split; what the row adds
    is three things and no more:

    * every arm AVOIDS the quiet state ([RuleAvoid], recomputed from the
      arm's own chain by [LapAvoid]);
    * a visit chain per state OTHER than the quiet one (the quiet state has
      none, which is the whole point);
    * the quiet state's LAST visit, and that the window from it to the boot
      anchor is quiet too -- both concrete indices, both [vm_compute].

    These are declared after [boardph_neverqh], so a never-quasihalting board
    does not carry them and a quasihalting one does not carry [vis]. *)

Hypothesis HAiV : forall d r, d < fm_b F - 1 -> r < N0i + sti ->
  RuleAvoid tm (negb (fm_left F)) (fm_left F) qa (Aint d r).
Hypothesis HAfV : forall r ph, 0 < r -> r < N0f + stf -> ph < NPH ->
  RuleAvoid tm true true qa (Afill r ph).

Hypothesis HvisitQ : forall r q, q <> qa -> 0 < r -> r < N0f + stf ->
  srun_st tm true true (visq r q) (lr_lhs (Afill r pv)) = Some q.

Hypothesis Hqvis : VisitsAt tm qa sq.
Hypothesis Hqwin : forall n c, sq < n < t0 ->
  stepn tm n InitES = Some c -> fst c <> qa.

Lemma board_lap_avoid : forall s, Inv F NPH s ->
  exists s' m, fam_succ F s = Some s' /\ 0 < m
    /\ csteps tm m (fam_cfg F s) = Some (fam_cfg F s')
    /\ AvoidRun tm qa m (fam_cfg F s).
Proof.
  intros s Hi.
  destruct (board_arm (fun el er A => RuleSound tm el er A
                                      /\ RuleAvoid tm el er qa A)
              (fun d r Hd Hr => conj (HAiS d r Hd Hr) (HAiV d r Hd Hr))
              (fun r ph H0 Hr Hp => conj (HAfS r ph H0 Hr Hp)
                                         (HAfV r ph H0 Hr Hp)) s Hi)
    as (s' & A & el & er & X & n & Hsucc & (HAs & HAv) & HL & HR & Hl & Hr & Hcb).
  exists s', (lr_ca A * n + lr_cb A).
  split; [exact Hsucc | split; [nia | split]].
  - rewrite Hl, Hr. exact (HAs _ _ n HL HR).
  - rewrite Hl. exact (HAv _ _ n HL HR).
Qed.

Theorem boardph_iqh : NonHalt tm /\ QHBound (S sq) tm /\ QuasiHaltsSt tm.
Proof.
  apply (glue_qh_quietN tm CfB qa t0 sq).
  - (* boot, at the concrete index the bound is stated against *)
    unfold CfB; simpl. rewrite <- lift_c0. apply csteps_lift. exact Hboot.
  - (* the lap, and that it never enters [qa] *)
    intros n.
    destruct (iter_total n s0 inv0) as (s & Hit & Hi).
    destruct (board_lap_avoid s Hi) as (s' & m & Hsucc & Hm & Hrun & Hav).
    exists m, (fam_cfg F s'). unfold CfB. rewrite Hit.
    split; [exact Hrun | split; [| split; [exact Hm | exact Hav]]].
    replace (S n) with (n + 1) by lia.
    rewrite fam_iter_add, Hit. simpl. rewrite Hsucc. reflexivity.
  - (* visits, for every state but the quiet one: [boardph_neverqh]'s third
       bullet with [q <> qa] carried *)
    intros q N Hq.
    exact (board_visit visq q N (fun r H0 Hr => HvisitQ r q Hq H0 Hr)).
  - exact Hqvis.
  - exact Hqwin.
Qed.

End BoardPh.

(** ** 9. The one-phase board, with the interface it had before section 7 was
    phase-indexed.

    Every board emitted so far is a one-phase family, and this is exactly
    that instance: [NPH = 1], the boot in phase [0], one fill arm per index
    rather than one per index and phase.  It is a WRAPPER and not a second
    proof -- the whole content is [boardph_neverqh] at [NPH := 1] -- which is
    the same discipline [board_arm] enforces between the two closers.  The
    argument order is the one the emitted boards pass. *)

Section BoardOne.

Variable tm    : TM.
Variable F     : Fam.
Variable Aint  : nat -> nat -> LRule.
Variable N0i sti : nat.
Variable Afill : nat -> LRule.
Variable N0f stf : nat.
Variable fm1 fm2 : nat -> nat.
Variable vis   : nat -> St -> list lstep.
Variable ds0   : list nat.
Variable t0    : nat.
Variable qa    : St.
Variable sq    : nat.
Variable visq  : nat -> St -> list lstep.

Hypothesis Hb    : 1 < fm_b F.
Hypothesis Hcode : fm_code F = Binary.
Hypothesis Hstep : fm_step F = 1.
Hypothesis Hfpre : Forall (fun d => d < fm_b F) (f_pre (fam_fill F 0)).
Hypothesis Hfsuf : Forall (fun d => d < fm_b F) (f_suf (fam_fill F 0)).
Hypothesis Hfmid : f_mid (fam_fill F 0) < fm_b F.
Hypothesis Hfs   : length (f_pre (fam_fill F 0)) + length (f_suf (fam_fill F 0))
                   <= 1 + f_s (fam_fill F 0).
Hypothesis Hfto  : f_to (fam_fill F 0) = 0.

Hypothesis Hfm12 : forall r, 0 < r -> r < N0f + stf ->
  fm1 r + fm2 r
  + (length (f_pre (fam_fill F 0)) + length (f_suf (fam_fill F 0)))
  = r + f_s (fam_fill F 0).

Hypothesis Hbnd0 : Forall (fun d => d < fm_b F) ds0.
Hypothesis Hlen0 : 0 < length ds0.
Hypothesis Hboot : csteps tm t0 CTape.c0 = Some (fam_cfg F (ds0, 0, 0)).

Hypothesis Hsti : 0 < sti.
Hypothesis HAiS : forall d r, d < fm_b F - 1 -> r < N0i + sti ->
  RuleSound tm (negb (fm_left F)) (fm_left F) (Aint d r).
Hypothesis HAiL : forall d r, d < fm_b F - 1 -> r < N0i + sti ->
  lr_lhs (Aint d r)
    = cls_conf F (cls_side F [] (fm_b F - 1) r (astride N0i sti r) [d]).
Hypothesis HAiR : forall d r, d < fm_b F - 1 -> r < N0i + sti ->
  lr_rhs (Aint d r)
    = cls_conf F (cls_side F [] 0 r (astride N0i sti r) [S d]).
Hypothesis HAiC : forall d r, d < fm_b F - 1 -> r < N0i + sti ->
  0 < lr_cb (Aint d r).

Hypothesis Hstf : 0 < stf.
Hypothesis HN0f : 0 < N0f.
Hypothesis HAfS : forall r, 0 < r -> r < N0f + stf ->
  RuleSound tm true true (Afill r).
Hypothesis HAfL : forall r, 0 < r -> r < N0f + stf ->
  lr_lhs (Afill r)
    = cls_conf F (run_side F (fm_b F - 1) r (astride N0f stf r) 0 0 [] []).
Hypothesis HAfR : forall r, 0 < r -> r < N0f + stf ->
  lr_rhs (Afill r)
    = cls_conf F (run_side F (f_mid (fam_fill F 0)) (fm1 r)
                    (astride N0f stf r) (fm2 r) 0
                    (f_pre (fam_fill F 0)) (f_suf (fam_fill F 0))).
Hypothesis HAfC : forall r, 0 < r -> r < N0f + stf -> 0 < lr_cb (Afill r).

Hypothesis Hvisit : forall r q, 0 < r -> r < N0f + stf ->
  srun_st tm true true (vis r q) (lr_lhs (Afill r)) = Some q.

(** The one-phase family read as a one-element cycle.  [ph < 1] IS [ph = 0],
    which is what turns each hypothesis above into the phase-indexed one:
    every obligation is this section's own hypothesis with the phase
    substituted, and none of them is a new proof. *)
Ltac one_phase_tac :=
  try assumption; try lia;
  intros;
  repeat match goal with
         | [ H : ?p < 1 |- _ ] => assert (p = 0) by lia; subst p
         end;
  rewrite ?Hfto;
  try assumption; try lia; try (exists 0; reflexivity); eauto.

Theorem board_neverqh : NeverQuasiHaltsSt tm.
Proof.
  apply (boardph_neverqh tm F 1 Aint N0i sti (fun r _ => Afill r) N0f stf
                         (fun r _ => fm1 r) (fun r _ => fm2 r) 0 vis
                         ds0 0 t0); one_phase_tac.
Qed.

Hypothesis HAiV : forall d r, d < fm_b F - 1 -> r < N0i + sti ->
  RuleAvoid tm (negb (fm_left F)) (fm_left F) qa (Aint d r).
Hypothesis HAfV : forall r, 0 < r -> r < N0f + stf ->
  RuleAvoid tm true true qa (Afill r).

Hypothesis HvisitQ : forall r q, q <> qa -> 0 < r -> r < N0f + stf ->
  srun_st tm true true (visq r q) (lr_lhs (Afill r)) = Some q.

Hypothesis Hqvis : VisitsAt tm qa sq.
Hypothesis Hqwin : forall n c, sq < n < t0 ->
  stepn tm n InitES = Some c -> fst c <> qa.

Theorem board_iqh : NonHalt tm /\ QHBound (S sq) tm /\ QuasiHaltsSt tm.
Proof.
  apply (boardph_iqh tm F 1 Aint N0i sti (fun r _ => Afill r) N0f stf
                     (fun r _ => fm1 r) (fun r _ => fm2 r) 0
                     ds0 0 t0 qa sq visq);
    one_phase_tac.
Qed.

End BoardOne.

(** ** 10. The board at [(Gray, 2)]

    Section 7's board is [(Binary, 1)] in three places and nowhere else: the
    class law it calls ([pos1_class_succ]), the case split it runs on
    ([digs_decomp] at [t = b-1]), and the shape it gives the fill arm's
    left-hand side ([pos1_top_shape]).  Section 3b replaces all three, so this
    is the same argument over the same [glue_neverqhN], with:

    * FOUR interior classes rather than [b-1], indexed by [i < 4] and served
      by the same arm scheme (section 2b) -- and the class carries a fixed
      word before the run, which is what [cls_side]'s [u] is for;
    * the fill arm indexed by the WIDTH and carrying a fixed word at EACH end
      ([run_side]'s [w1]/[w2]), because the top of a width is
      [1-p] ++ 0^(k-2) ++ [1] and not a bare run.  Its index range starts at
      2, not at 1: no width is below 2 and the two fixed digits are part of
      every one;
    * one phase.  All six gray core rows are one-phase, so there is no cycle
      to lap and no [pv] to choose.

    A row that quasihalts would want section 8's twin of this; none of the
    gray rows does ([live = ABCD], measured), so it is not built. *)

Section BoardG.

Variable tm    : TM.
Variable F     : Fam.
Variable p     : nat.                  (** the family's parity *)
Variable Aint  : nat -> nat -> LRule.  (** the interior arm for class [i] at
                                           arm index [r] *)
Variable N0i sti : nat.
Variable Afill : nat -> LRule.         (** the fill arm at WIDTH index [r] *)
Variable N0f stf : nat.
Variable fw1 fw2 : nat -> nat.         (** how the top's concrete copies of the
                                           run divide about the block *)
Variable fm1 fm2 : nat -> nat.         (** and the fill target's *)
Variable vis   : nat -> St -> list lstep.
Variable ds0   : list nat.
Variable t0    : nat.

(** *** The family's parameters *)
Hypothesis HbF   : fm_b F = 2.
Hypothesis HcF   : fm_code F = Gray.
Hypothesis HsF   : fm_step F = 2.
Hypothesis Hp    : p < 2.
Hypothesis Hfpre : Forall (fun d => d < 2) (f_pre (fam_fill F 0)).
Hypothesis Hfsuf : Forall (fun d => d < 2) (f_suf (fam_fill F 0)).
Hypothesis Hfmid : f_mid (fam_fill F 0) < 2.
Hypothesis Hfs   : length (f_pre (fam_fill F 0))
                   + length (f_suf (fam_fill F 0))
                   <= 2 + f_s (fam_fill F 0).
Hypothesis Hfto  : f_to (fam_fill F 0) = 0.
Hypothesis Hfpar : forall k, 2 <= k -> dsum (filled F 0 k) mod 2 = p.

(** *** The boot.  It is a MEMBER, which is the parity's base case. *)
Hypothesis Hbnd0 : Forall (fun d => d < 2) ds0.
Hypothesis Hlen0 : 2 <= length ds0.
Hypothesis Hpar0 : dsum ds0 mod 2 = p.
Hypothesis Hboot : csteps tm t0 CTape.c0 = Some (fam_cfg F (ds0, 0, 0)).

(** *** The interior arms, one per CLASS and arm index *)
Hypothesis Hsti : 0 < sti.
Hypothesis HAiS : forall i r, i < 4 -> r < N0i + sti ->
  RuleSound tm (negb (fm_left F)) (fm_left F) (Aint i r).
Hypothesis HAiL : forall i r, i < 4 -> r < N0i + sti ->
  lr_lhs (Aint i r)
    = cls_conf F (cls_side F (cs_u (g2c p i)) (cs_t (g2c p i)) r
                    (astride N0i sti r) (cs_w (g2c p i))).
Hypothesis HAiR : forall i r, i < 4 -> r < N0i + sti ->
  lr_rhs (Aint i r)
    = cls_conf F (cls_side F (cs_u' (g2c p i)) (cs_t' (g2c p i)) r
                    (astride N0i sti r) (cs_w' (g2c p i))).
Hypothesis HAiC : forall i r, i < 4 -> r < N0i + sti -> 0 < lr_cb (Aint i r).

(** *** The fill arms, at both tails known empty, one per WIDTH index *)
Hypothesis Hstf : 0 < stf.
Hypothesis HN0f : 2 <= N0f.
Hypothesis Hfw   : forall r, 2 <= r -> r < N0f + stf -> fw1 r + fw2 r + 2 = r.
Hypothesis Hfm12 : forall r, 2 <= r -> r < N0f + stf ->
  fm1 r + fm2 r
  + (length (f_pre (fam_fill F 0)) + length (f_suf (fam_fill F 0)))
  = r + f_s (fam_fill F 0).
Hypothesis HAfS : forall r, 2 <= r -> r < N0f + stf ->
  RuleSound tm true true (Afill r).
Hypothesis HAfL : forall r, 2 <= r -> r < N0f + stf ->
  lr_lhs (Afill r)
    = cls_conf F (run_side F 0 (fw1 r) (astride N0f stf r) (fw2 r) 0
                    [1 - p] [1]).
Hypothesis HAfR : forall r, 2 <= r -> r < N0f + stf ->
  lr_rhs (Afill r)
    = cls_conf F (run_side F (f_mid (fam_fill F 0)) (fm1 r)
                    (astride N0f stf r) (fm2 r) 0
                    (f_pre (fam_fill F 0)) (f_suf (fam_fill F 0))).
Hypothesis HAfC : forall r, 2 <= r -> r < N0f + stf -> 0 < lr_cb (Afill r).

(** *** Liveness: every state is reached from every fill arm's anchor *)
Hypothesis Hvisit : forall r q, 2 <= r -> r < N0f + stf ->
  srun_st tm true true (vis r q) (lr_lhs (Afill r)) = Some q.

Let sg0 : CtrSt := (ds0, 0, 0).

Definition CfG (n : nat) : cconf :=
  match fam_iter F sg0 n with
  | Some s => fam_cfg F s
  | None => CTape.c0
  end.

Lemma invG0 : InvG p sg0.
Proof. unfold InvG, sg0. repeat split; assumption. Qed.

(** Section 5b's exports, at this section's own parameters. *)
Lemma iterG_total : forall N s,
  InvG p s -> exists s', fam_iter F s N = Some s' /\ InvG p s'.
Proof. intros N s Hi. eapply famG_iter_total; eassumption. Qed.

Lemma topsG_cof : forall s N,
  InvG p s ->
  exists n s', N <= n /\ fam_iter F s n = Some s'
               /\ fam_is_top F (ct_ds s') = true /\ InvG p s'.
Proof. intros s N Hi. eapply topsG_cofinal; eassumption. Qed.

Lemma fillG_top : forall ds, 2 <= length ds -> fam_is_top F ds = true ->
  fam_next F ds 0 = Some (filled F 0 (length ds)).
Proof. intros ds Hk Ht. eapply fillG_at_top; eassumption. Qed.

(** The cells of the top of a width, as the fill arm's left-hand side: a run
    of zeros with [1-p] before it and [1] after, and the arm at index [r]
    carries [fw1 r] copies before the block and [fw2 r] after. *)
Lemma cells_topG : forall k m1 s n m2, m1 + s * n + m2 + 2 = k ->
  fam_cells F (g2top p k) 0
    = sden [] n (run_side F 0 m1 s m2 0 [1 - p] [1]).
Proof.
  intros k m1 s n m2 Hk. unfold g2top.
  transitivity (fam_cells F ([1 - p] ++ repeat 0 (m1 + s * n + m2) ++ [1]) 0).
  - f_equal. cbn [app]. do 3 f_equal. lia.
  - apply fam_cells_run.
Qed.

Lemma cells_filledG : forall k a s n c,
  a + s * n + c
    = k + f_s (fam_fill F 0)
      - (length (f_pre (fam_fill F 0)) + length (f_suf (fam_fill F 0))) ->
  fam_cells F (filled F 0 k) 0
    = sden [] n (run_side F (f_mid (fam_fill F 0)) a s c 0
                   (f_pre (fam_fill F 0)) (f_suf (fam_fill F 0))).
Proof.
  intros k a s n c Hk.
  transitivity (fam_cells F
    (f_pre (fam_fill F 0)
     ++ repeat (f_mid (fam_fill F 0)) (a + s * n + c)
     ++ f_suf (fam_fill F 0)) 0).
  - f_equal. unfold filled. rewrite Hk. reflexivity.
  - apply fam_cells_run.
Qed.

(** The lap, by section 3b's four-way split: a member of a width is the top,
    where a fill arm applies, or an instance of one of the four classes, where
    an interior arm does.  [gray_split] is what [digs_decomp] was. *)
Lemma board_armG : forall (P : bool -> bool -> LRule -> Prop),
  (forall i r, i < 4 -> r < N0i + sti ->
     P (negb (fm_left F)) (fm_left F) (Aint i r)) ->
  (forall r, 2 <= r -> r < N0f + stf -> P true true (Afill r)) ->
  forall s, InvG p s ->
  exists s' A el er X n,
    fam_succ F s = Some s'
    /\ P el er A
    /\ (el = true -> tailL F X = []) /\ (er = true -> tailR F X = [])
    /\ fam_cfg F s  = cden (tailL F X) (tailR F X) n (lr_lhs A)
    /\ fam_cfg F s' = cden (tailL F X) (tailR F X) n (lr_rhs A)
    /\ 0 < lr_cb A.
Proof.
  intros P HPi HPf [[ds q] ph] Hi.
  destruct Hi as (Hbnd & Hk & -> & Hpar).
  destruct (gray_split p ds Hp Hbnd Hpar Hk)
    as [Htop | (i & n & rest & Hi4 & Hrest & Hds)].
  - (* the top of a width: the FILL arm at the width's own index *)
    remember (aoff N0f stf (length ds)) as r eqn:Er.
    assert (Hr2 : 2 <= r) by (subst r; apply arm_index_ge2; assumption).
    assert (Hrlt : r < N0f + stf) by (subst r; apply arm_index_lt; assumption).
    assert (Hidx : r + astride N0f stf r * acnt N0f stf (length ds) = length ds)
      by (subst r; apply arm_index; assumption).
    pose proof (Hfw r Hr2 Hrlt) as Hfwr.
    assert (Hist : fam_is_top F ds = true).
    { rewrite Htop at 1. apply g2top_is_top; try assumption; lia. }
    exists (filled F 0 (length ds), q, 0), (Afill r).
    exists true, true, [], (acnt N0f stf (length ds)).
    split; [|split; [|split; [|split; [|split; [|split]]]]].
    + unfold fam_succ.
      rewrite (fillG_top ds Hk Hist), Hist, Hfto.
      reflexivity.
    + exact (HPf r Hr2 Hrlt).
    + intros _; apply tailL_nil.
    + intros _; apply tailR_nil.
    + rewrite (HAfL r Hr2 Hrlt). symmetry.
      apply cden_cls_conf. rewrite Htop at 1. apply cells_topG. lia.
    + rewrite (HAfR r Hr2 Hrlt). symmetry.
      apply cden_cls_conf. apply cells_filledG.
      pose proof (Hfm12 r Hr2 Hrlt). lia.
    + exact (HAfC r Hr2 Hrlt).
  - (* not the top: the INTERIOR arm of the class the split named *)
    remember (aoff N0i sti n) as r eqn:Er.
    assert (Hrlt : r < N0i + sti) by (subst r; apply arm_index_lt; assumption).
    assert (Hidx : r + astride N0i sti r * acnt N0i sti n = n)
      by (subst r; apply arm_index; assumption).
    destruct (gray2_class F HbF HcF HsF p i n rest Hp Hrest
                ltac:(unfold g2par; rewrite <- Hds; exact Hpar))
      as (Hnt & Hnx & _).
    exists (cls_rhs (g2c p i) n rest, q, 0), (Aint i r).
    exists (negb (fm_left F)), (fm_left F), (cls_tail F rest 0).
    exists (acnt N0i sti n).
    split; [|split; [|split; [|split; [|split; [|split]]]]].
    + unfold fam_succ. rewrite Hds, (Hnx 0), Hnt. reflexivity.
    + exact (HPi i r Hi4 Hrlt).
    + intros He. unfold tailL. destruct (fm_left F); [discriminate|reflexivity].
    + intros He. unfold tailR. rewrite He. reflexivity.
    + rewrite (HAiL i r Hi4 Hrlt). symmetry. apply cden_cls_conf.
      rewrite Hds. unfold cls_lhs. rewrite <- Hidx at 1.
      apply (fam_cells_class F (cs_u (g2c p i)) (cs_t (g2c p i)) r
               (astride N0i sti r) (acnt N0i sti n) (cs_w (g2c p i)) rest 0).
    + rewrite (HAiR i r Hi4 Hrlt). symmetry. apply cden_cls_conf.
      unfold cls_rhs. rewrite <- Hidx at 1.
      apply (fam_cells_class F (cs_u' (g2c p i)) (cs_t' (g2c p i)) r
               (astride N0i sti r) (acnt N0i sti n) (cs_w' (g2c p i)) rest 0).
    + exact (HAiC i r Hi4 Hrlt).
Qed.

Lemma board_lapG : forall s, InvG p s ->
  exists s' m, fam_succ F s = Some s' /\ 0 < m /\
               csteps tm m (fam_cfg F s) = Some (fam_cfg F s').
Proof.
  intros s Hi.
  destruct (board_armG (RuleSound tm) HAiS HAfS s Hi)
    as (s' & A & el & er & X & n & Hsucc & HA & HL & HR & Hl & Hr & Hcb).
  exists s', (lr_ca A * n + lr_cb A).
  split; [exact Hsucc | split; [nia|]].
  rewrite Hl, Hr. exact (HA _ _ n HL HR).
Qed.

Lemma board_visitG : forall q N,
  exists n k c, N <= n /\ csteps tm k (CfG n) = Some c /\ fst c = q.
Proof.
  intros q N.
  destruct (topsG_cof sg0 N invG0) as (n & s' & HN & Hit & Htop & Hi').
  exists n.
  destruct s' as [[ds' q'] ph']. simpl in Htop.
  destruct Hi' as (Hbnd' & Hk' & Hph' & Hpar').
  assert (Hsh : ds' = g2top p (length ds'))
    by (apply (gray_top_shape F HbF HcF HsF); assumption).
  remember (aoff N0f stf (length ds')) as r eqn:Er.
  assert (Hr2 : 2 <= r) by (subst r; apply arm_index_ge2; assumption).
  assert (Hrlt : r < N0f + stf) by (subst r; apply arm_index_lt; assumption).
  assert (Hidx : r + astride N0f stf r * acnt N0f stf (length ds') = length ds')
    by (subst r; apply arm_index; assumption).
  pose proof (Hfw r Hr2 Hrlt) as Hfwr.
  assert (Hden : CfG n
                 = cden [] [] (acnt N0f stf (length ds')) (lr_lhs (Afill r))).
  { unfold CfG. rewrite Hit, (HAfL r Hr2 Hrlt), Hph'.
    rewrite <- (cden_cls_conf F
                  (run_side F 0 (fw1 r) (astride N0f stf r) (fw2 r) 0
                     [1 - p] [1])
                  [] (acnt N0f stf (length ds')) ds' q' 0).
    - unfold tailL, tailR; destruct (fm_left F); reflexivity.
    - rewrite Hsh at 1. apply cells_topG. lia. }
  destruct (vis_of_run tm (fun _ => CfG n) true true (vis r q)
              (lr_lhs (Afill r)) 1%positive (acnt N0f stf (length ds'))
              [] [] q (Hvisit r q Hr2 Hrlt)
              (fun _ => eq_refl) (fun _ => eq_refl) Hden) as (k & c & Hc & Hq).
  exists k, c. split; [exact HN | split; [exact Hc | exact Hq]].
Qed.

Theorem boardG_neverqh : NeverQuasiHaltsSt tm.
Proof.
  apply (glue_neverqhN tm CfG).
  - exists t0. unfold CfG; simpl.
    rewrite <- lift_c0. apply csteps_lift. exact Hboot.
  - intros n.
    destruct (iterG_total n sg0 invG0) as (s & Hit & Hi).
    destruct (board_lapG s Hi) as (s' & m & Hsucc & Hm & Hrun).
    exists m, (fam_cfg F s'). unfold CfG. rewrite Hit.
    split; [exact Hrun | split; [|exact Hm]].
    replace (S n) with (n + 1) by lia.
    rewrite fam_iter_add, Hit. simpl. rewrite Hsucc. reflexivity.
  - intros q N. exact (board_visitG q N).
Qed.

End BoardG.
