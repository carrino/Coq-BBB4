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

(** The class [t^(r + s*m) ++ w ++ rest] IS one [sside], with [rest] opaque.

    The STRIDE [s] is there because the cost of a carry ripple need not be
    affine in the run length: measured (LADDER_PLAN 4i), four live-core rows
    walk the run at one cost on even lengths and another on odd, so their
    class splits into one arm per residue and each arm's block is [s] copies
    of the digit word.  [s = 1], [r = 0] is the ordinary case; [s = 0] is a
    flat arm, and [blk] is what makes that shape derivable. *)
Definition cls_side (t r s : nat) (w : list nat) : sside :=
  blk (fm_pre F ++ rep (dig F t) r) (dig F t) s (flat_map (dig F) w).

Lemma fam_cells_class : forall t r s m w rest ph,
  fam_cells F (repeat t (r + s * m) ++ w ++ rest) ph
    = sden (cls_tail rest ph) m (cls_side t r s w).
Proof.
  intros t r s m w rest ph.
  rewrite fam_cells_eq. unfold cls_side, cls_tail.
  rewrite blk_den, flat_map_repeat, flat_map_app, rep_add, !app_assoc.
  reflexivity.
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
  { unfold fam_is_top. apply Nat.ltb_ge. lia. }
  unfold fam_next. rewrite Htop.
  rewrite <- Hsucc. unfold fam_of_value. rewrite Hcode.
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
  unfold fam_is_top in Htop. apply Nat.ltb_lt in Htop.
  rewrite Hstep in Htop.
  assert (Hv : fam_value F ds = Nat.pow (fm_b F) (length ds) - 1) by lia.
  unfold fam_value in Hv. rewrite Hcode in Hv.
  transitivity (pos_of (fm_b F) (length ds) (val_pos (fm_b F) ds)).
  - symmetry. apply pos_of_val_pos; assumption.
  - rewrite Hv. apply pos_of_max; lia.
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

(** ** 5. The widths are cofinal, hence the fill arm fires forever

    4h(b): "the value strictly increases by [fm_step] within a width and is
    bounded by [b^k - 1], so the top of every width is reached and the fill
    fires there, and the width grows without bound."  That is
    [top_reached] and [tops_cofinal], and it is what turns the
    certificate's MEASUREMENT [arms_infinitely_often] into a theorem. *)

Definition ct_ds (s : CtrSt) : list nat := let '(ds, _, _) := s in ds.

Section Iter.

Variable F : Fam.
Hypothesis Hb    : 1 < fm_b F.
Hypothesis Hcode : fm_code F = Binary.
Hypothesis Hstep : fm_step F = 1.
Hypothesis Hfpre : Forall (fun d => d < fm_b F) (f_pre (fam_fill F 0)).
Hypothesis Hfsuf : Forall (fun d => d < fm_b F) (f_suf (fam_fill F 0)).
Hypothesis Hfmid : f_mid (fam_fill F 0) < fm_b F.
Hypothesis Hfs   : length (f_pre (fam_fill F 0)) + length (f_suf (fam_fill F 0))
                   <= 1 + f_s (fam_fill F 0).
Hypothesis Hfto  : f_to (fam_fill F 0) = 0.

(** What a reachable counter state carries.  The phase is pinned because a
    one-phase family's fill lands back in phase 0; a multi-phase family
    carries the phase cycle here instead, which is a change to this
    predicate and not to anything above it. *)
Definition Inv (s : CtrSt) : Prop :=
  let '(ds, _, ph) := s in
  Forall (fun d => d < fm_b F) ds /\ 0 < length ds /\ ph = 0.

Lemma inv_value_lt : forall s,
  Inv s -> fam_value F (ct_ds s) < Nat.pow (fm_b F) (length (ct_ds s)).
Proof.
  intros [[ds p] ph] (Hbnd & _ & _); simpl.
  unfold fam_value. rewrite Hcode. apply val_pos_lt; [lia | exact Hbnd].
Qed.

(** The fill at the top, spelled out for a family whose fill law is a pure
    widening (no target prefix or suffix). *)
Definition filled (k : nat) : list nat :=
  f_pre (fam_fill F 0)
  ++ repeat (f_mid (fam_fill F 0))
       (k + f_s (fam_fill F 0)
        - (length (f_pre (fam_fill F 0)) + length (f_suf (fam_fill F 0))))
  ++ f_suf (fam_fill F 0).

Lemma fill_at_top : forall ds,
  0 < length ds -> fam_is_top F ds = true ->
  fam_next F ds 0 = Some (filled (length ds)).
Proof.
  intros ds Hk Htop. unfold fam_next, filled. rewrite Htop.
  unfold fill_apply.
  destruct (Nat.leb_spec (length (f_pre (fam_fill F 0))
                          + length (f_suf (fam_fill F 0)))
              (length ds + f_s (fam_fill F 0))); [reflexivity | lia].
Qed.

Lemma filled_length : forall k, 0 < k ->
  length (filled k) = k + f_s (fam_fill F 0).
Proof.
  intros k Hk. unfold filled.
  rewrite !app_length, repeat_length. lia.
Qed.

Lemma filled_bnd : forall k, Forall (fun d => d < fm_b F) (filled k).
Proof.
  intros k. unfold filled. apply Forall_app. split; [exact Hfpre|].
  apply Forall_app. split; [|exact Hfsuf].
  apply Forall_forall. intros x Hx. apply repeat_spec in Hx. lia.
Qed.

Lemma fam_succ_total : forall s,
  Inv s -> exists s', fam_succ F s = Some s' /\ Inv s'.
Proof.
  intros [[ds p] ph] Hi. destruct Hi as (Hbnd & Hlen & ->).
  destruct (fam_is_top F ds) eqn:Htop.
  - (* the fill *)
    eexists. unfold fam_succ.
    rewrite (fill_at_top ds Hlen Htop), Htop, Hfto.
    split; [reflexivity|]. simpl. repeat split.
    + apply filled_bnd.
    + rewrite filled_length by exact Hlen. lia.
  - (* an interior step *)
    assert (Hlt : fam_value F ds + fm_step F < Nat.pow (fm_b F) (length ds)).
    { unfold fam_is_top in Htop. apply Nat.ltb_ge in Htop.
      pose proof (pow_pos (fm_b F) (length ds) ltac:(lia)). lia. }
    unfold fam_succ, fam_next. rewrite Htop.
    unfold fam_of_value. rewrite Hcode.
    destruct (Nat.ltb_spec (fam_value F ds + fm_step F)
                (Nat.pow (fm_b F) (length ds))); [|lia].
    eexists. split; [reflexivity|]. simpl. repeat split.
    + apply pos_of_lt; lia.
    + rewrite pos_of_length. exact Hlen.
Qed.

Lemma fam_iter_total : forall N s,
  Inv s -> exists s', fam_iter F s N = Some s' /\ Inv s'.
Proof.
  induction N as [|N IH]; intros s Hi; [exists s; split; [reflexivity|exact Hi]|].
  destruct (fam_succ_total s Hi) as (s1 & H1 & Hi1).
  destruct (IH s1 Hi1) as (s' & H' & Hi').
  exists s'. split; [|exact Hi']. simpl. rewrite H1. exact H'.
Qed.

(** Within a width the measure [b^k - value] strictly decreases, so the top
    of the width is reached in finitely many anchor visits. *)
Lemma top_reached_aux : forall m s,
  Inv s ->
  Nat.pow (fm_b F) (length (ct_ds s)) - fam_value F (ct_ds s) <= m ->
  exists n s', fam_iter F s n = Some s' /\ fam_is_top F (ct_ds s') = true.
Proof.
  induction m as [|m IH]; intros s Hi Hm.
  - exfalso. pose proof (inv_value_lt s Hi). lia.
  - destruct (fam_is_top F (ct_ds s)) eqn:Htop.
    + exists 0, s. split; [reflexivity | exact Htop].
    + destruct s as [[ds p] ph]. simpl in Htop.
      destruct Hi as (Hbnd & Hlen & ->).
      assert (Hi : Inv (ds, p, 0)) by (simpl; repeat split; assumption).
      destruct (fam_succ_total _ Hi) as (s1 & H1 & Hi1).
      (* the interior step: value up by [fm_step], width unchanged *)
      unfold fam_succ in H1. rewrite Htop in H1.
      destruct (fam_next F ds 0) as [nd|] eqn:Hnd; [|discriminate].
      injection H1 as <-.
      destruct (fam_next_interior F ds 0 nd Hb Htop Hnd) as (Hval & Hlen').
      destruct (IH (nd, p, 0) Hi1) as (n & s' & Hit & Htop').
      { simpl. simpl in Hm. rewrite Hval, Hlen'. lia. }
      exists (S n), s'. split; [|exact Htop'].
      simpl. unfold fam_succ. rewrite Htop, Hnd. exact Hit.
Qed.

Lemma top_reached : forall s,
  Inv s ->
  exists n s', fam_iter F s n = Some s' /\ fam_is_top F (ct_ds s') = true.
Proof.
  intros s Hi.
  apply (top_reached_aux
           (Nat.pow (fm_b F) (length (ct_ds s)) - fam_value F (ct_ds s)) s Hi).
  lia.
Qed.

(** ...and since a fill widens, tops keep coming: for every bound there is
    a later anchor at the top of its width.  This is the premise
    [glue_neverqhN] needs, and the reason it needs only the weak one. *)
Theorem tops_cofinal : forall s N,
  Inv s ->
  exists n s', N <= n /\ fam_iter F s n = Some s'
               /\ fam_is_top F (ct_ds s') = true /\ Inv s'.
Proof.
  intros s N Hi.
  destruct (fam_iter_total N s Hi) as (sN & HN & HiN).
  destruct (top_reached sN HiN) as (m & s' & Hm & Htop).
  assert (Hi' : Inv s').
  { destruct (fam_iter_total m sN HiN) as (s'' & H'' & Hi'').
    rewrite Hm in H''. injection H'' as <-. exact Hi''. }
  exists (N + m), s'. repeat split; [lia | | exact Htop | exact Hi'].
  rewrite fam_iter_add, HN. exact Hm.
Qed.

End Iter.

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
    live: [N0i]/[sti] for the interior, [N0f]/[stf] for the fill. *)

Section Board.

Variable tm    : TM.
Variable F     : Fam.
Variable Aint  : nat -> nat -> LRule.  (** the interior arm for digit [d] at
                                           arm index [r] *)
Variable N0i sti : nat.             (** its threshold and its stride *)
Variable Afill : nat -> LRule.      (** the arm that sees the counter's end,
                                        at arm index [r] *)
Variable N0f stf : nat.             (** and ITS threshold and stride -- the
                                        same scheme, its own two knobs *)
Variable fm1 fm2 : nat -> nat.      (** how the fill's guaranteed copies split,
                                        per arm index *)
Variable vis   : nat -> St -> list lstep.  (** a chain to each state, from
                                               each fill arm's anchor *)
Variable ds0   : list nat.          (** the boot digit string *)
Variable t0    : nat.               (** and how many steps reach it *)

(** And, for a row that QUASIHALTS rather than never quasihalting (section 8
    below), the quiet state, its last visit, and the visit chains for the
    other three.  [board_neverqh] does not use them, so it does not carry
    them: a never-quasihalting board supplies [vis] and a quasihalting one
    supplies [visq]. *)
Variable qa   : St.
Variable sq   : nat.
Variable visq : nat -> St -> list lstep.

(** *** The family's parameters *)
Hypothesis Hb    : 1 < fm_b F.
Hypothesis Hcode : fm_code F = Binary.
Hypothesis Hstep : fm_step F = 1.
Hypothesis Hfpre : Forall (fun d => d < fm_b F) (f_pre (fam_fill F 0)).
Hypothesis Hfsuf : Forall (fun d => d < fm_b F) (f_suf (fam_fill F 0)).
Hypothesis Hfmid : f_mid (fam_fill F 0) < fm_b F.
Hypothesis Hfs   : length (f_pre (fam_fill F 0)) + length (f_suf (fam_fill F 0))
                   <= 1 + f_s (fam_fill F 0).
Hypothesis Hfto  : f_to (fam_fill F 0) = 0.

(** How many of the fill target's guaranteed digit copies sit before the
    symbolic run and how many after.  The emitter picks the split the chain
    search normalises to; the kernel only asks that they add up -- and what
    they add up to now depends on the arm, because an arm at offset [r] has
    [r] copies of the run on its left-hand side rather than one. *)
Hypothesis Hfm12 : forall r, 0 < r -> r < N0f + stf ->
  fm1 r + fm2 r
  + (length (f_pre (fam_fill F 0)) + length (f_suf (fam_fill F 0)))
  = r + f_s (fam_fill F 0).

(** *** The boot *)
Hypothesis Hbnd0 : Forall (fun d => d < fm_b F) ds0.
Hypothesis Hlen0 : 0 < length ds0.
Hypothesis Hboot : csteps tm t0 CTape.c0 = Some (fam_cfg F (ds0, 0, 0)).

(** *** The interior arms, one per digit below the top and per arm index *)
Hypothesis Hsti : 0 < sti.
Hypothesis HAiS : forall d r, d < fm_b F - 1 -> r < N0i + sti ->
  RuleSound tm (negb (fm_left F)) (fm_left F) (Aint d r).
Hypothesis HAiL : forall d r, d < fm_b F - 1 -> r < N0i + sti ->
  lr_lhs (Aint d r)
    = cls_conf F (cls_side F (fm_b F - 1) r (astride N0i sti r) [d]).
Hypothesis HAiR : forall d r, d < fm_b F - 1 -> r < N0i + sti ->
  lr_rhs (Aint d r) = cls_conf F (cls_side F 0 r (astride N0i sti r) [S d]).
Hypothesis HAiC : forall d r, d < fm_b F - 1 -> r < N0i + sti ->
  0 < lr_cb (Aint d r).

(** *** The fill arms, at both tails known empty.  [0 < N0f] is what keeps
    [r = 0] out of the index range: no width is [0], so no fill arm is. *)
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

(** *** Liveness: every state is reached from every fill arm's anchor *)
Hypothesis Hvisit : forall r q, 0 < r -> r < N0f + stf ->
  srun_st tm true true (vis r q) (lr_lhs (Afill r)) = Some q.

Let s0 : CtrSt := (ds0, 0, 0).

Definition CfB (n : nat) : cconf :=
  match fam_iter F s0 n with
  | Some s => fam_cfg F s
  | None => CTape.c0
  end.

Lemma inv0 : Inv F s0.
Proof. simpl. repeat split; assumption. Qed.

(** The cells of a top-of-width string, as the fill arm's left-hand side.
    The arm is the one at index [m1], and it walks the width in blocks of
    [s]: [m1 + s*n = k] is [arm_index] and nothing else. *)
Lemma cells_top : forall k m1 s n, m1 + s * n = k ->
  fam_cells F (repeat (fm_b F - 1) k) 0
    = sden [] n (run_side F (fm_b F - 1) m1 s 0 0 [] []).
Proof.
  intros k m1 s n Hk.
  transitivity
    (fam_cells F ([] ++ repeat (fm_b F - 1) (m1 + s * n + 0) ++ []) 0).
  - f_equal. rewrite Nat.add_0_r, Hk, app_nil_r. reflexivity.
  - apply fam_cells_run.
Qed.

(** ...and of what the fill law puts there, as its right-hand side.  The
    law's own prefix and suffix ride along as the fixed words either side of
    the run, which is what lets a family whose fill is not a bare widening
    use the same arm shape. *)
Lemma cells_filled : forall k a s n c,
  a + s * n + c
    = k + f_s (fam_fill F 0)
      - (length (f_pre (fam_fill F 0)) + length (f_suf (fam_fill F 0))) ->
  fam_cells F (filled F k) 0
    = sden [] n
        (run_side F (f_mid (fam_fill F 0)) a s c 0
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

(** The lap, by the case split: a state is at the top of its width, where a
    fill arm applies, or it is not, where an interior arm does.

    Stated ONCE, for both closers.  What a closer wants OF the arm it lands
    on is the parameter [P]: [board_neverqh] wants [RuleSound], and the
    quasihalt board (Checkers/LadderQH.v) wants [RuleSound] and [RuleAvoid]
    of the same arm.  Everything else -- which arm serves the state, at what
    index and block count, and that the configurations either side of the
    lap are that arm's two [cden]s -- is common, and duplicating it is how
    two closers drift apart. *)
Lemma board_arm : forall (P : bool -> bool -> LRule -> Prop),
  (forall d r, d < fm_b F - 1 -> r < N0i + sti ->
     P (negb (fm_left F)) (fm_left F) (Aint d r)) ->
  (forall r, 0 < r -> r < N0f + stf -> P true true (Afill r)) ->
  forall s, Inv F s ->
  exists s' A el er X n,
    fam_succ F s = Some s'
    /\ P el er A
    /\ (el = true -> tailL F X = []) /\ (er = true -> tailR F X = [])
    /\ fam_cfg F s  = cden (tailL F X) (tailR F X) n (lr_lhs A)
    /\ fam_cfg F s' = cden (tailL F X) (tailR F X) n (lr_rhs A)
    /\ 0 < lr_cb A.
Proof.
  intros P HPi HPf [[ds p] ph] Hi. destruct Hi as (Hbnd & Hlen & ->).
  destruct (digs_decomp (fm_b F - 1) ds) as [Htop | (n & d & rest & -> & Hd)].
  - (* the top of a width: the FILL arm at index [aoff N0f stf (length ds)] *)
    remember (aoff N0f stf (length ds)) as r eqn:Er.
    assert (Hr0 : 0 < r) by (subst r; apply arm_index_pos; assumption).
    assert (Hrlt : r < N0f + stf) by (subst r; apply arm_index_lt; assumption).
    assert (Hk : r + astride N0f stf r * acnt N0f stf (length ds) = length ds)
      by (subst r; apply arm_index; assumption).
    assert (Hist : fam_is_top F ds = true).
    { rewrite Htop at 1. apply pos1_is_top; assumption. }
    exists (filled F (length ds), p, 0), (Afill r), true, true, [].
    exists (acnt N0f stf (length ds)).
    split; [|split; [|split; [|split; [|split; [|split]]]]].
    + unfold fam_succ.
      erewrite fill_at_top by (assumption || lia).
      rewrite Hist, Hfto. reflexivity.
    + exact (HPf r Hr0 Hrlt).
    + intros _; apply tailL_nil.
    + intros _; apply tailR_nil.
    + rewrite (HAfL r Hr0 Hrlt). symmetry.
      apply cden_cls_conf. rewrite Htop at 1. apply cells_top. exact Hk.
    + rewrite (HAfR r Hr0 Hrlt). symmetry.
      apply cden_cls_conf. apply cells_filled.
      pose proof (Hfm12 r Hr0 Hrlt). lia.
    + exact (HAfC r Hr0 Hrlt).
  - (* not the top: an INTERIOR arm, for the digit that is not the top one *)
    apply Forall_app in Hbnd as [Hrun Hrest'].
    inversion Hrest' as [|? ? Hdb Hrest]; subst.
    assert (Hdlt : d < fm_b F - 1) by lia.
    remember (aoff N0i sti n) as r eqn:Er.
    assert (Hrlt : r < N0i + sti) by (subst r; apply arm_index_lt; assumption).
    assert (Hn : r + astride N0i sti r * acnt N0i sti n = n)
      by (subst r; apply arm_index; assumption).
    exists (repeat 0 n ++ S d :: rest, p, 0), (Aint d r).
    exists (negb (fm_left F)), (fm_left F), (cls_tail F rest 0).
    exists (acnt N0i sti n).
    split; [|split; [|split; [|split; [|split; [|split]]]]].
    + assert (Hns : fam_next F (repeat (fm_b F - 1) n ++ d :: rest) 0
                    = Some (repeat 0 n ++ S d :: rest))
        by exact (pos1_class_succ F d Hb Hcode Hstep Hdlt n rest 0 Hrest I).
      unfold fam_succ. rewrite Hns.
      destruct (fam_is_top F (repeat (fm_b F - 1) n ++ d :: rest));
        [rewrite Hfto|]; reflexivity.
    + exact (HPi d r Hdlt Hrlt).
    + intros He. unfold tailL. destruct (fm_left F); [discriminate|reflexivity].
    + intros He. unfold tailR. rewrite He. reflexivity.
    + rewrite (HAiL d r Hdlt Hrlt). symmetry. apply cden_cls_conf.
      rewrite <- Hn at 1.
      apply (fam_cells_class F (fm_b F - 1) r (astride N0i sti r)
               (acnt N0i sti n) [d] rest 0).
    + rewrite (HAiR d r Hdlt Hrlt). symmetry. apply cden_cls_conf.
      rewrite <- Hn at 1.
      apply (fam_cells_class F 0 r (astride N0i sti r)
               (acnt N0i sti n) [S d] rest 0).
    + exact (HAiC d r Hdlt Hrlt).
Qed.

Lemma board_lap : forall s, Inv F s ->
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

Theorem board_neverqh : NeverQuasiHaltsSt tm.
Proof.
  apply (glue_neverqhN tm CfB).
  - (* boot *)
    exists t0. unfold CfB; simpl.
    rewrite <- lift_c0. apply csteps_lift. exact Hboot.
  - (* lap *)
    intros n.
    destruct (fam_iter_total F Hb Hcode Hstep Hfpre Hfsuf Hfmid Hfs Hfto
                n s0 inv0) as (s & Hit & Hi).
    destruct (board_lap s Hi) as (s' & m & Hsucc & Hm & Hrun).
    exists m, (fam_cfg F s'). unfold CfB. rewrite Hit.
    split; [exact Hrun | split; [|exact Hm]].
    replace (S n) with (n + 1) by lia.
    rewrite fam_iter_add, Hit. simpl. rewrite Hsucc. reflexivity.
  - (* visits: at every top, and the tops are cofinal *)
    intros q N.
    destruct (tops_cofinal F Hb Hcode Hstep Hfpre Hfsuf Hfmid Hfs Hfto s0 N
                inv0) as (n & s' & HN & Hit & Htop & Hi').
    exists n.
    destruct s' as [[ds' p'] ph']. simpl in Htop.
    destruct Hi' as (Hbnd' & Hlen' & ->).
    assert (Hsh : ds' = repeat (fm_b F - 1) (length ds'))
      by (apply pos1_top_shape; assumption).
    remember (aoff N0f stf (length ds')) as r eqn:Er.
    assert (Hr0 : 0 < r) by (subst r; apply arm_index_pos; assumption).
    assert (Hrlt : r < N0f + stf) by (subst r; apply arm_index_lt; assumption).
    assert (Hk : r + astride N0f stf r * acnt N0f stf (length ds') = length ds')
      by (subst r; apply arm_index; assumption).
    assert (Hden : CfB n
                   = cden [] [] (acnt N0f stf (length ds')) (lr_lhs (Afill r))).
    { unfold CfB. rewrite Hit, (HAfL r Hr0 Hrlt).
      rewrite <- (cden_cls_conf F
                    (run_side F (fm_b F - 1) r (astride N0f stf r) 0 0 [] [])
                    [] (acnt N0f stf (length ds')) ds' p' 0).
      - unfold tailL, tailR; destruct (fm_left F); reflexivity.
      - rewrite Hsh at 1. apply cells_top. exact Hk. }
    destruct (vis_of_run tm (fun _ => CfB n) true true (vis r q)
                (lr_lhs (Afill r)) 1%positive (acnt N0f stf (length ds'))
                [] [] q (Hvisit r q Hr0 Hrlt)
                (fun _ => eq_refl) (fun _ => eq_refl) Hden) as (k & c & Hc & Hq).
    exists k, c. split; [exact HN | split; [exact Hc | exact Hq]].
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

    These are declared after [board_neverqh], so a never-quasihalting board
    does not carry them and a quasihalting one does not carry [vis]. *)

Hypothesis HAiV : forall d r, d < fm_b F - 1 -> r < N0i + sti ->
  RuleAvoid tm (negb (fm_left F)) (fm_left F) qa (Aint d r).
Hypothesis HAfV : forall r, 0 < r -> r < N0f + stf ->
  RuleAvoid tm true true qa (Afill r).

Hypothesis HvisitQ : forall r q, q <> qa -> 0 < r -> r < N0f + stf ->
  srun_st tm true true (visq r q) (lr_lhs (Afill r)) = Some q.

Hypothesis Hqvis : VisitsAt tm qa sq.
Hypothesis Hqwin : forall n c, sq < n < t0 ->
  stepn tm n InitES = Some c -> fst c <> qa.

Lemma board_lap_avoid : forall s, Inv F s ->
  exists s' m, fam_succ F s = Some s' /\ 0 < m
    /\ csteps tm m (fam_cfg F s) = Some (fam_cfg F s')
    /\ AvoidRun tm qa m (fam_cfg F s).
Proof.
  intros s Hi.
  destruct (board_arm (fun el er A => RuleSound tm el er A
                                      /\ RuleAvoid tm el er qa A)
              (fun d r Hd Hr => conj (HAiS d r Hd Hr) (HAiV d r Hd Hr))
              (fun r H0 Hr => conj (HAfS r H0 Hr) (HAfV r H0 Hr)) s Hi)
    as (s' & A & el & er & X & n & Hsucc & (HAs & HAv) & HL & HR & Hl & Hr & Hcb).
  exists s', (lr_ca A * n + lr_cb A).
  split; [exact Hsucc | split; [nia | split]].
  - rewrite Hl, Hr. exact (HAs _ _ n HL HR).
  - rewrite Hl. exact (HAv _ _ n HL HR).
Qed.

Theorem board_iqh : NonHalt tm /\ QHBound (S sq) tm /\ QuasiHaltsSt tm.
Proof.
  apply (glue_qh_quietN tm CfB qa t0 sq).
  - (* boot, at the concrete index the bound is stated against *)
    unfold CfB; simpl. rewrite <- lift_c0. apply csteps_lift. exact Hboot.
  - (* the lap, and that it never enters [qa] *)
    intros n.
    destruct (fam_iter_total F Hb Hcode Hstep Hfpre Hfsuf Hfmid Hfs Hfto
                n s0 inv0) as (s & Hit & Hi).
    destruct (board_lap_avoid s Hi) as (s' & m & Hsucc & Hm & Hrun & Hav).
    exists m, (fam_cfg F s'). unfold CfB. rewrite Hit.
    split; [exact Hrun | split; [| split; [exact Hm | exact Hav]]].
    replace (S n) with (n + 1) by lia.
    rewrite fam_iter_add, Hit. simpl. rewrite Hsucc. reflexivity.
  - (* visits, for every state but the quiet one: at every top, and the tops
       are cofinal -- [board_neverqh]'s third bullet with [q <> qa] carried *)
    intros q N Hq.
    destruct (tops_cofinal F Hb Hcode Hstep Hfpre Hfsuf Hfmid Hfs Hfto s0 N
                inv0) as (n & s' & HN & Hit & Htop & Hi').
    exists n.
    destruct s' as [[ds' p'] ph']. simpl in Htop.
    destruct Hi' as (Hbnd' & Hlen' & ->).
    assert (Hsh : ds' = repeat (fm_b F - 1) (length ds'))
      by (apply pos1_top_shape; assumption).
    remember (aoff N0f stf (length ds')) as r eqn:Er.
    assert (Hr0 : 0 < r) by (subst r; apply arm_index_pos; assumption).
    assert (Hrlt : r < N0f + stf) by (subst r; apply arm_index_lt; assumption).
    assert (Hk : r + astride N0f stf r * acnt N0f stf (length ds') = length ds')
      by (subst r; apply arm_index; assumption).
    assert (Hden : CfB n
                   = cden [] [] (acnt N0f stf (length ds')) (lr_lhs (Afill r))).
    { unfold CfB. rewrite Hit, (HAfL r Hr0 Hrlt).
      rewrite <- (cden_cls_conf F
                    (run_side F (fm_b F - 1) r (astride N0f stf r) 0 0 [] [])
                    [] (acnt N0f stf (length ds')) ds' p' 0).
      - unfold tailL, tailR; destruct (fm_left F); reflexivity.
      - rewrite Hsh at 1. apply cells_top. exact Hk. }
    destruct (vis_of_run tm (fun _ => CfB n) true true (visq r q)
                (lr_lhs (Afill r)) 1%positive (acnt N0f stf (length ds'))
                [] [] q (HvisitQ r q Hq Hr0 Hrlt)
                (fun _ => eq_refl) (fun _ => eq_refl) Hden) as (k & c & Hc & Hq').
    exists k, c. split; [exact HN | split; [exact Hc | exact Hq']].
  - exact Hqvis.
  - exact Hqwin.
Qed.

End Board.
