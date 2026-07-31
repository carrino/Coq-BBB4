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
From BBB4.Counters Require Import WTape.
From BBB4.Checkers Require Import LapDecider LadderKernel LadderFam.
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

Section Cells.

Variable F : Fam.

(** The opaque tail an arm sees: everything the class does not name. *)
Definition cls_tail (rest : list nat) (ph : nat) : list Sym :=
  flat_map (dig F) rest ++ nth ph (fm_tails F) [].

(** The class [t^n ++ w ++ rest] IS one [sside], with [rest] opaque. *)
Definition cls_side (t : nat) (w : list nat) : sside :=
  mkS (fm_pre F) (dig F t) 1 0 (flat_map (dig F) w).

Lemma fam_cells_class : forall t n w rest ph,
  fam_cells F (repeat t n ++ w ++ rest) ph
    = sden (cls_tail rest ph) n (cls_side t w).
Proof.
  intros t n w rest ph.
  rewrite fam_cells_eq. unfold sden, cls_side, cls_tail; simpl.
  rewrite flat_map_repeat, flat_map_app.
  rewrite ?Nat.mul_1_l, ?Nat.add_0_r.
  rewrite !app_assoc. reflexivity.
Qed.

(** The class [t^(m1 + n + m2)] with NOTHING opaque -- the shape the fill
    arm needs, because it must see the end of the counter.  The guaranteed
    copies are materialised into [s_pre] and [s_post] (4h: without that the
    fill arm has no chain at all, since a symbolic block count cannot have
    one copy peeled off its front). *)
Definition run_side (t m1 m2 ph : nat) : sside :=
  mkS (fm_pre F ++ rep (dig F t) m1) (dig F t) 1 0
      (rep (dig F t) m2 ++ nth ph (fm_tails F) []).

Lemma fam_cells_run : forall t m1 n m2 ph,
  fam_cells F (repeat t (m1 + n + m2)) ph = sden [] n (run_side t m1 m2 ph).
Proof.
  intros t m1 n m2 ph.
  rewrite fam_cells_eq. unfold sden, run_side; simpl.
  rewrite (flat_map_repeat_nil F t (m1 + n + m2)).
  rewrite ?Nat.mul_1_l, ?Nat.add_0_r.
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
    class's run length. *)

Lemma lap_from_arm : forall tm F (A : LRule) el er X n sd sd' ds ds' p ph,
  RuleSound tm el er A ->
  (el = true -> tailL F X = []) -> (er = true -> tailR F X = []) ->
  lr_lhs A = cls_conf F sd -> lr_rhs A = cls_conf F sd' ->
  fam_cells F ds ph = sden X n sd ->
  fam_cells F ds' ph = sden X n sd' ->
  csteps tm (lr_ca A * n + lr_cb A) (fam_cfg F (ds, p, ph))
    = Some (fam_cfg F (ds', p, ph)).
Proof.
  intros tm F A el er X n sd sd' ds ds' p ph HA HL HR Hl Hr Hc Hc'.
  specialize (HA (tailL F X) (tailR F X) n HL HR).
  rewrite Hl, Hr in HA.
  rewrite (cden_cls_conf F sd X n ds p ph Hc),
          (cden_cls_conf F sd' X n ds' p ph Hc') in HA.
  exact HA.
Qed.

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
Hypothesis Hfpre : f_pre (fam_fill F 0) = [].
Hypothesis Hfsuf : f_suf (fam_fill F 0) = [].
Hypothesis Hfmid : f_mid (fam_fill F 0) < fm_b F.
Hypothesis Hfs   : 0 < f_s (fam_fill F 0).
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
Lemma fill_at_top : forall ds,
  fam_is_top F ds = true ->
  fam_next F ds 0
    = Some (repeat (f_mid (fam_fill F 0)) (length ds + f_s (fam_fill F 0))).
Proof.
  intros ds Htop. unfold fam_next. rewrite Htop.
  unfold fill_apply. rewrite Hfpre, Hfsuf; simpl.
  rewrite Nat.sub_0_r, app_nil_r. reflexivity.
Qed.

Lemma fam_succ_total : forall s,
  Inv s -> exists s', fam_succ F s = Some s' /\ Inv s'.
Proof.
  intros [[ds p] ph] Hi. destruct Hi as (Hbnd & Hlen & ->).
  destruct (fam_is_top F ds) eqn:Htop.
  - (* the fill *)
    eexists. unfold fam_succ. rewrite (fill_at_top ds Htop), Htop, Hfto.
    split; [reflexivity|]. simpl. repeat split.
    + apply Forall_forall. intros x Hx. apply repeat_spec in Hx. lia.
    + rewrite repeat_length. lia.
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

    Two arms carry the whole lap: an INTERIOR arm per non-top digit, and
    the FILL arm.  That is not a coincidence of this row -- it is the case
    split of [digs_decomp], and the emitted certificate's dozen arms are
    specialisations of these two at pinned run lengths. *)

Section Board.

Variable tm    : TM.
Variable F     : Fam.
Variable Aint  : nat -> LRule.      (** the interior arm for digit [d] *)
Variable Afill : LRule.             (** the arm that sees the counter's end *)
Variable vis   : St -> list lstep.  (** a chain to each state, from the fill *)
Variable ds0   : list nat.          (** the boot digit string *)
Variable t0    : nat.               (** and how many steps reach it *)

(** *** The family's parameters *)
Hypothesis Hb    : 1 < fm_b F.
Hypothesis Hcode : fm_code F = Binary.
Hypothesis Hstep : fm_step F = 1.
Hypothesis Hfpre : f_pre (fam_fill F 0) = [].
Hypothesis Hfsuf : f_suf (fam_fill F 0) = [].
Hypothesis Hfmid : f_mid (fam_fill F 0) < fm_b F.
Hypothesis Hfs   : 0 < f_s (fam_fill F 0).
Hypothesis Hfto  : f_to (fam_fill F 0) = 0.

(** *** The boot *)
Hypothesis Hbnd0 : Forall (fun d => d < fm_b F) ds0.
Hypothesis Hlen0 : 0 < length ds0.
Hypothesis Hboot : csteps tm t0 CTape.c0 = Some (fam_cfg F (ds0, 0, 0)).

(** *** The interior arms, one per digit below the top *)
Hypothesis HAiS : forall d, d < fm_b F - 1 ->
  RuleSound tm (negb (fm_left F)) (fm_left F) (Aint d).
Hypothesis HAiL : forall d, d < fm_b F - 1 ->
  lr_lhs (Aint d) = cls_conf F (cls_side F (fm_b F - 1) [d]).
Hypothesis HAiR : forall d, d < fm_b F - 1 ->
  lr_rhs (Aint d) = cls_conf F (cls_side F 0 [S d]).
Hypothesis HAiC : forall d, d < fm_b F - 1 -> 0 < lr_cb (Aint d).

(** *** The fill arm, at both tails known empty *)
Hypothesis HAfS : RuleSound tm true true Afill.
Hypothesis HAfL : lr_lhs Afill = cls_conf F (run_side F (fm_b F - 1) 1 0 0).
Hypothesis HAfR : lr_rhs Afill
  = cls_conf F (run_side F (f_mid (fam_fill F 0)) 1 (f_s (fam_fill F 0)) 0).
Hypothesis HAfC : 0 < lr_cb Afill.

(** *** Liveness: every state is reached from the fill's anchor *)
Hypothesis Hvisit : forall q,
  srun_st tm true true (vis q) (lr_lhs Afill) = Some q.

Let s0 : CtrSt := (ds0, 0, 0).

Definition CfB (n : nat) : cconf :=
  match fam_iter F s0 n with
  | Some s => fam_cfg F s
  | None => CTape.c0
  end.

Lemma inv0 : Inv F s0.
Proof. simpl. repeat split; assumption. Qed.

(** The cells of a top-of-width string, as the fill arm's left-hand side. *)
Lemma cells_top : forall k, 0 < k ->
  fam_cells F (repeat (fm_b F - 1) k) 0
    = sden [] (k - 1) (run_side F (fm_b F - 1) 1 0 0).
Proof.
  intros k Hk. rewrite <- (fam_cells_run F (fm_b F - 1) 1 (k - 1) 0 0).
  f_equal. f_equal. lia.
Qed.

(** ...and of what the fill law puts there, as its right-hand side. *)
Lemma cells_filled : forall k, 0 < k ->
  fam_cells F (repeat (f_mid (fam_fill F 0)) (k + f_s (fam_fill F 0))) 0
    = sden [] (k - 1)
        (run_side F (f_mid (fam_fill F 0)) 1 (f_s (fam_fill F 0)) 0).
Proof.
  intros k Hk.
  rewrite <- (fam_cells_run F (f_mid (fam_fill F 0)) 1 (k - 1)
                (f_s (fam_fill F 0)) 0).
  f_equal. f_equal. lia.
Qed.

(** The lap, by the case split: a state is at the top of its width, where
    the fill arm applies, or it is not, where an interior arm does. *)
Lemma board_lap : forall s, Inv F s ->
  exists s' m, fam_succ F s = Some s' /\ 0 < m /\
               csteps tm m (fam_cfg F s) = Some (fam_cfg F s').
Proof.
  intros [[ds p] ph] Hi. destruct Hi as (Hbnd & Hlen & ->).
  destruct (digs_decomp (fm_b F - 1) ds) as [Htop | (n & d & rest & -> & Hd)].
  - (* the top of a width: the FILL arm *)
    assert (Hist : fam_is_top F ds = true).
    { rewrite Htop at 1. apply pos1_is_top; assumption. }
    exists (repeat (f_mid (fam_fill F 0)) (length ds + f_s (fam_fill F 0)), p, 0).
    exists (lr_ca Afill * (length ds - 1) + lr_cb Afill).
    split; [|split].
    + unfold fam_succ. rewrite (fill_at_top F Hfpre Hfsuf ds Hist), Hist, Hfto.
      reflexivity.
    + nia.
    + apply (lap_from_arm tm F Afill true true [] (length ds - 1)
               (run_side F (fm_b F - 1) 1 0 0)
               (run_side F (f_mid (fam_fill F 0)) 1 (f_s (fam_fill F 0)) 0));
        try assumption.
      * intros _; apply tailL_nil.
      * intros _; apply tailR_nil.
      * rewrite Htop at 1. apply cells_top. exact Hlen.
      * apply cells_filled. exact Hlen.
  - (* not the top: an INTERIOR arm, for the digit that is not the top one *)
    apply Forall_app in Hbnd as [Hrun Hrest'].
    inversion Hrest' as [|? ? Hdb Hrest]; subst.
    assert (Hdlt : d < fm_b F - 1) by lia.
    exists (repeat 0 n ++ S d :: rest, p, 0).
    exists (lr_ca (Aint d) * n + lr_cb (Aint d)).
    split; [|split].
    + assert (Hns : fam_next F (repeat (fm_b F - 1) n ++ d :: rest) 0
                    = Some (repeat 0 n ++ S d :: rest))
        by exact (pos1_class_succ F d Hb Hcode Hstep Hdlt n rest 0 Hrest I).
      unfold fam_succ. rewrite Hns.
      destruct (fam_is_top F (repeat (fm_b F - 1) n ++ d :: rest));
        [rewrite Hfto|]; reflexivity.
    + pose proof (HAiC d Hdlt). nia.
    + apply (lap_from_arm tm F (Aint d) (negb (fm_left F)) (fm_left F)
               (cls_tail F rest 0) n
               (cls_side F (fm_b F - 1) [d]) (cls_side F 0 [S d]));
        try (apply HAiS || apply HAiL || apply HAiR); try assumption.
      * intros He. unfold tailL. destruct (fm_left F); [discriminate|reflexivity].
      * intros He. unfold tailR. rewrite He. reflexivity.
      * apply (fam_cells_class F (fm_b F - 1) n [d] rest 0).
      * apply (fam_cells_class F 0 n [S d] rest 0).
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
    assert (Hden : CfB n = cden [] [] (length ds' - 1) (lr_lhs Afill)).
    { unfold CfB. rewrite Hit, HAfL.
      rewrite <- (cden_cls_conf F (run_side F (fm_b F - 1) 1 0 0) []
                    (length ds' - 1) ds' p' 0).
      - unfold tailL, tailR; destruct (fm_left F); reflexivity.
      - rewrite Hsh at 1. apply cells_top. exact Hlen'. }
    destruct (vis_of_run tm (fun _ => CfB n) true true (vis q) (lr_lhs Afill)
                1%positive (length ds' - 1) [] [] q (Hvisit q)
                (fun _ => eq_refl) (fun _ => eq_refl) Hden) as (k & c & Hc & Hq).
    exists k, c. split; [exact HN | split; [exact Hc | exact Hq]].
Qed.

End Board.
