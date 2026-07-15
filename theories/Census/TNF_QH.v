(** * Census/TNF_QH: TNF enumeration refounded on quasihalting.

    The port of Coq-BB5's [TNF.v] + [TM.v] tree machinery
    (NEXT_SESSION.md "Scope B", SCOPING.md section 7) with the halting
    contract replaced by a quasihalting one.

    The node predicate replacing BB5's [HaltTimeUpperBound]:

      [NodeDecided B D tm  :=  forall tm' extending tm,
                                 QHBound B tm' \/ Deferred D tm']

    where [QHBound B tm] bounds every quiet state's last visit -- the
    exact quasihalting analogue of a halting-time bound: it is vacuous
    for never-quasihalting machines, equals the score bound for
    quasihalting ones, and is invariant under state renaming and
    mirroring, which is what lets the TNF tree's canonical-form
    expansion (unused-state pointer, first-move-right) cover the whole
    (4,2) space.  [Deferred D] is the swap/mirror/completion orbit of
    an explicit machine list -- the census analogue of BB5's
    hardcoded + sporadic tail (here: the BBB(4) holdout list plus the
    measured census-hard residue).

    Differences from the halting census, both forced by quasihalting
    (SCOPING section 7):

    - NO [cnt = 1] pruning: a machine whose last undefined transition
      gets filled can still quasihalt or not, so full machines are
      enumerated and decided like any others ([node_expand] always
      expands).  BB5's [CountHaltTrans_0_NonHalt] shortcut is sound
      only for halting.

    - The "don't-care completion" lemma ([qhbound_le], [nonhalt_le]):
      a leaf machine never reaches its undefined transitions, so every
      completion has the SAME trace, hence the same quasihalting
      status and scores.  This is the quasihalting analogue of BB5's
      [LE_NonHalts] and discharges the leaf side of the tree. *)

From Coq Require Import Arith Lia Bool List.
From Coq Require Import FunctionalExtensionality.
From BBB4 Require Import BBB4_Statement Mirror.
Import ListNotations.

Set Default Goal Selector "!".

(** ** Boolean helpers *)

Lemma st_eqb_refl : forall q, st_eqb q q = true.
Proof. intro q. apply st_eqb_spec. reflexivity. Qed.

Lemma st_eqb_neq : forall a b, st_eqb a b = false -> a <> b.
Proof.
  intros a b E H. subst. rewrite st_eqb_refl in E. discriminate.
Qed.

Lemma sym_eqb_refl : forall s, sym_eqb s s = true.
Proof. intro s. apply sym_eqb_spec. reflexivity. Qed.

Lemma sym_eqb_neq : forall a b, sym_eqb a b = false -> a <> b.
Proof.
  intros a b E H. subst. rewrite sym_eqb_refl in E. discriminate.
Qed.

Lemma st_eqb_false : forall a b, a <> b -> st_eqb a b = false.
Proof.
  intros a b H.
  destruct (st_eqb a b) eqn:E.
  - apply st_eqb_spec in E. congruence.
  - reflexivity.
Qed.

(** ** The score bound

    [QHBound B tm]: every state that is eventually quiet made its last
    visit before configuration index [B] (so its BBB score, last visit
    + 1 in harness terms, is at most [B]).  Never-quasihalting
    machines satisfy it vacuously; halting machines satisfy it with
    [B] = their halting step; quasihalting machines satisfy it iff
    their score is at most [B]. *)

Definition QHBound (B : nat) (tm : TM) : Prop :=
  forall q s, QuietAfter tm q s -> S s <= B.

Lemma qhbound_mono : forall B B' tm,
  B <= B' -> QHBound B tm -> QHBound B' tm.
Proof.
  intros B B' tm Hb H q s Hq.
  specialize (H q s Hq). lia.
Qed.

Lemma neverqh_qhbound : forall B tm,
  NeverQuasiHaltsSt tm -> QHBound B tm.
Proof.
  intros B tm H q s [Hvis Hq].
  destruct (H q (ex_intro _ s Hvis) (S s)) as (n & Hn & Hv).
  exfalso. apply (Hq n); [lia | exact Hv].
Qed.

(** ** Machine extension (the don't-care order)

    [TM_le tm tm']: [tm'] agrees with [tm] wherever [tm] is defined.
    BB5's [LE]. *)

Definition TM_le (tm tm' : TM) : Prop :=
  forall q s, tm q s = None \/ tm' q s = tm q s.

Lemma TM_le_refl : forall tm, TM_le tm tm.
Proof. intros tm q s. right. reflexivity. Qed.

Lemma TM_le_TM0 : forall tm0 tm, (forall q s, tm0 q s = None) -> TM_le tm0 tm.
Proof. intros tm0 tm H q s. left. apply H. Qed.

Lemma TM_le_step : forall tm tm' c c',
  TM_le tm tm' -> step tm c = Some c' -> step tm' c = Some c'.
Proof.
  intros tm tm' [q tp] c' Hle H. simpl in *.
  destruct (Hle q (t_head tp)) as [E | E].
  - rewrite E in H. discriminate.
  - rewrite E. exact H.
Qed.

Lemma TM_le_stepn : forall tm tm' n c c',
  TM_le tm tm' -> stepn tm n c = Some c' -> stepn tm' n c = Some c'.
Proof.
  intros tm tm'.
  induction n; intros c c' Hle H; simpl in *.
  - exact H.
  - destruct (step tm c) as [c1|] eqn:E; [|discriminate].
    rewrite (TM_le_step tm tm' c c1 Hle E).
    apply IHn; assumption.
Qed.

(** The don't-care completion argument: a non-halting machine's
    completions have the same trace, hence the same visits, quiet
    states and scores.  (The quasihalting analogue of BB5's
    [CountHaltTrans_0_NonHalt] / [LE_NonHalts] pair.) *)

Lemma nonhalt_le : forall tm tm',
  NonHalt tm -> TM_le tm tm' -> NonHalt tm'.
Proof.
  intros tm tm' Hnh Hle n E.
  destruct (stepn tm n InitES) as [c|] eqn:Ec.
  - rewrite (TM_le_stepn tm tm' n InitES c Hle Ec) in E. discriminate.
  - exact (Hnh n Ec).
Qed.

Lemma visits_le : forall tm tm' q n,
  NonHalt tm -> TM_le tm tm' ->
  (VisitsAt tm' q n <-> VisitsAt tm q n).
Proof.
  intros tm tm' q n Hnh Hle.
  destruct (stepn tm n InitES) as [c|] eqn:Ec;
    [| exfalso; exact (Hnh n Ec)].
  pose proof (TM_le_stepn tm tm' n InitES c Hle Ec) as Ec'.
  split; intros (c0 & H0 & Hq).
  - rewrite Ec' in H0. injection H0 as <-.
    exists c. split; [exact Ec | exact Hq].
  - rewrite Ec in H0. injection H0 as <-.
    exists c. split; [exact Ec' | exact Hq].
Qed.

Lemma quiet_le : forall tm tm' q s,
  NonHalt tm -> TM_le tm tm' ->
  (QuietAfter tm' q s <-> QuietAfter tm q s).
Proof.
  intros tm tm' q s Hnh Hle.
  unfold QuietAfter.
  split; intros [Hvis Hq]; split.
  - apply (visits_le tm tm' q s Hnh Hle); exact Hvis.
  - intros n Hn Hv. apply (Hq n Hn), (visits_le tm tm' q n Hnh Hle), Hv.
  - apply (visits_le tm tm' q s Hnh Hle); exact Hvis.
  - intros n Hn Hv. apply (Hq n Hn), (visits_le tm tm' q n Hnh Hle), Hv.
Qed.

Lemma qhbound_le : forall B tm tm',
  NonHalt tm -> QHBound B tm -> TM_le tm tm' -> QHBound B tm'.
Proof.
  intros B tm tm' Hnh H Hle q s Hq.
  apply (H q s), (quiet_le tm tm' q s Hnh Hle), Hq.
Qed.

(** ** The halting side: a machine that reaches an undefined
    transition at index [n] has every state quiet by [n]. *)

Lemma halt_le_qhbound : forall B tm tm0 n s tp,
  TM_le tm tm0 ->
  stepn tm n InitES = Some (s, tp) ->
  tm0 s (t_head tp) = None ->
  S n <= B ->
  QHBound B tm0.
Proof.
  intros B tm tm0 n s tp Hle Hn Hhalt HB q s0 [Hvis _].
  destruct Hvis as (c & Hc & _).
  (* all configurations of tm0 die after index n *)
  assert (Hno : forall k, 1 <= k -> stepn tm0 (n + k) InitES = None).
  { intros k Hk.
    rewrite stepn_add.
    rewrite (TM_le_stepn tm tm0 n InitES (s, tp) Hle Hn).
    destruct k; [lia|].
    simpl. rewrite Hhalt. reflexivity. }
  destruct (le_lt_dec s0 n) as [Hle0 | Hgt]; [lia|].
  exfalso.
  specialize (Hno (s0 - n) ltac:(lia)).
  replace (n + (s0 - n)) with s0 in Hno by lia.
  rewrite Hno in Hc. discriminate.
Qed.

(** ** State swaps (the unused-state renaming argument)

    A transposition of two non-start states; traces are isomorphic, so
    [QHBound] and [NonHalt] transfer.  BB5's [TM_swap] section, redone
    in the head-relative model (the tape is untouched -- only the state
    component and transition targets swap). *)

Definition St_swap (u v q : St) : St :=
  if st_eqb q u then v else if st_eqb q v then u else q.

Definition Trans_swap (u v : St) (tr : Trans) : Trans :=
  mkTrans (t_write tr) (t_dir tr) (St_swap u v (t_next tr)).

Definition TM_swap (u v : St) (tm : TM) : TM :=
  fun q s => option_map (Trans_swap u v) (tm (St_swap u v q) s).

Definition es_swap (u v : St) (c : ExecState) : ExecState :=
  (St_swap u v (fst c), snd c).

Lemma St_swap_swap : forall u v q, St_swap u v (St_swap u v q) = q.
Proof.
  intros u v q. unfold St_swap.
  destruct (st_eqb q u) eqn:Equ.
  - apply st_eqb_spec in Equ; subst.
    destruct (st_eqb v u) eqn:E1.
    + apply st_eqb_spec in E1; congruence.
    + rewrite st_eqb_refl. reflexivity.
  - destruct (st_eqb q v) eqn:Eqv.
    + apply st_eqb_spec in Eqv; subst.
      rewrite st_eqb_refl. reflexivity.
    + rewrite Equ, Eqv. reflexivity.
Qed.

Lemma St_swap_A : forall u v,
  u <> StA -> v <> StA -> St_swap u v StA = StA.
Proof.
  intros u v HuA HvA. unfold St_swap.
  destruct (st_eqb StA u) eqn:E1.
  - apply st_eqb_spec in E1; congruence.
  - destruct (st_eqb StA v) eqn:E2.
    + apply st_eqb_spec in E2; congruence.
    + reflexivity.
Qed.

Lemma es_swap_swap : forall u v c, es_swap u v (es_swap u v c) = c.
Proof.
  intros u v [q tp]. unfold es_swap; simpl.
  rewrite St_swap_swap. reflexivity.
Qed.

Lemma es_swap_init : forall u v,
  u <> StA -> v <> StA -> es_swap u v InitES = InitES.
Proof.
  intros u v HuA HvA.
  unfold es_swap, InitES; simpl. rewrite St_swap_A by assumption. reflexivity.
Qed.

Lemma step_swap : forall u v tm c,
  step (TM_swap u v tm) c = option_map (es_swap u v) (step tm (es_swap u v c)).
Proof.
  intros u v tm [q tp]. simpl.
  unfold TM_swap.
  destruct (tm (St_swap u v q) (t_head tp)) as [[w d nx]|] eqn:E; simpl.
  - reflexivity.
  - reflexivity.
Qed.

Lemma stepn_swap : forall u v tm n c,
  stepn (TM_swap u v tm) n c = option_map (es_swap u v) (stepn tm n (es_swap u v c)).
Proof.
  intros u v tm.
  induction n; intros c.
  - simpl. rewrite es_swap_swap. reflexivity.
  - cbn [stepn].
    rewrite step_swap.
    destruct (step tm (es_swap u v c)) as [c1|] eqn:E; cbn [option_map].
    + rewrite IHn, es_swap_swap. reflexivity.
    + reflexivity.
Qed.

Lemma visits_swap : forall u v tm q n,
  u <> StA -> v <> StA ->
  (VisitsAt (TM_swap u v tm) q n <-> VisitsAt tm (St_swap u v q) n).
Proof.
  intros u v tm q n HuA HvA. unfold VisitsAt.
  rewrite stepn_swap, es_swap_init by assumption.
  destruct (stepn tm n InitES) as [c|]; simpl.
  - split.
    + intros (c0 & H0 & Hq). injection H0 as <-.
      exists c. split; [reflexivity|].
      unfold es_swap in Hq; simpl in Hq.
      rewrite <- Hq, St_swap_swap. reflexivity.
    + intros (c0 & H0 & Hq). injection H0 as <-.
      eexists. split; [reflexivity|].
      unfold es_swap; simpl. rewrite Hq, St_swap_swap. reflexivity.
  - split; intros (c0 & H0 & _); discriminate.
Qed.

Lemma quiet_swap : forall u v tm q s,
  u <> StA -> v <> StA ->
  (QuietAfter (TM_swap u v tm) q s <-> QuietAfter tm (St_swap u v q) s).
Proof.
  intros u v tm q s HuA HvA. unfold QuietAfter.
  split; intros [Hvis Hq]; split.
  - apply (visits_swap u v tm q s HuA HvA); exact Hvis.
  - intros n Hn Hv. apply (Hq n Hn), (visits_swap u v tm q n HuA HvA), Hv.
  - apply (visits_swap u v tm q s HuA HvA); exact Hvis.
  - intros n Hn Hv. apply (Hq n Hn), (visits_swap u v tm q n HuA HvA), Hv.
Qed.

Lemma qhbound_swap : forall u v B tm,
  u <> StA -> v <> StA ->
  QHBound B tm -> QHBound B (TM_swap u v tm).
Proof.
  intros u v B tm HuA HvA H q s Hq.
  apply (H (St_swap u v q) s), (quiet_swap u v tm q s HuA HvA), Hq.
Qed.

Lemma nonhalt_swap : forall u v tm,
  u <> StA -> v <> StA ->
  NonHalt tm -> NonHalt (TM_swap u v tm).
Proof.
  intros u v tm HuA HvA H n E.
  rewrite stepn_swap, es_swap_init in E by assumption.
  destruct (stepn tm n InitES) as [c|] eqn:Ec; simpl in E.
  - discriminate.
  - exact (H n Ec).
Qed.

Lemma TM_le_swap : forall u v tm tm',
  TM_le tm tm' -> TM_le (TM_swap u v tm) (TM_swap u v tm').
Proof.
  intros u v tm tm' Hle q s.
  unfold TM_swap.
  destruct (Hle (St_swap u v q) s) as [E | E].
  - left. rewrite E. reflexivity.
  - right. rewrite E. reflexivity.
Qed.

Lemma Trans_swap_swap : forall u v tr, Trans_swap u v (Trans_swap u v tr) = tr.
Proof.
  intros u v [w d nx]. unfold Trans_swap; simpl.
  rewrite St_swap_swap. reflexivity.
Qed.

Lemma TM_swap_swap : forall u v tm, TM_swap u v (TM_swap u v tm) = tm.
Proof.
  intros u v tm.
  apply functional_extensionality; intro q.
  apply functional_extensionality; intro s.
  unfold TM_swap.
  rewrite St_swap_swap.
  destruct (tm q s) as [tr|]; simpl.
  - rewrite Trans_swap_swap. reflexivity.
  - reflexivity.
Qed.

(** ** Mirror transfer (uses theories/Mirror.v) *)

Lemma quiet_mirror : forall tm q s,
  QuietAfter (mirror_tm tm) q s <-> QuietAfter tm q s.
Proof.
  intros tm q s. unfold QuietAfter.
  split; intros [Hvis Hq]; split.
  - apply mirror_visits; exact Hvis.
  - intros n Hn Hv. apply (Hq n Hn), mirror_visits, Hv.
  - apply mirror_visits; exact Hvis.
  - intros n Hn Hv. apply (Hq n Hn), mirror_visits, Hv.
Qed.

Lemma qhbound_mirror : forall B tm,
  QHBound B (mirror_tm tm) -> QHBound B tm.
Proof.
  intros B tm H q s Hq.
  apply (H q s), quiet_mirror, Hq.
Qed.

Lemma TM_le_mirror : forall tm tm',
  TM_le tm tm' -> TM_le (mirror_tm tm) (mirror_tm tm').
Proof.
  intros tm tm' Hle q s.
  unfold mirror_tm.
  destruct (Hle q s) as [E | E].
  - left. rewrite E. reflexivity.
  - right. rewrite E. reflexivity.
Qed.

(** ** The deferred orbit

    The census defers an explicit machine list [D] (holdouts + the
    measured hard residue).  The orbit closes [D] under completion,
    non-start state swaps and mirroring -- exactly the transformations
    the TNF tree quotients by.  Any semantic property invariant under
    those (quasihalting status, scores) proven later for all of [D]
    lifts to the orbit. *)

Inductive Deferred (D : list TM) : TM -> Prop :=
| Deferred_base : forall h tm, In h D -> TM_le h tm -> Deferred D tm
| Deferred_swap : forall u v tm,
    u <> v -> u <> StA -> v <> StA ->
    Deferred D (TM_swap u v tm) -> Deferred D tm
| Deferred_mirror : forall tm, Deferred D (mirror_tm tm) -> Deferred D tm.

(** ** The census predicate *)

Section Census.

Variable B : nat.          (** the global score bound *)
Variable D : list TM.      (** the deferred list *)

Definition Decided (tm : TM) : Prop := QHBound B tm \/ Deferred D tm.

(** the node predicate: all completions decided *)
Definition NodeDecided (tm : TM) : Prop :=
  forall tm', TM_le tm tm' -> Decided tm'.

(** leaf discharge lemmas *)

Lemma node_decided_leaf : forall tm,
  NonHalt tm -> QHBound B tm -> NodeDecided tm.
Proof.
  intros tm Hnh Hb tm' Hle.
  left. apply (qhbound_le B tm tm' Hnh Hb Hle).
Qed.

Lemma node_decided_neverqh : forall tm,
  NeverQuasiHaltsSt tm -> NodeDecided tm.
Proof.
  intros tm H.
  apply node_decided_leaf.
  - apply never_qh_nonhalt; exact H.
  - apply neverqh_qhbound; exact H.
Qed.

Lemma node_decided_deferred : forall tm,
  In tm D -> NodeDecided tm.
Proof.
  intros tm H tm' Hle.
  right. exact (Deferred_base D tm tm' H Hle).
Qed.

(** transfer of [Decided] along swap/mirror, wrapped for use at
    expansion and at the root *)

Lemma decided_unswap : forall u v tm,
  u <> v -> u <> StA -> v <> StA ->
  Decided (TM_swap u v tm) -> Decided tm.
Proof.
  intros u v tm Huv HuA HvA [H | H].
  - left.
    pose proof (qhbound_swap u v B (TM_swap u v tm) HuA HvA H) as H'.
    rewrite (TM_swap_swap u v) in H'. exact H'.
  - right. exact (Deferred_swap D u v tm Huv HuA HvA H).
Qed.

Lemma decided_unmirror : forall tm,
  Decided (mirror_tm tm) -> Decided tm.
Proof.
  intros tm [H | H].
  - left. apply qhbound_mirror; exact H.
  - right. exact (Deferred_mirror D tm H).
Qed.

(** ** Machine updates *)

Definition TM_upd (tm : TM) (q : St) (s : Sym) (otr : option Trans) : TM :=
  fun q0 s0 =>
    if st_eqb q0 q && sym_eqb s0 s then otr else tm q0 s0.

Lemma TM_upd_at : forall tm q s otr, TM_upd tm q s otr q s = otr.
Proof.
  intros. unfold TM_upd. rewrite st_eqb_refl, sym_eqb_refl. reflexivity.
Qed.

Lemma TM_upd_neq : forall tm q s otr q0 s0,
  (q0, s0) <> (q, s) -> TM_upd tm q s otr q0 s0 = tm q0 s0.
Proof.
  intros tm q s otr q0 s0 Hne. unfold TM_upd.
  destruct (st_eqb q0 q) eqn:Eq; simpl.
  - apply st_eqb_spec in Eq; subst.
    destruct (sym_eqb s0 s) eqn:Es.
    + apply sym_eqb_spec in Es; subst. congruence.
    + reflexivity.
  - reflexivity.
Qed.

Lemma TM_le_upd : forall tm tm' q s tr,
  TM_le tm tm' ->
  tm' q s = Some tr ->
  TM_le (TM_upd tm q s (Some tr)) tm'.
Proof.
  intros tm tm' q s tr Hle E q0 s0.
  destruct (st_eqb q0 q) eqn:Eq.
  - apply st_eqb_spec in Eq; subst.
    destruct (sym_eqb s0 s) eqn:Es.
    + apply sym_eqb_spec in Es; subst.
      right. rewrite TM_upd_at. exact E.
    + rewrite TM_upd_neq by (intro H; injection H as H; apply (sym_eqb_neq _ _ Es); auto).
      apply Hle.
  - rewrite TM_upd_neq by (intro H; injection H as H _; apply (st_eqb_neq _ _ Eq); auto).
    apply Hle.
Qed.

(** term-size control for computation (BB5's [TM_simplify]) *)

Definition TM_simplify (tm : TM) : TM :=
  let aA0 := tm StA S0 in let aA1 := tm StA S1 in
  let aB0 := tm StB S0 in let aB1 := tm StB S1 in
  let aC0 := tm StC S0 in let aC1 := tm StC S1 in
  let aD0 := tm StD S0 in let aD1 := tm StD S1 in
  fun q s =>
    match q, s with
    | StA, S0 => aA0 | StA, S1 => aA1
    | StB, S0 => aB0 | StB, S1 => aB1
    | StC, S0 => aC0 | StC, S1 => aC1
    | StD, S0 => aD0 | StD, S1 => aD1
    end.

Lemma TM_simplify_spec : forall tm, TM_simplify tm = tm.
Proof.
  intro tm.
  apply functional_extensionality; intro q.
  apply functional_extensionality; intro s.
  destruct q, s; reflexivity.
Qed.

Definition TM_upd' (tm : TM) (q : St) (s : Sym) (otr : option Trans) : TM :=
  TM_simplify (TM_upd tm q s otr).

Lemma TM_upd'_spec : forall tm q s otr,
  TM_upd' tm q s otr = TM_upd tm q s otr.
Proof. intros. apply TM_simplify_spec. Qed.

(** ** Unused states and the enumeration pointer *)

Definition UnusedState (tm : TM) (s0 : St) : Prop :=
  (forall q s tr, tm q s = Some tr -> t_next tr <> s0) /\
  (forall s, tm s0 s = None) /\
  s0 <> StA.

Definition St_to_nat (q : St) : nat :=
  match q with StA => 0 | StB => 1 | StC => 2 | StD => 3 end.

Lemma St_to_nat_inj : forall q1 q2, St_to_nat q1 = St_to_nat q2 -> q1 = q2.
Proof. intros q1 q2. destruct q1, q2; simpl; congruence || lia. Qed.

(** [Some p]: the unused states are exactly those at or above [p].
    [None]: no unused states. *)
Definition UnusedState_ptr (tm : TM) (p : option St) : Prop :=
  match p with
  | Some p0 => forall s0, UnusedState tm s0 <-> St_to_nat p0 <= St_to_nat s0
  | None => forall s0, ~ UnusedState tm s0
  end.

(** a state reached by the run is not unused *)
Lemma stepn_reached_used : forall tm n s tp,
  stepn tm n InitES = Some (s, tp) -> ~ UnusedState tm s.
Proof.
  intros tm n s tp Hn (Hin & Hout & HA).
  destruct n.
  - simpl in Hn. unfold InitES in Hn.
    injection Hn as Hn _. congruence.
  - replace (S n) with (n + 1) in Hn by lia.
    rewrite stepn_add in Hn.
    destruct (stepn tm n InitES) as [[q0 tp0]|] eqn:E0; [|discriminate].
    cbn [stepn] in Hn.
    destruct (step tm (q0, tp0)) as [c1|] eqn:E1; [|discriminate].
    injection Hn as ->.
    simpl in E1.
    destruct (tm q0 (t_head tp0)) as [tr|] eqn:E2; [|discriminate].
    injection E1 as E1 _.
    exact (Hin q0 (t_head tp0) tr E2 E1).
Qed.

Lemma UnusedState_upd : forall tm s i tr s0,
  tm s i = None ->
  ~ UnusedState tm s ->
  (UnusedState (TM_upd tm s i (Some tr)) s0 <->
   (UnusedState tm s0 /\ s0 <> t_next tr)).
Proof.
  intros tm s i tr s0 Hhole Hused.
  split.
  - intros (Hin & Hout & HA).
    assert (Hs0s : s0 <> s).
    { intro; subst s0.
      specialize (Hout i). rewrite TM_upd_at in Hout. discriminate. }
    repeat split.
    + intros q s1 tr1 E1.
      destruct (st_eqb q s) eqn:Eq.
      * apply st_eqb_spec in Eq; subst q.
        destruct (sym_eqb s1 i) eqn:Es.
        -- apply sym_eqb_spec in Es; subst s1. congruence.
        -- apply (Hin s s1 tr1).
           rewrite TM_upd_neq by (intro H; injection H as H; apply (sym_eqb_neq _ _ Es); auto).
           exact E1.
      * apply (Hin q s1 tr1).
        rewrite TM_upd_neq by (intro H; injection H as H _; apply (st_eqb_neq _ _ Eq); auto).
        exact E1.
    + intros s1.
      specialize (Hout s1).
      rewrite TM_upd_neq in Hout by (intro H; injection H as H _; congruence).
      exact Hout.
    + exact HA.
    + intro; subst s0.
      apply (Hin s i tr).
      * apply TM_upd_at.
      * reflexivity.
  - intros ((Hin & Hout & HA) & Hne).
    assert (Hs0s : s0 <> s).
    { intro; subst s0. apply Hused. repeat split; assumption. }
    repeat split.
    + intros q s1 tr1 E1.
      destruct (st_eqb q s) eqn:Eq.
      * apply st_eqb_spec in Eq; subst q.
        destruct (sym_eqb s1 i) eqn:Es.
        -- apply sym_eqb_spec in Es; subst s1.
           rewrite TM_upd_at in E1. injection E1 as <-. auto.
        -- rewrite TM_upd_neq in E1 by (intro H; injection H as H; apply (sym_eqb_neq _ _ Es); auto).
           exact (Hin s s1 tr1 E1).
      * rewrite TM_upd_neq in E1 by (intro H; injection H as H _; apply (st_eqb_neq _ _ Eq); auto).
        exact (Hin q s1 tr1 E1).
    + intros s1.
      rewrite TM_upd_neq by (intro H; injection H as H _; congruence).
      apply Hout.
    + exact HA.
Qed.

Definition St_suc (q : St) : option St :=
  match q with
  | StA => Some StB | StB => Some StC | StC => Some StD | StD => None
  end.

Definition ptr_after (p : option St) (nx : St) : option St :=
  match p with
  | Some p0 => if st_eqb nx p0 then St_suc p0 else p
  | None => None
  end.

Definition trans_ok (p : option St) (tr : Trans) : bool :=
  match p with
  | Some p0 => Nat.leb (St_to_nat (t_next tr)) (St_to_nat p0)
  | None => true
  end.

Lemma UnusedState_ptr_upd : forall tm s i tr p,
  tm s i = None ->
  ~ UnusedState tm s ->
  UnusedState_ptr tm p ->
  trans_ok p tr = true ->
  UnusedState_ptr (TM_upd tm s i (Some tr)) (ptr_after p (t_next tr)).
Proof.
  intros tm s i tr p Hhole Hused Hp Hok.
  destruct p as [p0|]; simpl in *.
  - apply Nat.leb_le in Hok.
    destruct (st_eqb (t_next tr) p0) eqn:Enx.
    + apply st_eqb_spec in Enx.
      (* filling the pointer state: unused set moves up *)
      destruct (St_suc p0) as [p1|] eqn:Esuc; simpl.
      * intros s0.
        rewrite (UnusedState_upd tm s i tr s0 Hhole Hused).
        rewrite Hp.
        assert (Hsn : St_to_nat p1 = S (St_to_nat p0))
          by (destruct p0; simpl in Esuc; try discriminate;
              injection Esuc as <-; reflexivity).
        rewrite Hsn.
        split.
        -- intros [Hge Hne].
           assert (St_to_nat p0 <> St_to_nat s0)
             by (intro E; apply Hne; rewrite Enx;
                 apply St_to_nat_inj; lia).
           lia.
        -- intros Hge. split; [lia|].
           intro E; subst s0. rewrite Enx in Hge. lia.
      * intros s0.
        rewrite (UnusedState_upd tm s i tr s0 Hhole Hused).
        rewrite Hp.
        intros [Hge Hne].
        assert (St_to_nat p0 = 3)
          by (destruct p0; simpl in Esuc; try discriminate; reflexivity).
        assert (St_to_nat s0 <= 3) by (destruct s0; simpl; lia).
        apply Hne. rewrite Enx. apply St_to_nat_inj. lia.
    + (* the filled target is strictly below the pointer *)
      pose proof (st_eqb_neq _ _ Enx) as Hne.
      assert (Hlt : St_to_nat (t_next tr) < St_to_nat p0).
      { assert (St_to_nat (t_next tr) <> St_to_nat p0)
          by (intro E; apply Hne, St_to_nat_inj, E).
        lia. }
      intros s0.
      rewrite (UnusedState_upd tm s i tr s0 Hhole Hused).
      rewrite Hp.
      split.
      -- intros [Hge _]. exact Hge.
      -- intros Hge. split; [exact Hge|].
         intro E; subst s0. lia.
  - intros s0 H.
    rewrite (UnusedState_upd tm s i tr s0 Hhole Hused) in H.
    destruct H as [H _]. exact (Hp s0 H).
Qed.

(** ** The swap argument at expansion time

    Filling the hole with a transition to a beyond-pointer unused
    state is covered, up to a swap of two unused states, by the child
    that fills it with the pointer state (BB5's
    [HaltTimeUpperBound_LE_HaltsAtES_UnusedState]). *)

Lemma Trans_swap_id : forall u v tr,
  t_next tr <> u -> t_next tr <> v ->
  Trans_swap u v tr = tr.
Proof.
  intros u v [w d nx] Hu Hv. unfold Trans_swap; simpl in *.
  unfold St_swap.
  destruct (st_eqb nx u) eqn:E1.
  - apply st_eqb_spec in E1; congruence.
  - destruct (st_eqb nx v) eqn:E2.
    + apply st_eqb_spec in E2; congruence.
    + reflexivity.
Qed.

Lemma TM_swap_upd_unused : forall tm s i w d u v,
  tm s i = None ->
  ~ UnusedState tm s ->
  UnusedState tm u ->
  UnusedState tm v ->
  u <> v ->
  TM_swap u v (TM_upd tm s i (Some (mkTrans w d u))) =
  TM_upd tm s i (Some (mkTrans w d v)).
Proof.
  intros tm s i w d u v Hhole Hused (Huin & Huout & HuA) (Hvin & Hvout & HvA) Huv.
  assert (Hus : u <> s) by (intro; subst u; apply Hused; repeat split; assumption).
  assert (Hvs : v <> s) by (intro; subst v; apply Hused; repeat split; assumption).
  apply functional_extensionality; intro q.
  apply functional_extensionality; intro s0.
  unfold TM_swap.
  (* case on q relative to u, v *)
  destruct (st_eqb q u) eqn:Equ.
  - apply st_eqb_spec in Equ; subst q.
    replace (St_swap u v u) with v
      by (unfold St_swap; rewrite st_eqb_refl; reflexivity).
    (* lhs looks up v; v is unused and <> s so both sides are None *)
    rewrite TM_upd_neq by (intro H; injection H as H _; congruence).
    rewrite (Hvout s0); simpl.
    rewrite TM_upd_neq by (intro H; injection H as H _; congruence).
    rewrite (Huout s0). reflexivity.
  - destruct (st_eqb q v) eqn:Eqv.
    + apply st_eqb_spec in Eqv; subst q.
      replace (St_swap u v v) with u
        by (unfold St_swap; rewrite (st_eqb_false v u) by congruence;
            rewrite st_eqb_refl; reflexivity).
      rewrite TM_upd_neq by (intro H; injection H as H _; congruence).
      rewrite (Huout s0); simpl.
      rewrite TM_upd_neq by (intro H; injection H as H _; congruence).
      rewrite (Hvout s0). reflexivity.
    + replace (St_swap u v q) with q
        by (unfold St_swap; rewrite Equ, Eqv; reflexivity).
      pose proof (st_eqb_neq _ _ Equ) as Hqu.
      pose proof (st_eqb_neq _ _ Eqv) as Hqv.
      destruct (st_eqb q s) eqn:Eqs.
      * apply st_eqb_spec in Eqs; subst q.
        destruct (sym_eqb s0 i) eqn:Es0.
        -- apply sym_eqb_spec in Es0; subst s0.
           rewrite TM_upd_at, TM_upd_at; simpl.
           unfold Trans_swap; simpl.
           unfold St_swap. rewrite st_eqb_refl. reflexivity.
        -- rewrite TM_upd_neq by (intro H; injection H as H; apply (sym_eqb_neq _ _ Es0); auto).
           rewrite TM_upd_neq by (intro H; injection H as H; apply (sym_eqb_neq _ _ Es0); auto).
           destruct (tm s s0) as [tr0|] eqn:E0; simpl; [|reflexivity].
           rewrite Trans_swap_id;
             [reflexivity | exact (Huin s s0 tr0 E0) | exact (Hvin s s0 tr0 E0)].
      * pose proof (st_eqb_neq _ _ Eqs) as Hqs.
        rewrite TM_upd_neq by (intro H; injection H as H _; auto).
        rewrite TM_upd_neq by (intro H; injection H as H _; auto).
        destruct (tm q s0) as [tr0|] eqn:E0; simpl; [|reflexivity].
        rewrite Trans_swap_id;
          [reflexivity | exact (Huin q s0 tr0 E0) | exact (Hvin q s0 tr0 E0)].
Qed.

Lemma node_decided_swap_unused : forall tm s i w d u v,
  tm s i = None ->
  ~ UnusedState tm s ->
  UnusedState tm u ->
  UnusedState tm v ->
  u <> v ->
  NodeDecided (TM_upd tm s i (Some (mkTrans w d v))) ->
  NodeDecided (TM_upd tm s i (Some (mkTrans w d u))).
Proof.
  intros tm s i w d u v Hhole Hused Hu Hv Huv Hnd tm0 Hle.
  assert (HuA : u <> StA) by (destruct Hu as (_ & _ & HA); exact HA).
  assert (HvA : v <> StA) by (destruct Hv as (_ & _ & HA); exact HA).
  apply (decided_unswap u v tm0 Huv HuA HvA).
  apply Hnd.
  rewrite <- (TM_swap_upd_unused tm s i w d u v Hhole Hused Hu Hv Huv).
  apply TM_le_swap; assumption.
Qed.

(** ** TNF nodes and expansion *)

Record TNF_Node := mkNode {
  node_tm : TM;
  node_ptr : option St
}.

Definition Node_WF (x : TNF_Node) : Prop :=
  UnusedState_ptr (node_tm x) (node_ptr x).

Definition all_trans : list Trans :=
  [ mkTrans S0 DL StA; mkTrans S0 DL StB; mkTrans S0 DL StC; mkTrans S0 DL StD;
    mkTrans S0 DR StA; mkTrans S0 DR StB; mkTrans S0 DR StC; mkTrans S0 DR StD;
    mkTrans S1 DL StA; mkTrans S1 DL StB; mkTrans S1 DL StC; mkTrans S1 DL StD;
    mkTrans S1 DR StA; mkTrans S1 DR StB; mkTrans S1 DR StC; mkTrans S1 DR StD ].

Lemma all_trans_spec : forall tr, In tr all_trans.
Proof.
  intros [w d nx]. destruct w, d, nx; simpl; tauto.
Qed.

(** children of a node that reached the undefined transition (q, s).
    NOTE: no cnt=1 shortcut -- every reached hole expands (SCOPING
    section 7: full machines can still quasihalt). *)
Definition node_expand (x : TNF_Node) (q : St) (s : Sym) : list TNF_Node :=
  map (fun tr => mkNode (TM_upd' (node_tm x) q s (Some tr))
                        (ptr_after (node_ptr x) (t_next tr)))
      (filter (trans_ok (node_ptr x)) all_trans).

(** the heart: children cover the node *)
Lemma node_expand_spec : forall tm p n s tp,
  stepn tm n InitES = Some (s, tp) ->
  tm s (t_head tp) = None ->
  S n <= B ->
  UnusedState_ptr tm p ->
  (forall x', In x' (node_expand (mkNode tm p) s (t_head tp)) -> Node_WF x') /\
  ((forall x', In x' (node_expand (mkNode tm p) s (t_head tp)) ->
               NodeDecided (node_tm x')) ->
   NodeDecided tm).
Proof.
  intros tm p n s tp Hstep Hhole HB Hp.
  pose proof (stepn_reached_used tm n s tp Hstep) as Hused.
  split.
  - (* children well-formed *)
    intros x' Hin.
    unfold node_expand in Hin.
    apply in_map_iff in Hin.
    destruct Hin as (tr & <- & Hin).
    apply filter_In in Hin.
    destruct Hin as [_ Hok].
    unfold Node_WF; simpl.
    rewrite TM_upd'_spec.
    apply UnusedState_ptr_upd; assumption.
  - (* children decided -> node decided *)
    intros Hch tm0 Hle.
    destruct (tm0 s (t_head tp)) as [tr|] eqn:E0.
    + (* the completion continues: covered by a child, up to a swap *)
      pose proof (TM_le_upd tm tm0 s (t_head tp) tr Hle E0) as Hle'.
      destruct tr as [w d nx].
      destruct (trans_ok p (mkTrans w d nx)) eqn:Eok.
      * (* in-range target: literally a child *)
        refine (Hch (mkNode (TM_upd' tm s (t_head tp) (Some (mkTrans w d nx)))
                            (ptr_after p nx)) _ tm0 _).
        -- unfold node_expand.
           apply in_map_iff.
           exists (mkTrans w d nx).
           split; [reflexivity|].
           apply filter_In.
           split; [apply all_trans_spec | exact Eok].
        -- simpl. rewrite TM_upd'_spec. exact Hle'.
      * (* beyond-pointer target: swap with the pointer state *)
        destruct p as [p0|]; simpl in Eok; [|discriminate].
        apply Nat.leb_gt in Eok.
        simpl in Hp.
        assert (Hnx : UnusedState tm nx) by (apply Hp; simpl; lia).
        assert (Hp0 : UnusedState tm p0) by (apply Hp; simpl; lia).
        assert (Hnep : nx <> p0)
          by (intro E; subst; lia).
        assert (Hok' : trans_ok (Some p0) (mkTrans w d p0) = true)
          by (simpl; apply Nat.leb_refl).
        refine (node_decided_swap_unused tm s (t_head tp) w d nx p0
                  Hhole Hused Hnx Hp0 Hnep _ tm0 Hle').
        refine (fun tmx Hx => Hch (mkNode (TM_upd' tm s (t_head tp) (Some (mkTrans w d p0)))
                            (ptr_after (Some p0) p0)) _ tmx _).
        -- unfold node_expand.
           apply in_map_iff.
           exists (mkTrans w d p0).
           split; [reflexivity|].
           apply filter_In.
           split; [apply all_trans_spec | exact Hok'].
        -- simpl. rewrite TM_upd'_spec. exact Hx.
    + (* the completion also halts here: score bounded by S n *)
      left.
      exact (halt_le_qhbound B tm tm0 n s tp Hle Hstep E0 HB).
Qed.

(** ** The decider contract *)

Inductive QHResult :=
| R_Halt (s : St) (i : Sym)   (** reached an undefined transition: expand *)
| R_NeverQH                   (** proven never-quasihalting: leaf *)
| R_QH                        (** proven quasihalting, score under B: leaf *)
| R_Leaf                      (** proven non-halting with QHBound B: leaf *)
| R_Deferred                  (** in the deferred list: leaf *)
| R_Unknown.

Definition QHDecider := TM -> QHResult.

Definition QHDecider_WF (f : QHDecider) : Prop :=
  forall tm,
    match f tm with
    | R_Halt s i => exists n tp,
        stepn tm n InitES = Some (s, tp) /\ t_head tp = i /\
        tm s i = None /\ S n <= B
    | R_NeverQH => NeverQuasiHaltsSt tm
    | R_QH => NonHalt tm /\ QHBound B tm /\ QuasiHaltsSt tm
    | R_Leaf => NonHalt tm /\ QHBound B tm
    | R_Deferred => In tm D
    | R_Unknown => True
    end.

(** ** The search queue (verbatim BB5 port modulo the contract) *)

Definition SearchQueue : Type := (list TNF_Node) * (list TNF_Node).

Definition SearchQueue_WF (q : SearchQueue) (x0 : TNF_Node) : Prop :=
  let (q1, q2) := q in
  (forall x, In x (q1 ++ q2) -> Node_WF x) /\
  ((forall x, In x (q1 ++ q2) -> NodeDecided (node_tm x)) ->
   NodeDecided (node_tm x0)).

Definition SearchQueue_upd (q : SearchQueue) (f : QHDecider) : SearchQueue :=
  match q with
  | (h :: t, q2) =>
      match f (node_tm h) with
      | R_Halt s i => (node_expand h s i ++ t, q2)
      | R_NeverQH | R_QH | R_Leaf | R_Deferred => (t, q2)
      | R_Unknown => (t, h :: q2)
      end
  | _ => q
  end.

Lemma SearchQueue_upd_spec : forall q x0 f,
  SearchQueue_WF q x0 ->
  QHDecider_WF f ->
  SearchQueue_WF (SearchQueue_upd q f) x0.
Proof.
  intros [q1 q2] x0 f Hq Hf.
  destruct q1 as [| h t]; [exact Hq |].
  destruct Hq as [Hwf Hdec].
  simpl.
  specialize (Hf (node_tm h)).
  destruct (f (node_tm h)) eqn:Ef.
  - (* halt: expand *)
    destruct Hf as (n & tp & Hstep & Hhead & Hhole & HB).
    subst i.
    destruct h as [tm p].
    simpl in *.
    pose proof (node_expand_spec tm p n s tp Hstep Hhole HB
                  (Hwf (mkNode tm p) (or_introl eq_refl))) as [Hexp_wf Hexp_dec].
    split.
    + intros x Hin.
      rewrite in_app_iff in Hin. rewrite in_app_iff in Hin.
      destruct Hin as [[Hin | Hin] | Hin].
      * apply Hexp_wf; exact Hin.
      * apply Hwf. simpl. rewrite in_app_iff. tauto.
      * apply Hwf. simpl. rewrite in_app_iff. tauto.
    + intros H.
      apply Hdec.
      intros x Hin. simpl in Hin.
      destruct Hin as [<- | Hin].
      * simpl. apply Hexp_dec.
        intros x' Hin'. apply H.
        rewrite in_app_iff. rewrite in_app_iff. tauto.
      * apply H.
        rewrite in_app_iff. rewrite in_app_iff.
        rewrite in_app_iff in Hin. tauto.
  - (* never-QH leaf *)
    split.
    + intros x Hin. apply Hwf. simpl. rewrite in_app_iff.
      rewrite in_app_iff in Hin. tauto.
    + intros H. apply Hdec.
      intros x Hin. simpl in Hin.
      destruct Hin as [<- | Hin].
      * apply node_decided_neverqh; exact Hf.
      * apply H. rewrite in_app_iff. rewrite in_app_iff in Hin. tauto.
  - (* QH leaf *)
    destruct Hf as (Hnh & Hb & _).
    split.
    + intros x Hin. apply Hwf. simpl. rewrite in_app_iff.
      rewrite in_app_iff in Hin. tauto.
    + intros H. apply Hdec.
      intros x Hin. simpl in Hin.
      destruct Hin as [<- | Hin].
      * apply node_decided_leaf; assumption.
      * apply H. rewrite in_app_iff. rewrite in_app_iff in Hin. tauto.
  - (* undifferentiated leaf *)
    destruct Hf as (Hnh & Hb).
    split.
    + intros x Hin. apply Hwf. simpl. rewrite in_app_iff.
      rewrite in_app_iff in Hin. tauto.
    + intros H. apply Hdec.
      intros x Hin. simpl in Hin.
      destruct Hin as [<- | Hin].
      * apply node_decided_leaf; assumption.
      * apply H. rewrite in_app_iff. rewrite in_app_iff in Hin. tauto.
  - (* deferred leaf *)
    split.
    + intros x Hin. apply Hwf. simpl. rewrite in_app_iff.
      rewrite in_app_iff in Hin. tauto.
    + intros H. apply Hdec.
      intros x Hin. simpl in Hin.
      destruct Hin as [<- | Hin].
      * apply node_decided_deferred; exact Hf.
      * apply H. rewrite in_app_iff. rewrite in_app_iff in Hin. tauto.
  - (* unknown: push to the back queue *)
    split.
    + intros x Hin. apply Hwf.
      simpl. rewrite in_app_iff. simpl.
      rewrite in_app_iff in Hin. simpl in Hin. tauto.
    + intros H. apply Hdec.
      intros x Hin. apply H.
      simpl in Hin. rewrite in_app_iff in Hin.
      rewrite in_app_iff. simpl. tauto.
Qed.

Definition SearchQueue_init (x0 : TNF_Node) : SearchQueue := ([x0], []).

Lemma SearchQueue_init_spec : forall x0,
  Node_WF x0 -> SearchQueue_WF (SearchQueue_init x0) x0.
Proof.
  intros x0 H.
  split.
  - intros x [<- | []]. exact H.
  - intros Hd. apply Hd. left. reflexivity.
Qed.

Fixpoint SearchQueue_upds (q : SearchQueue) (f : QHDecider) (n : nat) : SearchQueue :=
  match fst q with
  | [] => q
  | _ =>
      match n with
      | O => SearchQueue_upd q f
      | S n0 => SearchQueue_upds (SearchQueue_upds q f n0) f n0
      end
  end.

Lemma SearchQueue_upds_spec : forall n q x0 f,
  SearchQueue_WF q x0 ->
  QHDecider_WF f ->
  SearchQueue_WF (SearchQueue_upds q f n) x0.
Proof.
  induction n; intros q x0 f Hq Hf; simpl.
  - destruct (fst q); [exact Hq | apply SearchQueue_upd_spec; assumption].
  - destruct (fst q); [exact Hq |].
    apply IHn; [apply IHn|]; assumption.
Qed.

(** the census closes when the queue empties *)
Lemma SearchQueue_empty_decided : forall x0,
  SearchQueue_WF ([], []) x0 -> NodeDecided (node_tm x0).
Proof.
  intros x0 [_ Hdec].
  apply Hdec.
  intros x [].
Qed.

(** mirror transfer for whole nodes (used at the root, where the
    first-move-left children are covered by their mirrors) *)
Lemma node_decided_mirror : forall tm,
  NodeDecided (mirror_tm tm) -> NodeDecided tm.
Proof.
  intros tm H tm0 Hle.
  apply decided_unmirror.
  apply H.
  apply TM_le_mirror; exact Hle.
Qed.

End Census.
