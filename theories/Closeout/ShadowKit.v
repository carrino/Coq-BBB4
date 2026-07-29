(** * ShadowKit: the re-root disjunct for the closeout's skipped set.

    The bbchallenge community's 0RB observation, made kernel-checked: a
    machine whose start transition writes the blank runs an all-blank
    prefix and then IS its re-root [TM_swap StA q*] started fresh
    (Census/Reroot.v).  When that re-root's behaviour is itself one of
    the still-undecided core machines, the 0RB machine is a SHADOW of an
    open problem, not a new one -- so the skipped set is stated as

      [skipped R tm :=  Deferred R tm
                    \/  exists qs t, stepn tm t InitES = Some (qs, snd InitES)
                                  /\ Deferred R (TM_swap StA qs tm)]

    and shadow rows leave [remaining_rows] entirely: the generated
    stages prove each one lands in the second disjunct.  A shadow
    resolves automatically the moment its core machine is boarded.

    Contents:
    - [tm_le_b] -- reflective [TM_le] between concrete machines;
    - [stepn_le] / [prefix_ok_le] -- a blank prefix certified on a row
      transfers to every completion;
    - monotonicity of [TM_swap]/[mirror_tm] under [TM_le];
    - the conjugation identities moving [TM_swap StA q] through the
      census orbit's swap/mirror constructors;
    - [skipped_unswap] / [skipped_unmirror] -- [skipped] descends the
      [Deferred] orbit;
    - [deferred_split_sh] -- the three-way split (proven / core /
      shadow) behind the generated Closeout.v.

    Axiom footprint: [functional_extensionality_dep] only (via
    [tm_ext]). *)

From Coq Require Import Arith Lia Bool List FunctionalExtensionality.
From BBB4 Require Import BBB4_Statement Mirror.
From BBB4.Census Require Import TNF_QH Deferred_Defs Reroot.
From BBB4.Closeout Require Import CloseoutKit.
Import ListNotations.

(** ** The skipped predicate *)

Definition skipped (R : list TM) (tm : TM) : Prop :=
  Deferred R tm
  \/ exists qs t, stepn tm t InitES = Some (qs, snd InitES)
                  /\ Deferred R (TM_swap StA qs tm).

Lemma skipped_of_deferred : forall R tm, Deferred R tm -> skipped R tm.
Proof. intros R tm H. left. exact H. Qed.

(** ** Reflective [TM_le] on concrete machines *)

Definition slot_le_b (a b : TM) (q : St) (s : Sym) : bool :=
  match a q s with
  | None => true
  | Some tr => match b q s with
               | Some tr' => trans_eqb tr tr'
               | None => false
               end
  end.

Lemma slot_le_b_sound : forall a b q s,
  slot_le_b a b q s = true -> a q s = None \/ b q s = a q s.
Proof.
  intros a b q s H. unfold slot_le_b in H.
  destruct (a q s) eqn:Ea; [right | left; reflexivity].
  destruct (b q s) eqn:Eb; [| discriminate].
  apply trans_eqb_eq in H. congruence.
Qed.

Definition tm_le_b (a b : TM) : bool :=
  slot_le_b a b StA S0 && slot_le_b a b StA S1
  && slot_le_b a b StB S0 && slot_le_b a b StB S1
  && slot_le_b a b StC S0 && slot_le_b a b StC S1
  && slot_le_b a b StD S0 && slot_le_b a b StD S1.

Lemma tm_le_b_sound : forall a b, tm_le_b a b = true -> TM_le a b.
Proof.
  intros a b H q s. unfold tm_le_b in H.
  repeat (apply andb_prop in H; destruct H as [H ?]).
  destruct q, s; apply slot_le_b_sound; assumption.
Qed.

Lemma TM_le_trans : forall a b c, TM_le a b -> TM_le b c -> TM_le a c.
Proof.
  intros a b c Hab Hbc q s.
  destruct (Hab q s) as [Ha | Hb]; [left; exact Ha |].
  destruct (Hbc q s) as [Hb' | Hc].
  - left. congruence.
  - right. congruence.
Qed.

(** ** A blank prefix transfers to completions *)

Lemma stepn_le : forall a b n c c',
  TM_le a b -> stepn a n c = Some c' -> stepn b n c = Some c'.
Proof.
  intros a b n. induction n as [|n IH]; intros c c' Hle H.
  - exact H.
  - cbn [stepn] in *.
    destruct (step a c) as [c1|] eqn:E; [| discriminate].
    rewrite (TM_le_step a b c c1 Hle E).
    exact (IH c1 c' Hle H).
Qed.

Lemma prefix_ok_le : forall r qs t tm',
  prefix_ok (row_to_tm r) qs t = true ->
  TM_le (row_to_tm r) tm' ->
  stepn tm' t InitES = Some (qs, snd InitES).
Proof.
  intros r qs t tm' Hpre Hle.
  exact (stepn_le (row_to_tm r) tm' t InitES (qs, snd InitES) Hle
           (prefix_ok_sound (row_to_tm r) qs t Hpre)).
Qed.

(** ** Monotonicity of the orbit operations under [TM_le] *)

Lemma TM_le_swap_mono : forall u v a b,
  TM_le a b -> TM_le (TM_swap u v a) (TM_swap u v b).
Proof.
  intros u v a b Hle q s. unfold TM_swap.
  destruct (Hle (St_swap u v q) s) as [Ha | Hb].
  - left. rewrite Ha. reflexivity.
  - right. rewrite Hb. reflexivity.
Qed.

Lemma TM_le_mirror_mono : forall a b,
  TM_le a b -> TM_le (mirror_tm a) (mirror_tm b).
Proof.
  intros a b Hle q s. unfold mirror_tm.
  destruct (Hle q s) as [Ha | Hb].
  - left. rewrite Ha. reflexivity.
  - right. rewrite Hb. reflexivity.
Qed.

(** ** Conjugation: [TM_swap StA q] through the orbit's swaps and mirror *)

Lemma St_swap_conj1 : forall u v q x,
  u <> StA -> v <> StA ->
  St_swap StA q (St_swap u v x)
  = St_swap u v (St_swap StA (St_swap u v q) x).
Proof.
  intros u v q x HuA HvA.
  destruct u, v, q, x; try congruence; reflexivity.
Qed.

Lemma St_swap_conj2 : forall u v q x,
  u <> StA -> v <> StA ->
  St_swap u v (St_swap StA q x)
  = St_swap StA (St_swap u v q) (St_swap u v x).
Proof.
  intros u v q x HuA HvA.
  destruct u, v, q, x; try congruence; reflexivity.
Qed.

Lemma TM_swap_conj : forall u v q tm,
  u <> StA -> v <> StA ->
  TM_swap StA q (TM_swap u v tm)
  = TM_swap u v (TM_swap StA (St_swap u v q) tm).
Proof.
  intros u v q tm HuA HvA.
  apply tm_ext; intros p s. unfold TM_swap.
  rewrite <- (St_swap_conj2 u v q p HuA HvA).
  destruct (tm (St_swap u v (St_swap StA q p)) s) as [tr|]; simpl;
    [| reflexivity].
  f_equal. unfold Trans_swap; simpl. f_equal.
  apply St_swap_conj1; assumption.
Qed.

Lemma TM_swap_mirror : forall u v tm,
  TM_swap u v (mirror_tm tm) = mirror_tm (TM_swap u v tm).
Proof.
  intros u v tm.
  apply tm_ext; intros p s. unfold TM_swap, mirror_tm.
  destruct (tm (St_swap u v p) s) as [tr|]; reflexivity.
Qed.

Lemma mirror_tape_invol : forall t, mirror_tape (mirror_tape t) = t.
Proof. intros [l h r]. reflexivity. Qed.

(** ** [skipped] descends the [Deferred] orbit *)

Lemma skipped_unswap : forall R u v tm,
  u <> v -> u <> StA -> v <> StA ->
  skipped R (TM_swap u v tm) -> skipped R tm.
Proof.
  intros R u v tm Huv HuA HvA [H | (qs & t & Hpre & Hdef)].
  - left. exact (Deferred_swap R u v tm Huv HuA HvA H).
  - right.
    exists (St_swap u v qs), t. split.
    + (* the prefix transfers through the swap *)
      rewrite stepn_swap, es_swap_init in Hpre by assumption.
      destruct (stepn tm t InitES) as [[cq ct]|] eqn:E; [| discriminate].
      simpl in Hpre.
      injection Hpre as H1 H2.
      subst ct.
      rewrite <- H1, St_swap_swap. reflexivity.
    + (* the deferred fact conjugates *)
      apply (Deferred_swap R u v _ Huv HuA HvA).
      rewrite <- (TM_swap_conj u v qs tm HuA HvA).
      exact Hdef.
Qed.

Lemma skipped_unmirror : forall R tm,
  skipped R (mirror_tm tm) -> skipped R tm.
Proof.
  intros R tm [H | (qs & t & Hpre & Hdef)].
  - left. exact (Deferred_mirror R tm H).
  - right.
    exists qs, t. split.
    + rewrite mirror_stepn_init in Hpre.
      destruct (stepn tm t InitES) as [[cq [l h r]]|] eqn:E; [| discriminate].
      unfold mirror_es in Hpre; simpl in Hpre.
      injection Hpre as H1 H2 H3 H4.
      subst. reflexivity.
    + apply (Deferred_mirror R _).
      rewrite <- (TM_swap_mirror StA qs tm).
      exact Hdef.
Qed.

(** ** The three-way split: proven / core / shadow *)

Lemma deferred_split_sh :
  forall Drows Prows Rrows Srows : list (list (option Trans)),
  forallb (fun r => row_inb r Prows || row_inb r Rrows || row_inb r Srows)
          Drows = true ->
  Forall covers (map row_to_tm Prows) ->
  Forall (fun h => forall tm, TM_le h tm -> skipped (map row_to_tm Rrows) tm)
         (map row_to_tm Srows) ->
  forall tm, Deferred (map row_to_tm Drows) tm ->
  boarded tm \/ skipped (map row_to_tm Rrows) tm.
Proof.
  intros Drows Prows Rrows Srows Hsplit Hcov Hsh tm HD.
  induction HD as [h tm Hin Hle | u v tm Huv HuA HvA HD IH | tm HD IH].
  - apply in_map_iff in Hin. destruct Hin as (r & Heq & Hr).
    rewrite forallb_forall in Hsplit.
    specialize (Hsplit r Hr).
    apply orb_true_iff in Hsplit.
    destruct Hsplit as [HPR | HS].
    + apply orb_true_iff in HPR. destruct HPR as [HP | HR].
      * left.
        rewrite Forall_forall in Hcov.
        refine (Hcov h _ tm Hle).
        rewrite <- Heq. apply in_map. exact (row_inb_In _ _ HP).
      * right. left.
        apply (Deferred_base _ h tm); [| exact Hle].
        rewrite <- Heq. apply in_map. exact (row_inb_In _ _ HR).
    + right.
      rewrite Forall_forall in Hsh.
      refine (Hsh h _ tm Hle).
      rewrite <- Heq. apply in_map. exact (row_inb_In _ _ HS).
  - destruct IH as [Hb | Hs].
    + left. exact (boarded_unswap u v tm HuA HvA Hb).
    + right. exact (skipped_unswap _ u v tm Huv HuA HvA Hs).
  - destruct IH as [Hb | Hs].
    + left. exact (boarded_unmirror tm Hb).
    + right. exact (skipped_unmirror _ tm Hs).
Qed.

(** ** The per-shadow discharge helper the generated stages use

    A shadow row [r] with blank prefix to [qs] whose re-root's
    completions all land in the core orbit: the two hypotheses are one
    [vm_compute] (the prefix check) and a per-row orbit path built from
    [Deferred_base]/[Deferred_swap]/[Deferred_mirror] plus
    [tm_le_b_sound] and the monotonicity lemmas. *)

Lemma shadow_at : forall (r : list (option Trans)) (qs : St) (t : nat)
                         (R : list TM),
  prefix_ok (row_to_tm r) qs t = true ->
  (forall tm', TM_le (row_to_tm r) tm' ->
               Deferred R (TM_swap StA qs tm')) ->
  forall tm', TM_le (row_to_tm r) tm' -> skipped R tm'.
Proof.
  intros r qs t R Hpre Hdef tm' Hle.
  right. exists qs, t. split.
  - exact (prefix_ok_le r qs t tm' Hpre Hle).
  - exact (Hdef tm' Hle).
Qed.
