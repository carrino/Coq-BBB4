(** * CloseoutKit: route A of the census closeout (docs/NGHIST_WAVE5.md S5).

    The census theorem ([Census/Compute/Census_Theorem.v]) says every (4,2)
    machine satisfies [QHBound B_census] or is [Deferred D_census] -- membership
    in the orbit of the frozen 5,156-row list under completion ([TM_le]),
    non-start state swaps, and mirroring.  This kit provides the generic lemma
    that trades the deferred list down against per-machine boards:

      [deferred_split] : if every row of [D] is either COVERED (all its
      completions boarded) or listed in [R], then
      [Deferred D tm -> boarded tm \/ Deferred R tm].

    - [boarded] is Census/Assembly.v's predicate restated (quasihalting
      behaviour settled: never-QH, or a quasihalter with SOME certified
      last-visit bound);
    - [covers h] discharges from a single theorem about the row's own
      machine -- [NeverQuasiHaltsSt h] or the [NonHalt/QHBound/QuasiHaltsSt]
      triple -- because a non-halting machine's completions share its trace
      ([TNF_QH]'s [visits_le] family; holes never fire);
    - the swap/mirror cases transport [boarded] backwards through the orbit
      ([boarded_unswap], [boarded_unmirror]);
    - the row split hypothesis is a boolean check ([forallb]/[row_inb]),
      evaluated by [vm_compute] in the assembly file.

    Nothing here touches the census: this file only CONSUMES [Deferred].
    Downstream: generated stage files (CB_*.v) prove [Forall covers] over the
    proven rows; Closeout.v instantiates [deferred_split] against the frozen
    tables and chains [census_decided]. *)

From Coq Require Import Arith Bool List FunctionalExtensionality.
From BBB4 Require Import BBB4_Statement Mirror.
From BBB4.Census Require Import TNF_QH Deferred_Defs.
Import ListNotations.

(** ** The boarded predicate (Census/Assembly.v's, restated verbatim)

    The bound is existential on purpose: a deferred machine may be a
    perfectly well-understood quasihalter whose quiet states go quiet after
    step 2000 (the census's in-walk tier strength); deciding the machine is
    what matters, not the size of its bound. *)
Definition boarded (tm : TM) : Prop :=
  NeverQuasiHaltsSt tm
  \/ (NonHalt tm /\ (exists B, QHBound B tm) /\ QuasiHaltsSt tm).

(** [covers h]: every completion of [h] is boarded.  This is exactly the
    obligation [Deferred_base] induces for a listed row [h]. *)
Definition covers (h : TM) : Prop := forall tm, TM_le h tm -> boarded tm.

(** ** Completion transports ([TM_le]): the don't-care argument *)

Lemma never_qh_le : forall h tm',
  NeverQuasiHaltsSt h -> TM_le h tm' -> NeverQuasiHaltsSt tm'.
Proof.
  intros h tm' H Hle.
  pose proof (never_qh_nonhalt h H) as Hnh.
  intros q Hv N.
  destruct Hv as (n0 & Hv0).
  apply (proj1 (visits_le h tm' q n0 Hnh Hle)) in Hv0.
  destruct (H q (ex_intro _ n0 Hv0) N) as (n & Hn & Hvis).
  exists n. split; [exact Hn |].
  apply (proj2 (visits_le h tm' q n Hnh Hle)). exact Hvis.
Qed.

Lemma qh_le : forall h tm',
  NonHalt h -> TM_le h tm' -> QuasiHaltsSt h -> QuasiHaltsSt tm'.
Proof.
  intros h tm' Hnh Hle (q & (n0 & Hv0) & N & HN).
  exists q. split.
  - exists n0. apply (proj2 (visits_le h tm' q n0 Hnh Hle)). exact Hv0.
  - exists N. intros n Hn Hvis.
    apply (HN n Hn).
    apply (proj1 (visits_le h tm' q n Hnh Hle)). exact Hvis.
Qed.

Lemma covers_nqh : forall h, NeverQuasiHaltsSt h -> covers h.
Proof.
  intros h H tm Hle. left. exact (never_qh_le h tm H Hle).
Qed.

Lemma covers_iqh : forall B h,
  NonHalt h -> QHBound B h -> QuasiHaltsSt h -> covers h.
Proof.
  intros B h Hnh Hb Hqh tm Hle. right.
  split; [exact (nonhalt_le h tm Hnh Hle) |].
  split; [exists B; exact (qhbound_le B h tm Hnh Hb Hle) |].
  exact (qh_le h tm Hnh Hle Hqh).
Qed.

(** ** Row-level entry points for the generated stages

    A stage discharges [covers (row_to_tm r)] from the board theorem about
    its own [tm] constant; the pointwise premise is an 8-way case split that
    FAILS TO COMPILE on any row/board mismatch -- the untrusted inventory is
    re-checked here by the kernel. *)

Lemma tm_ext : forall a b : TM, (forall q s, a q s = b q s) -> a = b.
Proof.
  intros a b E.
  apply functional_extensionality; intro q.
  apply functional_extensionality; intro s.
  apply E.
Qed.

Lemma covers_nqh_at : forall (t : TM) (r : list (option Trans)),
  NeverQuasiHaltsSt t ->
  (forall q s, row_to_tm r q s = t q s) ->
  covers (row_to_tm r).
Proof.
  intros t r H E. rewrite (tm_ext (row_to_tm r) t E). exact (covers_nqh t H).
Qed.

Lemma covers_iqh_at : forall (t : TM) (r : list (option Trans)),
  NonHalt t /\ QHBound 2000 t /\ QuasiHaltsSt t ->
  (forall q s, row_to_tm r q s = t q s) ->
  covers (row_to_tm r).
Proof.
  intros t r (Hnh & Hb & Hq) E.
  rewrite (tm_ext (row_to_tm r) t E). exact (covers_iqh 2000 t Hnh Hb Hq).
Qed.

(** ** Swap transport, backwards (the [Deferred_swap] case) *)

Lemma never_qh_unswap : forall u v tm,
  u <> StA -> v <> StA ->
  NeverQuasiHaltsSt (TM_swap u v tm) -> NeverQuasiHaltsSt tm.
Proof.
  intros u v tm HuA HvA H q Hv N.
  destruct Hv as (n0 & Hv0).
  assert (Hv0' : VisitsAt (TM_swap u v tm) (St_swap u v q) n0).
  { apply (proj2 (visits_swap u v tm (St_swap u v q) n0 HuA HvA)).
    rewrite St_swap_swap. exact Hv0. }
  destruct (H (St_swap u v q) (ex_intro _ n0 Hv0') N) as (n & Hn & Hvis).
  exists n. split; [exact Hn |].
  pose proof (proj1 (visits_swap u v tm (St_swap u v q) n HuA HvA) Hvis) as Hv2.
  rewrite St_swap_swap in Hv2. exact Hv2.
Qed.

Lemma qh_unswap : forall u v tm,
  u <> StA -> v <> StA ->
  QuasiHaltsSt (TM_swap u v tm) -> QuasiHaltsSt tm.
Proof.
  intros u v tm HuA HvA (q & (n0 & Hv0) & N & HN).
  exists (St_swap u v q). split.
  - exists n0. exact (proj1 (visits_swap u v tm q n0 HuA HvA) Hv0).
  - exists N. intros n Hn Hvis.
    apply (HN n Hn).
    apply (proj2 (visits_swap u v tm q n HuA HvA)). exact Hvis.
Qed.

Lemma boarded_unswap : forall u v tm,
  u <> StA -> v <> StA ->
  boarded (TM_swap u v tm) -> boarded tm.
Proof.
  intros u v tm HuA HvA [H | (Hnh & (B & Hb) & Hq)].
  - left. exact (never_qh_unswap u v tm HuA HvA H).
  - right. split.
    + pose proof (nonhalt_swap u v (TM_swap u v tm) HuA HvA Hnh) as H2.
      rewrite TM_swap_swap in H2. exact H2.
    + split.
      * exists B.
        pose proof (qhbound_swap u v B (TM_swap u v tm) HuA HvA Hb) as H2.
        rewrite TM_swap_swap in H2. exact H2.
      * exact (qh_unswap u v tm HuA HvA Hq).
Qed.

(** ** Mirror transport, backwards (the [Deferred_mirror] case) *)

Lemma boarded_unmirror : forall tm, boarded (mirror_tm tm) -> boarded tm.
Proof.
  intros tm [H | (Hnh & (B & Hb) & Hq)].
  - left. exact (mirror_never_qh tm H).
  - right. split; [exact (mirror_nonhalt tm Hnh) |].
    split; [exists B; exact (qhbound_mirror B tm Hb) |].
    exact (mirror_qh tm Hq).
Qed.

(** ** Reflective row membership (the split hypothesis is one [vm_compute]) *)

Definition dir_eqb (a b : Dir) : bool :=
  match a, b with DL, DL | DR, DR => true | _, _ => false end.

Lemma dir_eqb_eq : forall a b, dir_eqb a b = true -> a = b.
Proof. destruct a, b; simpl; congruence. Qed.

Definition trans_eqb (a b : Trans) : bool :=
  sym_eqb (t_write a) (t_write b)
  && dir_eqb (t_dir a) (t_dir b)
  && st_eqb (t_next a) (t_next b).

Lemma trans_eqb_eq : forall a b, trans_eqb a b = true -> a = b.
Proof.
  intros [w1 d1 n1] [w2 d2 n2] H. unfold trans_eqb in H; simpl in H.
  apply andb_true_iff in H; destruct H as [H Hn].
  apply andb_true_iff in H; destruct H as [Hw Hd].
  apply sym_eqb_spec in Hw. apply dir_eqb_eq in Hd. apply st_eqb_spec in Hn.
  congruence.
Qed.

Definition otrans_eqb (a b : option Trans) : bool :=
  match a, b with
  | None, None => true
  | Some x, Some y => trans_eqb x y
  | _, _ => false
  end.

Lemma otrans_eqb_eq : forall a b, otrans_eqb a b = true -> a = b.
Proof.
  intros [x|] [y|] H; simpl in H; try discriminate; [| reflexivity].
  apply trans_eqb_eq in H. congruence.
Qed.

Fixpoint row_eqb (a b : list (option Trans)) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => otrans_eqb x y && row_eqb a' b'
  | _, _ => false
  end.

Lemma row_eqb_eq : forall a b, row_eqb a b = true -> a = b.
Proof.
  induction a as [| x a' IH]; intros [| y b'] H; simpl in H;
    try discriminate; [reflexivity |].
  apply andb_true_iff in H; destruct H as [Hx Hr].
  apply otrans_eqb_eq in Hx. rewrite (IH b' Hr). congruence.
Qed.

Definition row_inb (r : list (option Trans))
                   (l : list (list (option Trans))) : bool :=
  existsb (row_eqb r) l.

Lemma row_inb_In : forall r l, row_inb r l = true -> In r l.
Proof.
  intros r l H. unfold row_inb in H.
  apply existsb_exists in H. destruct H as (r' & Hin & Heq).
  apply row_eqb_eq in Heq. rewrite Heq. exact Hin.
Qed.

(** ** The split lemma: one induction over the deferred orbit *)

Lemma deferred_split :
  forall Drows Prows Rrows : list (list (option Trans)),
  forallb (fun r => row_inb r Prows || row_inb r Rrows) Drows = true ->
  Forall covers (map row_to_tm Prows) ->
  forall tm, Deferred (map row_to_tm Drows) tm ->
  boarded tm \/ Deferred (map row_to_tm Rrows) tm.
Proof.
  intros Drows Prows Rrows Hsplit Hcov tm HD.
  induction HD as [h tm Hin Hle | u v tm Huv HuA HvA HD IH | tm HD IH].
  - apply in_map_iff in Hin. destruct Hin as (r & Heq & Hr).
    rewrite forallb_forall in Hsplit.
    specialize (Hsplit r Hr). apply orb_true_iff in Hsplit.
    destruct Hsplit as [HP | HR].
    + left.
      rewrite Forall_forall in Hcov.
      refine (Hcov h _ tm Hle).
      rewrite <- Heq. apply in_map. exact (row_inb_In _ _ HP).
    + right.
      apply (Deferred_base _ h tm); [| exact Hle].
      rewrite <- Heq. apply in_map. exact (row_inb_In _ _ HR).
  - destruct IH as [Hb | Hd].
    + left. exact (boarded_unswap u v tm HuA HvA Hb).
    + right. exact (Deferred_swap _ u v tm Huv HuA HvA Hd).
  - destruct IH as [Hb | Hd].
    + left. exact (boarded_unmirror tm Hb).
    + right. exact (Deferred_mirror _ tm Hd).
Qed.
