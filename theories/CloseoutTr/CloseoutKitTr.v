(** * CloseoutKitTr: the transition-level census closeout.

    The transition-level census theorem
    ([CensusTr/Compute/Census_TheoremTr.v]) says every (4,2) machine
    satisfies [QHBoundTr B_tr] or is [Deferred D_tr]: in the orbit of the
    frozen deferred list (v10: 10,924 rows) under completion ([TM_le]),
    non-start state swaps and mirroring.  This kit trades that list down
    against per-machine boards WITHOUT re-walking the census, exactly as
    [Closeout/CloseoutKit.v] does at state level:

      [deferred_split_tr] : if every row of [D] is either COVERED (all its
      completions boarded) or listed in [R], then
      [Deferred D tm -> QHBoundTr B_close tm \/ Deferred R tm].

    It is simpler than the state-level kit in one respect: at transition
    level never-quasihalting machines satisfy [QHBoundTr] at every bound
    ([neverqhtr_qhboundtr]), and [QHBoundTr] already transports along
    completion ([qhboundtr_le]), swap and mirror ([TNF_QHTr]).  So the
    boarded predicate is [QHBoundTr B_close] alone, the census's own left
    disjunct, and no new transport lemma is needed.

    [B_close] is the literal 32779478, written the way [RunTr.B_tr] and the
    proven-QH stages write it, so the three are convertible and no
    32.8M-constructor numeral is ever normalised.

    Batch files ([CBT_<TAG>_<NN>.v], one tag per workstream) prove
    [Forall coversTr (map row_to_tm rows)] for their rows; the generated
    [CloseoutTr.v] concatenates them and checks the split reflectively.
    Nothing here touches the census: this file only CONSUMES [Deferred]. *)

From Coq Require Import Arith Bool List NArith PArith FMapPositive.
From BBB4 Require Import BBB4_Statement BBBT4_Statement Mirror.
From BBB4.Census Require Import TNF_QH Deferred_Defs.
From BBB4.CensusTr Require Import TNF_QHTr.
From BBB4.Closeout Require Import CloseoutKit.
Import ListNotations.

Definition B_close : nat := 32779478.

(** [coversTr h]: every completion of [h] is quiet by [B_close] at
    instruction level.  This is exactly the obligation [Deferred_base]
    induces for a listed row [h]. *)
Definition coversTr (h : TM) : Prop :=
  forall tm, TM_le h tm -> QHBoundTr B_close tm.

(** ** Entry points for batch files *)

Lemma coversTr_nqh : forall h, NeverQuasiHaltsTr h -> coversTr h.
Proof.
  intros h H tm Hle.
  exact (qhboundtr_le B_close h tm (never_qh_tr_nonhalt h H)
           (neverqhtr_qhboundtr B_close h H) Hle).
Qed.

(** a quasihalter needs [NonHalt] for the don't-care argument (a hole it
    reached would be filled differently in a completion) *)
Lemma coversTr_qh : forall h,
  NonHalt h -> QHBoundTr B_close h -> coversTr h.
Proof.
  intros h Hnh Hb tm Hle. exact (qhboundtr_le B_close h tm Hnh Hb Hle).
Qed.

(** the shape the proven-QH stages already produce
    ([provqh_tr_all], [QHConveyorTr.rwqh_stage]) *)
Lemma coversTr_qh3 : forall h,
  NonHalt h /\ QHBoundTr 32779478 h /\ QuasiHaltsTr h -> coversTr h.
Proof. intros h (Hnh & Hb & _). exact (coversTr_qh h Hnh Hb). Qed.

(** Row-level variants: the theorem is about a stage's own [tm] constant,
    the pointwise premise is an 8-way case split that fails to compile on
    any row/board mismatch. *)
Lemma coversTr_nqh_at : forall (t : TM) (r : list (option Trans)),
  NeverQuasiHaltsTr t ->
  (forall q s, row_to_tm r q s = t q s) ->
  coversTr (row_to_tm r).
Proof.
  intros t r H E. rewrite (tm_ext (row_to_tm r) t E). exact (coversTr_nqh t H).
Qed.

Lemma coversTr_qh3_at : forall (t : TM) (r : list (option Trans)),
  NonHalt t /\ QHBoundTr 32779478 t /\ QuasiHaltsTr t ->
  (forall q s, row_to_tm r q s = t q s) ->
  coversTr (row_to_tm r).
Proof.
  intros t r H E. rewrite (tm_ext (row_to_tm r) t E). exact (coversTr_qh3 t H).
Qed.

(** ** Orbit transports, backwards *)

Lemma qhboundtr_unswap : forall u v B tm,
  u <> StA -> v <> StA ->
  QHBoundTr B (TM_swap u v tm) -> QHBoundTr B tm.
Proof.
  intros u v B tm HuA HvA H.
  pose proof (qhboundtr_swap u v B (TM_swap u v tm) HuA HvA H) as H'.
  rewrite (TM_swap_swap u v) in H'. exact H'.
Qed.

(** ** Fast reflective membership

    [row_inb] is a linear scan, so checking 10,924 deferred rows against
    10,924 proven-or-remaining rows costs 6e7 row comparisons (9 minutes
    of [vm_compute]).  Instead the rows go into a [PositiveMap] keyed by a
    base-17 reading of the row (slot codes 0..16), and a lookup's hit is
    re-compared with [row_eqb]: the whole check takes about a second.
    Soundness needs only that whatever the map returns came from the list
    ([row_map_sound]); the key need not be proved injective (a collision
    could only make the check fail, never pass wrongly). *)

Definition st_n (q : St) : N :=
  match q with StA => 0 | StB => 1 | StC => 2 | StD => 3 end.

Definition otrans_n (o : option Trans) : N :=
  match o with
  | None => 0
  | Some t =>
      1 + (match t_write t with S0 => 0 | S1 => 8 end)
        + (match t_dir t with DL => 0 | DR => 4 end)
        + st_n (t_next t)
  end%N.

Definition row_key (r : list (option Trans)) : positive :=
  N.succ_pos (fold_left (fun acc o => acc * 17 + otrans_n o)%N r 0%N).

Definition row_map (l : list (list (option Trans)))
  : PositiveMap.t (list (option Trans)) :=
  fold_right (fun r m => PositiveMap.add (row_key r) r m)
             (PositiveMap.empty _) l.

Definition row_memb (m : PositiveMap.t (list (option Trans)))
                    (r : list (option Trans)) : bool :=
  match PositiveMap.find (row_key r) m with
  | Some r' => row_eqb r r'
  | None => false
  end.

Lemma row_map_sound : forall l k v,
  PositiveMap.find k (row_map l) = Some v -> In v l.
Proof.
  induction l as [| a l IH]; intros k v H; simpl in H.
  - rewrite PositiveMap.gempty in H. discriminate.
  - destruct (Pos.eq_dec k (row_key a)) as [-> | Hne].
    + rewrite PositiveMap.gss in H. injection H as <-. left. reflexivity.
    + rewrite PositiveMap.gso in H by exact Hne. right. exact (IH k v H).
Qed.

Lemma row_memb_In : forall l r, row_memb (row_map l) r = true -> In r l.
Proof.
  intros l r H. unfold row_memb in H.
  destruct (PositiveMap.find (row_key r) (row_map l)) as [r'|] eqn:E;
    [| discriminate].
  apply row_eqb_eq in H. subst r'. exact (row_map_sound l _ r E).
Qed.

(** the check the assembly file evaluates: the two maps are built ONCE
    (a [let] outside the [forallb]; inside the lambda the VM would rebuild
    them per row) *)
Definition split_ok (Drows Prows Rrows : list (list (option Trans))) : bool :=
  let mp := row_map Prows in
  let mr := row_map Rrows in
  forallb (fun r => row_memb mp r || row_memb mr r) Drows.

(** ** The split lemma: one induction over the deferred orbit *)

Lemma deferred_split_tr :
  forall Drows Prows Rrows : list (list (option Trans)),
  split_ok Drows Prows Rrows = true ->
  Forall coversTr (map row_to_tm Prows) ->
  forall tm, Deferred (map row_to_tm Drows) tm ->
  QHBoundTr B_close tm \/ Deferred (map row_to_tm Rrows) tm.
Proof.
  intros Drows Prows Rrows Hsplit Hcov tm HD.
  unfold split_ok in Hsplit.
  induction HD as [h tm Hin Hle | u v tm Huv HuA HvA HD IH | tm HD IH].
  - apply in_map_iff in Hin. destruct Hin as (r & Heq & Hr).
    rewrite forallb_forall in Hsplit.
    specialize (Hsplit r Hr). apply orb_true_iff in Hsplit.
    destruct Hsplit as [HP | HR].
    + left.
      rewrite Forall_forall in Hcov.
      refine (Hcov h _ tm Hle).
      rewrite <- Heq. apply in_map. exact (row_memb_In _ _ HP).
    + right.
      apply (Deferred_base _ h tm); [| exact Hle].
      rewrite <- Heq. apply in_map. exact (row_memb_In _ _ HR).
  - destruct IH as [Hb | Hd].
    + left. exact (qhboundtr_unswap u v B_close tm HuA HvA Hb).
    + right. exact (Deferred_swap _ u v tm Huv HuA HvA Hd).
  - destruct IH as [Hb | Hd].
    + left. exact (qhboundtr_mirror B_close tm Hb).
    + right. exact (Deferred_mirror _ tm Hd).
Qed.
