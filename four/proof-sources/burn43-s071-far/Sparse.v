From Coq Require Import List Bool PArith FSets.FMapPositive SetoidList.
Import ListNotations.
Set Implicit Arguments.
Module PM := PositiveMap.

Definition get {A : Type} (m : PM.t (list A)) (k : positive) : list A :=
  match PM.find k m with Some xs => xs | None => [] end.

Definition all_map {A : Type} (f : positive -> A -> bool) (m : PM.t A) : bool :=
  forallb (fun kv => f (fst kv) (snd kv)) (PM.elements m).

Lemma find_in_elements {A} (m : PM.t A) k v :
  PM.find k m = Some v -> In (k,v) (PM.elements m).
Proof.
  intro H; apply PM.find_2, PM.elements_1 in H.
  induction H as [x xs Hx | x xs Hin IH].
  - destruct x as [k' v']; unfold PM.eq_key_elt in Hx; simpl in Hx.
    destruct Hx as [Hk Hv]. change (k = k') in Hk.
    subst; now left.
  - now right.
Qed.

Lemma all_map_sound {A} (m : PM.t A) f : all_map f m = true ->
  forall k v, PM.find k m = Some v -> f k v = true.
Proof.
  unfold all_map; rewrite forallb_forall.
  intros H k v F. apply (H (k,v)). now apply find_in_elements.
Qed.

Arguments all_map_sound {A m f} _ {k v} _.

Lemma all_get_sound {A} (m : PM.t (list A)) f :
  all_map (fun k xs => forallb (f k) xs) m = true ->
  forall k v, In v (get m k) -> f k v = true.
Proof.
  intros H k v HIn; unfold get in HIn.
  destruct (PM.find k m) as [xs|] eqn:F; [|contradiction].
  pose proof (all_map_sound H F) as G.
  rewrite forallb_forall in G; now apply G.
Qed.

Arguments all_get_sound {A m f} _ {k v} _.

Definition set := PM.t unit.
Definition mem (m : set) (k : positive) : bool :=
  match PM.find k m with Some _ => true | None => false end.

Lemma mem_find m k : mem m k = true -> PM.find k m = Some tt.
Proof. unfold mem; destruct (PM.find k m) as [[]|]; congruence. Qed.
Arguments mem_find {m k} _.

Lemma all_set_sound m f : all_map (fun k _ => f k) m = true ->
  forall k, mem m k = true -> f k = true.
Proof. intros H k M; exact (all_map_sound H (mem_find M)). Qed.

Definition adj := PM.t (list positive).
Definition edge (m : adj) (a b : positive) : bool :=
  existsb (Pos.eqb b) (get m a).

Lemma edge_in m a b : edge m a b = true <-> In b (get m a).
Proof.
  unfold edge; rewrite existsb_exists; split.
  - intros [v [Hv E]]. apply Pos.eqb_eq in E; now subst.
  - intro H; exists b; split; auto. now apply Pos.eqb_refl.
Qed.

Lemma all_edge_sound m f :
  all_map (fun k xs => forallb (f k) xs) m = true ->
  forall k v, edge m k v = true -> f k v = true.
Proof.
  intros H k v E. apply (all_get_sound H); now apply edge_in.
Qed.

Definition all_adj (f : positive -> positive -> bool) (m : adj) : bool :=
  all_map (fun k xs => forallb (f k) xs) m.

Lemma all_adj_sound m f : all_adj f m = true ->
  forall k v, edge m k v = true -> f k v = true.
Proof. apply all_edge_sound. Qed.
