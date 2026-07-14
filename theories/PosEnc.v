(** * PosEnc: [positive] encodings and Patricia-trie sets/tables.

    The performance pass promised by SCOPING (risk 4, "Compile-time
    blowup ... positive encodings", the Coq-BB5 playbook): reflective
    checkers replace list membership (an [existsb] over a boolean
    equality, O(|S|) per lookup and O(|S|^2) per closure check) with
    Patricia-trie lookups keyed by injective [positive] encodings --
    [MSetPositive] for sets, [FMapPositive] for [nat]-valued tables.

    - [sym_app]/[syms_app]/[st_app] are *self-delimiting* bit
      encoders: each prepends a value's bits onto a [positive]
      continuation and is injective in BOTH the value and the
      continuation (a cons is marked by a [1] bit, end-of-list by
      [0]), so they compose into the injective configuration encoding
      [cconf_enc] with no length-prefix bookkeeping.

    - [pset_mem]/[pset_add]/[pset_of] wrap [PositiveSet] under an
      encoding.  [pset_of_mem] is the ONLY fact trusted checkers
      need: trie membership over an injectively encoded list implies
      list membership.  (The reverse direction is never used: the
      tries are rebuilt from the candidate lists inside the checkers,
      so a missing element merely fails the check.)

    - [pmap_of]/[pmap_get] give [nat]-valued lookup tables
      ([PositiveMap]) for certificate rank/potential data.  Their
      values are re-checked edge-by-edge by the closure engine, so
      any function would be sound and they need no lemmas at all. *)

From Coq Require Import Arith Lia Bool List PArith.
From Coq Require Export MSets.MSetPositive FSets.FMapPositive.
From BBB4 Require Import BBB4_Statement CTape.
Import ListNotations.

(** ** Self-delimiting bit encoders *)

Definition sym_app (s : Sym) (p : positive) : positive :=
  match s with S0 => xO p | S1 => xI p end.

Lemma sym_app_inj : forall x y p q,
  sym_app x p = sym_app y q -> x = y /\ p = q.
Proof.
  destruct x, y; simpl; intros p q H; split; congruence.
Qed.

Fixpoint syms_app (l : list Sym) (p : positive) : positive :=
  match l with
  | [] => xO p
  | x :: t => xI (sym_app x (syms_app t p))
  end.

Lemma syms_app_inj : forall l1 l2 p q,
  syms_app l1 p = syms_app l2 q -> l1 = l2 /\ p = q.
Proof.
  induction l1 as [|x t IH]; destruct l2 as [|y u]; simpl; intros p q H;
    try (split; congruence).
  injection H as H.
  destruct (sym_app_inj _ _ _ _ H) as [-> H2].
  destruct (IH _ _ _ H2) as [-> ->]. auto.
Qed.

Definition syms_enc (l : list Sym) : positive := syms_app l xH.

Lemma syms_enc_inj : forall a b, syms_enc a = syms_enc b -> a = b.
Proof.
  intros a b H. exact (proj1 (syms_app_inj _ _ _ _ H)).
Qed.

Definition st_app (q : St) (p : positive) : positive :=
  match q with
  | StA => xO (xO p)
  | StB => xI (xO p)
  | StC => xO (xI p)
  | StD => xI (xI p)
  end.

Lemma st_app_inj : forall x y p q,
  st_app x p = st_app y q -> x = y /\ p = q.
Proof.
  destruct x, y; simpl; intros p q H; split; congruence.
Qed.

(** ** The configuration encoding *)

Definition cconf_enc (c : cconf) : positive :=
  let '(q, (l, h, r)) := c in
  st_app q (sym_app h (syms_app l (syms_enc r))).

Lemma cconf_enc_inj : forall c1 c2, cconf_enc c1 = cconf_enc c2 -> c1 = c2.
Proof.
  intros [q1 [[l1 h1] r1]] [q2 [[l2 h2] r2]] H; simpl in H.
  destruct (st_app_inj _ _ _ _ H) as [-> H1].
  destruct (sym_app_inj _ _ _ _ H1) as [-> H2].
  destruct (syms_app_inj _ _ _ _ H2) as [-> H3].
  rewrite (syms_enc_inj _ _ H3). reflexivity.
Qed.

(** ** Sets and tables of encoded elements *)

Section EncSets.

  Variable A : Type.
  Variable enc : A -> positive.

  Definition pset_mem (a : A) (s : PositiveSet.t) : bool :=
    PositiveSet.mem (enc a) s.

  Definition pset_add (a : A) (s : PositiveSet.t) : PositiveSet.t :=
    PositiveSet.add (enc a) s.

  Definition pset_of (l : list A) : PositiveSet.t :=
    fold_left (fun s a => pset_add a s) l PositiveSet.empty.

  Definition pmap_of (tbl : list (A * nat)) : PositiveMap.tree nat :=
    fold_left (fun m p => PositiveMap.add (enc (fst p)) (snd p) m)
              tbl (PositiveMap.empty nat).

  Definition pmap_get (m : PositiveMap.tree nat) (a : A) : nat :=
    match PositiveMap.find (enc a) m with
    | Some n => n
    | None => 0
    end.

  Hypothesis enc_inj : forall x y, enc x = enc y -> x = y.

  Lemma pset_of_acc_mem : forall l s a,
    PositiveSet.mem (enc a) (fold_left (fun s a => pset_add a s) l s) = true ->
    PositiveSet.mem (enc a) s = true \/ In a l.
  Proof.
    induction l as [|x t IH]; simpl; intros s a H.
    - left; exact H.
    - destruct (IH _ _ H) as [Hm | Hin]; [|right; right; assumption].
      unfold pset_add in Hm.
      apply PositiveSet.mem_spec, PositiveSet.add_spec in Hm.
      destruct Hm as [E | Hin].
      + right; left. symmetry. apply enc_inj, E.
      + left. apply PositiveSet.mem_spec, Hin.
  Qed.

  Lemma pset_of_mem : forall a l, pset_mem a (pset_of l) = true -> In a l.
  Proof.
    intros a l H.
    destruct (pset_of_acc_mem l PositiveSet.empty a H) as [Hm |]; [|assumption].
    apply PositiveSet.mem_spec in Hm.
    now apply PositiveSet.empty_spec in Hm.
  Qed.

End EncSets.
