(** Exhaustive coverage of the two-state ternary domain.  A checker may
    certify one first-cell shard at a time; all 13^6 partial tables are
    represented, including undefined transitions and arbitrary first moves. *)
From Coq Require Import List Arith Lia Bool FunctionalExtensionality.
From SmallBB Require Import Statement Size.
Import ListNotations.

Definition choices23 : list (option Trans) :=
  [None;
   Some (mkTrans S0 DL StA); Some (mkTrans S0 DL StB);
   Some (mkTrans S0 DR StA); Some (mkTrans S0 DR StB);
   Some (mkTrans S1 DL StA); Some (mkTrans S1 DL StB);
   Some (mkTrans S1 DR StA); Some (mkTrans S1 DR StB);
   Some (mkTrans S2 DL StA); Some (mkTrans S2 DL StB);
   Some (mkTrans S2 DR StA); Some (mkTrans S2 DR StB)].

Definition table23 a b c d e f : TM := fun q s =>
  match q,s with
  | StA,S0 => a | StA,S1 => b | StA,S2 => c
  | StB,S0 => d | StB,S1 => e | StB,S2 => f | _,_ => None
  end.

Lemma choice23_complete : forall tm, Admissible 2 3 tm ->
  forall q s, In (tm q s) choices23.
Proof.
  intros tm Had q s; destruct (tm q s) as [[w dr p]|] eqn:E; [|cbn;auto].
  pose proof (admissible_output 2 3 tm Had q s _ E) as H.
  unfold output_ok in H; destruct w,dr,p; cbn in H; try lia; cbn; tauto.
Qed.

Lemma table23_complete : forall tm, Admissible 2 3 tm ->
  tm = table23 (tm StA S0) (tm StA S1) (tm StA S2)
               (tm StB S0) (tm StB S1) (tm StB S2).
Proof.
  intros tm Had; extensionality q; extensionality s; destruct q,s;
    unfold table23; try reflexivity; apply (proj2 Had); cbn; lia.
Qed.

(** A two-cell shard has 13^4 = 28,561 tables. A one-cell shard has
    13^5 = 371,293 tables. Keeping these definitions separate permits
    bounded-size native checker obligations and independent kernel audits. *)
Definition check23_tail (check : TM -> bool) a b :=
  forallb (fun c => forallb (fun d => forallb (fun e => forallb
    (fun f => check (table23 a b c d e f)) choices23) choices23) choices23) choices23.

Definition check23_head (check : TM -> bool) a :=
  forallb (fun b => check23_tail check a b) choices23.

Definition check23_all (check : TM -> bool) :=
  forallb (check23_head check) choices23.

Lemma check23_tail_spec : forall check a b,
  check23_tail check a b = true ->
  forall c d e f, In c choices23 -> In d choices23 ->
    In e choices23 -> In f choices23 -> check (table23 a b c d e f) = true.
Proof.
  intros check a b H c d e f Hc Hd He Hf.
  unfold check23_tail in H.
  apply forallb_forall with (x:=c) in H; [|exact Hc].
  apply forallb_forall with (x:=d) in H; [|exact Hd].
  apply forallb_forall with (x:=e) in H; [|exact He].
  apply forallb_forall with (x:=f) in H; [exact H|exact Hf].
Qed.

Lemma check23_head_spec : forall check a,
  check23_head check a = true ->
  forall b c d e f, In b choices23 -> In c choices23 -> In d choices23 ->
    In e choices23 -> In f choices23 -> check (table23 a b c d e f) = true.
Proof.
  intros check a H b c d e f Hb Hc Hd He Hf.
  unfold check23_head in H.
  apply forallb_forall with (x:=b) in H; [|exact Hb].
  eapply check23_tail_spec; eauto.
Qed.

Theorem check23_complete : forall check,
  check23_all check = true ->
  forall tm, Admissible 2 3 tm -> check tm = true.
Proof.
  intros check H tm Had.
  unfold check23_all in H.
  apply forallb_forall with (x:=tm StA S0) in H;
    [|now apply choice23_complete].
  pose proof (check23_head_spec check (tm StA S0) H
    (tm StA S1) (tm StA S2) (tm StB S0) (tm StB S1) (tm StB S2)) as Htm.
  assert (E : check (table23 (tm StA S0) (tm StA S1) (tm StA S2)
                       (tm StB S0) (tm StB S1) (tm StB S2)) = true).
  { apply Htm; now apply choice23_complete. }
  rewrite <- (table23_complete tm Had) in E; exact E.
Qed.

Theorem census23_sound : forall (P : TM -> Prop) check,
  (forall tm, check tm = true -> P tm) -> check23_all check = true ->
  forall tm, Admissible 2 3 tm -> P tm.
Proof.
  intros P check Hsound Hall tm Had; apply Hsound.
  eapply check23_complete; eauto.
Qed.

(** This equivalent interface is convenient when checker shards are
    generated and compiled as individual modules. *)
Theorem census23_shards_sound : forall (P : TM -> Prop) check,
  (forall tm, check tm = true -> P tm) ->
  (forall a b, In a choices23 -> In b choices23 -> check23_tail check a b = true) ->
  forall tm, Admissible 2 3 tm -> P tm.
Proof.
  intros P check Hsound Hshards.
  apply (census23_sound P check Hsound).
  unfold check23_all; apply forallb_forall; intros a Ha.
  unfold check23_head; apply forallb_forall; intros b Hb.
  now apply Hshards.
Qed.
