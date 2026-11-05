(** Exhaustive coverage of the three-state binary domain.  A checker may
    certify one first-cell shard at a time; all 13^6 partial tables are
    represented, including undefined transitions and arbitrary first moves. *)
From Coq Require Import List Arith Lia Bool FunctionalExtensionality.
From SmallBB Require Import Statement Size.
Import ListNotations.

Definition choices32 : list (option Trans) :=
  [None;
   Some (mkTrans S0 DL StA); Some (mkTrans S0 DL StB); Some (mkTrans S0 DL StC);
   Some (mkTrans S0 DR StA); Some (mkTrans S0 DR StB); Some (mkTrans S0 DR StC);
   Some (mkTrans S1 DL StA); Some (mkTrans S1 DL StB); Some (mkTrans S1 DL StC);
   Some (mkTrans S1 DR StA); Some (mkTrans S1 DR StB); Some (mkTrans S1 DR StC)].

Definition table32 a b c d e f : TM := fun q s =>
  match q,s with
  | StA,S0 => a | StA,S1 => b | StB,S0 => c | StB,S1 => d
  | StC,S0 => e | StC,S1 => f | _,_ => None
  end.

Lemma choice32_complete : forall tm, Admissible 3 2 tm ->
  forall q s, In (tm q s) choices32.
Proof.
  intros tm Had q s; destruct (tm q s) as [[w dr p]|] eqn:E; [|cbn;auto].
  pose proof (admissible_output 3 2 tm Had q s _ E) as H.
  unfold output_ok in H; destruct w,dr,p; cbn in H; try lia; cbn; tauto.
Qed.

Lemma table32_complete : forall tm, Admissible 3 2 tm ->
  tm = table32 (tm StA S0) (tm StA S1) (tm StB S0)
               (tm StB S1) (tm StC S0) (tm StC S1).
Proof.
  intros tm Had; extensionality q; extensionality s; destruct q,s;
    unfold table32; try reflexivity; apply (proj2 Had); cbn; lia.
Qed.

(** A two-cell shard has 13^4 = 28,561 tables. A one-cell shard has
    13^5 = 371,293 tables. Keeping these definitions separate permits
    bounded-size native checker obligations and independent kernel audits. *)
Definition check32_tail (check : TM -> bool) a b :=
  forallb (fun c => forallb (fun d => forallb (fun e => forallb
    (fun f => check (table32 a b c d e f)) choices32) choices32) choices32) choices32.

Definition check32_head (check : TM -> bool) a :=
  forallb (fun b => check32_tail check a b) choices32.

Definition check32_all (check : TM -> bool) :=
  forallb (check32_head check) choices32.

Lemma check32_tail_spec : forall check a b,
  check32_tail check a b = true ->
  forall c d e f, In c choices32 -> In d choices32 ->
    In e choices32 -> In f choices32 -> check (table32 a b c d e f) = true.
Proof.
  intros check a b H c d e f Hc Hd He Hf.
  unfold check32_tail in H.
  apply forallb_forall with (x:=c) in H; [|exact Hc].
  apply forallb_forall with (x:=d) in H; [|exact Hd].
  apply forallb_forall with (x:=e) in H; [|exact He].
  apply forallb_forall with (x:=f) in H; [exact H|exact Hf].
Qed.

Lemma check32_head_spec : forall check a,
  check32_head check a = true ->
  forall b c d e f, In b choices32 -> In c choices32 -> In d choices32 ->
    In e choices32 -> In f choices32 -> check (table32 a b c d e f) = true.
Proof.
  intros check a H b c d e f Hb Hc Hd He Hf.
  unfold check32_head in H.
  apply forallb_forall with (x:=b) in H; [|exact Hb].
  eapply check32_tail_spec; eauto.
Qed.

Theorem check32_complete : forall check,
  check32_all check = true ->
  forall tm, Admissible 3 2 tm -> check tm = true.
Proof.
  intros check H tm Had.
  unfold check32_all in H.
  apply forallb_forall with (x:=tm StA S0) in H;
    [|now apply choice32_complete].
  pose proof (check32_head_spec check (tm StA S0) H
    (tm StA S1) (tm StB S0) (tm StB S1) (tm StC S0) (tm StC S1)) as Htm.
  assert (E : check (table32 (tm StA S0) (tm StA S1) (tm StB S0)
                       (tm StB S1) (tm StC S0) (tm StC S1)) = true).
  { apply Htm; now apply choice32_complete. }
  rewrite <- (table32_complete tm Had) in E; exact E.
Qed.

Theorem census32_sound : forall (P : TM -> Prop) check,
  (forall tm, check tm = true -> P tm) -> check32_all check = true ->
  forall tm, Admissible 3 2 tm -> P tm.
Proof.
  intros P check Hsound Hall tm Had; apply Hsound.
  eapply check32_complete; eauto.
Qed.

(** This equivalent interface is convenient when checker shards are
    generated and compiled as individual modules. *)
Theorem census32_shards_sound : forall (P : TM -> Prop) check,
  (forall tm, check tm = true -> P tm) ->
  (forall a b, In a choices32 -> In b choices32 -> check32_tail check a b = true) ->
  forall tm, Admissible 3 2 tm -> P tm.
Proof.
  intros P check Hsound Hshards.
  apply (census32_sound P check Hsound).
  unfold check32_all; apply forallb_forall; intros a Ha.
  unfold check32_head; apply forallb_forall; intros b Hb.
  now apply Hshards.
Qed.
