(** * WTape: two-sided windowed runs and repetition cycles.

    The counter machines' laps decompose into phases that each touch
    only a bounded window of the tape.  A windowed run ([wsteps])
    executes on explicit finite lists with a per-side mode flag:

    - a [true] ("walled") side is a WINDOW of a larger unknown tape:
      popping past its end FAILS the run, so a successful run
      certifies that the phase never looked deeper -- and therefore
      commutes with appending arbitrary material below the window
      ([wsteps_transport]);
    - a [false] side is the ENTIRE half-tape: popping past its end
      materializes a blank, exactly like [CTape.cstep], and the
      transport appends nothing there.

    On top of the transport sit the two repetition lemmas that close
    the translated-cycle phases of a lap (comb crossings, carry runs,
    walk-backs) by induction on the repetition count:

    - [cycR]: a unit run [(q,([],h,u)) -P-> (q,(w,h,[]))] crosses
      [rep u k] rightward in [P*k] steps, depositing [rep w k];
    - [cycL]: a unit run [(q,(u,h,rw)) -P-> (q,([],h,rw++w))] crosses
      [rep u k] leftward, keeping a fixed right window [rw] and
      depositing [rep w k] under it.

    [rep] and its algebra ([rep_shift], [rep_rot], [rep_dbl]) provide
    the alignment rewrites (comb-unit rotations) the per-machine
    proofs need.  No axioms. *)

From Coq Require Import Arith Lia Bool List FunctionalExtensionality.
From BBB4 Require Import BBB4_Statement CTape.
Import ListNotations.

(** ** Windowed stepping *)

Definition wstep (bl br : bool) (tm : TM) (c : cconf) : option cconf :=
  let (q, t) := c in
  let '(l, h, r) := t in
  match tm q h with
  | None => None
  | Some tr =>
      match t_dir tr with
      | DR => match r, br with
              | [], true => None
              | _, _ => Some (t_next tr, (t_write tr :: l, chd r, ctl r))
              end
      | DL => match l, bl with
              | [], true => None
              | _, _ => Some (t_next tr, (ctl l, chd l, t_write tr :: r))
              end
      end
  end.

Fixpoint wsteps (bl br : bool) (tm : TM) (n : nat) (c : cconf)
  : option cconf :=
  match n with
  | 0 => Some c
  | S m => match wstep bl br tm c with
           | None => None
           | Some c' => wsteps bl br tm m c'
           end
  end.

(** ** Transport: a windowed run commutes with deeper context *)

Lemma wstep_transport : forall bl br tm q l h r q' l' h' r' L R,
  wstep bl br tm (q, (l, h, r)) = Some (q', (l', h', r')) ->
  (bl = false -> L = []) ->
  (br = false -> R = []) ->
  cstep tm (q, (l ++ L, h, r ++ R)) = Some (q', (l' ++ L, h', r' ++ R)).
Proof.
  intros bl br tm q l h r q' l' h' r' L R H HL HR.
  unfold wstep in H; unfold cstep.
  destruct (tm q h) as [tr|] eqn:E; [|discriminate].
  destruct (t_dir tr) eqn:Ed.
  - (* DL *)
    destruct l as [|x l0].
    + destruct bl; [discriminate|].
      rewrite (HL eq_refl). injection H as <- <- <- <-.
      reflexivity.
    + injection H as <- <- <- <-. reflexivity.
  - (* DR *)
    destruct r as [|y r0].
    + destruct br; [discriminate|].
      rewrite (HR eq_refl). injection H as <- <- <- <-.
      reflexivity.
    + injection H as <- <- <- <-. reflexivity.
Qed.

Lemma wsteps_transport : forall bl br tm n q l h r q' l' h' r' L R,
  wsteps bl br tm n (q, (l, h, r)) = Some (q', (l', h', r')) ->
  (bl = false -> L = []) ->
  (br = false -> R = []) ->
  csteps tm n (q, (l ++ L, h, r ++ R)) = Some (q', (l' ++ L, h', r' ++ R)).
Proof.
  intros bl br tm n; induction n;
    intros q l h r q' l' h' r' L R H HL HR; cbn [wsteps] in H.
  - injection H as <- <- <- <-. reflexivity.
  - destruct (wstep bl br tm (q, (l, h, r))) as [[q1 [[l1 h1] r1]]|] eqn:E;
      [|discriminate].
    cbn [csteps].
    rewrite (wstep_transport _ _ _ _ _ _ _ _ _ _ _ L R E HL HR).
    apply IHn; assumption.
Qed.

(** Both-sides-walled transport (the common case). *)
Lemma wsteps_frame : forall tm n q l h r q' l' h' r' L R,
  wsteps true true tm n (q, (l, h, r)) = Some (q', (l', h', r')) ->
  csteps tm n (q, (l ++ L, h, r ++ R)) = Some (q', (l' ++ L, h', r' ++ R)).
Proof.
  intros; apply (wsteps_transport true true); [assumption | discriminate ..].
Qed.

(** Left side is the whole half-tape (runs at the left tape edge). *)
Lemma wsteps_frame_l : forall tm n q l h r q' l' h' r' R,
  wsteps false true tm n (q, (l, h, r)) = Some (q', (l', h', r')) ->
  csteps tm n (q, (l, h, r ++ R)) = Some (q', (l', h', r' ++ R)).
Proof.
  intros.
  rewrite <- (app_nil_r l), <- (app_nil_r l').
  apply (wsteps_transport false true); [assumption | | discriminate].
  intros _; reflexivity.
Qed.

(** Right side is the whole half-tape (runs at the right tape edge). *)
Lemma wsteps_frame_r : forall tm n q l h r q' l' h' r' L,
  wsteps true false tm n (q, (l, h, r)) = Some (q', (l', h', r')) ->
  csteps tm n (q, (l ++ L, h, r)) = Some (q', (l' ++ L, h', r')).
Proof.
  intros.
  rewrite <- (app_nil_r r), <- (app_nil_r r').
  apply (wsteps_transport true false); [assumption | discriminate |].
  intros _; reflexivity.
Qed.

(** ** Repetition ([rep]) and its algebra *)

Fixpoint rep (u : list Sym) (k : nat) : list Sym :=
  match k with
  | 0 => []
  | S m => u ++ rep u m
  end.

Lemma rep_add : forall u j k, rep u (j + k) = rep u j ++ rep u k.
Proof.
  induction j; intros; simpl.
  - reflexivity.
  - rewrite IHj, app_assoc. reflexivity.
Qed.

Lemma rep_shift : forall u k, rep u k ++ u = u ++ rep u k.
Proof.
  induction k; simpl.
  - rewrite app_nil_r. reflexivity.
  - rewrite <- app_assoc, IHk. reflexivity.
Qed.

(** Rotating a unit across a fixed cell. *)
Lemma rep_rot : forall (x : Sym) u k,
  x :: rep (u ++ [x]) k = rep (x :: u) k ++ [x].
Proof.
  induction k; simpl.
  - reflexivity.
  - f_equal. rewrite <- app_assoc. cbn [app]. rewrite IHk.
    rewrite app_assoc. reflexivity.
Qed.

(** A single repeated cell slides across its own repetition. *)
Lemma rep_slide : forall (x : Sym) k Y,
  x :: rep [x] k ++ Y = rep [x] k ++ x :: Y.
Proof.
  induction k; intros; simpl.
  - reflexivity.
  - rewrite IHk. reflexivity.
Qed.

Lemma rep_dbl : forall (x : Sym) k, rep [x; x] k = rep [x] (2 * k).
Proof.
  induction k; simpl.
  - reflexivity.
  - rewrite IHk.
    replace (k + S (k + 0)) with (S (2 * k)) by lia.
    reflexivity.
Qed.

(** ** The repetition cycles *)

(** Rightward: one unit run crosses [u], deposits [w], and returns to
    the same state and head symbol; then [rep u k] crosses in [P*k]. *)
Lemma cycR : forall tm P q h u w,
  wsteps true true tm P (q, ([], h, u)) = Some (q, (w, h, [])) ->
  forall k L R,
  csteps tm (P * k) (q, (L, h, rep u k ++ R)) =
  Some (q, (rep w k ++ L, h, R)).
Proof.
  intros tm P q h u w Hu.
  induction k; intros L R.
  - rewrite Nat.mul_0_r. reflexivity.
  - replace (P * S k) with (P + P * k) by lia.
    rewrite csteps_add.
    simpl rep. rewrite <- app_assoc.
    pose proof (wsteps_frame tm P q [] h u q w h [] L (rep u k ++ R) Hu)
      as Hstep; cbn [app] in Hstep.
    rewrite Hstep, IHk.
    rewrite app_assoc, rep_shift, <- app_assoc.
    reflexivity.
Qed.

(** Leftward with a carried marker: one unit run consumes [u] from
    under a fixed left window [lw] (which it may traverse and must
    restore), keeping a fixed right window [rw] and depositing [w]
    below it. *)
Lemma cycLW : forall tm P q h lw u rw w,
  wsteps true true tm P (q, (lw ++ u, h, rw)) = Some (q, (lw, h, rw ++ w)) ->
  forall k L R,
  csteps tm (P * k) (q, (lw ++ rep u k ++ L, h, rw ++ R)) =
  Some (q, (lw ++ L, h, rw ++ rep w k ++ R)).
Proof.
  intros tm P q h lw u rw w Hu.
  induction k; intros L R.
  - rewrite Nat.mul_0_r. reflexivity.
  - replace (P * S k) with (P + P * k) by lia.
    rewrite csteps_add.
    simpl rep. rewrite <- app_assoc.
    pose proof (wsteps_frame tm P q (lw ++ u) h rw q lw h (rw ++ w)
                  (rep u k ++ L) R Hu) as Hstep;
      rewrite <- !app_assoc in Hstep.
    rewrite Hstep, IHk.
    assert (Hsh : rep w k ++ w ++ R = w ++ rep w k ++ R).
    { rewrite app_assoc, rep_shift, <- app_assoc. reflexivity. }
    rewrite Hsh, <- app_assoc. reflexivity.
Qed.

(** Leftward: one unit run consumes [u] from the left list under a
    fixed right window [rw], depositing [w] below [rw]. *)
Lemma cycL : forall tm P q h u rw w,
  wsteps true true tm P (q, (u, h, rw)) = Some (q, ([], h, rw ++ w)) ->
  forall k L R,
  csteps tm (P * k) (q, (rep u k ++ L, h, rw ++ R)) =
  Some (q, (L, h, rw ++ rep w k ++ R)).
Proof.
  intros tm P q h u rw w Hu.
  induction k; intros L R.
  - rewrite Nat.mul_0_r. reflexivity.
  - replace (P * S k) with (P + P * k) by lia.
    rewrite csteps_add.
    simpl rep. rewrite <- app_assoc.
    pose proof (wsteps_frame tm P q u h rw q [] h (rw ++ w)
                  (rep u k ++ L) R Hu) as Hstep;
      cbn [app] in Hstep; rewrite <- app_assoc in Hstep.
    rewrite Hstep, IHk.
    assert (Hsh : rep w k ++ w ++ R = w ++ rep w k ++ R).
    { rewrite app_assoc, rep_shift, <- app_assoc. reflexivity. }
    rewrite Hsh, <- app_assoc. reflexivity.
Qed.

(** ** Composition and denotation helpers *)

Lemma csteps_chain : forall tm n1 n2 c c1 c2,
  csteps tm n1 c = Some c1 ->
  csteps tm n2 c1 = Some c2 ->
  csteps tm (n1 + n2) c = Some c2.
Proof.
  intros. rewrite csteps_add, H. assumption.
Qed.

(** A trailing blank on a half-tape list is denotationally invisible. *)
Lemma lift_side_app_blank : forall r,
  lift_side (r ++ [S0]) = lift_side r.
Proof.
  intros; apply functional_extensionality; intro n.
  unfold lift_side, nthb.
  destruct (lt_dec n (length r)) as [Hlt | Hge].
  - apply app_nth1; assumption.
  - rewrite (nth_overflow r) by lia.
    destruct (Nat.eq_dec n (length r)) as [-> | Hne].
    + replace (length r) with (length r + 0) by lia.
      rewrite app_nth2_plus. reflexivity.
    + rewrite nth_overflow; [reflexivity|].
      rewrite app_length; simpl; lia.
Qed.

Lemma lift_app_blank : forall q l h r,
  lift (q, (l, h, r ++ [S0])) = lift (q, (l, h, r)).
Proof.
  intros. unfold lift; simpl.
  rewrite lift_side_app_blank. reflexivity.
Qed.
