(** * MeasureGlue: well-founded composition of counter laps.

    The closer the bounce_counter family needs (SCOPING section 5,
    Group B: "only bounce_counter needs a well-founded measure").
    A bounce macro-lap D(k) -> D(k+1) is not one parametric run: it
    chains an unbounded number of micro laps -- the nested
    working-area binary counter -- and only a measure bounds how
    many.  [mrun] composes a measure-decreasing abstract recurrence
    of exact micro laps into one [csteps] run reaching a terminal
    goal configuration:

    - [stepA] is the family's recurrence on abstract micro states
      ([None] = terminal), guarded by an invariant [P] (the
      conservation law tying the abstract state to the macro index);
    - every recurrence step is realized by a concrete lap ending
      EXACTLY at the next micro state's denotation and strictly
      decreasing the measure [mu];
    - terminal states realize the goal up to blank padding.

    The composition is by strong induction on the measure (fuel).
    The per-anchor step of the resulting macro family is the plain
    successor again, so [LapGlue.glue_neverqh] closes
    never-quasihalting exactly as for the single-run families: the
    unboundedness of the whole run comes from the macro index, the
    finiteness of each macro lap from the measure. *)

From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape.
Import ListNotations.

Section MeasureRun.

Variable tm : TM.
Variable A : Type.
Variable stepA : A -> option A.
Variable mu : A -> nat.
Variable P : A -> Prop.
Variable Cf : A -> cconf.
Variable goal : cconf.

Hypothesis Hstep : forall x x', P x -> stepA x = Some x' ->
  P x' /\ mu x' < mu x /\
  exists n, csteps tm n (Cf x) = Some (Cf x') /\ 0 < n.
Hypothesis Hterm : forall x, P x -> stepA x = None ->
  exists n c', csteps tm n (Cf x) = Some c' /\ lift c' = lift goal /\ 0 < n.

Lemma mrun_fuel : forall f x, mu x < f -> P x ->
  exists n c', csteps tm n (Cf x) = Some c' /\ lift c' = lift goal /\ 0 < n.
Proof.
  induction f; intros x Hf HP; [lia|].
  destruct (stepA x) as [x'|] eqn:E.
  - destruct (Hstep x x' HP E) as (HP' & Hmu & n1 & Hrun & Hn).
    destruct (IHf x') as (n2 & c' & Hrun2 & Hlift & _); [lia | exact HP' |].
    exists (n1 + n2), c'.
    split; [|split; [exact Hlift | lia]].
    eapply csteps_chain; eauto.
  - exact (Hterm x HP E).
Qed.

(** From any invariant-satisfying micro state, the run reaches the
    goal in finitely many, at least one, steps. *)
Theorem mrun : forall x, P x ->
  exists n c', csteps tm n (Cf x) = Some c' /\ lift c' = lift goal /\ 0 < n.
Proof.
  intros x HP.
  exact (mrun_fuel (S (mu x)) x (Nat.lt_succ_diag_r _) HP).
Qed.

End MeasureRun.
