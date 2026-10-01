(** * Transport finite configurations through a state map and reflection.

    The state map need only be surjective for instruction liveness.  A
    separate concrete boot is supplied for the target machine, so the
    map need not fix the initial state. *)
From Coq Require Import Arith List Bool.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape Mirror.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
From BBB4.Counters Require Import ValueLapTr.
Import ListNotations.

Definition cconj (p : St -> St) (flip : bool) (c : cconf) : cconf :=
  let '(q,(l,h,r)) := c in (p q, if flip then (r,h,l) else (l,h,r)).

Definition tconj (p : St -> St) (flip : bool) (t : Trans) : Trans :=
  mkTrans (t_write t) (if flip then mirror_dir (t_dir t) else t_dir t) (p (t_next t)).

Section Conjugate.
Variable src dst : TM.
Variable p : St -> St.
Variable flip : bool.
Hypothesis Htable : forall q s,
  dst (p q) s = option_map (tconj p flip) (src q s).

Lemma cconj_step : forall c,
  cstep dst (cconj p flip c) = option_map (cconj p flip) (cstep src c).
Proof.
  intros [q [[l h] r]]. unfold cstep, cconj.
  destruct flip; cbn; rewrite Htable;
    destruct (src q h) as [[w d nq]|]; cbn [option_map tconj];
    try reflexivity; destruct d; reflexivity.
Qed.

Lemma cconj_steps : forall n c d,
  csteps src n c = Some d -> csteps dst n (cconj p flip c) = Some (cconj p flip d).
Proof.
  induction n as [|n IH]; intros c d H.
  - injection H as <-. reflexivity.
  - cbn [csteps] in H |- *. rewrite cconj_step.
    destruct (cstep src c) as [e|] eqn:E; [|discriminate].
    cbn [option_map]. apply IH. exact H.
Qed.

Lemma cconj_instr : forall c,
  cinstr (cconj p flip c) = (p (fst (cinstr c)),snd (cinstr c)).
Proof. intros [q [[l h] r]]; destruct flip; reflexivity. Qed.

Variable V : Type.
Variable next : V -> V.
Variable Cf : nat -> V -> cconf.
Variable x0 : V.
Hypothesis Honto : forall q, exists q0, p q0 = q.
Hypothesis Hboot : exists n,
  stepn dst n InitES = Some (lift (cconj p flip (Cf 0 x0))).
Hypothesis Hlap : forall n x, exists k,
  csteps src k (Cf n x) = Some (Cf (S n) (next x)) /\ 0 < k.
Hypothesis Hfire : forall n x t, exists k c,
  csteps src k (Cf n x) = Some c /\ cinstr c = t.

Theorem cconj_value_neverqhtr : NeverQuasiHaltsTr dst.
Proof.
  apply (value_lap_neverqhtr dst V next (fun n x => cconj p flip (Cf n x)) x0).
  - exact Hboot.
  - intros n x. destruct (Hlap n x) as (k & H & Hk).
    exists k, (cconj p flip (Cf (S n) (next x))).
    split; [apply cconj_steps; exact H|]. split; [reflexivity|exact Hk].
  - intros n x [q s]. destruct (Honto q) as (q0 & Hp).
    destruct (Hfire n x (q0,s)) as (k & c & H & Hi).
    exists k, (cconj p flip c). split; [apply cconj_steps; exact H|].
    rewrite cconj_instr, Hi. cbn. rewrite Hp. reflexivity.
Qed.
End Conjugate.
