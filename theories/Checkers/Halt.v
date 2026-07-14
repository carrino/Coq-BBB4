(** * Halt: halting machines quasihalt trivially.

    The harness's [halt] certificate: the machine reaches an
    undefined transition after [h] steps (the halting step is [h+1]
    in BBB's 1-indexed counting).  After the halt there are no
    configurations at all, so every state is eventually quiet and
    the machine quasihalts (score = the halting step). *)

From Coq Require Import Arith Lia Bool List.
From BBB4 Require Import BBB4_Statement CTape.
Import ListNotations.

Definition halt_check (tm : TM) (h : nat) : bool :=
  match csteps tm h c0 with
  | Some cc => match cstep tm cc with None => true | Some _ => false end
  | None => false
  end.

Lemma cstep_none_lift : forall tm cc,
  cstep tm cc = None -> step tm (lift cc) = None.
Proof.
  intros tm [q [[l h] r]] H.
  unfold cstep in H. unfold step; simpl.
  destruct (tm q h); [discriminate | reflexivity].
Qed.

Theorem halt_check_sound : forall tm h,
  halt_check tm h = true ->
  Halts tm /\ QuasiHaltsSt tm.
Proof.
  intros tm h H. unfold halt_check in H.
  destruct (csteps tm h c0) as [cc|] eqn:Eh; [|discriminate].
  destruct (cstep tm cc) eqn:Es; [discriminate|].
  assert (Hnone : stepn tm (h + 1) InitES = None).
  { rewrite stepn_add, <- lift_c0, (csteps_lift _ _ _ _ Eh).
    cbn [stepn]. rewrite (cstep_none_lift _ _ Es). reflexivity. }
  split.
  - exists (h + 1). exact Hnone.
  - exists StA. split.
    + exists 0, InitES. split; reflexivity.
    + exists (h + 1). intros n Hn (c & Hc & _).
      replace n with ((h + 1) + (n - (h + 1))) in Hc by lia.
      rewrite stepn_add, Hnone in Hc. discriminate.
Qed.
