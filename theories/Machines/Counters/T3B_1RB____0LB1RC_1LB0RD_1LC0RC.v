(** * T3B_1RB____0LB1RC_1LB0RD_1LC0RC: 1RB---_0LB1RC_1LB0RD_1LC0RC boards as [iqh].

    [StA]'s [S1] transition is undefined and nothing targets [StA], so [StA]
    fires exactly once, at configuration index 0: the machine QUASIHALTS with
    score 1 and [NeverQuasiHaltsSt] is false for it.  The three defined
    states are the BASE-THREE wall bouncer (alternating outward sweep) of [Counters/Ter3WallB.v] with
    roles [qW = StB], [qX = StC], [qY = StD], so the whole board is that
    closer plus five [vm_compute] facts.

    Read at [(qW, ([], S1, Wf t))] over the 2-cell digits [00]/[10]/[11]
    the lap is [4j + 2] and [4j + 4] on the two interior branches -- see
    [tools/counters/radix_infer.py].  At base 2 the same row reads as a
    [Theta(3^j)] "EXP3", which is what [tools/closeout/residue_map.tsv] calls
    it and why every base-2 emitter in the tree bounces off it.

    [Print Assumptions] = [functional_extensionality_dep] only. *)

From Coq Require Import Arith Lia Bool List.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Census Require Import TNF_QH.
From BBB4.Checkers Require Import ReachStI.
From BBB4.Counters Require Import WTape LapGlueQuiet LapGlueIx TernCounter.
From BBB4.Counters Require Ter3WallB.
Import ListNotations.

Definition mk (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).

(** 1RB---_0LB1RC_1LB0RD_1LC0RC *)
Definition tm_1RB____0LB1RC_1LB0RD_1LC0RC : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DR StB       | StA, S1 => None
  | StB, S0 => mk S0 DL StB       | StB, S1 => mk S1 DR StC
  | StC, S0 => mk S1 DL StB       | StC, S1 => mk S0 DR StD
  | StD, S0 => mk S1 DL StC       | StD, S1 => mk S0 DR StC end.
Local Notation tm := tm_1RB____0LB1RC_1LB0RD_1LC0RC.

Definition i0_1RB____0LB1RC_1LB0RD_1LC0RC : tern := (tD2 tE).
Definition Wf_1RB____0LB1RC_1LB0RD_1LC0RC : tern -> list Sym := Tw [S0;S0] [S1;S0] [S1;S1] [].

Lemma boot_1RB____0LB1RC_1LB0RD_1LC0RC :
  stepn tm 8 InitES = Some (lift (StB, ([], S1, Wf_1RB____0LB1RC_1LB0RD_1LC0RC i0_1RB____0LB1RC_1LB0RD_1LC0RC))).
Proof.
  assert (H : match csteps tm 8 c0 with
              | Some c => ceqb c (StB, ([], S1, Wf_1RB____0LB1RC_1LB0RD_1LC0RC i0_1RB____0LB1RC_1LB0RD_1LC0RC))
              | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 8 c0) as [c|] eqn:E; [| discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

Lemma bq_1RB____0LB1RC_1LB0RD_1LC0RC : forall n c, 0 < n < 8 ->
  stepn tm n InitES = Some c -> fst c <> StA.
Proof.
  intros n c Hn Hc.
  refine (bootquiet_chk_sound tm StA 1 7 _ n c _ Hc);
    [vm_compute; reflexivity | lia].
Qed.

(** The census R_QH predicate, stated locally so [tools/closeout/inventory.py]
    can verify it is literally the intended triple rather than trusting a name. *)
Definition iqh (tm : TM) : Prop :=
  NonHalt tm /\ QHBound 2000 tm /\ QuasiHaltsSt tm.

Theorem iqh_1RB____0LB1RC_1LB0RD_1LC0RC : iqh tm.
Proof.
  exact (Ter3WallB.ter3wallb_qh tm StB StC StD 8 i0_1RB____0LB1RC_1LB0RD_1LC0RC
           eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
           ltac:(intro q; destruct q; auto)
           ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
           ltac:(vm_compute; reflexivity)
           Wf_1RB____0LB1RC_1LB0RD_1LC0RC tsucc Ter3WallB.ter_stepB_nil
           boot_1RB____0LB1RC_1LB0RD_1LC0RC bq_1RB____0LB1RC_1LB0RD_1LC0RC).
Qed.

Theorem nonhalt_1RB____0LB1RC_1LB0RD_1LC0RC : NonHalt tm.
Proof. apply (proj1 iqh_1RB____0LB1RC_1LB0RD_1LC0RC). Qed.
