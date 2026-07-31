(** * T3_1RB____1LC1LB_0LC1RD_0RB0RD: 1RB---_1LC1LB_0LC1RD_0RB0RD boards as [iqh].

    [StA]'s [S1] transition is undefined and nothing targets [StA], so [StA]
    fires exactly once, at configuration index 0: the machine QUASIHALTS with
    score 1 and [NeverQuasiHaltsSt] is false for it.  The three defined
    states are the BASE-THREE wall bouncer of [Counters/Ter3Wall.v] with
    roles [qW = StC], [qC = StD], [qD = StB], so the whole board is that
    closer plus five [vm_compute] facts.

    Read at [(qW, ([], S1, Wf t))] over the 2-cell digits [00]/[01]/[11]
    (increment [tsuccT]) the lap is [4j + 4] in the carry length -- see
    [tools/counters/radix_infer.py].  At base 2 the same row reads as a
    [Theta(3^j)] "EXP3", which is what [tools/closeout/residue_map.tsv] calls
    it and why every base-2 emitter in the tree bounces off it.

    [Print Assumptions] = [functional_extensionality_dep] only. *)

From Coq Require Import Arith Lia Bool List.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Census Require Import TNF_QH.
From BBB4.Checkers Require Import ReachStI.
From BBB4.Counters Require Import WTape LapGlueQuiet LapGlueIx TernCounter.
From BBB4.Counters Require Ter3Wall.
Import ListNotations.

Definition mk (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).

(** 1RB---_1LC1LB_0LC1RD_0RB0RD *)
Definition tm_1RB____1LC1LB_0LC1RD_0RB0RD : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DR StB       | StA, S1 => None
  | StB, S0 => mk S1 DL StC       | StB, S1 => mk S1 DL StB
  | StC, S0 => mk S0 DL StC       | StC, S1 => mk S1 DR StD
  | StD, S0 => mk S0 DR StB       | StD, S1 => mk S0 DR StD end.
Local Notation tm := tm_1RB____1LC1LB_0LC1RD_0RB0RD.

Definition i0_1RB____1LC1LB_0LC1RD_0RB0RD : tern := (tD0 tE).
Definition Wf_1RB____1LC1LB_0LC1RD_0RB0RD : tern -> list Sym := Tw [S0;S0] [S0;S1] [S1;S1] [S1].

Lemma boot_1RB____1LC1LB_0LC1RD_0RB0RD :
  stepn tm 8 InitES = Some (lift (StC, ([], S1, Wf_1RB____1LC1LB_0LC1RD_0RB0RD i0_1RB____1LC1LB_0LC1RD_0RB0RD))).
Proof.
  assert (H : match csteps tm 8 c0 with
              | Some c => ceqb c (StC, ([], S1, Wf_1RB____1LC1LB_0LC1RD_0RB0RD i0_1RB____1LC1LB_0LC1RD_0RB0RD))
              | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 8 c0) as [c|] eqn:E; [| discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

Lemma bq_1RB____1LC1LB_0LC1RD_0RB0RD : forall n c, 0 < n < 8 ->
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

Theorem iqh_1RB____1LC1LB_0LC1RD_0RB0RD : iqh tm.
Proof.
  exact (Ter3Wall.ter3wall_qh tm StC StD StB 8 i0_1RB____1LC1LB_0LC1RD_0RB0RD
           eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
           ltac:(intro q; destruct q; auto)
           ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
           ltac:(vm_compute; reflexivity)
           Wf_1RB____1LC1LB_0LC1RD_0RB0RD tsuccT ter_step_one
           boot_1RB____1LC1LB_0LC1RD_0RB0RD bq_1RB____1LC1LB_0LC1RD_0RB0RD).
Qed.

Theorem nonhalt_1RB____1LC1LB_0LC1RD_0RB0RD : NonHalt tm.
Proof. apply (proj1 iqh_1RB____1LC1LB_0LC1RD_0RB0RD). Qed.
