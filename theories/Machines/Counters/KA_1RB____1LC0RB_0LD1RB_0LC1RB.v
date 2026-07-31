(** * KA_1RB____1LC0RB_0LD1RB_0LC1RB: 1RB---_1LC0RB_0LD1RB_0LC1RB boards as [iqh].

    [StA]'s [S1] transition is undefined and nothing targets [StA], so [StA]
    fires exactly once, at configuration index 0: the machine QUASIHALTS with
    score 1 and [NeverQuasiHaltsSt] is false for it.  The three defined
    states are the alternating-return wall bouncer of [Counters/KpWallAlt.v]
    with roles [qD = StB], [qA = StC], [qB = StD], so the whole board is
    that closer plus five [vm_compute] facts.

    Read at [(qD, ([S1], S0, Kp p))] the lap is [2j + 6] in the carry length
    [j], affine on both branches; the return sweep alternates [StC]/[StD],
    which is why this row needs [KpWallAlt] rather than a
    [Checkers/LapDecider.v] chain (an [SCycL] unit must return to its own
    state, and this one does so only every second cell).

    [Print Assumptions] = [functional_extensionality_dep] only. *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Census Require Import TNF_QH.
From BBB4.Checkers Require Import ReachStI.
From BBB4.Counters Require Import WTape LapGlue LapGlueQuiet MonoCounter
                                  KpCounter.
From BBB4.Counters Require KpWallAlt.
Import ListNotations.

Definition mk (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).

(** 1RB---_1LC0RB_0LD1RB_0LC1RB *)
Definition tm_1RB____1LC0RB_0LD1RB_0LC1RB : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DR StB       | StA, S1 => None
  | StB, S0 => mk S1 DL StC       | StB, S1 => mk S0 DR StB
  | StC, S0 => mk S0 DL StD       | StC, S1 => mk S1 DR StB
  | StD, S0 => mk S0 DL StC       | StD, S1 => mk S1 DR StB end.
Local Notation tm := tm_1RB____1LC0RB_0LD1RB_0LC1RB.

Lemma boot_1RB____1LC0RB_0LD1RB_0LC1RB :
  stepn tm 7 InitES = Some (lift (StB, ([S1], S0, Kp 1))).
Proof.
  assert (H : match csteps tm 7 c0 with
              | Some c => ceqb c (StB, ([S1], S0, Kp 1)) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 7 c0) as [c|] eqn:E; [| discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

Lemma bq_1RB____1LC0RB_0LD1RB_0LC1RB : forall n c, 0 < n < 7 ->
  stepn tm n InitES = Some c -> fst c <> StA.
Proof.
  intros n c Hn Hc.
  refine (bootquiet_chk_sound tm StA 1 6 _ n c _ Hc);
    [vm_compute; reflexivity | lia].
Qed.

(** The census R_QH predicate, stated locally so [tools/closeout/inventory.py]
    can verify it is literally the intended triple rather than trusting a name. *)
Definition iqh (tm : TM) : Prop :=
  NonHalt tm /\ QHBound 2000 tm /\ QuasiHaltsSt tm.

Theorem iqh_1RB____1LC0RB_0LD1RB_0LC1RB : iqh tm.
Proof.
  exact (KpWallAlt.kpwallalt_qh tm StB StC StD 7 1
           eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
           ltac:(intro q; destruct q; auto)
           ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
           ltac:(vm_compute; reflexivity)
           boot_1RB____1LC0RB_0LD1RB_0LC1RB bq_1RB____1LC0RB_0LD1RB_0LC1RB).
Qed.

Theorem nonhalt_1RB____1LC0RB_0LD1RB_0LC1RB : NonHalt tm.
Proof. apply (proj1 iqh_1RB____1LC0RB_0LD1RB_0LC1RB). Qed.
