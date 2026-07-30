(** * KQ_1RB____1LC0RD_0LC1RD_1LC0RB: 1RB---_1LC0RD_0LC1RD_1LC0RB boards as [iqh].

    [StA]'s [S1] transition is undefined and nothing targets [StA], so [StA]
    fires exactly once, at configuration index 0: the machine QUASIHALTS with
    score 1 and [NeverQuasiHaltsSt] is false for it.  The three defined
    states are the plain-counter wall bouncer of [Counters/KpWallQH.v] with
    roles [qW = StC], [qR1 = StD], [qR2 = StB], so the whole board is that
    closer plus five [vm_compute] facts.

    Issue #61 files this row under "no interior j = S j' chain"; the gate was
    the emitter's anchor search.  Read at [(qW, ([], S1, Kp p))] the lap is
    [2 + 2j], affine on both branches -- see [tools/counters/radix_infer.py].

    [Print Assumptions] = [functional_extensionality_dep] only. *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Census Require Import TNF_QH.
From BBB4.Checkers Require Import ReachStI.
From BBB4.Counters Require Import WTape LapGlue LapGlueQuiet MonoCounter
                                  KpCounter.
From BBB4.Counters Require KpWallQH.
Import ListNotations.

Definition mk (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).

(** 1RB---_1LC0RD_0LC1RD_1LC0RB *)
Definition tm_1RB____1LC0RD_0LC1RD_1LC0RB : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DR StB   | StA, S1 => None
  | StB, S0 => mk S1 DL StC   | StB, S1 => mk S0 DR StD
  | StC, S0 => mk S0 DL StC   | StC, S1 => mk S1 DR StD
  | StD, S0 => mk S1 DL StC   | StD, S1 => mk S0 DR StB end.
Local Notation tm := tm_1RB____1LC0RD_0LC1RD_1LC0RB.

Lemma boot_1RB____1LC0RD_0LC1RD_1LC0RB : stepn tm 2 InitES = Some (lift (StC, ([], S1, Kp 1))).
Proof.
  assert (H : match csteps tm 2 c0 with
              | Some c => ceqb c (StC, ([], S1, Kp 1)) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 2 c0) as [c|] eqn:E; [| discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

Lemma bq_1RB____1LC0RD_0LC1RD_1LC0RB : forall n c, 0 < n < 2 ->
  stepn tm n InitES = Some c -> fst c <> StA.
Proof.
  intros n c Hn Hs.
  destruct (stepn_csteps tm n c Hs) as (cc & Hcc & Hl).
  rewrite <- Hl, lift_state.
  assert (n = 1) as -> by lia. vm_compute in Hcc; injection Hcc as <-; discriminate.
Qed.

(** The census R_QH predicate, stated locally so [tools/closeout/inventory.py]
    can verify it is literally the intended triple rather than trusting a name. *)
Definition iqh (tm : TM) : Prop :=
  NonHalt tm /\ QHBound 2000 tm /\ QuasiHaltsSt tm.

Theorem iqh_1RB____1LC0RD_0LC1RD_1LC0RB : iqh tm.
Proof.
  exact (KpWallQH.kpwall_qh tm StC StD StB 2
           eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
           ltac:(intro q; destruct q; auto)
           ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
           ltac:(vm_compute; reflexivity)
           boot_1RB____1LC0RD_0LC1RD_1LC0RB bq_1RB____1LC0RD_0LC1RD_1LC0RB).
Qed.
