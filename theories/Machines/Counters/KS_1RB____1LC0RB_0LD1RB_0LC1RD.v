(** * KS_1RB____1LC0RB_0LD1RB_0LC1RD: 1RB---_1LC0RB_0LD1RB_0LC1RD boards as [iqh].

    [StA]'s [S1] transition is undefined and nothing targets [StA], so [StA]
    fires exactly once, at configuration index 0: the machine QUASIHALTS with
    score 1 and [NeverQuasiHaltsSt] is false for it.  The three defined
    states are the alternating-return wall bouncer of [Counters/KpWallScan.v]
    with roles [qR = StB], [qQ = StC], [qP = StD], so the whole board is
    that closer plus five [vm_compute] facts.

    Read at [(qQ, ([], S1, Kp p))] the lap is [2j + 2] for an even carry
    length [j] and [2j + 4] for an odd one -- the "PARITY-AFFINE" reading of
    [tools/closeout/residue_map.tsv].  The return sweep alternates
    [StC]/[StD] and the two do NOT agree at the wall, which is why this
    row needs [KpWallScan] rather than a [Checkers/LapDecider.v] chain.

    [Print Assumptions] = [functional_extensionality_dep] only. *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Census Require Import TNF_QH.
From BBB4.Checkers Require Import ReachStI.
From BBB4.Counters Require Import WTape LapGlue LapGlueQuiet MonoCounter
                                  KpCounter.
From BBB4.Counters Require KpWallScan.
Import ListNotations.

Definition mk (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).

(** 1RB---_1LC0RB_0LD1RB_0LC1RD *)
Definition tm_1RB____1LC0RB_0LD1RB_0LC1RD : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DR StB       | StA, S1 => None
  | StB, S0 => mk S1 DL StC       | StB, S1 => mk S0 DR StB
  | StC, S0 => mk S0 DL StD       | StC, S1 => mk S1 DR StB
  | StD, S0 => mk S0 DL StC       | StD, S1 => mk S1 DR StD end.
Local Notation tm := tm_1RB____1LC0RB_0LD1RB_0LC1RD.

Lemma boot_1RB____1LC0RB_0LD1RB_0LC1RD :
  stepn tm 2 InitES = Some (lift (StC, ([], S1, Kp 1))).
Proof.
  assert (H : match csteps tm 2 c0 with
              | Some c => ceqb c (StC, ([], S1, Kp 1)) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 2 c0) as [c|] eqn:E; [| discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

Lemma bq_1RB____1LC0RB_0LD1RB_0LC1RD : forall n c, 0 < n < 2 ->
  stepn tm n InitES = Some c -> fst c <> StA.
Proof.
  intros n c Hn Hc.
  refine (bootquiet_chk_sound tm StA 1 1 _ n c _ Hc);
    [vm_compute; reflexivity | lia].
Qed.

(** The census R_QH predicate, stated locally so [tools/closeout/inventory.py]
    can verify it is literally the intended triple rather than trusting a name. *)
Definition iqh (tm : TM) : Prop :=
  NonHalt tm /\ QHBound 2000 tm /\ QuasiHaltsSt tm.

Theorem iqh_1RB____1LC0RB_0LD1RB_0LC1RD : iqh tm.
Proof.
  exact (KpWallScan.kpwallscan_qh tm StB StC StD 2 1
           eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
           ltac:(intro q; destruct q; auto)
           ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
           ltac:(vm_compute; reflexivity)
           boot_1RB____1LC0RB_0LD1RB_0LC1RD bq_1RB____1LC0RB_0LD1RB_0LC1RD).
Qed.

Theorem nonhalt_1RB____1LC0RB_0LD1RB_0LC1RD : NonHalt tm.
Proof. apply (proj1 iqh_1RB____1LC0RB_0LD1RB_0LC1RD). Qed.
