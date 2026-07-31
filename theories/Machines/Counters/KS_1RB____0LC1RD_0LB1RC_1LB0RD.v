(** * KS_1RB____0LC1RD_0LB1RC_1LB0RD: 1RB---_0LC1RD_0LB1RC_1LB0RD boards as [iqh].

    [StA]'s [S1] transition is undefined and nothing targets [StA], so [StA]
    fires exactly once, at configuration index 0: the machine QUASIHALTS with
    score 1 and [NeverQuasiHaltsSt] is false for it.  The three defined
    states are the alternating-return wall bouncer of [Counters/KpWallScan.v]
    with roles [qR = StD], [qQ = StB], [qP = StC], so the whole board is
    that closer plus five [vm_compute] facts.

    Read at [(qQ, ([], S1, Kp p))] the lap is [2j + 2] for an even carry
    length [j] and [2j + 4] for an odd one -- the "PARITY-AFFINE" reading of
    [tools/closeout/residue_map.tsv].  The return sweep alternates
    [StB]/[StC] and the two do NOT agree at the wall, which is why this
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

(** 1RB---_0LC1RD_0LB1RC_1LB0RD *)
Definition tm_1RB____0LC1RD_0LB1RC_1LB0RD : TM := fun q s => match q, s with
  | StA, S0 => mk S1 DR StB       | StA, S1 => None
  | StB, S0 => mk S0 DL StC       | StB, S1 => mk S1 DR StD
  | StC, S0 => mk S0 DL StB       | StC, S1 => mk S1 DR StC
  | StD, S0 => mk S1 DL StB       | StD, S1 => mk S0 DR StD end.
Local Notation tm := tm_1RB____0LC1RD_0LB1RC_1LB0RD.

Lemma boot_1RB____0LC1RD_0LB1RC_1LB0RD :
  stepn tm 6 InitES = Some (lift (StB, ([], S1, Kp 1))).
Proof.
  assert (H : match csteps tm 6 c0 with
              | Some c => ceqb c (StB, ([], S1, Kp 1)) | None => false end = true)
    by (vm_compute; reflexivity).
  destruct (csteps tm 6 c0) as [c|] eqn:E; [| discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E). f_equal. apply ceqb_lift. exact H.
Qed.

Lemma bq_1RB____0LC1RD_0LB1RC_1LB0RD : forall n c, 0 < n < 6 ->
  stepn tm n InitES = Some c -> fst c <> StA.
Proof.
  intros n c Hn Hc.
  refine (bootquiet_chk_sound tm StA 1 5 _ n c _ Hc);
    [vm_compute; reflexivity | lia].
Qed.

(** The census R_QH predicate, stated locally so [tools/closeout/inventory.py]
    can verify it is literally the intended triple rather than trusting a name. *)
Definition iqh (tm : TM) : Prop :=
  NonHalt tm /\ QHBound 2000 tm /\ QuasiHaltsSt tm.

Theorem iqh_1RB____0LC1RD_0LB1RC_1LB0RD : iqh tm.
Proof.
  exact (KpWallScan.kpwallscan_qh tm StD StB StC 6 1
           eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
           ltac:(intro q; destruct q; auto)
           ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
           ltac:(vm_compute; reflexivity)
           boot_1RB____0LC1RD_0LB1RC_1LB0RD bq_1RB____0LC1RD_0LB1RC_1LB0RD).
Qed.

Theorem nonhalt_1RB____0LC1RD_0LB1RC_1LB0RD : NonHalt tm.
Proof. apply (proj1 iqh_1RB____0LC1RD_0LB1RC_1LB0RD). Qed.
