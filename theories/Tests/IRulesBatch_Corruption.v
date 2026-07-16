(** * IRulesBatch_Corruption: negative controls for the mass-board.

    The IRules mass-board (theories/Machines/IRules_Batch_*.v) is
    generated data: TM + [IRCert] literals transcribed from upstream
    certificates, each closed by one [vm_compute] through
    [irules_check_neverqh].  These controls demonstrate the checker
    actually discriminates: corrupting any ingredient of a passing
    instance -- the machine, the meta map, the anchor -- flips the
    check to [false].

    Base instance: 1RB1RD_1RC1RB_1LC1LA_0RC0RD (boarded in
    IRules_Batch_*, same certificate as [IRules_Examples.tm_ir1]):
    anchor 1,245,560, k0 1822, meta map k -> 3k + 1, one rule.

    - [mutant_tm_rejected]: one flipped transition (D1: 0RD -> 1RD)
      makes [irules_check_neverqh] return [false] outright.
    - [wrong_meta_map_rejected]: perturbing the meta map to
      k -> 3k + 2 (b = 1 -> 2) makes the check [<> true].
    - [wrong_anchor_rejected]: an off-by-one anchor step makes the
      check [<> true].

    Fuel note: the meta-map control runs at fuel 2000 rather than
    the boarding fuel 300000.  A corrupted map never closes the
    meta-cycle, so the replay burns its entire fuel with a growing
    symbolic state (>12 GB at fuel 300000).  [good_accepted_lowfuel]
    shows the genuine pair already passes at fuel 2000, so rejection
    at that same fuel is a real discrimination, not fuel
    exhaustion. *)

From Coq Require Import ZArith List.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Checkers.IRules Require Import Expr RLE Engine Rules Meta.
Import ListNotations.
Open Scope Z_scope.

Definition mk (w : Sym) (d : Dir) (n : St) : option Trans :=
  Some (mkTrans w d n).

(** The genuine machine and certificate (as boarded). *)

Definition tm_good : TM := fun q s =>
  match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S1 DR StD
  | StB, S0 => mk S1 DR StC | StB, S1 => mk S1 DR StB
  | StC, S0 => mk S1 DL StC | StC, S1 => mk S1 DL StA
  | StD, S0 => mk S0 DR StC | StD, S1 => mk S0 DR StD
  end.

Definition cert_good : IRCert := mkIRCert
  1245560%nat 1822 3 3 1 StC S0
  [(S1, 1, 0)]
  []
  [mkRule StC S1 [(S1, RV (-1) 2)] [(S1, RV 3 1)]].

(** Control: the genuine pair passes (same instance as the batch). *)

Lemma good_accepted :
  irules_check_neverqh tm_good cert_good 300000 = true.
Proof. vm_compute. reflexivity. Qed.

(** The genuine pair also passes at the low fuel used by the
    meta-map control below. *)
Lemma good_accepted_lowfuel :
  irules_check_neverqh tm_good cert_good 2000 = true.
Proof. vm_compute. reflexivity. Qed.

(** ** Mutant machine: flip one transition (D reading 1: 0RD -> 1RD).
    The certificate no longer describes this machine; the checker
    must reject. *)

Definition tm_mut : TM := fun q s =>
  match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S1 DR StD
  | StB, S0 => mk S1 DR StC | StB, S1 => mk S1 DR StB
  | StC, S0 => mk S1 DL StC | StC, S1 => mk S1 DL StA
  | StD, S0 => mk S0 DR StC | StD, S1 => mk S1 DR StD
  end.

Lemma mutant_tm_rejected :
  irules_check_neverqh tm_mut cert_good 300000 = false.
Proof. vm_compute. reflexivity. Qed.

(** ** Wrong meta map: k -> 3k + 2 instead of 3k + 1.  The symbolic
    replay can no longer close the meta-cycle on the claimed target
    template. *)

Definition cert_badmap : IRCert := mkIRCert
  1245560%nat 1822 3 3 2 StC S0
  [(S1, 1, 0)]
  []
  [mkRule StC S1 [(S1, RV (-1) 2)] [(S1, RV 3 1)]].

Lemma wrong_meta_map_rejected :
  irules_check_neverqh tm_good cert_badmap 2000 <> true.
Proof. vm_compute. discriminate. Qed.

(** ** Wrong anchor: one step late.  The re-simulated configuration
    no longer matches the claimed template instance C(k0). *)

Definition cert_badanchor : IRCert := mkIRCert
  1245561%nat 1822 3 3 1 StC S0
  [(S1, 1, 0)]
  []
  [mkRule StC S1 [(S1, RV (-1) 2)] [(S1, RV 3 1)]].

Lemma wrong_anchor_rejected :
  irules_check_neverqh tm_good cert_badanchor 300000 <> true.
Proof. vm_compute. discriminate. Qed.
