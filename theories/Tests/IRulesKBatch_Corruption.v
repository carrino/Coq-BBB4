(** * IRulesKBatch_Corruption: negative controls for the multi-decrement board.

    The general step-size IRules board (theories/Machines/IRulesK_Batch_*.v)
    is generated data: TM + [IRCert] literals transcribed from upstream v3
    certificates, each closed by one [vm_compute] through
    [MetaK.irulesk_check_neverqh].  These controls show the general-delta
    checker actually discriminates -- corrupting any ingredient of a
    passing instance, at the applier's binding-run / survival / step-size
    checks OR at the machine, flips the result to [false].

    Base instance: [1RB---_0LC0LB_1RC0RD_1LB1LA] (boarded in
    IRulesK_Batch_01): anchor 1,406,217, k0 1023, map k -> 2k+1, two
    rules; rule 1 [mkRule StC S0 [] [(S0, RV 4 1); (S1, RV -2 3)]] is the
    genuine multi-decrement (a +4 increment beside a -2 drain).

    Applier-level controls (fast; exercise [ruleK_apply] / [appK_side]
    directly on rule 1 at a concrete matching configuration):

    - [apply_good]: the genuine (rule, config) applies -- the -2 run
      drains to [lb - d = 1], the +4 run steps to [5 + 4*3 = 17].
    - [nondividing_rejected]: a config where the binding run's
      [e - lb = 8 - 3 = 5] is NOT divisible by [d = 2] leaves no binding
      run ([find_binding = None]).
    - [lb_below_delta_rejected]: dropping the drain run's [lb] to [1 < d]
      would land it on [lb - d = -1 < 0]; the [- d <=? lb] guard rejects.
    - [survive_violated_rejected]: forcing an over-large count
      [Rex = 5] (the honest one is 3) makes the -2 run fail to survive
      [R] rounds ([e + d*Rex = 7 - 10 = -3 < lb + d = 1]); [appK_side]
      rejects it, and [survive_ok] shows the honest [Rex = 3] passes.

    Whole-checker controls (at fuel 2000; the genuine pair already passes
    there -- [good_accepted_lowfuel] -- so rejection is discrimination,
    not fuel exhaustion.  A corrupted rule/replay never closes, so a high
    fuel would burn it on a growing symbolic state):

    - [mutant_tm_rejected]: one flipped transition (B0: 0LC -> 1LC)
      breaks rule 0's validation.
    - [delta_demoted_rejected]: demoting the -2 drain to -1 (the v1
      engine's only step size) no longer matches the machine's genuine
      two-step decrement. *)

From Coq Require Import ZArith List.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Checkers.IRules Require Import Expr RLE Engine Rules Meta RulesK MetaK.
Import ListNotations.
Open Scope Z_scope.

Definition mk (w : Sym) (d : Dir) (n : St) : option Trans :=
  Some (mkTrans w d n).

(** ** The genuine machine, certificate, and the multi-decrement rule *)

Definition tm_good : TM := fun q s =>
  match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => None
  | StB, S0 => mk S0 DL StC | StB, S1 => mk S0 DL StB
  | StC, S0 => mk S1 DR StC | StC, S1 => mk S0 DR StD
  | StD, S0 => mk S1 DL StB | StD, S1 => mk S1 DL StA
  end.

Definition cert_good : IRCert := mkIRCert
  1406217%nat (1023) (1) (2) (1) StD S0
  [(S0, 0, 1); (S1, 2, 0)]
  []
  [ mkRule StB S0 [(S1, RV (-1) (2))] [(S1, RV (1) (1))];
    mkRule StC S0 [] [(S0, RV (4) (1)); (S1, RV (-2) (3))] ].

Definition rule1 : Rule :=
  mkRule StC S0 [] [(S0, RV (4) (1)); (S1, RV (-2) (3))].

(** A concrete configuration [rule1] matches: binding run [(S1, 7)] has
    [e - lb = 4] divisible by [d = 2], so [R = 3]. *)
Definition cfg_good : SCfg :=
  mkSCfg StC S0 [] [(S0, econst 5); (S1, econst 7)].

Definition k_applies (lo : list Z) (r : Rule) (c : SCfg) : bool :=
  match ruleK_apply lo r c with Some _ => true | None => false end.

Definition k_appside (lo : list Z) (Rex : Expr) (rr : list RRun)
    (mr : list SRun) : bool :=
  match appK_side lo Rex rr mr with Some _ => true | None => false end.

(** ** Applier-level positive controls *)

Lemma apply_good : k_applies [1] rule1 cfg_good = true.
Proof. vm_compute. reflexivity. Qed.

Lemma survive_ok :
  k_appside [1] (econst 3) [(S1, RV (-2) (3))] [(S1, econst 7)] = true.
Proof. vm_compute. reflexivity. Qed.

(** ** Corruption 1: the binding run points at a non-dividing run *)

Definition cfg_nondiv : SCfg :=
  mkSCfg StC S0 [] [(S0, econst 5); (S1, econst 8)].

Lemma nondividing_rejected : k_applies [1] rule1 cfg_nondiv = false.
Proof. vm_compute. reflexivity. Qed.

(** ** Corruption 2: [lb] lowered below the step so the drain goes negative *)

Definition rule1_lblow : Rule :=
  mkRule StC S0 [] [(S0, RV (4) (1)); (S1, RV (-2) (1))].

Lemma lb_below_delta_rejected : k_applies [1] rule1_lblow cfg_good = false.
Proof. vm_compute. reflexivity. Qed.

(** ** Corruption 3: the survive-R-rounds premise violated (over-count) *)

Lemma survive_violated_rejected :
  k_appside [1] (econst 5) [(S1, RV (-2) (3))] [(S1, econst 7)] = false.
Proof. vm_compute. reflexivity. Qed.

(** ** Whole-checker controls (fuel 2000) *)

Lemma good_accepted : irulesk_check_neverqh tm_good cert_good 300000 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma good_accepted_lowfuel :
  irulesk_check_neverqh tm_good cert_good 2000 = true.
Proof. vm_compute. reflexivity. Qed.

(** ** Corruption 4: a flipped transition (B0: 0LC -> 1LC) *)

Definition tm_mut : TM := fun q s =>
  match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => None
  | StB, S0 => mk S1 DL StC | StB, S1 => mk S0 DL StB
  | StC, S0 => mk S1 DR StC | StC, S1 => mk S0 DR StD
  | StD, S0 => mk S1 DL StB | StD, S1 => mk S1 DL StA
  end.

Lemma mutant_tm_rejected : irulesk_check_neverqh tm_mut cert_good 2000 = false.
Proof. vm_compute. reflexivity. Qed.

(** ** Corruption 5: the -2 drain demoted to -1 (the v1 engine's only step) *)

Definition cert_demoted : IRCert := mkIRCert
  1406217%nat (1023) (1) (2) (1) StD S0
  [(S0, 0, 1); (S1, 2, 0)]
  []
  [ mkRule StB S0 [(S1, RV (-1) (2))] [(S1, RV (1) (1))];
    mkRule StC S0 [] [(S0, RV (4) (1)); (S1, RV (-1) (3))] ].

Lemma delta_demoted_rejected :
  irulesk_check_neverqh tm_good cert_demoted 2000 = false.
Proof. vm_compute. reflexivity. Qed.
