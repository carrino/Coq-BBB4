(** * IRules_Corruption: negative controls for the irules checker.

    The BBB corruption-suite discipline: mutate every load-bearing
    certificate field and require rejection.  The mutations cover
    each phase of the check -- static sanity, rule validation, the
    symbolic meta-cycle replay, and the anchor re-simulation.
    (Mutations that fail before the anchor phase are cheap; the
    anchor-phase ones re-simulate the 1.2M-step prefix.) *)

From Coq Require Import ZArith List.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Checkers.IRules Require Import Expr RLE Engine Rules Meta.
From BBB4.Machines Require Import IRules_Examples.
Import ListNotations.
Open Scope Z_scope.

(* k0 below kmin: static sanity. *)
Example ir_corrupt_k0 :
  irules_check_neverqh tm_ir1 (mkIRCert 1245560%nat 2 3 3 1 StC S0
    [(S1, 1, 0)] [] (c_rules cert_ir1)) 300000 = false.
Proof. vm_compute. reflexivity. Qed.

(* meta map not inward: kmin > a*kmin + b. *)
Example ir_corrupt_inward :
  irules_check_neverqh tm_ir1 (mkIRCert 1245560%nat 1822 3 0 1 StC S0
    [(S1, 1, 0)] [] (c_rules cert_ir1)) 5000 = false.
Proof. vm_compute. reflexivity. Qed.

(* insufficient kmin: the meta-cycle decrement can no longer prove
   its count stays >= 1, so the symbolic replay fails. *)
Example ir_corrupt_kmin :
  irules_check_neverqh tm_ir1 (mkIRCert 1245560%nat 1822 1 3 1 StC S0
    [(S1, 1, 0)] [] (c_rules cert_ir1)) 5000 = false.
Proof. vm_compute. reflexivity. Qed.

(* wrong meta map: the replay never matches C(2k + 1). *)
Example ir_corrupt_meta :
  irules_check_neverqh tm_ir1 (mkIRCert 1245560%nat 1822 3 2 1 StC S0
    [(S1, 1, 0)] [] (c_rules cert_ir1)) 5000 = false.
Proof. vm_compute. reflexivity. Qed.

(* corrupted rule delta: the fresh-variable replay lands on
   w + 3, not w + 2. *)
Example ir_corrupt_rule_delta :
  irules_check_neverqh tm_ir1 (mkIRCert 1245560%nat 1822 3 3 1 StC S0
    [(S1, 1, 0)] []
    [mkRule StC S1 [(S1, RV (-1) 2)] [(S1, RV 2 1)]]) 5000 = false.
Proof. vm_compute. reflexivity. Qed.

(* corrupted rule bound: with lb = 1 the rule's own decrement cannot
   keep its count provably >= 1 during the validation replay. *)
Example ir_corrupt_rule_lb :
  irules_check_neverqh tm_ir1 (mkIRCert 1245560%nat 1822 3 3 1 StC S0
    [(S1, 1, 0)] []
    [mkRule StC S1 [(S1, RV (-1) 1)] [(S1, RV 3 1)]]) 5000 = false.
Proof. vm_compute. reflexivity. Qed.

(* wrong anchor step: the re-simulated configuration is not C(k0). *)
Example ir_corrupt_anchor :
  irules_check_neverqh tm_ir1 (mkIRCert 1245561%nat 1822 3 3 1 StC S0
    [(S1, 1, 0)] [] (c_rules cert_ir1)) 300000 = false.
Proof. vm_compute. reflexivity. Qed.

(* wrong k0: template instance does not match the anchor tape. *)
Example ir_corrupt_k0_value :
  irules_check_neverqh tm_ir1 (mkIRCert 1245560%nat 1821 3 3 1 StC S0
    [(S1, 1, 0)] [] (c_rules cert_ir1)) 300000 = false.
Proof. vm_compute. reflexivity. Qed.

(* retargeted machine: tm_ir2's certificate on tm_ir1. *)
Example ir_corrupt_retarget :
  irules_check_neverqh tm_ir1 cert_ir2 5000 = false.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions tm_ir1_never_quasihalts.
Print Assumptions tm_ir2_never_quasihalts.
