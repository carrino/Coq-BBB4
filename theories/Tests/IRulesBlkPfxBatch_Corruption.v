(** Negative controls for the Phase-2 block-prefix checker
    ([MetaBlkPfx.irulesblkpfx_check_neverqh]): tampered certificates
    MUST be rejected.  Each mutant below alters ONE mechanism-bearing
    field of a genuine boarded certificate; the checker must return
    [false].  Honest-pass controls at the SAME reduced fuel (3000)
    show the rejections are caused by the tamper, not the fuel.

    Donors: 1RB0LC_0LA1RA_1LA0RD_1LD1RC (v6: rulepfx + rmdok, 2 blocks,
    5 prefix rules; Batch_01) and 1RB1RA_1LC0RB_1LB1LD_0RA1RB (v7: adds
    a rulerunm lattice run [BVm 2 3 2 1]; Batch_05).

    Python-mirror verdicts for the corresponding .cert mutations
    (irulesblkpfx_prover_ext.py): all rejected (see PHASE2_DESIGN.md
    section 5's differential table for the measured classes). *)

From Coq Require Import ZArith List.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Checkers Require Import Cycle.
From BBB4.Checkers.IRules Require Import Expr RLE Engine Rules Meta RulesK
     EngineK RulesBlk MetaBlk EngineKS RulesBlkPfx MetaBlkPfx.
Import ListNotations.
Open Scope Z_scope.
Definition mkc (w : Sym) (d : Dir) (n : St) : option Trans :=
  Some (mkTrans w d n).

(** ** The two donor machines *)

Definition tmc_v6 : TM := fun q s =>
  match q, s with
  | StA, S0 => mkc S1 DR StB
  | StA, S1 => mkc S0 DL StC
  | StB, S0 => mkc S0 DL StA
  | StB, S1 => mkc S1 DR StA
  | StC, S0 => mkc S1 DL StA
  | StC, S1 => mkc S0 DR StD
  | StD, S0 => mkc S1 DL StD
  | StD, S1 => mkc S1 DR StC
  end.

Definition tmc_v7 : TM := fun q s =>
  match q, s with
  | StA, S0 => mkc S1 DR StB
  | StA, S1 => mkc S1 DR StA
  | StB, S0 => mkc S1 DL StC
  | StB, S1 => mkc S0 DR StB
  | StC, S0 => mkc S1 DL StB
  | StC, S1 => mkc S1 DL StD
  | StD, S0 => mkc S0 DR StA
  | StD, S1 => mkc S1 DR StB
  end.

(** The genuine certificates (copied verbatim from the batches). *)
Definition certc_v6 : BIRCertP := mkBIRCertP
  694011%nat (511) (8) (2) (1) StB S0
  [(2%nat, [S0; S1]);
   (3%nat, [S1; S0])]
  [(1%nat, (2), (1))]
  []
  [mkBRuleP StD S1 [(0%nat, BC (1)); (3%nat, BV (1) (1)); (1%nat, BV (0) (1))] [(1%nat, BV (-2) (3))] (true, true);
   mkBRuleP StC S1 [(3%nat, BV (1) (2)); (1%nat, BV (0) (1))] [(0%nat, BC (1)); (3%nat, BV (-1) (2)); (1%nat, BC (1))] (true, true);
   mkBRuleP StC S1 [(3%nat, BV (2) (9)); (1%nat, BV (-2) (4))] [] (true, false);
   mkBRuleP StD S0 [(2%nat, BV (1) (2))] [(3%nat, BV (-1) (2)); (1%nat, BC (1))] (true, true);
   mkBRuleP StD S1 [(2%nat, BV (1) (1))] [(1%nat, BV (-2) (3))] (true, true)].

Definition certc_v7 : BIRCertP := mkBIRCertP
  698027%nat (1023) (4) (2) (1) StB S0
  []
  [(1%nat, (1), (0))]
  []
  [mkBRuleP StC S0 [(0%nat, BV (-2) (3)); (1%nat, BV (0) (1))] [(1%nat, BV (2) (1))] (true, true);
   mkBRuleP StC S1 [(1%nat, BV (-1) (2))] [(1%nat, BVm (2) (3) (2) (1))] (true, false)].

(** ** Honest-pass controls at the reduced fuel used below *)

Example honest_v6_reduced_fuel :
  irulesblkpfx_check_neverqh tmc_v6 certc_v6 200000 3000 = true.
Proof. vm_compute. reflexivity. Qed.

Example honest_v7_reduced_fuel :
  irulesblkpfx_check_neverqh tmc_v7 certc_v7 200000 3000 = true.
Proof. vm_compute. reflexivity. Qed.

(** ** v6 mutants (each MUST be rejected) *)

(** Prefix flags of rule 3 flipped (true,false) -> (false,true): the
    L side loses its prefix licence (exact-match + non-sentinel
    required) and the empty R side becomes an opaque prefix. *)
Definition certc_v6_pfxflip : BIRCertP := mkBIRCertP
  694011%nat (511) (8) (2) (1) StB S0
  [(2%nat, [S0; S1]);
   (3%nat, [S1; S0])]
  [(1%nat, (2), (1))]
  []
  [mkBRuleP StD S1 [(0%nat, BC (1)); (3%nat, BV (1) (1)); (1%nat, BV (0) (1))] [(1%nat, BV (-2) (3))] (true, true);
   mkBRuleP StC S1 [(3%nat, BV (1) (2)); (1%nat, BV (0) (1))] [(0%nat, BC (1)); (3%nat, BV (-1) (2)); (1%nat, BC (1))] (true, true);
   mkBRuleP StC S1 [(3%nat, BV (2) (9)); (1%nat, BV (-2) (4))] [] (false, true);
   mkBRuleP StD S0 [(2%nat, BV (1) (2))] [(3%nat, BV (-1) (2)); (1%nat, BC (1))] (true, true);
   mkBRuleP StD S1 [(2%nat, BV (1) (1))] [(1%nat, BV (-2) (3))] (true, true)].

Example corrupt_v6_pfxflip :
  irulesblkpfx_check_neverqh tmc_v6 certc_v6_pfxflip 200000 3000 = false.
Proof. vm_compute. reflexivity. Qed.

(** Rule 1's binding-run lower bound 3 -> 2: shifts the v6 remainder
    [rmd = (e - lb) mod 2] parity, so the drained run ends at the wrong
    constant and the rule's replay cannot close. *)
Definition certc_v6_lb : BIRCertP := mkBIRCertP
  694011%nat (511) (8) (2) (1) StB S0
  [(2%nat, [S0; S1]);
   (3%nat, [S1; S0])]
  [(1%nat, (2), (1))]
  []
  [mkBRuleP StD S1 [(0%nat, BC (1)); (3%nat, BV (1) (1)); (1%nat, BV (0) (1))] [(1%nat, BV (-2) (2))] (true, true);
   mkBRuleP StC S1 [(3%nat, BV (1) (2)); (1%nat, BV (0) (1))] [(0%nat, BC (1)); (3%nat, BV (-1) (2)); (1%nat, BC (1))] (true, true);
   mkBRuleP StC S1 [(3%nat, BV (2) (9)); (1%nat, BV (-2) (4))] [] (true, false);
   mkBRuleP StD S0 [(2%nat, BV (1) (2))] [(3%nat, BV (-1) (2)); (1%nat, BC (1))] (true, true);
   mkBRuleP StD S1 [(2%nat, BV (1) (1))] [(1%nat, BV (-2) (3))] (true, true)].

Example corrupt_v6_lb :
  irulesblkpfx_check_neverqh tmc_v6 certc_v6_lb 200000 3000 = false.
Proof. vm_compute. reflexivity. Qed.

(** Block 2's cells [S0;S1] -> [S0;S0]: every hop/peel/template
    denotation through the table changes. *)
Definition certc_v6_blk : BIRCertP := mkBIRCertP
  694011%nat (511) (8) (2) (1) StB S0
  [(2%nat, [S0; S0]);
   (3%nat, [S1; S0])]
  [(1%nat, (2), (1))]
  []
  [mkBRuleP StD S1 [(0%nat, BC (1)); (3%nat, BV (1) (1)); (1%nat, BV (0) (1))] [(1%nat, BV (-2) (3))] (true, true);
   mkBRuleP StC S1 [(3%nat, BV (1) (2)); (1%nat, BV (0) (1))] [(0%nat, BC (1)); (3%nat, BV (-1) (2)); (1%nat, BC (1))] (true, true);
   mkBRuleP StC S1 [(3%nat, BV (2) (9)); (1%nat, BV (-2) (4))] [] (true, false);
   mkBRuleP StD S0 [(2%nat, BV (1) (2))] [(3%nat, BV (-1) (2)); (1%nat, BC (1))] (true, true);
   mkBRuleP StD S1 [(2%nat, BV (1) (1))] [(1%nat, BV (-2) (3))] (true, true)].

Example corrupt_v6_blk :
  irulesblkpfx_check_neverqh tmc_v6 certc_v6_blk 200000 3000 = false.
Proof. vm_compute. reflexivity. Qed.

(** Meta map a: 2 -> 3: the replayed cycle cannot reach the shifted
    want-template. *)
Definition certc_v6_meta : BIRCertP := mkBIRCertP
  694011%nat (511) (8) (3) (1) StB S0
  [(2%nat, [S0; S1]);
   (3%nat, [S1; S0])]
  [(1%nat, (2), (1))]
  []
  [mkBRuleP StD S1 [(0%nat, BC (1)); (3%nat, BV (1) (1)); (1%nat, BV (0) (1))] [(1%nat, BV (-2) (3))] (true, true);
   mkBRuleP StC S1 [(3%nat, BV (1) (2)); (1%nat, BV (0) (1))] [(0%nat, BC (1)); (3%nat, BV (-1) (2)); (1%nat, BC (1))] (true, true);
   mkBRuleP StC S1 [(3%nat, BV (2) (9)); (1%nat, BV (-2) (4))] [] (true, false);
   mkBRuleP StD S0 [(2%nat, BV (1) (2))] [(3%nat, BV (-1) (2)); (1%nat, BC (1))] (true, true);
   mkBRuleP StD S1 [(2%nat, BV (1) (1))] [(1%nat, BV (-2) (3))] (true, true)].

Example corrupt_v6_meta :
  irulesblkpfx_check_neverqh tmc_v6 certc_v6_meta 200000 3000 = false.
Proof. vm_compute. reflexivity. Qed.

(** Rule 3's L side loses its DRAIN run [(1, BV -2 4)] (load-bearing:
    the body consumes those cells): the prefix body must now read past
    its declared runs into the opaque rest, which the sentinel engine
    hard-fails (self-validation rejects).  NOTE deleting a trailing
    delta-0 run instead is ACCEPTED -- that mutant is a valid
    GENERALIZED rule (the run's content just joins the untouched
    opaque rest), measured and expected. *)
Definition certc_v6_readpast : BIRCertP := mkBIRCertP
  694011%nat (511) (8) (2) (1) StB S0
  [(2%nat, [S0; S1]);
   (3%nat, [S1; S0])]
  [(1%nat, (2), (1))]
  []
  [mkBRuleP StD S1 [(0%nat, BC (1)); (3%nat, BV (1) (1)); (1%nat, BV (0) (1))] [(1%nat, BV (-2) (3))] (true, true);
   mkBRuleP StC S1 [(3%nat, BV (1) (2)); (1%nat, BV (0) (1))] [(0%nat, BC (1)); (3%nat, BV (-1) (2)); (1%nat, BC (1))] (true, true);
   mkBRuleP StC S1 [(3%nat, BV (2) (9))] [] (true, false);
   mkBRuleP StD S0 [(2%nat, BV (1) (2))] [(3%nat, BV (-1) (2)); (1%nat, BC (1))] (true, true);
   mkBRuleP StD S1 [(2%nat, BV (1) (1))] [(1%nat, BV (-2) (3))] (true, true)].

Example corrupt_v6_readpast :
  irulesblkpfx_check_neverqh tmc_v6 certc_v6_readpast 200000 3000 = false.
Proof. vm_compute. reflexivity. Qed.

(** ** v7 mutants (the lattice run [BVm 2 3 2 1] of rule 2)

    NOTE the lenience class (PHASE2_DESIGN.md section 6): tampers that
    merely make the lattice rule STRUCTURALLY dead ([latt_ok] false --
    e.g. res 1->0 or mod 2->4, which verify.c rejects at parse time)
    are ACCEPTED by this checker: the dead rule still self-validates
    or the meta replay routes around it with plain engine steps, and
    everything actually verified remains true.  Soundness-preserving,
    non-canonical (measured: the res 1->0 mutant is accepted).  The
    negative controls below therefore tamper what the certificate
    CLAIMS: the lattice run's drain delta (rule validation must fail)
    and the meta map (the cycle target is wrong). *)

(** Lattice run delta 2 -> 4 (still a lattice multiple, so the guard
    passes): the rule body now claims it ends at [2w+1+4] instead of
    [2w+1+2]; the sentinel replay cannot reach the false end config. *)
Definition certc_v7_del : BIRCertP := mkBIRCertP
  698027%nat (1023) (4) (2) (1) StB S0
  []
  [(1%nat, (1), (0))]
  []
  [mkBRuleP StC S0 [(0%nat, BV (-2) (3)); (1%nat, BV (0) (1))] [(1%nat, BV (2) (1))] (true, true);
   mkBRuleP StC S1 [(1%nat, BV (-1) (2))] [(1%nat, BVm (4) (3) (2) (1))] (true, false)].

Example corrupt_v7_del :
  irulesblkpfx_check_neverqh tmc_v7 certc_v7_del 200000 3000 = false.
Proof. vm_compute. reflexivity. Qed.

(** Meta map a: 2 -> 1 (preconditions still hold: kmin <= kmin + 1):
    the cycle's want-template is wrong; the meta replay exhausts its
    fuel without matching. *)
Definition certc_v7_meta : BIRCertP := mkBIRCertP
  698027%nat (1023) (4) (1) (1) StB S0
  []
  [(1%nat, (1), (0))]
  []
  [mkBRuleP StC S0 [(0%nat, BV (-2) (3)); (1%nat, BV (0) (1))] [(1%nat, BV (2) (1))] (true, true);
   mkBRuleP StC S1 [(1%nat, BV (-1) (2))] [(1%nat, BVm (2) (3) (2) (1))] (true, false)].

Example corrupt_v7_meta :
  irulesblkpfx_check_neverqh tmc_v7 certc_v7_meta 200000 3000 = false.
Proof. vm_compute. reflexivity. Qed.
(** Mutant MACHINE under the genuine v6 certificate (StD,S1 write
    flipped): the anchor re-simulation cannot match the template. *)
Definition tmc_v6_mut : TM := fun q s =>
  match q, s with
  | StA, S0 => mkc S1 DR StB
  | StA, S1 => mkc S0 DL StC
  | StB, S0 => mkc S0 DL StA
  | StB, S1 => mkc S1 DR StA
  | StC, S0 => mkc S1 DL StA
  | StC, S1 => mkc S0 DR StD
  | StD, S0 => mkc S1 DL StD
  | StD, S1 => mkc S0 DR StC
  end.

Example corrupt_v6_machine :
  irulesblkpfx_check_neverqh tmc_v6_mut certc_v6 200000 3000 = false.
Proof. vm_compute. reflexivity. Qed.
