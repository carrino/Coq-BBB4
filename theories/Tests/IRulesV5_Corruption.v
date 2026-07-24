(** Negative controls for the v5 end-match engine extension
    ([StreamEq.cseq] / [StreamEq.bend_eqb2] /
    [MetaBlkPfxV5.irulesblkpfx_check_neverqh_v5]) -- the ONE new trust
    surface of the v5-gap boards (theories/Machines/ListCV5Stage).  It
    MUST NOT accept anything the landed engine's soundness contract
    doesn't already justify.

    Three families, all [vm_compute]-closed:

    1. The new recogniser [cseq] in isolation: it ACCEPTS a genuine
       block re-encoding (the closing-vs-template shape the whole
       extension exists to recognise) and REJECTS non-cell-equal pairs
       (a rotated tail, an off-by-one pump) -- so it is not vacuously
       true.

    2. The v5 checker on a genuinely never-QH donor (its own boarded
       certificate): the extension is LOAD-BEARING (the landed
       [irulesblkpfx_check_neverqh] REFUSES the same machine+cert, the
       v5 checker accepts it), and every single-field cert mutation is
       REJECTED (block cells, meta map, a rule count).

    3. A halting machine and a mutant machine under the genuine cert are
       REJECTED (the anchor re-simulation / state coverage stay
       load-bearing under the v5 end-match).

    Donor: 0RB1LC_1RC1RD_1LD1RA_1LA0LC (v6, boarded as
    ListCV5Stage/LCV5_00.v [nqh_v5_00000]). *)

From Coq Require Import ZArith List Bool.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Checkers Require Import Cycle.
From BBB4.Checkers.IRules Require Import Expr RLE Engine Rules Meta RulesK
     EngineK RulesBlk MetaBlk EngineKS RulesBlkPfx MetaBlkPfx StreamEq
     MetaBlkPfxV5.
Import ListNotations.
Open Scope Z_scope.
Definition mkc (w : Sym) (d : Dir) (n : St) : option Trans :=
  Some (mkTrans w d n).

(** ** 1. The new recogniser [cseq] in isolation

    Block 2 denotes the cell word [S0;S1].  At [k = k0 + t] each list
    below denotes a one-pump tape; [cseq] decides equality for ALL
    [k >= 4]. *)

Definition tblc : BTbl := mk_tbl [(2%nat, [S0; S1])].

(** [b2^(1+k)] vs [b2^k . b0 . b1] -- the LAST [b0.b1] respells one more
    copy of [b2], so they are cell-equal for every k.  This is exactly
    the closing-vs-template re-encoding the v5 end-match must accept and
    the landed [bstreams_eq] refuses (it cannot expand the variable
    [b2^k]). *)
Example cseq_accepts_reencoding :
  cseq tblc [4]
    [(2%nat, {| e_c0 := 1; e_cf := [1] |})]
    [(2%nat, {| e_c0 := 0; e_cf := [1] |});
     (0%nat, {| e_c0 := 1; e_cf := [] |});
     (1%nat, {| e_c0 := 1; e_cf := [] |})] = true.
Proof. vm_compute. reflexivity. Qed.

(** The landed [bstreams_eq] REFUSES that same pair (it only expands
    constant-count multi-cell blocks): the v5 extension is why the gap
    machines board at all. *)
Example bstreams_eq_refuses_reencoding :
  bstreams_eq tblc [4]
    [(2%nat, {| e_c0 := 1; e_cf := [1] |})]
    [(2%nat, {| e_c0 := 0; e_cf := [1] |});
     (0%nat, {| e_c0 := 1; e_cf := [] |});
     (1%nat, {| e_c0 := 1; e_cf := [] |})] = false.
Proof. vm_compute. reflexivity. Qed.

(** Rotated tail [b1 . b0] = [S1;S0] != [S0;S1]: NOT cell-equal, MUST
    be rejected. *)
Example cseq_rejects_rotated_tail :
  cseq tblc [4]
    [(2%nat, {| e_c0 := 1; e_cf := [1] |})]
    [(2%nat, {| e_c0 := 0; e_cf := [1] |});
     (1%nat, {| e_c0 := 1; e_cf := [] |});
     (0%nat, {| e_c0 := 1; e_cf := [] |})] = false.
Proof. vm_compute. reflexivity. Qed.

(** Off-by-one pump [b2^(1+k)] vs [b2^(2+k)]: equal length coefficient
    but different constant -- MUST be rejected. *)
Example cseq_rejects_offby_one :
  cseq tblc [4]
    [(2%nat, {| e_c0 := 1; e_cf := [1] |})]
    [(2%nat, {| e_c0 := 2; e_cf := [1] |})] = false.
Proof. vm_compute. reflexivity. Qed.

(** Different pump RATE [b2^k] vs [b2^(2k)]: MUST be rejected (the
    length check / t=1 check fires). *)
Example cseq_rejects_pump_rate :
  cseq tblc [4]
    [(2%nat, {| e_c0 := 0; e_cf := [1] |})]
    [(2%nat, {| e_c0 := 0; e_cf := [2] |})] = false.
Proof. vm_compute. reflexivity. Qed.

(** ** 2. The v5 checker on the genuine donor *)

Definition tmc5 : TM := fun q s =>
  match q, s with
  | StA, S0 => mkc S0 DR StB
  | StA, S1 => mkc S1 DL StC
  | StB, S0 => mkc S1 DR StC
  | StB, S1 => mkc S1 DR StD
  | StC, S0 => mkc S1 DL StD
  | StC, S1 => mkc S1 DR StA
  | StD, S0 => mkc S1 DL StA
  | StD, S1 => mkc S0 DL StC
  end.

Definition certc5 : BIRCertP := mkBIRCertP
  199086%nat (104) (4) (1) (2) StA S0
  [(2%nat, [S0; S1]);
   (3%nat, [S1; S0])]
  []
  [(1%nat, (0), (2)); (0%nat, (0), (1)); (1%nat, (0), (1)); (0%nat, (0), (1)); (1%nat, (0), (4)); (2%nat, (3), (0))]
  [mkBRuleP StD S1 [(1%nat, BC (1)); (2%nat, BV (1) (1)); (1%nat, BC (1)); (0%nat, BC (1)); (1%nat, BC (1))] [(1%nat, BV (-2) (3)); (2%nat, BV (0) (1))] (true, true);
   mkBRuleP StB S1 [(2%nat, BV (3) (1)); (1%nat, BC (1)); (0%nat, BC (1)); (1%nat, BC (1))] [(1%nat, BC (1)); (2%nat, BV (-3) (4))] (true, true);
   mkBRuleP StD S1 [(1%nat, BC (1)); (2%nat, BV (1) (1)); (1%nat, BC (1)); (0%nat, BC (1)); (1%nat, BC (1))] [(1%nat, BV (-2) (3))] (true, true)].

(** Honest control: the v5 checker ACCEPTS the genuine machine+cert. *)
Example honest_v5 :
  irulesblkpfx_check_neverqh_v5 tmc5 certc5 200000 3000 = true.
Proof. vm_compute. reflexivity. Qed.

(** LOAD-BEARING: the LANDED checker REFUSES this same machine+cert
    (its constant-count end-match cannot close the cycle).  The v5
    end-match is doing genuine work, not rubber-stamping. *)
Example landed_refuses_donor :
  irulesblkpfx_check_neverqh tmc5 certc5 200000 3000 = false.
Proof. vm_compute. reflexivity. Qed.

(** Block 2's cells [S0;S1] -> [S0;S0]: the template / hop denotations
    change, the cycle cannot close.  MUST be rejected. *)
Definition certc5_blk : BIRCertP := mkBIRCertP
  199086%nat (104) (4) (1) (2) StA S0
  [(2%nat, [S0; S0]);
   (3%nat, [S1; S0])]
  []
  [(1%nat, (0), (2)); (0%nat, (0), (1)); (1%nat, (0), (1)); (0%nat, (0), (1)); (1%nat, (0), (4)); (2%nat, (3), (0))]
  [mkBRuleP StD S1 [(1%nat, BC (1)); (2%nat, BV (1) (1)); (1%nat, BC (1)); (0%nat, BC (1)); (1%nat, BC (1))] [(1%nat, BV (-2) (3)); (2%nat, BV (0) (1))] (true, true);
   mkBRuleP StB S1 [(2%nat, BV (3) (1)); (1%nat, BC (1)); (0%nat, BC (1)); (1%nat, BC (1))] [(1%nat, BC (1)); (2%nat, BV (-3) (4))] (true, true);
   mkBRuleP StD S1 [(1%nat, BC (1)); (2%nat, BV (1) (1)); (1%nat, BC (1)); (0%nat, BC (1)); (1%nat, BC (1))] [(1%nat, BV (-2) (3))] (true, true)].

Example corrupt_v5_blk :
  irulesblkpfx_check_neverqh_v5 tmc5 certc5_blk 200000 3000 = false.
Proof. vm_compute. reflexivity. Qed.

(** Meta map a: 1 -> 2 (preconditions still hold): the shifted
    want-template is wrong; no reachable configuration is cell-equal to
    it, so even [cseq] cannot close.  MUST be rejected. *)
Definition certc5_meta : BIRCertP := mkBIRCertP
  199086%nat (104) (4) (2) (2) StA S0
  [(2%nat, [S0; S1]);
   (3%nat, [S1; S0])]
  []
  [(1%nat, (0), (2)); (0%nat, (0), (1)); (1%nat, (0), (1)); (0%nat, (0), (1)); (1%nat, (0), (4)); (2%nat, (3), (0))]
  [mkBRuleP StD S1 [(1%nat, BC (1)); (2%nat, BV (1) (1)); (1%nat, BC (1)); (0%nat, BC (1)); (1%nat, BC (1))] [(1%nat, BV (-2) (3)); (2%nat, BV (0) (1))] (true, true);
   mkBRuleP StB S1 [(2%nat, BV (3) (1)); (1%nat, BC (1)); (0%nat, BC (1)); (1%nat, BC (1))] [(1%nat, BC (1)); (2%nat, BV (-3) (4))] (true, true);
   mkBRuleP StD S1 [(1%nat, BC (1)); (2%nat, BV (1) (1)); (1%nat, BC (1)); (0%nat, BC (1)); (1%nat, BC (1))] [(1%nat, BV (-2) (3))] (true, true)].

Example corrupt_v5_meta :
  irulesblkpfx_check_neverqh_v5 tmc5 certc5_meta 200000 3000 = false.
Proof. vm_compute. reflexivity. Qed.

(** Template run [(2, al 3, be 0)] -> [(2, al 3, be 1)]: the shifted
    want-template gains one extra block-2 cell group, so no reachable
    configuration is cell-equal to it -- the new [cseq] end-match must
    NOT paper over the mismatch.  MUST be rejected. *)
Definition certc5_want : BIRCertP := mkBIRCertP
  199086%nat (104) (4) (1) (2) StA S0
  [(2%nat, [S0; S1]);
   (3%nat, [S1; S0])]
  []
  [(1%nat, (0), (2)); (0%nat, (0), (1)); (1%nat, (0), (1)); (0%nat, (0), (1)); (1%nat, (0), (4)); (2%nat, (3), (1))]
  [mkBRuleP StD S1 [(1%nat, BC (1)); (2%nat, BV (1) (1)); (1%nat, BC (1)); (0%nat, BC (1)); (1%nat, BC (1))] [(1%nat, BV (-2) (3)); (2%nat, BV (0) (1))] (true, true);
   mkBRuleP StB S1 [(2%nat, BV (3) (1)); (1%nat, BC (1)); (0%nat, BC (1)); (1%nat, BC (1))] [(1%nat, BC (1)); (2%nat, BV (-3) (4))] (true, true);
   mkBRuleP StD S1 [(1%nat, BC (1)); (2%nat, BV (1) (1)); (1%nat, BC (1)); (0%nat, BC (1)); (1%nat, BC (1))] [(1%nat, BV (-2) (3))] (true, true)].

Example corrupt_v5_want :
  irulesblkpfx_check_neverqh_v5 tmc5 certc5_want 200000 3000 = false.
Proof. vm_compute. reflexivity. Qed.

(** ** 3. Halter and mutant machine under the genuine cert *)

(** A machine that halts on its first step ([StA,S0] undefined): the
    anchor re-simulation reaches no configuration, so NO certificate
    boards it.  MUST be rejected. *)
Definition tmc5_halt : TM := fun q s =>
  match q, s with
  | StA, S0 => None
  | StA, S1 => mkc S1 DL StC
  | StB, S0 => mkc S1 DR StC
  | StB, S1 => mkc S1 DR StD
  | StC, S0 => mkc S1 DL StD
  | StC, S1 => mkc S1 DR StA
  | StD, S0 => mkc S1 DL StA
  | StD, S1 => mkc S0 DL StC
  end.

Example corrupt_v5_halter :
  irulesblkpfx_check_neverqh_v5 tmc5_halt certc5 200000 3000 = false.
Proof. vm_compute. reflexivity. Qed.

(** Mutant machine ([StD,S1] write S0 -> S1) under the genuine cert:
    the anchor re-simulation / state coverage no longer match.  MUST be
    rejected. *)
Definition tmc5_mut : TM := fun q s =>
  match q, s with
  | StA, S0 => mkc S0 DR StB
  | StA, S1 => mkc S1 DL StC
  | StB, S0 => mkc S1 DR StC
  | StB, S1 => mkc S1 DR StD
  | StC, S0 => mkc S1 DL StD
  | StC, S1 => mkc S1 DR StA
  | StD, S0 => mkc S1 DL StA
  | StD, S1 => mkc S1 DL StC
  end.

Example corrupt_v5_machine :
  irulesblkpfx_check_neverqh_v5 tmc5_mut certc5 200000 3000 = false.
Proof. vm_compute. reflexivity. Qed.
