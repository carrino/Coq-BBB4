(** * Tests/IRulesQH_Corruption: negative controls for the irules-QH
    corollary checkers (wave 3).

    The wave-3 harvest boards list-C state-QH machines with
    [NonHalt /\ QHBound 2000 /\ QuasiHaltsSt] through the NEW dual
    extraction checkers [MetaQH.irules_check_qh] (v1 certificates) and
    [MetaBlkPfxQH.irulesblkpfx_check_qh] (v3/v5/v6/v7 certificates):
    the certificate's forward-behavior model plus a witness state [qz]
    that is prefix-visited but owns NO transition in the meta-cycle's
    fired set [F], plus the score-window pass at [B].

    This is a NEW checker feature, so it gets controls that MUST fail:

    - a genuinely NEVER-quasihalting machine (its own verified irules
      certificate, every state live) must be rejected for EVERY choice
      of witness -- a checker that certified it would transfer a bogus
      [QuasiHaltsSt];
    - a HALTING machine must be rejected (halting machines have no
      anchor configuration; a halter reaching the R_QH tier would be
      unsound for [NonHalt]);
    - a LIVE state offered as the witness must be rejected (the
      extracted quiet state must really be outside [F]);
    - a [B] below the quiet state's real last visit must be rejected
      (the score-window gate is what turns [QHBound anchor] into the
      census's [QHBound 2000]; without it a late-quieting machine
      would overclaim its score bound).

    Every control is closed by [vm_compute]; a regression that made
    either checker accept any of them BREAKS THIS FILE. *)

From Coq Require Import ZArith List.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Checkers Require Import Cycle.
From BBB4.Checkers.IRules Require Import Expr RLE Engine Rules Meta RulesK
     EngineK RulesBlk MetaBlk EngineKS RulesBlkPfx MetaBlkPfx MetaQH
     MetaBlkPfxQH.
Import ListNotations.
Open Scope Z_scope.

Definition mk (w : Sym) (d : Dir) (n : St) : option Trans :=
  Some (mkTrans w d n).

(** ** The genuine state-QH baseline (v6 block certificate)

    [1RB---_0LC1RD_---1LD_1RB0LC], a list-C residue machine the ngram
    wrap sweep mis-binned never-QH: state A fires once (step 1) and
    never recurs; B/C/D run a growing block sweep forever.  Its
    bin/irules certificate carries the model; the checker extracts the
    QH verdict with witness [StA] at the census bound B = 2000. *)

Definition tm_qh : TM := fun q s =>
  match q, s with
  | StA, S0 => mk S1 DR StB
  | StA, S1 => None
  | StB, S0 => mk S0 DL StC
  | StB, S1 => mk S1 DR StD
  | StC, S0 => None
  | StC, S1 => mk S1 DL StD
  | StD, S0 => mk S1 DR StB
  | StD, S1 => mk S0 DL StC
  end.

Definition cert_qh_real : BIRCertP := mkBIRCertP
  199396%nat (315) (10) (1) (1) StB S0
  [(2%nat, [S1; S0]);
   (3%nat, [S0; S1])]
  [(1%nat, (2), (1))]
  []
  [mkBRuleP StC S1 [(1%nat, BV (-2) (3))] [(3%nat, BV (1) (1))] (true, true)].

(** the checker FIRES on the genuine quasihalter with the real quiet
    state as witness (the positive baseline every mutant below breaks) *)
Example qh_accepts_real :
  irulesblkpfx_check_qh tm_qh cert_qh_real StA 2000 200000 300000 = true.
Proof. vm_compute. reflexivity. Qed.

(** ** Negative control 1 -- a LIVE state offered as witness

    [StB] recurs forever (it owns transitions in the fired set); a
    checker that accepted it as the quiet witness would certify a
    false [QuietFrom].  Must be [false]. *)
Example qh_rejects_live_witness :
  irulesblkpfx_check_qh tm_qh cert_qh_real StB 2000 200000 300000 = false.
Proof. vm_compute. reflexivity. Qed.

Example qh_rejects_live_witness_D :
  irulesblkpfx_check_qh tm_qh cert_qh_real StD 2000 200000 300000 = false.
Proof. vm_compute. reflexivity. Qed.

(** ** Negative control 2 -- a HALTING machine

    [tm_halt] mutates [tm_qh]'s [StB] read-0 to undefined: from the
    blank tape it halts at step 2.  No anchor configuration exists, so
    the checker must return [false] for every witness -- a halter
    reaching the R_QH tier would break [NonHalt]. *)
Definition tm_halt : TM := fun q s =>
  match q, s with
  | StA, S0 => mk S1 DR StB
  | StA, S1 => None
  | StB, S0 => None
  | StB, S1 => mk S1 DR StD
  | StC, S0 => None
  | StC, S1 => mk S1 DL StD
  | StD, S0 => mk S1 DR StB
  | StD, S1 => mk S0 DL StC
  end.

Example qh_rejects_halter_A :
  irulesblkpfx_check_qh tm_halt cert_qh_real StA 2000 200000 300000 = false.
Proof. vm_compute. reflexivity. Qed.

Example qh_rejects_halter_B :
  irulesblkpfx_check_qh tm_halt cert_qh_real StB 2000 200000 300000 = false.
Proof. vm_compute. reflexivity. Qed.

(** ** Negative control 3 -- the score-window gate is load-bearing

    [1RB0LC_1RC1LD_1RD0RB_0LB1LA] (v3 certificate) quasihalts with
    quiet state [StC] whose LAST VISIT is at index ~1459.  At the
    census bound B = 2000 the checker fires; at B = 100 the window
    [100, anchor) still contains [StC] visits, so a sound checker must
    refuse the (false) claim [QHBound 100].  If the window pass were
    removed, this control would wrongly return [true]. *)

Definition tm_qh2 : TM := fun q s =>
  match q, s with
  | StA, S0 => mk S1 DR StB
  | StA, S1 => mk S0 DL StC
  | StB, S0 => mk S1 DR StC
  | StB, S1 => mk S1 DL StD
  | StC, S0 => mk S1 DR StD
  | StC, S1 => mk S0 DR StB
  | StD, S0 => mk S0 DL StB
  | StD, S1 => mk S1 DL StA
  end.

Definition cert_qh2_real : BIRCertP := mkBIRCertP
  199999%nat (66181) (2) (1) (1) StA S0
  [(2%nat, [S1; S0; S1; S1]);
   (3%nat, [S0; S1]);
   (4%nat, [S1; S0]);
   (5%nat, [S1; S1; S0; S1]);
   (6%nat, [S1; S1; S1; S0]);
   (7%nat, [S0; S1; S1; S1])]
  []
  [(1%nat, (1), (0)); (0%nat, (0), (1)); (1%nat, (0), (3)); (0%nat, (0), (1)); (1%nat, (0), (3)); (0%nat, (0), (1)); (1%nat, (0), (3)); (0%nat, (0), (1)); (1%nat, (0), (3)); (0%nat, (0), (1)); (1%nat, (0), (3)); (0%nat, (0), (1)); (1%nat, (0), (3)); (0%nat, (0), (1)); (1%nat, (0), (3)); (0%nat, (0), (1)); (1%nat, (0), (3)); (0%nat, (0), (1)); (1%nat, (0), (3)); (0%nat, (0), (1)); (1%nat, (0), (3)); (0%nat, (0), (1)); (1%nat, (0), (3))]
  [].

Example qh2_accepts_census_bound :
  irulesblkpfx_check_qh tm_qh2 cert_qh2_real StC 2000 200000 300000 = true.
Proof. vm_compute. reflexivity. Qed.

Example qh2_rejects_low_bound :
  irulesblkpfx_check_qh tm_qh2 cert_qh2_real StC 100 200000 300000 = false.
Proof. vm_compute. reflexivity. Qed.

(** ** Negative control 4 -- a genuinely NEVER-quasihalting machine

    [1RB0LC_0RC0RD_1LC1LA_1RA1LB] is a list-C machine whose own
    verified irules certificate (0 rules, pure template cycle) shows
    EVERY visited state live.  The QH checker must reject it for every
    choice of witness: whatever [qz] is offered is either in the fired
    set or not prefix-visited. *)

Definition tm_nqh : TM := fun q s =>
  match q, s with
  | StA, S0 => mk S1 DR StB
  | StA, S1 => mk S0 DL StC
  | StB, S0 => mk S0 DR StC
  | StB, S1 => mk S0 DR StD
  | StC, S0 => mk S1 DL StC
  | StC, S1 => mk S1 DL StA
  | StD, S0 => mk S1 DR StA
  | StD, S1 => mk S1 DL StB
  end.

Definition cert_nqh_real : BIRCertP := mkBIRCertP
  199213%nat (148) (1) (1) (1) StA S0
  [(2%nat, [S1; S0; S1; S1; S1]);
   (3%nat, [S1; S1; S0; S1; S1]);
   (4%nat, [S1; S0; S1; S1; S0]);
   (5%nat, [S0; S1; S1; S1; S1]);
   (6%nat, [S0; S1; S1; S0; S1])]
  []
  [(4%nat, (1), (0)); (1%nat, (0), (3))]
  [].

Example nqh_rejects_A :
  irulesblkpfx_check_qh tm_nqh cert_nqh_real StA 2000 200000 300000 = false.
Proof. vm_compute. reflexivity. Qed.

Example nqh_rejects_B :
  irulesblkpfx_check_qh tm_nqh cert_nqh_real StB 2000 200000 300000 = false.
Proof. vm_compute. reflexivity. Qed.

Example nqh_rejects_C :
  irulesblkpfx_check_qh tm_nqh cert_nqh_real StC 2000 200000 300000 = false.
Proof. vm_compute. reflexivity. Qed.

Example nqh_rejects_D :
  irulesblkpfx_check_qh tm_nqh cert_nqh_real StD 2000 200000 300000 = false.
Proof. vm_compute. reflexivity. Qed.

(** ** The v1 checker ([MetaQH.irules_check_qh]) controls

    [1RB1RD_1RC1RB_1LC1LA_0RC0RD] is a landed never-QH holdout with a
    verified v1 certificate (all states live).  The v1 QH checker must
    reject it for every witness, and must reject a halting mutant
    ([StA] read-0 undefined => halts at step 0). *)

Definition tm_v1 : TM := fun q s =>
  match q, s with
  | StA, S0 => mk S1 DR StB
  | StA, S1 => mk S1 DR StD
  | StB, S0 => mk S1 DR StC
  | StB, S1 => mk S1 DR StB
  | StC, S0 => mk S1 DL StC
  | StC, S1 => mk S1 DL StA
  | StD, S0 => mk S0 DR StC
  | StD, S1 => mk S0 DR StD
  end.

Definition cert_v1 : IRCert := mkIRCert
  1245560%nat (1822) (3) (3) (1) StC S0
  [(S1, 1, 0)]
  []
  [mkRule StC S1 [(S1, RV (-1) (2))] [(S1, RV (3) (1))]].

Example v1_nqh_rejects_A :
  irules_check_qh tm_v1 cert_v1 StA 2000 300000 = false.
Proof. vm_compute. reflexivity. Qed.

Example v1_nqh_rejects_B :
  irules_check_qh tm_v1 cert_v1 StB 2000 300000 = false.
Proof. vm_compute. reflexivity. Qed.

Example v1_nqh_rejects_C :
  irules_check_qh tm_v1 cert_v1 StC 2000 300000 = false.
Proof. vm_compute. reflexivity. Qed.

Example v1_nqh_rejects_D :
  irules_check_qh tm_v1 cert_v1 StD 2000 300000 = false.
Proof. vm_compute. reflexivity. Qed.

Definition tm_v1_halt : TM := fun q s =>
  match q, s with
  | StA, S0 => None
  | StA, S1 => mk S1 DR StD
  | StB, S0 => mk S1 DR StC
  | StB, S1 => mk S1 DR StB
  | StC, S0 => mk S1 DL StC
  | StC, S1 => mk S1 DL StA
  | StD, S0 => mk S0 DR StC
  | StD, S1 => mk S0 DR StD
  end.

Example v1_rejects_halter :
  irules_check_qh tm_v1_halt cert_v1 StA 2000 300000 = false.
Proof. vm_compute. reflexivity. Qed.
