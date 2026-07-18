(** * DriftBatch_Corruption: negative controls for the drift-checker
    boarding pipeline (tools/gen_drift_certs.py ->
    [ngram_check_neverqh_driftw], Checkers/Drift.v).

    Test subjects:

    - tm_drift_00001 = 1RB0LA_0RC0RD_1LA1LC_0LC0RB (n=2 t=0 fuel=1448
      rounds=12): one LEFT-drift gate (16 nodes on state D's graph) --
      the plain rule-(c3) shape;
    - tm_drift_00015 = 1RB1LC_1LC0RB_1RD0LC_0RD1LA (n=2 t=0 fuel=1256
      rounds=12): state B carries BOTH gates at once (a net-right SCC
      and a net-left SCC in one q-avoiding graph) -- the machine that
      forced the two-sided design.

    The genuine runs are the positive controls; every corruption a
    buggy or adversarial generator could emit -- a mutated transition,
    erased gates, gutted potentials, gates swapped between sides
    (drift direction flipped), gates merged (disjointness violated),
    a zeroed scale W, the certificate demoted to the fuel checker
    (rule (c3) is load-bearing), a starved closure budget -- must make
    the checker compute [false]. *)

From Coq Require Import List.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Checkers Require Import NGram FuelWide Drift.
From BBB4.Machines Require Import Drift_Batch_01.
Import ListNotations.

(** ** Certificate manglers *)

Definition drop_gates (c : dw_cert) : dw_cert :=
  let '(comps, gR, phiR, gL, phiL, W) := c in
  (comps, [], [], [], [], W).

Definition zero_pots (c : dw_cert) : dw_cert :=
  let '(comps, gR, phiR, gL, phiL, W) := c in
  (comps, gR, [], gL, [], W).

Definition swap_gates (c : dw_cert) : dw_cert :=
  let '(comps, gR, phiR, gL, phiL, W) := c in
  (comps, gL, phiL, gR, phiR, W).

Definition merge_gates (c : dw_cert) : dw_cert :=
  let '(comps, gR, phiR, gL, phiL, W) := c in
  (comps, gR ++ gL, phiR ++ phiL, gR ++ gL, phiR ++ phiL, W).

Definition zero_W (c : dw_cert) : dw_cert :=
  let '(comps, gR, phiR, gL, phiL, _) := c in
  (comps, gR, phiR, gL, phiL, 0).

(** ** Positive controls (the boarded theorems rely on these) *)

Example drift_accept_genuine_00001 :
  ngram_check_neverqh_driftw tm_drift_00001 2 0 1448 12
    cert_drift_00001 = true.
Proof. vm_compute. reflexivity. Qed.

Example drift_accept_genuine_00015 :
  ngram_check_neverqh_driftw tm_drift_00015 2 0 1256 12
    cert_drift_00015 = true.
Proof. vm_compute. reflexivity. Qed.

(** ** One-transition mutant (StC,S1: 1LC -> 1RC): the refined
    closure the checker re-derives no longer matches the
    certificate's world.  (Not every one-transition mutation is a
    negative control: flipping StD,S0 yields machines the SAME
    tables genuinely certify -- the checker re-derives everything,
    so acceptance there is a sound proof about the mutant, not a
    leak.  This mutation is measured rejected.) *)

Definition tm_mutant : TM := fun q s =>
  match q, s with
  | StC, S1 => Some (mkTrans S1 DR StC)
  | q, s => tm_drift_00001 q s
  end.
Example drift_reject_mutant :
  ngram_check_neverqh_driftw tm_mutant 2 0 1448 12
    cert_drift_00001 = false.
Proof. vm_compute. reflexivity. Qed.

(** ** Erased gates: the drift SCC's edges are left with no
    discharge (the lex components are equal across them). *)

Example drift_reject_erased_gates :
  ngram_check_neverqh_driftw tm_drift_00001 2 0 1448 12
    (fun q => drop_gates (cert_drift_00001 q)) = false.
Proof. vm_compute. reflexivity. Qed.

Example drift_reject_erased_gates_00015 :
  ngram_check_neverqh_driftw tm_drift_00015 2 0 1256 12
    (fun q => drop_gates (cert_drift_00015 q)) = false.
Proof. vm_compute. reflexivity. Qed.

(** ** Corrupted potentials: with phi == 0 every away-moving gate
    edge demands 0 + W + 1 <= 0, so a genuinely mixed-direction
    (post-(c2)) SCC must be rejected. *)

Example drift_reject_zeroed_potentials :
  ngram_check_neverqh_driftw tm_drift_00001 2 0 1448 12
    (fun q => zero_pots (cert_drift_00001 q)) = false.
Proof. vm_compute. reflexivity. Qed.

Example drift_reject_zeroed_potentials_00015 :
  ngram_check_neverqh_driftw tm_drift_00015 2 0 1256 12
    (fun q => zero_pots (cert_drift_00015 q)) = false.
Proof. vm_compute. reflexivity. Qed.

(** ** Swapped gates: the drift DIRECTION is load-bearing -- putting
    the net-left SCC in the right gate (and vice versa) flips every
    potential inequality's orientation. *)

Example drift_reject_swapped_gates :
  ngram_check_neverqh_driftw tm_drift_00001 2 0 1448 12
    (fun q => swap_gates (cert_drift_00001 q)) = false.
Proof. vm_compute. reflexivity. Qed.

Example drift_reject_swapped_gates_00015 :
  ngram_check_neverqh_driftw tm_drift_00015 2 0 1256 12
    (fun q => swap_gates (cert_drift_00015 q)) = false.
Proof. vm_compute. reflexivity. Qed.

(** ** Merged gates: gate DISJOINTNESS is load-bearing (the descent's
    single live budget depends on it) -- a node in both gates must be
    rejected by [dgate_ok] outright. *)

Example drift_reject_merged_gates_00015 :
  ngram_check_neverqh_driftw tm_drift_00015 2 0 1256 12
    (fun q => merge_gates (cert_drift_00015 q)) = false.
Proof. vm_compute. reflexivity. Qed.

(** ** Zeroed scale: W = 0 demands phi strictly decreasing along
    every gate edge -- impossible around a cycle. *)

Example drift_reject_zero_W :
  ngram_check_neverqh_driftw tm_drift_00001 2 0 1448 12
    (fun q => zero_W (cert_drift_00001 q)) = false.
Proof. vm_compute. reflexivity. Qed.

(** ** Demotion to the fuel checker: rule (c3) is load-bearing --
    the same lex components with the drift gates stripped to an
    (empty) rule-(c2) runner gate must fail the FuelWide checker
    (the drift SCCs are not uniform fueled right-movers). *)

Example drift_reject_demoted_fuelw :
  ngram_check_neverqh_fuelw tm_drift_00001 2 0 1448 12
    (fun q => let '(comps, _, _, _, _, _) := cert_drift_00001 q in
              (comps, [])) = false.
Proof. vm_compute. reflexivity. Qed.

Example drift_reject_demoted_fuelw_00015 :
  ngram_check_neverqh_fuelw tm_drift_00015 2 0 1256 12
    (fun q => let '(comps, _, _, _, _, _) := cert_drift_00015 q in
              (comps, [])) = false.
Proof. vm_compute. reflexivity. Qed.

(** ** The all-empty certificate is rejected. *)

Example drift_reject_empty_cert :
  ngram_check_neverqh_driftw tm_drift_00001 2 0 1448 12
    (fun _ => ([], [], [], [], [], 0)) = false.
Proof. vm_compute. reflexivity. Qed.

(** ** Starved closure budget: with fuel 1 the closure cannot finish,
    so the checker fails closed rather than trusting the
    certificate. *)

Example drift_reject_starved :
  ngram_check_neverqh_driftw tm_drift_00001 2 0 1 12
    cert_drift_00001 = false.
Proof. vm_compute. reflexivity. Qed.
