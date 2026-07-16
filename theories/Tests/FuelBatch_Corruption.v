(** * FuelBatch_Corruption: negative controls for the fuel-checker
    boarding pipeline (tools/gen_fuel_certs.py ->
    [ngram_check_neverqh_fuel]).

    Test subject: tm_bulk_00001 = 1RB---_0LC0RC_0LD1LC_1RA1LB with
    the parameters the generator re-derives for it (n=2 t=0 fuel=528
    rounds=11 -- digit-identical to Fuel_Examples.v, which is the
    differential check that the untrusted transcription matches the
    Coq engine).  The genuine run is the positive control; every
    corruption a buggy or adversarial generator could emit -- a
    mutated transition, a gutted measure table, a state wrongly
    marked runner-dischargeable, a starved closure budget -- must
    make the checker compute [false].

    The runner disjunct ([runner_ok]) has no positive control here
    because the IN-WINDOW instance cannot fire it on any blank-start
    machine with a nonempty q-avoiding edge set: the closure always
    reaches a context just past the last window nonblank, and that
    context either sits in state q or refutes [fnode_rfuel_ge1].
    Discharging real runner SCCs takes the FuelClass beyond-window
    classes (see tools/fuel_deferred.tsv and NEXT_SESSION.md). *)

From Coq Require Import List.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Checkers Require Import NGram Fuel.
From BBB4.Machines.Bulk Require Import Bulk_001.
Import ListNotations.

(* The genuine parameters pass: the positive control the mutations
   below are measured against (same numbers as Fuel_Examples.v). *)
Example fuel_accept_genuine :
  ngram_check_neverqh_fuel tm_bulk_00001 2 0 528 11 cert_bulk_00001 = true.
Proof. vm_compute. reflexivity. Qed.

(* One-transition mutant (StD,S0: 1RA -> 1LA): the closure the
   checker re-derives no longer matches the certificate's world. *)
Definition tm_mutant : TM := fun q s =>
  match q, s with
  | StD, S0 => Some (mkTrans S1 DL StA)
  | q, s => tm_bulk_00001 q s
  end.
Example fuel_reject_mutant :
  ngram_check_neverqh_fuel tm_mutant 2 0 528 11 cert_bulk_00001 = false.
Proof. vm_compute. reflexivity. Qed.

(* Wrong runner-state marking: an empty component list claims the
   state is discharged by the runner rule (c2) alone.  StA's
   q-avoiding graph is no runner (B/C/D contexts move both ways), so
   the gate [lex_ok || runner_ok] must fail. *)
Example fuel_reject_runner_marking :
  ngram_check_neverqh_fuel tm_bulk_00001 2 0 528 11
    (fun q => match q with StA => [] | q => cert_bulk_00001 q end) = false.
Proof. vm_compute. reflexivity. Qed.

(* Marking EVERY state runner-dischargeable (the all-empty
   certificate) is likewise rejected. *)
Example fuel_reject_empty_cert :
  ngram_check_neverqh_fuel tm_bulk_00001 2 0 528 11
    (fun _ => []) = false.
Proof. vm_compute. reflexivity. Qed.

(* Wrong measure certificate: gutting every rank table (phi := [])
   leaves edges with no strict decrease anywhere in the lex chain. *)
Definition gut_rank (c : ngcomp) : ngcomp :=
  match c with
  | NgRankE _ => NgRankE []
  | c => c
  end.
Example fuel_reject_gutted_rank :
  ngram_check_neverqh_fuel tm_bulk_00001 2 0 528 11
    (fun q => map gut_rank (cert_bulk_00001 q)) = false.
Proof. vm_compute. reflexivity. Qed.

(* Starved closure budget: with fuel 1 the closure cannot finish, so
   the checker fails closed rather than trusting the certificate. *)
Example fuel_reject_starved :
  ngram_check_neverqh_fuel tm_bulk_00001 2 0 1 11 cert_bulk_00001 = false.
Proof. vm_compute. reflexivity. Qed.
