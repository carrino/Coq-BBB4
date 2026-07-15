(** * Bulk_Corruption: negative controls for the bulk pattern-measure
    certificates (the BBB corruption-test tradition: every certificate
    feature gets mutations that MUST be rejected).

    Test subject: tm_bulk_00464 = 1RB0LD_0LC1RA_0RD1LC_1LC1LA, whose
    certificate is the first to need a digram measure ([S1;S1]/RgR --
    the C verifier's "11/R"); its state-C liveness has no single-cell
    certificate, which is exactly why the [ngmeas]-only checker could
    not board it. *)

From Coq Require Import List.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Checkers Require Import NGram.
From BBB4.Machines.Bulk Require Import Bulk_010.
Import ListNotations.

(* The genuine certificate passes (the theorem in Bulk_010 relies on
   it); rerun the boolean here as the positive control. *)
Example bulk_accept_genuine :
  ngram_check_neverqh_lex tm_bulk_00464 3 0 880 16 cert_bulk_00464 = true.
Proof. vm_compute. reflexivity. Qed.

(* Tampering the digram pattern (11 -> 10) breaks the measure. *)
Definition tamper_patt (c : ngcomp) : ngcomp :=
  match c with
  | NgPattE (S1 :: S1 :: nil) rg K phi gate =>
      NgPattE (S1 :: S0 :: nil) rg K phi gate
  | c => c
  end.
Example bulk_reject_patt :
  ngram_check_neverqh_lex tm_bulk_00464 3 0 880 16
    (fun q => map tamper_patt (cert_bulk_00464 q)) = false.
Proof. vm_compute. reflexivity. Qed.

(* Flipping the digram's region (R -> L) breaks it too. *)
Definition tamper_reg (c : ngcomp) : ngcomp :=
  match c with
  | NgPattE (S1 :: S1 :: nil) RgR K phi gate =>
      NgPattE (S1 :: S1 :: nil) RgL K phi gate
  | c => c
  end.
Example bulk_reject_reg :
  ngram_check_neverqh_lex tm_bulk_00464 3 0 880 16
    (fun q => map tamper_reg (cert_bulk_00464 q)) = false.
Proof. vm_compute. reflexivity. Qed.

(* A pattern with no nonblank has an infinite concrete count; the
   [pm_ok] guard denotes it as a no-op component, so the certificate
   fails closed rather than proving anything. *)
Definition tamper_blank (c : ngcomp) : ngcomp :=
  match c with
  | NgPattE (S1 :: S1 :: nil) rg K phi gate =>
      NgPattE (S0 :: nil) rg K phi gate
  | c => c
  end.
Example bulk_reject_blank_patt :
  ngram_check_neverqh_lex tm_bulk_00464 3 0 880 16
    (fun q => map tamper_blank (cert_bulk_00464 q)) = false.
Proof. vm_compute. reflexivity. Qed.

(* A pattern longer than the window has an uncoverable delta; the
   guard again fails closed. *)
Definition tamper_long (c : ngcomp) : ngcomp :=
  match c with
  | NgPattE (S1 :: S1 :: nil) rg K phi gate =>
      NgPattE (S1 :: S1 :: S0 :: S0 :: nil) rg K phi gate
  | c => c
  end.
Example bulk_reject_long_patt :
  ngram_check_neverqh_lex tm_bulk_00464 3 0 880 16
    (fun q => map tamper_long (cert_bulk_00464 q)) = false.
Proof. vm_compute. reflexivity. Qed.

(* Retargeting the certificate at a different machine is rejected
   (its neighbour in the enumeration, one transition apart). *)
Example bulk_reject_retarget :
  ngram_check_neverqh_lex tm_bulk_00465 3 0 912 16 cert_bulk_00464 = false.
Proof. vm_compute. reflexivity. Qed.

(* The empty certificate is rejected. *)
Example bulk_reject_empty :
  ngram_check_neverqh_lex tm_bulk_00464 3 0 880 16
    (fun _ => nil) = false.
Proof. vm_compute. reflexivity. Qed.

(* Starved growth rounds fail closed. *)
Example bulk_reject_rounds :
  ngram_check_neverqh_lex tm_bulk_00464 3 0 880 0 cert_bulk_00464 = false.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions nqh_1RB0LD_0LC1RA_0RD1LC_1LC1LA.
