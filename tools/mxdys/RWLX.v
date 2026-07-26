(* Extraction of RWLAcc's decide_nonhalt at BBinf, for the Stage 0 sweep. *)
Require Export NArith ZArith.
From BusyCoq Require Import RWLAcc BBinf.

Module RWL_inf := RWLAcc BBinf.

Definition rwl_decide (tm : RWL_inf.TM.TM) (bsz bmaxT : nat) (use_acc : bool)
  (mnc : N) (T : N) : bool :=
  RWL_inf.decide_nonhalt tm bsz bmaxT use_acc mnc T.

Require Import Extraction ExtrOCamlInt63 ExtrOCamlPArray ExtrOcamlNativeString.
Extract Constant PArray.array "'a" => "'a Parray.t".
Extraction NoInline PArray.array.
Extraction "RWLX" rwl_decide.
