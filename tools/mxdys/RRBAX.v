(* Extraction of RRBA's decide_loop2 at BBinf, for the Stage 0 sweep.
   The TM is passed as a function; the OCaml driver parses the text format. *)
Require Export NArith ZArith.
Require Uint63.
From BusyCoq Require Import RRBA BBinf.

Module RRBA_inf := RRBA BBinf.

Definition rrba_decide (tm : RRBA_inf.TM.TM) (mb0 mb1 n_skip k : nat)
  (l1al2 : bool) (maxT : N) : bool :=
  RRBA_inf.decide_loop2 tm
    (RRBA_inf.nat2int mb0, RRBA_inf.nat2int mb1) 1%nat n_skip l1al2
    (RRBA_inf.nat2int k) (Uint63.of_Z (Z.of_N maxT)).

Require Import Extraction ExtrOCamlInt63 ExtrOCamlPArray ExtrOcamlNativeString.
Extract Constant PArray.array "'a" => "'a Parray.t".
Extraction NoInline PArray.array.
Extraction "RRBAX" rrba_decide.
