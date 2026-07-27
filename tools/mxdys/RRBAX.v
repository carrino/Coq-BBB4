(* Extract RRBA's decide_loop2 at BBinf.

   RRBA is the decider mxdys describes as handling "shift-recursive"
   (counter balanced, counter inverting) and "sync bi-counter" -- i.e. exactly
   the recursive counter shapes our residue is made of.  The Inductive decider
   only claims "SOME of bell eats counters / sync bouncer counters".

   Earlier attempts stack-overflowed coqc, or ran >55 min without finishing.
   The usual cause is extraction's inliner blowing up on a large functor body,
   so turn it off. *)
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

(* [Unset Extraction AutoInline] is what makes this terminate at all: the
   default inliner explodes on RRBA's functor body (earlier attempts
   stack-overflowed coqc, or ran >55 min).

   Do NOT add [Set Extraction Conservative Types] -- it makes extraction emit
   erased type arguments that the OCaml compiler then rejects (a nullary
   [ReflectT] applied to [__], and [PArray.make] applied to three arguments). *)
Set Extraction Optimize.
Unset Extraction AutoInline.

Extraction "RRBAX" rrba_decide.
