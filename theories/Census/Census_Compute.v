(** * Census/Census_Compute: the census computation and theorem.

    The one heavy step: walk the whole TNF tree by native_compute and
    observe the empty queue.  Kept in its own file (and out of the
    default build) because it costs a full enumeration run; see
    NEXT_SESSION.md "The big compute".

    Run the probe first; when it prints (0, 0, []), enable the lemma
    and the theorem below.

<<
Definition q_probe := Eval native_compute in
  (let q := Nat.iter 700 q_suc q_0 in
   (length (fst q), length (snd q),
    map (fun x => tm_enc (node_tm x)) (firstn 5 (snd q)))).
Print q_probe.
>>
*)

From Coq Require Import Arith List.
From BBB4 Require Import BBB4_Statement.
From BBB4.Census Require Import TNF_QH Decide Deferred_Data Run.
Import ListNotations.

Lemma q_census_empty : Nat.iter 700 q_suc q_0 = ([], []).
Proof.
  native_cast_no_check (eq_refl (@nil TNF_Node, @nil TNF_Node)).
Qed.

(** The census: every 4-state 2-symbol Turing machine either has all
    its BBB scores (last visits of eventually-quiet states) below
    [B_census] = 2000, or lies in the swap/mirror/completion orbit of
    the explicit deferred list (the 3,713 BBB(4) holdouts plus the
    measured hard residue of the generic tiers). *)
Theorem census_decided :
  forall tm, QHBound B_census tm \/ Deferred D_census tm.
Proof.
  exact (census_from_empty 700 q_census_empty).
Qed.

Print Assumptions census_decided.
