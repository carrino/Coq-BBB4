(** * ClosureIdx_Corruption: negative controls for the interned
      closure engine.

    [ClosureIdx] moves the closedness and rank checks onto interned
    node indices and takes the rank assignment as a PARAMETER.  Two
    things therefore need negative controls that the generic
    [Closure] suite does not cover:

    - the single [edges_of] pass really is closedness (a machine
      whose exact closure escapes must still be rejected), and
    - soundness does not lean on the untrusted rank search: feeding
      the checker a deliberately corrupt [mkr] must never make it
      accept.

    Plus a differential control: on the same inputs the interned
    checker must agree with [closure_check_neverqh], accept for
    accept and reject for reject. *)

From Coq Require Import PArith.
From Coq Require Import FSets.FMapPositive.
From BBB4 Require Import BBB4_Statement CTape PosEnc Closure Mirror.
From BBB4.Checkers Require Import ExactClosure ClosureIdx.
From BBB4.Machines Require Import Cycle_Examples TCycler_Examples
                                  Closure_Examples.

(** the exact-closure instance of the interned engine *)
Definition idx_exact (tm : TM) (t fuel : nat) : bool :=
  match csteps tm t c0 with
  | Some ct =>
      idx_check_neverqh tm cconf cconf_enc ec_state (ec_succs tm)
        t fuel (norm ct) idx_ranks
  | None => false
  end.

(** ** Differential controls against the engine it replaces *)

(* accepts exactly what the current engine accepts *)
Example idx_agrees_accept :
  (exact_closure_check_neverqh tm_ex_neverqh 0 200,
   idx_exact tm_ex_neverqh 0 200) = (true, true).
Proof. vm_compute. reflexivity. Qed.

(* a quasihalting machine: state D goes quiet, the D-avoiding
   subgraph keeps the loop's cycle, no rank exists -- both reject *)
Example idx_agrees_reject_qh :
  (exact_closure_check_neverqh tm_ex_qh 0 200,
   idx_exact tm_ex_qh 0 200) = (false, false).
Proof. vm_compute. reflexivity. Qed.

(* an infinite exact closure: the search must exhaust its fuel *)
Example idx_agrees_reject_growing :
  (exact_closure_check_neverqh (mirror_tm tm_bbb_sample) 0 500,
   idx_exact (mirror_tm tm_bbb_sample) 0 500) = (false, false).
Proof. vm_compute. reflexivity. Qed.

(* zero fuel: the search cannot even start *)
Example idx_reject_fuel : idx_exact tm_ex_neverqh 0 0 = false.
Proof. vm_compute. reflexivity. Qed.

(** ** The rank search is untrusted: corrupt it and the checker must
       still refuse to accept *)

(* every node unranked (rank_at then reads 0 everywhere, so no edge
   can strictly decrease) *)
Definition mkr_empty (_ : list erow) (_ : St) : PositiveMap.tree nat :=
  PositiveMap.empty nat.

Example idx_corrupt_ranks_empty :
  match csteps tm_ex_neverqh 0 c0 with
  | Some ct =>
      idx_check_neverqh tm_ex_neverqh cconf cconf_enc ec_state
        (ec_succs tm_ex_neverqh) 0 200 (norm ct) mkr_empty
  | None => false
  end = false.
Proof. vm_compute. reflexivity. Qed.

(* a constant rank: every edge fails [rank_at j <? rank_at i] *)
Definition mkr_const (_ : list erow) (_ : St) : PositiveMap.tree nat :=
  PositiveMap.add 1%positive 7 (PositiveMap.empty nat).

Example idx_corrupt_ranks_const :
  match csteps tm_ex_neverqh 0 c0 with
  | Some ct =>
      idx_check_neverqh tm_ex_neverqh cconf cconf_enc ec_state
        (ec_succs tm_ex_neverqh) 0 200 (norm ct) mkr_const
  | None => false
  end = false.
Proof. vm_compute. reflexivity. Qed.

(** ** The footprint the whole point rests on *)

Print Assumptions idx_check_neverqh_sound.
