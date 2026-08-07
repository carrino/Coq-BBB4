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

From Coq Require Import List PArith.
From Coq Require Import FSets.FMapPositive.
From Coq Require Import MSets.MSetPositive.
From BBB4 Require Import BBB4_Statement CTape PosEnc Closure Mirror.
From BBB4.Checkers Require Import ExactClosure ClosureIdx RepWL.
From BBB4.Census Require Import RepWLSearch.
From BBB4.Machines Require Import Cycle_Examples TCycler_Examples
                                  Closure_Examples.
Import ListNotations.

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

(** ** ClosureIdx-lex: the same controls for the lexicographic half

    [lex_check_idx] is exercised through its only wiring, the RepWL
    tier ([rw_check_neverqh_idx]), which is what the census runs.  The
    certificate is a PARAMETER there too, so the controls that matter
    are: a corrupt certificate must never buy an accept, and the
    interned checker must agree with the one it replaces. *)

(* 0RB---_0LC0RD_1RD1LB_1RB1LA: the never-QH residue core the RepWL
   tier decides at (L,T,t) = (2,2,0) (Tests/Census_Corruption.v) *)
Definition rwc : TM :=
  fun q s => match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB) | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC) | StB, S1 => Some (mkTrans S0 DR StD)
  | StC, S0 => Some (mkTrans S1 DR StD) | StC, S1 => Some (mkTrans S1 DL StB)
  | StD, S0 => Some (mkTrans S1 DR StB) | StD, S1 => Some (mkTrans S1 DL StA)
  end.

(** the certificate the untrusted search actually emits, materialised
    as DATA so the controls below replay it into both checkers instead
    of re-running the search once per (checker, state) *)
Definition rwc_certdata : list (St * list rwcomp) :=
  match csteps rwc 0 c0 with
  | None => []
  | Some cc =>
      match close rconf rconf_enc (rw_succs rwc 2 2) 8192
                  [] PositiveSet.empty [rw_seed 2 2 cc] with
      | None => []
      | Some Sl => map (fun q => (q, rw_procedure rwc 2 2 Sl q)) all_St
      end
  end.

Definition rwc_cert (q : St) : list rwcomp :=
  match List.find (fun p => st_eqb (fst p) q) rwc_certdata with
  | Some p => snd p
  | None => []
  end.

(* both checkers accept the genuine certificate *)
Example lex_idx_agrees_accept :
  (rw_check_neverqh rwc 2 2 0 8192 rwc_cert,
   rw_check_neverqh_idx rwc 2 2 0 8192 rwc_cert) = (true, true).
Proof. vm_compute. reflexivity. Qed.

(* an EMPTY certificate: [lex_edge_ok []] is [false], so every live
   state's check must fail -- in both checkers *)
Definition cert_empty (_ : St) : list rwcomp := [].

Example lex_idx_agrees_reject_empty :
  (rw_check_neverqh rwc 2 2 0 8192 cert_empty,
   rw_check_neverqh_idx rwc 2 2 0 8192 cert_empty) = (false, false).
Proof. vm_compute. reflexivity. Qed.

(* a constant rank table: no edge can strictly decrease *)
Definition cert_const (_ : St) : list rwcomp :=
  [RwRankE [(1%positive, 7)]].

Example lex_idx_agrees_reject_const :
  (rw_check_neverqh rwc 2 2 0 8192 cert_const,
   rw_check_neverqh_idx rwc 2 2 0 8192 cert_const) = (false, false).
Proof. vm_compute. reflexivity. Qed.

(* the genuine certificate does NOT rescue a quasihalter: state B goes
   quiet and the B-avoiding subgraph keeps its cycle *)
Definition qhc : TM :=
  fun q s => match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB) | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC) | StB, S1 => None
  | StC, S0 => Some (mkTrans S0 DL StD) | StC, S1 => Some (mkTrans S1 DL StC)
  | StD, S0 => Some (mkTrans S1 DR StC) | StD, S1 => Some (mkTrans S1 DL StD)
  end.

Example lex_idx_agrees_reject_qh :
  (rw_check_neverqh qhc 2 2 0 2000 rwc_cert,
   rw_check_neverqh_idx qhc 2 2 0 2000 rwc_cert) = (false, false).
Proof. vm_compute. reflexivity. Qed.

(* fuel exhaustion: the closure cannot even start *)
Example lex_idx_agrees_reject_fuel :
  (rw_check_neverqh rwc 2 2 0 0 rwc_cert,
   rw_check_neverqh_idx rwc 2 2 0 0 rwc_cert) = (false, false).
Proof. vm_compute. reflexivity. Qed.

(* The parameter gates are still gates on the interned side.  Small
   fuel deliberately: Coq's [&&] is a FUNCTION, so under call-by-value
   the closure runs even when the gate has already failed, and L = 0
   makes [rw_succs] explore garbage until the fuel runs out. *)
Example lex_idx_gates :
  (rw_check_neverqh_idx rwc 0 2 0 2000 rwc_cert,
   rw_check_neverqh_idx rwc 2 1 0 2000 rwc_cert) = (false, false).
Proof. vm_compute. reflexivity. Qed.

(** ** The footprint the whole point rests on *)

Print Assumptions idx_check_neverqh_sound.
Print Assumptions lex_check_idx_spec.
Print Assumptions rw_check_neverqh_idx_sound.
