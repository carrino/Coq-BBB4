(** Where does one n-gram ladder catch actually spend its time?
    (UNTRUSTED probe, not in _CoqProject.)

    Splits [ngram_check_neverqh] into its stages on the same machine
    and rung the packed A/B uses (ProbePack.v), each stage looped so
    the per-stage cost is above timer noise.  Fuel is a NAMED constant
    for the same reason as in ProbePack.v: an inline literal is
    re-expanded into a 200,000-deep unary nat at every use. *)

From Coq Require Import Arith Bool List.
From BBB4 Require Import BBB4_Statement CTape PosEnc Closure.
From BBB4.Checkers Require Import NGram ExactClosure.
Import ListNotations.

Definition T (w : Sym) (d : Dir) (n : St) := Some (mkTrans w d n).
Definition mk8 (a0 a1 b0 b1 c0' c1 d0 d1 : option Trans) : TM :=
  fun q s => match q, s with
  | StA, S0 => a0 | StA, S1 => a1 | StB, S0 => b0 | StB, S1 => b1
  | StC, S0 => c0' | StC, S1 => c1 | StD, S0 => d0 | StD, S1 => d1 end.

Definition m6 : TM :=
  mk8 (T S1 DR StB) (T S0 DL StA) (T S1 DR StC) (T S1 DL StA)
      (T S1 DR StD) (T S0 DL StB) (T S1 DL StD) (T S1 DR StC).

Definition F200k : nat := 200000.
Definition R512 : nat := 512.
Definition n6 : nat := 6.
Definition t6 : nat := 800.

Definition cc6 : cconf := Eval vm_compute in
  match csteps m6 t6 c0 with Some c => c | None => c0 end.
Definition seed6l : gset := Eval vm_compute in
  match cc6 with (q,(l,h,r)) => gadds (ng_seed_side n6 l) gempty end.
Definition seed6r : gset := Eval vm_compute in
  match cc6 with (q,(l,h,r)) => gadds (ng_seed_side n6 r) gempty end.
Definition a06 : cconf := Eval vm_compute in ng_start n6 cc6.
Definition grown6 : gset * gset := Eval vm_compute in
  ng_grow m6 a06 F200k R512 seed6l seed6r.
Definition Sl6 : list cconf := Eval vm_compute in
  ng_explore m6 (fst grown6) (snd grown6) F200k [] PositiveSet.empty [a06].

Definition succs6 := ng_succs m6 (fst grown6) (snd grown6).

(* --- stage 1: the prefix simulation csteps t --- *)
Fixpoint rep_sim (k : nat) (acc : bool) : bool :=
  match k with O => acc
  | S j => rep_sim j (acc && match csteps m6 t6 c0 with Some _ => true | None => false end)
  end.

(* --- stage 2: the untrusted gram-set search --- *)
Fixpoint rep_grow (k : nat) (acc : bool) : bool :=
  match k with O => acc
  | S j => rep_grow j (acc && (Nat.eqb (PositiveSet.cardinal
             (fst (ng_grow m6 a06 F200k R512 seed6l seed6r))) 5))
  end.

(* --- stage 3: one closure exploration --- *)
Fixpoint rep_expl (k : nat) (acc : bool) : bool :=
  match k with O => acc
  | S j => rep_expl j (acc && Nat.eqb (List.length
             (ng_explore m6 (fst grown6) (snd grown6) F200k []
                PositiveSet.empty [a06])) 29)
  end.

(* --- stage 4: the verified closedness re-check --- *)
Fixpoint rep_closed (k : nat) (acc : bool) : bool :=
  match k with O => acc
  | S j => rep_closed j (acc && closed_b cconf cconf_enc succs6 Sl6)
  end.

(* --- stage 5: ranks + the verified rank check, per state --- *)
Fixpoint rep_rank (k : nat) (acc : bool) : bool :=
  match k with O => acc
  | S j => rep_rank j (acc && forallb (fun q =>
             rank_ok cconf ec_state succs6 Sl6 q
               (compute_ranks cconf cconf_enc ec_state succs6 Sl6 q)) all_St)
  end.

(* --- the whole checker, for reference --- *)
Fixpoint rep_full (k : nat) (acc : bool) : bool :=
  match k with O => acc
  | S j => rep_full j (acc && ngram_check_neverqh m6 n6 t6 F200k R512)
  end.

Eval vm_compute in (List.length Sl6, PositiveSet.cardinal (fst grown6),
                    PositiveSet.cardinal (snd grown6)).
Time Eval vm_compute in rep_sim 200 true.
Time Eval vm_compute in rep_grow 200 true.
Time Eval vm_compute in rep_expl 200 true.
Time Eval vm_compute in rep_closed 200 true.
Time Eval vm_compute in rep_rank 200 true.
Time Eval vm_compute in rep_full 200 true.
