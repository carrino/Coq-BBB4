(** The decisive packed-arc measurement: the RANK stage.
    (UNTRUSTED probe, not in _CoqProject.)

    ProbeSplit.v puts ~32% of one n-gram ladder catch in
    [rank_ok]+[compute_ranks], and ProbeRankAdj.v shows that
    memoising the edges under [cconf] keys buys almost nothing (1.14x)
    because [cconf_enc] costs as much as recomputing [succs].  That is
    the case FOR packed keys: with a one-word node, both the edge
    table and the rank table become cheap.

    Here the whole rank stage runs on packed int63 nodes -- edges
    carried alongside the node (no lookup at all) and ranks in a small
    int-keyed assoc list -- against the current implementation on the
    same closure. *)

From Coq Require Import Arith Bool List ZArith Uint63.
From BBB4 Require Import BBB4_Statement CTape PosEnc Closure ProbePack.
From BBB4.Checkers Require Import NGram ExactClosure.
Import ListNotations.
Open Scope uint63_scope.

Definition Sl6 : list cconf := Eval vm_compute in
  ng_explore m6 (fst grown6) (snd grown6) F200k [] PositiveSet.empty [a06].
Definition succs6 := ng_succs m6 (fst grown6) (snd grown6).

(** ** Packed side: closure carrying its own edges *)

(* [close] emitting (node, succs) pairs -- CENSUS_RUNTIME item 3(b) *)
Fixpoint pkc_explore (tm : TM) (n : nat) (lg rg : gbits) (fuel : nat)
    (seen : list (int * list int)) (todo : list int)
  : option (list (int * list int)) :=
  match fuel with
  | O => None
  | S f =>
      match todo with
      | [] => Some seen
      | a :: todo' =>
          if existsb (fun p => fst p =? a) seen
          then pkc_explore tm n lg rg f seen todo'
          else match pk_succs tm n lg rg a with
               | None => None
               | Some l => pkc_explore tm n lg rg f ((a, l) :: seen) (l ++ todo')
               end
      end
  end.

Definition pk_st (a : int) : int := a land 3.

(* ranks: small int-keyed assoc list; closures here are tens of nodes *)
Fixpoint rk_get (r : list (int * nat)) (a : int) : nat :=
  match r with
  | [] => 0%nat
  | (k, v) :: t => if k =? a then v else rk_get t a
  end.
Fixpoint rk_has (r : list (int * nat)) (a : int) : bool :=
  match r with
  | [] => false
  | (k, _) :: t => if k =? a then true else rk_has t a
  end.

Definition pk_nonq (q : int) (p : int * list int) : list int :=
  filter (fun a' => negb (pk_st a' =? q)) (snd p).

Definition pk_peel_pass (q : int)
    (st : list (int * nat) * list (int * list int) * bool)
    (rem : list (int * list int))
  : list (int * nat) * list (int * list int) * bool :=
  fold_left (fun '(r, stuck, prog) p =>
    let sl := pk_nonq q p in
    if forallb (rk_has r) sl
    then ((fst p,
           match sl with
           | [] => 0%nat
           | _ => S (fold_left Nat.max (map (rk_get r) sl) 0%nat)
           end) :: r, stuck, true)
    else (r, p :: stuck, prog)) rem st.

Fixpoint pk_peel_iter (k : nat) (q : int) (r : list (int * nat))
    (rem : list (int * list int)) : list (int * nat) :=
  match k, rem with
  | 0, _ | _, [] => r
  | S k', _ =>
      let '(r', stuck, prog) := pk_peel_pass q (r, [], false) rem in
      if prog then pk_peel_iter k' q r' stuck else r'
  end.

Definition pk_ranks (Sl : list (int * list int)) (q : int)
  : list (int * nat) :=
  pk_peel_iter (S (List.length Sl)) q []
    (filter (fun p => negb (pk_st (fst p) =? q)) Sl).

Definition pk_rank_ok (Sl : list (int * list int)) (q : int)
    (r : list (int * nat)) : bool :=
  forallb (fun p =>
    if pk_st (fst p) =? q then true
    else forallb (fun a' =>
           implb (negb (pk_st a' =? q))
                 (Nat.ltb (rk_get r a') (rk_get r (fst p))))
         (snd p)) Sl.

Definition pk_all_states : list int := [0; 1; 2; 3].

Definition pk_live (Sl : list (int * list int)) : bool :=
  forallb (fun q => pk_rank_ok Sl q (pk_ranks Sl q)) pk_all_states.

Definition pk_stage_of (a0 : int) : bool :=
  match pkc_explore m6 n6 lg6 rg6 F200k [] [a0] with
  | None => false
  | Some Sl => pk_live Sl
  end.

(* NB: a CLOSED constant would be evaluated once and memoised by the VM,
   making any loop over it measure nothing -- hence the argument. *)
Definition pk_stage : bool := pk_stage_of p06.

(** ** A/B: same closure, same four states *)

Eval vm_compute in
  (forallb (fun q => rank_ok cconf ec_state succs6 Sl6 q
             (compute_ranks cconf cconf_enc ec_state succs6 Sl6 q)) all_St,
   pk_stage,
   match pkc_explore m6 n6 lg6 rg6 F200k [] [p06] with
   | Some Sl => List.length Sl | None => 0%nat end).

(* CURRENT: rank stage only (closure already built) *)
Fixpoint rep_rank_now (k : nat) (acc : bool) : bool :=
  match k with O => acc
  | S j => rep_rank_now j (acc && forallb (fun q =>
             rank_ok cconf ec_state succs6 Sl6 q
               (compute_ranks cconf cconf_enc ec_state succs6 Sl6 q)) all_St)
  end.

(* PACKED: rank stage only, off a pre-built edge-carrying closure *)
Definition PSl6 : list (int * list int) := Eval vm_compute in
  match pkc_explore m6 n6 lg6 rg6 F200k [] [p06] with
  | Some Sl => Sl | None => [] end.

Fixpoint rep_rank_pk (k : nat) (acc : bool) : bool :=
  match k with O => acc
  | S j => rep_rank_pk j (acc && pk_live PSl6)
  end.

(* Both end-to-end loops take the start node as a VARIABLE.  A closed
   application like [pk_stage_of p06] is hoisted into the VM's constant
   pool and evaluated ONCE, so a loop over it reports 0.001 s at any
   iteration count -- measured, and the reason this probe threads a
   parameter through. *)

(* PACKED, end to end: explore (carrying edges) + all four rank checks *)
Fixpoint rep_stage_pk (k : nat) (a0 : int) (acc : bool) : bool :=
  match k with O => acc
  | S j => rep_stage_pk j a0 (acc && pk_stage_of a0) end.

(* CURRENT, comparable end to end: explore + all four rank checks *)
Definition stage_now_of (a0 : cconf) : bool :=
  let Sl := ng_explore m6 (fst grown6) (snd grown6) F200k []
              PositiveSet.empty [a0] in
  closed_b cconf cconf_enc succs6 Sl &&
  forallb (fun q => rank_ok cconf ec_state succs6 Sl q
             (compute_ranks cconf cconf_enc ec_state succs6 Sl q)) all_St.

Fixpoint rep_stage_now (k : nat) (a0 : cconf) (acc : bool) : bool :=
  match k with O => acc
  | S j => rep_stage_now j a0 (acc && stage_now_of a0) end.

Time Eval vm_compute in rep_rank_now 200 true.
Time Eval vm_compute in rep_rank_pk 200 true.
Time Eval vm_compute in rep_stage_now 200 a06 true.
Time Eval vm_compute in rep_stage_pk 200 p06 true.
