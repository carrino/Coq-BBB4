(** Ceiling probe for CENSUS_RUNTIME item 3(b): stop recomputing
    [succs] per state in the rank tier.  (UNTRUSTED, not in
    _CoqProject.)

    [closure_check_neverqh] runs, per catch, [rank_ok Sl q
    (compute_ranks Sl q)] for EVERY state q in [all_St].  Both
    [rank_ok] and [compute_ranks]/[nonq_succs] call [succs a] afresh
    for every node, so one catch recomputes the whole successor
    relation ~8 times.  Here the edge list is built ONCE and the same
    checks run off it, which bounds what a [close]-emits-edges
    restructure can buy. *)

From Coq Require Import Arith Bool List PArith.
From Coq Require Import FSets.FMapPositive.
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
Definition a06 : cconf := Eval vm_compute in ng_start n6 cc6.
Definition grown6 : gset * gset := Eval vm_compute in
  ng_grow m6 a06 F200k R512
    (match cc6 with (q,(l,h,r)) => gadds (ng_seed_side n6 l) gempty end)
    (match cc6 with (q,(l,h,r)) => gadds (ng_seed_side n6 r) gempty end).
Definition Sl6 : list cconf := Eval vm_compute in
  ng_explore m6 (fst grown6) (snd grown6) F200k [] PositiveSet.empty [a06].
Definition succs6 := ng_succs m6 (fst grown6) (snd grown6).

(** ** The edge list, built once *)

Definition edges_of (Sl : list cconf) : PositiveMap.tree (list cconf) :=
  fold_left (fun g a =>
    PositiveMap.add (cconf_enc a)
      (match succs6 a with Some l => l | None => [] end) g)
    Sl (PositiveMap.empty _).

Definition eget (g : PositiveMap.tree (list cconf)) (a : cconf) : list cconf :=
  match PositiveMap.find (cconf_enc a) g with Some l => l | None => [] end.

(* [succs] returning None must still reject, so record it separately *)
Definition alldef (Sl : list cconf) : bool :=
  forallb (fun a => match succs6 a with Some _ => true | None => false end) Sl.

(** rank_ok off the prebuilt edges *)
Definition rank_ok_adj (g : PositiveMap.tree (list cconf)) (Sl : list cconf)
    (q : St) (rnk : cconf -> nat) : bool :=
  forallb (fun a =>
    if st_eqb (ec_state a) q then true
    else forallb (fun a' =>
           implb (negb (st_eqb (ec_state a') q)) (Nat.ltb (rnk a') (rnk a)))
         (eget g a)) Sl.

(** compute_ranks off the prebuilt edges (same peeling shape) *)
Definition nonq_adj (g : PositiveMap.tree (list cconf)) (q : St) (a : cconf)
  : list cconf :=
  filter (fun a' => negb (st_eqb (ec_state a') q)) (eget g a).

Definition ranked' (r : PositiveMap.tree nat) (a : cconf) : bool :=
  match PositiveMap.find (cconf_enc a) r with Some _ => true | None => false end.
Definition lookup_rank' (r : PositiveMap.tree nat) (a : cconf) : nat :=
  pmap_get cconf cconf_enc r a.

Definition peel_pass' (g : PositiveMap.tree (list cconf)) (q : St)
    (st : PositiveMap.tree nat * list cconf * bool) (rem : list cconf)
  : PositiveMap.tree nat * list cconf * bool :=
  fold_left (fun '(r, stuck, prog) a =>
    let sl := nonq_adj g q a in
    if forallb (ranked' r) sl
    then (PositiveMap.add (cconf_enc a)
            (match sl with
             | [] => 0
             | _ => S (fold_left Nat.max (map (lookup_rank' r) sl) 0)
             end) r, stuck, true)
    else (r, a :: stuck, prog)) rem st.

Fixpoint peel_iter' (k : nat) (g : PositiveMap.tree (list cconf)) (q : St)
    (r : PositiveMap.tree nat) (rem : list cconf) : PositiveMap.tree nat :=
  match k, rem with
  | 0, _ | _, [] => r
  | S k', _ =>
      let '(r', stuck, prog) := peel_pass' g q (r, [], false) rem in
      if prog then peel_iter' k' g q r' stuck else r'
  end.

Definition compute_ranks' (g : PositiveMap.tree (list cconf))
    (Sl : list cconf) (q : St) : cconf -> nat :=
  lookup_rank'
    (peel_iter' (S (List.length Sl)) g q (PositiveMap.empty nat)
       (filter (fun a => negb (st_eqb (ec_state a) q)) Sl)).

(** ** A/B *)

(* CURRENT: per-state recomputation of succs, as in closure_check_neverqh *)
Fixpoint rep_now (k : nat) (acc : bool) : bool :=
  match k with O => acc
  | S j => rep_now j (acc && forallb (fun q =>
             rank_ok cconf ec_state succs6 Sl6 q
               (compute_ranks cconf cconf_enc ec_state succs6 Sl6 q)) all_St)
  end.

(* PREBUILT: one edge list, reused by all four states *)
Fixpoint rep_adj (k : nat) (acc : bool) : bool :=
  match k with O => acc
  | S j => rep_adj j (acc &&
             (let g := edges_of Sl6 in
              alldef Sl6 &&
              forallb (fun q => rank_ok_adj g Sl6 q (compute_ranks' g Sl6 q))
                      all_St))
  end.

(* agreement *)
Eval vm_compute in
  (forallb (fun q => rank_ok cconf ec_state succs6 Sl6 q
             (compute_ranks cconf cconf_enc ec_state succs6 Sl6 q)) all_St,
   let g := edges_of Sl6 in
   alldef Sl6 &&
   forallb (fun q => rank_ok_adj g Sl6 q (compute_ranks' g Sl6 q)) all_St).

Time Eval vm_compute in rep_now 200 true.
Time Eval vm_compute in rep_adj 200 true.
