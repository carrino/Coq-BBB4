(* The one-line fact this round turned on, in isolation (2026-08-07).

   docs/CENSUS_RUNTIME.md previously recorded, in "The winning-attempt
   A/B closes the loop":

     the probe's own "reordered pipeline" rows are eager-orb artifacts
     -- [a || b] evaluates both sides under CBV [...]  The real
     decider's [existsb] short-circuits correctly.

   The second sentence is FALSE.  [List.existsb] is

     Fixpoint existsb l := match l with [] => false | a::l => f a || existsb l end

   and [orb] is a FUNCTION, so [existsb] is exactly as eager as the
   bare [||] -- it runs [f] on EVERY element even after one returned
   true.  [forallb] is [f a && forallb l] and is eager the same way.

   Every rung ladder in Census/Decide.v was an [existsb] whose body is
   a whole tier attempt, so each ladder cost the SUM of all its rungs
   on every machine.  This file is the isolated demonstration; the
   pipeline-level numbers are in ProbeStrict.v / ProbeScanStrict.v.

   Untrusted probe: not in _CoqProject, loads into no proof. *)

From Coq Require Import List Arith Bool.
Import ListNotations.

(* an expensive boolean that returns [b] *)
Fixpoint burn (n acc : nat) : nat :=
  match n with 0 => acc | S k => burn k (S acc) end.
Definition cost (n : nat) (b : bool) : bool :=
  if Nat.eqb (burn n 0) n then b else negb b.

(* element 0 decides; elements 1..3 are expensive *)
Definition f (i : nat) : bool :=
  match i with 0 => cost 10 true | _ => cost 4000000 false end.
Definition g (i : nat) : bool :=
  match i with 0 => cost 10 false | _ => cost 4000000 true end.

Fixpoint anyb (h : nat -> bool) (l : list nat) : bool :=
  match l with [] => false | i :: r => if h i then true else anyb h r end.
Fixpoint allb (h : nat -> bool) (l : list nat) : bool :=
  match l with [] => true | i :: r => if h i then allb h r else false end.

(* identical values, and the cost of the deciding element alone *)
Time Eval vm_compute in existsb f [0;1;2;3].
Time Eval vm_compute in anyb   f [0;1;2;3].
Time Eval vm_compute in f 0.

Time Eval vm_compute in forallb g [0;1;2;3].
Time Eval vm_compute in allb    g [0;1;2;3].
