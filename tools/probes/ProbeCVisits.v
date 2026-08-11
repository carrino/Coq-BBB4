(** Is [Cycle.cvisits] paying the eager-[orb] tax?  (2026-08-09)

    [cvisits] is the "does state q occur in the next len steps" walk:

      Fixpoint cvisits tm c len q :=
        match len with
        | 0 => false
        | S m => st_eqb (fst c) q
                 || match cstep tm c with
                    | Some c' => cvisits tm c' m q
                    | None => false end
        end

    [orb] is a FUNCTION, so under CBV both arguments evaluate: the
    recursive call runs to the full [len] even when q is the state of
    the very first configuration.  Every [cvisits] therefore costs
    [len] steps, never fewer -- the same trap as [existsb] in the rung
    ladders (docs/CENSUS_RUNTIME.md, 2026-08-07).

    It is reached from the guards of every closure checker
    ([Closure.closure_check_neverqh]: four states, [t] up to 1024, per
    rung, per tier), from [Cycle.cycle_check_neverqh]/[_qh] in the C
    tier, and from [Wrap.v]'s prefix-quiet gates in the qhb tier.

    [cvisitsS] is the same boolean function with a nested [if] --
    definitionally equal, since [orb b x] IS [if b then true else x].
    This A/B measures the tax at the shapes the census calls it with
    before anything in theories/ is touched: the counts must agree.

    Untrusted probe: not in _CoqProject, loads into no proof. *)

From Coq Require Import Arith Bool List.
From BBB4 Require Import BBB4_Statement CTape ProbeWalkCommon ProbeTierCost.
From BBB4.Checkers Require Import Cycle.
From BBB4.Census Require Import TNF_QH Decide.
Import ListNotations.

Fixpoint cvisitsS (tm : TM) (c : cconf) (len : nat) (q : St) : bool :=
  match len with
  | 0 => false
  | S m => if st_eqb (fst c) q
           then true
           else match cstep tm c with
                | Some c' => cvisitsS tm c' m q
                | None => false
                end
  end.

(** the prefix lengths the census actually asks for: the n-gram rungs'
    [t] (100/200/400/800), the rank and qhb rungs' [t]
    (0/64/256/1024) *)
Definition ts : list nat := [0; 64; 100; 200; 256; 400; 800; 1024].

Definition sweep (f : TM -> cconf -> nat -> St -> bool) (ms : list TM) : nat :=
  fold_left (fun a tm =>
    fold_left (fun a t =>
      fold_left (fun a q => a + (if f tm c0 t q then 1 else 0)) all_St a)
      ts a) ms 0.

(** the residue + n-gram population: the machines that reach the
    closure checkers at all *)
Definition popL : list TM := grp_RES ++ grp_N2 ++ grp_N3 ++ grp_N4 ++ grp_N6.
(** the C/T bulk, which reaches [cycle_check_neverqh] *)
Definition popB : list TM := grp_C ++ grp_T.

(* warm-up, not a measurement *)
Time Eval vm_compute in (sweep cvisits (firstn 1 popL)).

(* --- ladder population: eager vs short-circuit (counts must match) --- *)
Time Eval vm_compute in (sweep cvisits  popL).
Time Eval vm_compute in (sweep cvisitsS popL).

(* --- bulk population --- *)
Time Eval vm_compute in (sweep cvisits  popB).
Time Eval vm_compute in (sweep cvisitsS popB).
