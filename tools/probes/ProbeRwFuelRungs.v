(** Per-rung rw fuel: is there anything left to take?  (2026-08-09)

    docs/CENSUS_RUNTIME.md sizes a per-rung `rw_fuel` from
    ProbeRwFuelDiff's max-pops-actually-used column:

      (2,2,0) 3,581   (2,3,0) 3,300   (3,2,0) 3,664   (4,2,0) 4,132

    -- so only (4,2,0) needs anything near the shipped uniform 5,120,
    while (2,2,0) is the rung every machine reaching the tier pays.
    What that column does NOT say is how much a lower cap would refund,
    because a cap is only charged on closures that DIVERGE: a converging
    closure stops at its own size and never sees the fuel.

    This is ProbeRwFuel's [pclose] at the shipped 5,120, run per rung
    over the machines that actually REACH that rung under the shipped
    ladder order [(2,2,0); (3,2,0); (4,2,0); (2,3,0)] -- i.e. those the
    earlier rungs missed.  Per rung it reports

      (reaching, converged, exhausted, blocked, max pops among converged)

    and the refund from a per-rung cap is then (exhausted) x (5120 - cap)
    pops out of (total pops the rung burns).

    status: 0 = fuel exhausted, 1 = closed, 2 = succs gave None

    Untrusted probe: not in _CoqProject, loads into no proof. *)

From Coq Require Import Arith Bool List PArith.
From BBB4 Require Import BBB4_Statement CTape PosEnc Closure
                         ProbeWalkCommon ProbeTierCost.
From BBB4.Checkers Require Import RepWL.
From BBB4.Census Require Import TNF_QH Decide RepWLSearch.
Import ListNotations.

Definition F : nat := 5120.       (** Run.v's [rw_fuel_census] *)

Fixpoint pclose (tm : TM) (L T fuel nseen : nat) (sp : PositiveSet.t)
    (todo : list rconf) : nat * nat * nat :=
  match fuel with
  | 0 => (0, nseen, 0)
  | S f =>
      match todo with
      | [] => (1, nseen, S f)
      | a :: todo' =>
          if pset_mem rconf rconf_enc a sp
          then pclose tm L T f nseen sp todo'
          else match rw_succs tm L T a with
               | None => (2, nseen, S f)
               | Some l =>
                   pclose tm L T f (S nseen)
                     (pset_add rconf rconf_enc a sp) (l ++ todo')
               end
      end
  end.

Definition runc (L T : nat) (tm : TM) : nat * nat * nat :=
  match csteps tm 0 c0 with
  | None => (2, 0, 0)
  | Some cc => pclose tm L T F 0 PositiveSet.empty [rw_seed L T cc]
  end.

Definition stat (r : nat * nat * nat) : nat := fst (fst r).
Definition pops (r : nat * nat * nat) : nat := F - snd r.

Fixpoint cnt {B} (l : list B) (f : B -> bool) (acc : nat) : nat :=
  match l with [] => acc | x :: t => cnt t f (acc + (if f x then 1 else 0)) end.
Fixpoint sumf {B} (l : list B) (f : B -> nat) (acc : nat) : nat :=
  match l with [] => acc | x :: t => sumf t f (acc + f x) end.
Fixpoint maxf {B} (l : list B) (f : B -> nat) (acc : nat) : nat :=
  match l with [] => acc | x :: t => maxf t f (Nat.max acc (f x)) end.

(** machines still undecided by the rw rungs already tried *)
Definition reach (done : list (nat * nat * nat)) (ms : list TM) : list TM :=
  filter (fun tm => negb (anyb (fun '(L, T, t) => rw_tier tm L T t F) done)) ms.

(** (reaching, converged, exhausted, blocked, max pops among converged,
     total pops the rung burns) *)
Definition row (L T : nat) (ms : list TM)
  : nat * nat * nat * nat * nat * nat :=
  let rs := map (runc L T) ms in
  (List.length ms,
   cnt rs (fun r => stat r =? 1) 0,
   cnt rs (fun r => stat r =? 0) 0,
   cnt rs (fun r => stat r =? 2) 0,
   maxf (filter (fun r => stat r =? 1) rs) pops 0,
   sumf rs pops 0).

Definition pop0 : list TM := grp_RES.
Definition pop1 : list TM := Eval vm_compute in reach [(2,2,0)] pop0.
Definition pop2 : list TM := Eval vm_compute in reach [(2,2,0);(3,2,0)] pop0.
Definition pop3 : list TM :=
  Eval vm_compute in reach [(2,2,0);(3,2,0);(4,2,0)] pop0.

(* warm-up, not a measurement *)
Time Eval vm_compute in (row 2 2 (firstn 1 pop0)).

(* (reaching, converged, exhausted, blocked, max pops converged, total pops) *)
(* --- rung (2,2,0), the rung every machine pays --- *)
Time Eval vm_compute in (row 2 2 pop0).
(* --- rung (3,2,0) --- *)
Time Eval vm_compute in (row 3 2 pop1).
(* --- rung (4,2,0) --- *)
Time Eval vm_compute in (row 4 2 pop2).
(* --- rung (2,3,0) --- *)
Time Eval vm_compute in (row 2 3 pop3).
