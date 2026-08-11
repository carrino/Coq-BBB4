(** The n-gram analogue of ProbeRwFuel (2026-08-09).

    docs/CENSUS_RUNTIME.md names [ng_fuel = 200000] the prime suspect
    for the walk's 6.8 GB/unit peak RSS: it bounds the n-gram / rank /
    qhb closures, so in principle it caps CPU and memory together, and
    it is 39x the rw fuel that was just cut to 5120.

    A cap only costs anything that is actually REACHED.  [ng_fuel]
    appears in three places, all with the same meaning -- one worklist
    pop each:

      1. [ng_explore], inside [ng_grow]'s per-round gram-set growth;
      2. [ng_explore] again, directly, in [try_qhb_lex_at];
      3. [Closure.close], as the closure fuel of
         [closure_check_neverqh] in [ngram_check_neverqh].

    So the question is a measurement, not an argument: over the
    machines the walk actually reaches, how many pops do (1) and (3)
    consume?  [pexplore] and [pclose] are those two loops instrumented
    to report (status, nodes seen, fuel LEFT) instead of their result;
    same walk, same order, same successor function.

    status: 0 = fuel exhausted, 1 = worklist emptied,
            2 = succs gave None (close only -- ng_explore skips those)

    Untrusted probe: not in _CoqProject, loads into no proof. *)

From Coq Require Import Arith Bool List PArith.
From BBB4 Require Import BBB4_Statement CTape PosEnc
                         ProbeWalkCommon ProbeTierCost.
From BBB4.Checkers Require Import NGram.
From BBB4.Census Require Import TNF_QH Decide.
Import ListNotations.

Definition NGF : nat := 200000.   (** Run.v's [ng_fuel] *)
Definition NGR : nat := 512.      (** Run.v's [ng_rounds] *)

(** [ng_explore], instrumented.  Note it SKIPS blocked contexts rather
    than failing on them, so it has only two exits. *)
Fixpoint pexplore (tm : TM) (lset rset : gset) (fuel nseen : nat)
    (sp : PositiveSet.t) (todo : list cconf) : nat * nat * nat :=
  match fuel with
  | 0 => (0, nseen, 0)
  | S f =>
      match todo with
      | [] => (1, nseen, S f)
      | a :: todo' =>
          if pset_mem cconf cconf_enc a sp
          then pexplore tm lset rset f nseen sp todo'
          else let sp' := pset_add cconf cconf_enc a sp in
               match ng_succs tm lset rset a with
               | None => pexplore tm lset rset f (S nseen) sp' todo'
               | Some l => pexplore tm lset rset f (S nseen) sp' (l ++ todo')
               end
      end
  end.

(** [Closure.close] at the n-gram successor function, instrumented. *)
Fixpoint pclose (tm : TM) (lset rset : gset) (fuel nseen : nat)
    (sp : PositiveSet.t) (todo : list cconf) : nat * nat * nat :=
  match fuel with
  | 0 => (0, nseen, 0)
  | S f =>
      match todo with
      | [] => (1, nseen, S f)
      | a :: todo' =>
          if pset_mem cconf cconf_enc a sp
          then pclose tm lset rset f nseen sp todo'
          else match ng_succs tm lset rset a with
               | None => (2, nseen, S f)
               | Some l =>
                   pclose tm lset rset f (S nseen)
                     (pset_add cconf cconf_enc a sp) (l ++ todo')
               end
      end
  end.

(** one machine at one rung: (explore status, explore pops used,
    close status, close pops used) *)
Definition ngrun (n t : nat) (tm : TM) : nat * nat * nat * nat :=
  match csteps tm t c0 with
  | None => (9, 0, 9, 0)
  | Some cc =>
      let '(q, (l, h, r)) := cc in
      let lset0 := gadds (ng_seed_side n l) gempty in
      let rset0 := gadds (ng_seed_side n r) gempty in
      let a0 := ng_start n cc in
      let '(lset, rset) := ng_grow tm a0 NGF NGR lset0 rset0 in
      let '(es, _, ef) := pexplore tm lset rset NGF 0 PositiveSet.empty [a0] in
      let '(cs, _, cf) := pclose tm lset rset NGF 0 PositiveSet.empty [a0] in
      (es, NGF - ef, cs, NGF - cf)
  end.

(** aggregate over a machine list: (# fuel-exhausted explores,
    max explore pops, # fuel-exhausted closes, max close pops) *)
Definition agg (n t : nat) (ms : list TM) : nat * nat * nat * nat :=
  fold_left (fun acc tm =>
    let '(be, me, bc, mc) := acc in
    let '(es, ep, cs, cp) := ngrun n t tm in
    (be + (if es =? 0 then 1 else 0), Nat.max me ep,
     bc + (if cs =? 0 then 1 else 0), Nat.max mc cp))
    ms (0, 0, 0, 0).

(** the machines that reach the ladder at all: the mirror-residue
    sample plus the four n-gram tier samples *)
Definition pop : list TM :=
  grp_RES ++ grp_N2 ++ grp_N3 ++ grp_N4 ++ grp_N6.

(* (explores that burned all 200000, max explore pops,
    closes that burned all 200000, max close pops) *)
(* --- rung (2,100) --- *)
Time Eval vm_compute in (List.length pop, agg 2 100 pop).
(* --- rung (3,200) --- *)
Time Eval vm_compute in (agg 3 200 pop).
(* --- rung (4,400) --- *)
Time Eval vm_compute in (agg 4 400 pop).
(* --- rung (6,800) --- *)
Time Eval vm_compute in (agg 6 800 pop).
