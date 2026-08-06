(* Where the rw verified stage's time actually goes at rung (3,2,0),
   and the ladder-level A/B (untrusted probe).

   ProbeRwIdx measured the interned checker at 1.98x on the (2,2,0)
   rung and 1.04x on (3,2,0).  These rows attribute the (3,2,0)
   checker per stage so the flat row is explained rather than
   reported.  Each row prints its own count; divide by 32 for the
   per-machine figure. *)

From Coq Require Import Arith Bool List ZArith PArith.
From Coq Require Import FSets.FMapPositive.
From BBB4 Require Import BBB4_Statement CTape PosEnc Closure
                         ProbeWalkCommon ProbeTierCost.
From BBB4.Checkers Require Import Cycle ClosureIdx RepWL.
From BBB4.Census Require Import TNF_QH Decide RepWLSearch.
Import ListNotations.

Definition F8k : nat := 8192.

Definition rwl : list TM := Eval vm_compute in
  filter (fun tm => rw_tier tm 2 2 0 F8k || rw_tier tm 3 2 0 F8k
                    || rw_tier tm 4 2 0 F8k || rw_tier tm 2 3 0 F8k)
         grp_RES.

(* --- the pieces of the (3,2,0) verified stage --------------------- *)

Definition poolof (tm : TM) : list rconf :=
  match csteps tm 0 c0 with
  | None => []
  | Some cc =>
      match close rconf rconf_enc (rw_succs tm 3 2) F8k
                  [] MSetPositive.PositiveSet.empty [rw_seed 3 2 cc] with
      | None => []
      | Some Sl => Sl
      end
  end.

Definition certdata (tm : TM) : list (St * list rwcomp) :=
  match csteps tm 0 c0 with
  | None => []
  | Some cc =>
      match close rconf rconf_enc (rw_succs tm 3 2) F8k
                  [] MSetPositive.PositiveSet.empty [rw_seed 3 2 cc] with
      | None => []
      | Some Sl =>
          map (fun q =>
                 (q, if cvisits tm c0 0 q
                        || existsb (fun a => st_eqb (rw_state a) q) Sl
                     then rw_procedure tm 3 2 Sl q
                     else [])) all_St
      end
  end.

Definition certfun (d : list (St * list rwcomp)) (q : St) : list rwcomp :=
  match List.find (fun p => st_eqb (fst p) q) d with
  | Some p => snd p | None => [] end.

Definition CD : list (TM * list (St * list rwcomp)) := Eval vm_compute in
  map (fun tm => (tm, certdata tm)) rwl.

Fixpoint sumf {B : Type} (l : list B) (f : B -> nat) (acc : nat) : nat :=
  match l with [] => acc | x :: t => sumf t f (acc + f x) end.

(* A. close alone (pool sizes) *)
Definition s_close (p : TM * list (St * list rwcomp)) : nat :=
  List.length (poolof (fst p)).

(* B. the certificate DENOTATION: rpm_of / rps_of per component per
   state -- common to both checkers, and the suspect for the flat row *)
Definition s_denote (p : TM * list (St * list rwcomp)) : nat :=
  sumf (snd p) (fun e => List.length (map (rw_comp_denote (fst p)) (snd e))) 0.

(* B'. the interned side's denotation, same shape *)
Definition s_epres (p : TM * list (St * list rwcomp)) : nat :=
  sumf (snd p) (fun e => List.length (map (rw_epres (fst p)) (snd e))) 0.

(* C. close + the one edges_of pass *)
Definition s_edges (p : TM * list (St * list rwcomp)) : nat :=
  let tm := fst p in
  let pool := poolof tm in
  match edges_of rconf rconf_enc rw_state (rw_succs tm 3 2)
          (build_imap rconf rconf_enc pool) pool with
  | Some rows => List.length rows
  | None => 0
  end.

(* D/E. the two whole checkers *)
Definition s_old (p : TM * list (St * list rwcomp)) : nat :=
  if rw_check_neverqh (fst p) 3 2 0 F8k (certfun (snd p)) then 1 else 0.
Definition s_new (p : TM * list (St * list rwcomp)) : nat :=
  if rw_check_neverqh_idx (fst p) 3 2 0 F8k (certfun (snd p)) then 1 else 0.

Eval vm_compute in List.length CD.
Time Eval vm_compute in sumf CD s_close 0.
Time Eval vm_compute in sumf CD s_denote 0.
Time Eval vm_compute in sumf CD s_epres 0.
Time Eval vm_compute in sumf CD s_edges 0.
Time Eval vm_compute in sumf CD s_old 0.
Time Eval vm_compute in sumf CD s_new 0.

(* the ladder as the walk actually pays it is ProbeRwLadder.v *)
