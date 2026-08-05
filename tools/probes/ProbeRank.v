(** Fine-grained cost attribution inside rank_tier at rung (3,0) on
    holdout #1 (a machine the rank tier catches).  Mirrors rank_tier's
    body stage by stage; untrusted scaffolding. *)

From Coq Require Import Arith Bool List.
From BBB4 Require Import BBB4_Statement CTape PosEnc.
From BBB4.Checkers Require Import NGram.
From BBB4.Census Require Import TNF_QH Decide RankSearch.
Import ListNotations.

Definition T (w : Sym) (d : Dir) (n : St) := Some (mkTrans w d n).
Definition mk8 (a0 a1 b0 b1 c0' c1 d0 d1 : option Trans) : TM :=
  fun q s => match q, s with
  | StA, S0 => a0 | StA, S1 => a1 | StB, S0 => b0 | StB, S1 => b1
  | StC, S0 => c0' | StC, S1 => c1 | StD, S0 => d0 | StD, S1 => d1 end.

Definition hold1 : TM :=
  mk8 (T S1 DR StB) (T S1 DL StA)
      (T S1 DL StC) (T S0 DR StA)
      (T S1 DL StD) (T S0 DL StD)
      (T S0 DR StB) (T S0 DL StC).

(* rank_tier body at (n=3, t=0): cc = c0 *)
Definition n3 : nat := 3.
Definition a0p : cconf := ng_start n3 c0.
Definition lset0 : gset := gadds (ng_seed_side n3 []) gempty.
Definition rset0 : gset := gadds (ng_seed_side n3 []) gempty.

(* stage 1: the grow loop (restart rounds) *)
Time Eval vm_compute in
  (let '(l, r) := ng_grow hold1 a0p 200000 512 lset0 rset0 in
   (PositiveSet.cardinal l, PositiveSet.cardinal r)).

Definition grown : gset * gset :=
  Eval vm_compute in ng_grow hold1 a0p 200000 512 lset0 rset0.

(* stage 2: ONE closure exploration with the final sets *)
Time Eval vm_compute in
  (length (ng_explore hold1 (fst grown) (snd grown) 200000 []
             PositiveSet.empty [a0p])).

Definition closure0 : list cconf :=
  Eval vm_compute in
    ng_explore hold1 (fst grown) (snd grown) 200000 []
      PositiveSet.empty [a0p].

(* stage 3: the SCC/rank machinery, one state *)
Time Eval vm_compute in
  (length (rank_procedure hold1 (fst grown) (snd grown) closure0 StA)).
Time Eval vm_compute in
  (length (rank_procedure hold1 (fst grown) (snd grown) closure0 StD)).

(* stage 4: the verified lex re-check with the cert function *)
Time Eval vm_compute in
  (ngram_check_neverqh_lex hold1 n3 0 200000 512
     (fun q => rank_procedure hold1 (fst grown) (snd grown) closure0 q)).

(* reference: the whole tier *)
Time Eval vm_compute in (rank_tier hold1 3 0 200000 512).
