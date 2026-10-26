(** State recurrence can use every read-symbol branch of the target state. *)
From Coq Require Import List Bool Arith.
From SmallBB Require Import Statement CTape PosEnc RankSearch RepWLSearch.
From SmallBB.Checkers Require Import NGram RepWL.
Import ListNotations.
Definition ng_state_rank tm ls rs (Sl:list cconf) q :=
 let nodes:=filter (fun a=>negb(st_eqb(fst a)q)) Sl in
 let g:=fold_left (fun g a=>adj_set g a
   (match ng_succs tm ls rs a with Some l=>filter(fun b=>negb(st_eqb(fst b)q))l |None=>[] end))
   nodes (PositiveMap.empty _) in
 match proc_rounds 200 tm (S(S(length nodes))) (S(length nodes*8+8)) nodes g [] with
 | Some cs=>cs |None=>[] end.
Definition rw_state_rank tm L T (Sl:list rconf) q :=
 let nodes:=filter (fun a=>negb(st_eqb(fst a)q)) Sl in
 let g:=fold_left (fun g a=>radj_set g a
   (match rw_succs tm L T a with Some l=>filter(fun b=>negb(st_eqb(fst b)q))l |None=>[] end))
   nodes (PositiveMap.empty _) in
 match rproc_rounds 100 tm (S(S(length nodes))) (S(length nodes*8+8)) nodes g [] with
 | Some cs=>cs |None=>[] end.
