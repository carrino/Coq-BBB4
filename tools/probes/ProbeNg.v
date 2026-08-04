From Coq Require Import Arith Bool List.
From BBB4 Require Import BBB4_Statement CTape PosEnc.
From BBB4.Checkers Require Import NGram.
Import ListNotations.
Definition T (w : Sym) (d : Dir) (n : St) := Some (mkTrans w d n).
Definition mk8 (a0 a1 b0 b1 c0' c1 d0 d1 : option Trans) : TM :=
  fun q s => match q, s with
  | StA, S0 => a0 | StA, S1 => a1 | StB, S0 => b0 | StB, S1 => b1
  | StC, S0 => c0' | StC, S1 => c1 | StD, S0 => d0 | StD, S1 => d1 end.
(* 1RB0LA_1RC1LA_1RD0LB_1LD1RC : caught at rung (6,800) *)
Definition m6 : TM :=
  mk8 (T S1 DR StB) (T S0 DL StA) (T S1 DR StC) (T S1 DL StA)
      (T S1 DR StD) (T S0 DL StB) (T S1 DL StD) (T S1 DR StC).
(* 1RB0LA_1RC1LA_1RD1LB_1LD1RC : caught at rung (4,400) *)
Definition m4 : TM :=
  mk8 (T S1 DR StB) (T S0 DL StA) (T S1 DR StC) (T S1 DL StA)
      (T S1 DR StD) (T S1 DL StB) (T S1 DL StD) (T S1 DR StC).
(* the winning-rung checks *)
Time Eval vm_compute in (ngram_check_neverqh m6 6 800 200000 512).
Time Eval vm_compute in (ngram_check_neverqh m4 4 400 200000 512).
(* failing earlier rungs, for the record *)
Time Eval vm_compute in (ngram_check_neverqh m6 4 400 200000 512).
(* stage: grow at the winning rung *)
Definition cc6 : cconf := match csteps m6 800 c0 with Some c => c | None => c0 end.
Definition seed6l : gset :=
  match cc6 with (q,(l,h,r)) => gadds (ng_seed_side 6 l) gempty end.
Definition seed6r : gset :=
  match cc6 with (q,(l,h,r)) => gadds (ng_seed_side 6 r) gempty end.
Time Eval vm_compute in
  (let '(ls, rs) := ng_grow m6 (ng_start 6 cc6) 200000 512 seed6l seed6r in
   (PositiveSet.cardinal ls, PositiveSet.cardinal rs)).
Definition grown6 : gset * gset :=
  Eval vm_compute in ng_grow m6 (ng_start 6 cc6) 200000 512 seed6l seed6r.
Time Eval vm_compute in
  (length (ng_explore m6 (fst grown6) (snd grown6) 200000 []
             PositiveSet.empty [ng_start 6 cc6])).
