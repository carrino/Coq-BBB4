From Coq Require Import Arith Bool List.
From BBB4 Require Import BBB4_Statement CTape PosEnc.
From BBB4.Census Require Import TNF_QH Decide.
Import ListNotations.
Definition T (w : Sym) (d : Dir) (n : St) := Some (mkTrans w d n).
Definition mk8 (a0 a1 b0 b1 c0' c1 d0 d1 : option Trans) : TM :=
  fun q s => match q, s with
  | StA, S0 => a0 | StA, S1 => a1 | StB, S0 => b0 | StB, S1 => b1
  | StC, S0 => c0' | StC, S1 => c1 | StD, S0 => d0 | StD, S1 => d1 end.
Definition qhbm : TM :=
  mk8 (T S0 DR StB) None (T S0 DL StC) None
      (T S0 DL StD) (T S1 DL StC) (T S1 DR StC) (T S1 DL StD).
Definition qlxm : TM :=
  mk8 (T S0 DR StB) None (T S0 DL StC) None
      (T S1 DL StD) (T S1 DR StC) (T S1 DR StC) (T S1 DL StD).
Definition rungs_t : list (nat * nat) := [(2, 100); (3, 200)].
Definition rrungs_t : list (nat * nat) := [(3, 0)].
Definition qhb_rungs_t : list (nat * nat) := [(2, 64)].
Definition rw_rungs_t : list (nat * nat * nat) := [(2, 2, 0)].
Eval vm_compute in (decide_easy 2000 130 1030 200000 512 rungs_t rrungs_t qhb_rungs_t
    rw_rungs_t 2000 (dmap_of []) (dmap_of []) (dmap_of []) (hmap_of []) qhbm).
Eval vm_compute in (decide_easy 2000 130 1030 200000 512 rungs_t rrungs_t qhb_rungs_t
    rw_rungs_t 2000 (dmap_of []) (dmap_of []) (dmap_of []) (hmap_of []) qlxm).
