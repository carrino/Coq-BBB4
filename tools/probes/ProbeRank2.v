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
  mk8 (T S1 DR StB) (T S1 DL StA) (T S1 DL StC) (T S0 DR StA)
      (T S1 DL StD) (T S0 DL StD) (T S0 DR StB) (T S0 DL StC).
Definition n3 : nat := 3.
Definition a0p : cconf := ng_start n3 c0.
Definition grown : gset * gset :=
  Eval vm_compute in
    ng_grow hold1 a0p 200000 512 (gadds (ng_seed_side n3 []) gempty)
            (gadds (ng_seed_side n3 []) gempty).
Definition closure0 : list cconf :=
  Eval vm_compute in
    ng_explore hold1 (fst grown) (snd grown) 200000 []
      PositiveSet.empty [a0p].
Definition nodes0 : list cconf :=
  Eval vm_compute in
    filter (fun a => negb (st_eqb (fst a) StD)) closure0.
Definition adj0 : Adj :=
  Eval vm_compute in
    build_adj hold1 (fst grown) (snd grown) StD nodes0.
(* stages of one rank_procedure call (q = StD, the slower state) *)
Time Eval vm_compute in (length (PositiveMap.elements
  (build_adj hold1 (fst grown) (snd grown) StD nodes0))).
Time Eval vm_compute in (length (scc_partition (S (length nodes0 * 8 + 8)) nodes0 adj0)).
Definition comps0 : list (list cconf) :=
  Eval vm_compute in scc_partition (S (length nodes0 * 8 + 8)) nodes0 adj0.
Time Eval vm_compute in (length (condensation_rank nodes0 adj0 comps0)).
Time Eval vm_compute in
  (match proc_rounds 200 hold1 (S (S (length nodes0)))
           (S (length nodes0 * 8 + 8)) nodes0 adj0 [] with
   | Some cs => length cs | None => 999 end).
Time Eval vm_compute in (length (rank_procedure hold1 (fst grown) (snd grown) closure0 StD)).
