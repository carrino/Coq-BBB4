(** A/B of the REAL checkers (UNTRUSTED probe, not in _CoqProject):
    [Closure.closure_check_neverqh] vs [ClosureIdx.idx_check_neverqh],
    both instantiated at the n-gram abstraction, same machine, same
    gram sets, same [close] search.

    ProbeIntern.v measured a stand-in re-implementation; this measures
    the file that would actually be wired into the ladder. *)

From Coq Require Import Arith Bool List.
From BBB4 Require Import BBB4_Statement CTape PosEnc Closure.
From BBB4.Checkers Require Import NGram ExactClosure ClosureIdx.
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

(* fuel/rounds as NAMED constants: an inline literal is
   [Init.Nat.of_num_uint ...], re-expanded at every use *)
Definition F200k : nat := 200000.
Definition R512 : nat := 512.

Section Inst.
  Variable tm : TM.
  Variable n t : nat.

  Definition cc : cconf :=
    match csteps tm t c0 with Some c => c | None => c0 end.
  Definition sets : gset * gset :=
    ng_grow tm (ng_start n cc) F200k R512
      (match cc with (q,(l,h,r)) => gadds (ng_seed_side n l) gempty end)
      (match cc with (q,(l,h,r)) => gadds (ng_seed_side n r) gempty end).
End Inst.

Definition cc6 : cconf := Eval vm_compute in cc m6 800.
Definition st6 : gset * gset := Eval vm_compute in sets m6 6 800.
Definition a06 : cconf := Eval vm_compute in ng_start 6 cc6.
Definition sc6 := ng_succs m6 (fst st6) (snd st6).

Definition cc4 : cconf := Eval vm_compute in cc m4 400.
Definition st4 : gset * gset := Eval vm_compute in sets m4 4 400.
Definition a04 : cconf := Eval vm_compute in ng_start 4 cc4.
Definition sc4 := ng_succs m4 (fst st4) (snd st4).

(** the two checkers, same arguments *)
Definition now6 (a0 : cconf) : bool :=
  closure_check_neverqh m6 cconf cconf_enc ec_state sc6 800 F200k a0.
Definition idx6 (a0 : cconf) : bool :=
  idx_check_neverqh m6 cconf cconf_enc ec_state sc6 800 F200k a0 idx_ranks.

Definition now4 (a0 : cconf) : bool :=
  closure_check_neverqh m4 cconf cconf_enc ec_state sc4 400 F200k a0.
Definition idx4 (a0 : cconf) : bool :=
  idx_check_neverqh m4 cconf cconf_enc ec_state sc4 400 F200k a0 idx_ranks.

(* both must say true on the machines their rung catches *)
Eval vm_compute in (now6 a06, idx6 a06, now4 a04, idx4 a04).

(* and both must say false when the rung is too weak (m6 at n=4) *)
Definition cc64 : cconf := Eval vm_compute in cc m6 400.
Definition st64 : gset * gset := Eval vm_compute in sets m6 4 400.
Definition a064 : cconf := Eval vm_compute in ng_start 4 cc64.
Definition sc64 := ng_succs m6 (fst st64) (snd st64).
Eval vm_compute in
  (closure_check_neverqh m6 cconf cconf_enc ec_state sc64 400 F200k a064,
   idx_check_neverqh m6 cconf cconf_enc ec_state sc64 400 F200k a064 idx_ranks).

(* loops take the start node as a parameter: a closed application gets
   hoisted into the VM constant pool and evaluated once *)
Fixpoint rep_now6 (k : nat) (a0 : cconf) (acc : bool) : bool :=
  match k with O => acc | S j => rep_now6 j a0 (acc && now6 a0) end.
Fixpoint rep_idx6 (k : nat) (a0 : cconf) (acc : bool) : bool :=
  match k with O => acc | S j => rep_idx6 j a0 (acc && idx6 a0) end.
Fixpoint rep_now4 (k : nat) (a0 : cconf) (acc : bool) : bool :=
  match k with O => acc | S j => rep_now4 j a0 (acc && now4 a0) end.
Fixpoint rep_idx4 (k : nat) (a0 : cconf) (acc : bool) : bool :=
  match k with O => acc | S j => rep_idx4 j a0 (acc && idx4 a0) end.

Time Eval vm_compute in rep_now6 200 a06 true.
Time Eval vm_compute in rep_idx6 200 a06 true.
Time Eval vm_compute in rep_now4 200 a04 true.
Time Eval vm_compute in rep_idx4 200 a04 true.
