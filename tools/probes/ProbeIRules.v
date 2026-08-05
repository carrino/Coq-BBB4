From Coq Require Import ZArith List.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Checkers Require Import Cycle.
From BBB4.Checkers.IRules Require Import Expr RLE Engine Rules Meta.
Import ListNotations.
Open Scope Z_scope.
Definition mk (w : Sym) (d : Dir) (n : St) : option Trans :=
  Some (mkTrans w d n).
(* batch 00, machine 1: anchor 2,802,368 *)
Definition tmX : TM := fun q s =>
  match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S1 DR StA
  | StB, S0 => mk S0 DL StC | StB, S1 => mk S0 DL StD
  | StC, S0 => mk S0 DR StB | StC, S1 => mk S1 DL StC
  | StD, S0 => mk S1 DR StA | StD, S1 => mk S1 DL StD
  end.
Definition certX : IRCert := mkIRCert
  2802368%nat (2048) (3) (2) (0) StC S0
  []
  [(S1, 1, 0)]
  [mkRule StA S0 [(S1, RV (2) (1))] [(S1, RV (-1) (2))]].
Time Eval vm_compute in (match check_rules tmX 300000%nat (c_rules certX) with Some _ => true | None => false end).
Time Eval vm_compute in (match csteps tmX (c_anchor certX) c0 with Some (q,_) => q | None => StA end).
Time Eval vm_compute in (cvisits tmX c0 (c_anchor certX) StA).
Time Eval vm_compute in (irules_check_neverqh tmX certX 300000%nat).

(* finer attribution *)
Definition rulesX := Eval vm_compute in
  match check_rules tmX 300000%nat (c_rules certX) with
  | Some r => r | None => [] end.
Time Eval vm_compute in
  (match replay tmX [c_kmin certX] rulesX
          (fun c => scfg_eqb c (want_cfg certX))
          300000%nat false (tpl_cfg certX) with
   | Some (_, F) => length F | None => 99%nat end).
Definition atX := Eval vm_compute in (csteps tmX (c_anchor certX) c0).
Time Eval vm_compute in
  (match atX with
   | Some (q, (l, h, r)) =>
       (lpad_eqb l (dside (fun _ => c_k0 certX) (tpl_start (c_TL certX))),
        lpad_eqb r (dside (fun _ => c_k0 certX) (tpl_start (c_TR certX))))
   | None => (false, false) end).
Time Eval vm_compute in (cvisits tmX c0 (c_anchor certX) StD).
