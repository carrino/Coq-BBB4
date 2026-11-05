(** A larger instruction-level witness; binary fuel throughout evaluation. *)
From Coq Require Import Arith Lia Bool NArith.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBBWait42 Require Import Spec BinaryScan Witness.
Definition instruction_hit (q : Instr) (c : cconf) :=
  instr_eqb (instr_of (lift c)) q.

Theorem first_instruction_hitN_lower : forall tm q B L,
  first_hitN tm (instruction_hit q) B L = true ->
  forall w, WaitBoundTr (N.to_nat B) w -> N.to_nat L <= w.
Proof.
  intros tm q B L HC w HW.
  destruct (first_hitN_sound _ _ _ _ HC) as [(d&HD&Hhit) Hnone].
  assert (HQ : instr_of (lift d) = q) by (apply instr_eqb_spec; exact Hhit).
  assert (HV : FiresAt tm q (N.to_nat B + N.to_nat L)).
  { exists (lift d). split; [rewrite <- lift_c0; apply csteps_lift; exact HD|exact HQ]. }
  destruct (HW tm q (ex_intro _ _ (conj (Nat.le_add_r _ _) HV))) as (t&Ht&Htw&HVt).
  destruct (le_dec (N.to_nat B + N.to_nat L) t) as [Hle|Hlt]; [lia|].
  destruct (csteps_prefix tm t (N.to_nat B + N.to_nat L) c0 d) as (e&HE&_); [lia|exact HD|].
  assert (Hfalse : instruction_hit q e = false) by (eapply Hnone; eauto; lia).
  destruct HVt as (E&Hrun&Hstate).
  assert (Hlift : stepn tm t InitES = Some (lift e)).
  { rewrite <- lift_c0; apply csteps_lift; exact HE. }
  rewrite Hlift in Hrun; injection Hrun as <-.
  unfold instruction_hit in Hfalse.
  assert (instr_eqb (instr_of (lift e)) q = true) by (apply instr_eqb_spec; exact Hstate).
  congruence.
Qed.

(** 1RB0LD_1RC1RB_1LA1LC_0RC1LA *)
Definition instruction_wait_machine : TM := fun q a => Some
  (match q,a with
   | StA,S0 => mkTrans S1 DR StB | StA,S1 => mkTrans S0 DL StD
   | StB,S0 => mkTrans S1 DR StC | StB,S1 => mkTrans S1 DR StB
   | StC,S0 => mkTrans S1 DL StA | StC,S1 => mkTrans S1 DL StC
   | StD,S0 => mkTrans S0 DR StC | StD,S1 => mkTrans S1 DL StA
   end).
Definition instruction_wait : N := 454402378%N.
Theorem instruction_wait_check :
  first_hitN instruction_wait_machine (instruction_hit (StD,S0))
    wait_start instruction_wait = true.
Proof. vm_compute. reflexivity. Qed.
Theorem instruction_wait_lower_bound : forall w,
  WaitBoundTr (N.to_nat wait_start) w -> N.to_nat instruction_wait <= w.
Proof. intros; eapply first_instruction_hitN_lower; [exact instruction_wait_check|assumption]. Qed.
