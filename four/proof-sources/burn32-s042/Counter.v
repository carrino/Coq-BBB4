(** S042 universal nine-frontier return, checked at arbitrary affine counts.
    The two loops consume one natural counter and increment another.
    Only the finite scan programs are evaluated by the checker. *)
From Coq Require Import List Arith Lia.
From BBB24 Require Import Statement CTape.
From BBB24Burn32S042 Require Import Programs Symbolic.
Import ListNotations.
Definition s42_start := s42_C StA S0 [(S2,(s42_E 1 0 0));(S0,(s42_E 1 0 0));(S3,(s42_E 13 0 0));(S2,(s42_E 1 0 0));(S0,(s42_E 1 0 0));(S3,(s42_E 3 0 0));(S0,(s42_E 1 0 0));(S3,(s42_E 3 2 0));(S0,(s42_E 1 0 0));(S3,(s42_E 9 0 0));(S0,(s42_E 1 0 0))] [].
Definition s42_F := s42_C StA S0 [(S3,(s42_E 1 2 0));(S2,(s42_E 1 0 0));(S0,(s42_E 1 0 0))] [(S2,(s42_E 14 0 2));(S0,(s42_E 1 0 0));(S1,(s42_E 1 0 2));(S2,(s42_E 9 0 0));(S0,(s42_E 1 0 0));(S1,(s42_E 1 0 0));(S2,(s42_E 2 0 0));(S0,(s42_E 1 0 0));(S1,(s42_E 1 0 0));(S2,(s42_E 1 0 0));(S0,(s42_E 1 0 0));(S1,(s42_E 3 0 0));(S2,(s42_E 1 0 0));(S0,(s42_E 1 0 0));(S1,(s42_E 1 0 0))].
Definition s42_G := s42_C StA S2 [(S0,(s42_E 1 0 0));(S3,(s42_E 17 2 0));(S0,(s42_E 1 0 0))] [(S2,(s42_E 1 0 6));(S1,(s42_E 1 2 0));(S2,(s42_E 9 0 0));(S0,(s42_E 1 0 0));(S1,(s42_E 1 0 0));(S2,(s42_E 2 0 0));(S0,(s42_E 1 0 0));(S1,(s42_E 1 0 0));(S2,(s42_E 1 0 0));(S0,(s42_E 1 0 0));(S1,(s42_E 3 0 0));(S2,(s42_E 1 0 0));(S0,(s42_E 1 0 0));(S1,(s42_E 1 0 0))].
Definition s42_x:=s42_E 0 1 0.
Definition s42_y:=s42_E 0 0 1.
Definition s42_sx:=s42_E 1 1 0.
Definition s42_sy:=s42_E 1 0 1.
Definition s42_x6:=s42_E 6 1 0.
Definition s42_next:=s42_E 27 3 0.
Definition s42_family n:=s42_den n 0 s42_start.
Definition s42_Fconf k m:=s42_den k m s42_F.
Definition s42_Gconf k m:=s42_den k m s42_G.
Lemma s42_prefix_check : s42_run 468 s42_start=Some(s42_sub s42_x6 s42_z s42_F).
Proof. vm_compute;reflexivity. Qed.
Lemma s42_F_check : s42_run 38(s42_sub s42_sx s42_y s42_F)=Some(s42_sub s42_x s42_sy s42_F).
Proof. vm_compute;reflexivity. Qed.
Lemma s42_bridge_check : s42_run 32(s42_sub s42_z s42_x6 s42_F)=Some(s42_sub s42_x6 s42_z s42_G).
Proof. vm_compute;reflexivity. Qed.
Lemma s42_G_check : s42_run 36(s42_sub s42_sx s42_y s42_G)=Some(s42_sub s42_x s42_sy s42_G).
Proof. vm_compute;reflexivity. Qed.
Lemma s42_suffix_check : s42_run 269(s42_sub s42_z s42_x6 s42_G)=Some(s42_sub s42_next s42_z s42_start).
Proof. vm_compute;reflexivity. Qed.
Lemma s42_prefix : forall n,exists k,468<=k /\
 csteps s42_tm k(s42_family n)=Some(s42_Fconf(n+6)0).
Proof.
 intro n;pose proof(s42_run_sound _ _ _ s42_prefix_check n 0)as H.
 rewrite s42_sub_den in H;unfold s42_val,s42_x6,s42_z,s42_sx,s42_x,s42_y,s42_sy,s42_next in H;cbn[e0 e1 e2]in H;repeat rewrite Nat.mul_1_l in H;repeat rewrite Nat.mul_0_l in H;repeat rewrite Nat.mul_0_r in H;repeat rewrite Nat.add_0_r in H;repeat rewrite Nat.add_0_l in H;change(exists k,468<=k/\csteps s42_tm k(s42_family n)=Some(s42_Fconf(6+n)0))in H.
 replace(6+n)with(n+6)in H by lia;exact H.
Qed.
Lemma s42_F_step : forall n m,exists k,38<=k /\
 csteps s42_tm k(s42_Fconf(S n)m)=Some(s42_Fconf n(S m)).
Proof.
 intros n m;pose proof(s42_run_sound _ _ _ s42_F_check n m)as H.
 rewrite !s42_sub_den in H;unfold s42_val,s42_x6,s42_z,s42_sx,s42_x,s42_y,s42_sy,s42_next in H;cbn[e0 e1 e2]in H;repeat rewrite Nat.mul_1_l in H;repeat rewrite Nat.mul_0_l in H;repeat rewrite Nat.mul_0_r in H;repeat rewrite Nat.add_0_r in H;repeat rewrite Nat.add_0_l in H;exact H.
Qed.
Lemma s42_G_step : forall n m,exists k,36<=k /\
 csteps s42_tm k(s42_Gconf(S n)m)=Some(s42_Gconf n(S m)).
Proof.
 intros n m;pose proof(s42_run_sound _ _ _ s42_G_check n m)as H.
 rewrite !s42_sub_den in H;unfold s42_val,s42_x6,s42_z,s42_sx,s42_x,s42_y,s42_sy,s42_next in H;cbn[e0 e1 e2]in H;repeat rewrite Nat.mul_1_l in H;repeat rewrite Nat.mul_0_l in H;repeat rewrite Nat.mul_0_r in H;repeat rewrite Nat.add_0_r in H;repeat rewrite Nat.add_0_l in H;exact H.
Qed.
Lemma s42_F_loop : forall n m,exists k,csteps s42_tm k(s42_Fconf n m)=Some(s42_Fconf 0(m+n)).
Proof.
 induction n;intro m.
 - exists 0;now rewrite Nat.add_0_r.
 - destruct(s42_F_step n m)as(a&Ha&Ea);destruct(IHn(S m))as(b&Eb).
   exists(a+b);rewrite csteps_add,Ea,Eb;replace(S m+n)with(m+S n)by lia;reflexivity.
Qed.
Lemma s42_G_loop : forall n m,exists k,csteps s42_tm k(s42_Gconf n m)=Some(s42_Gconf 0(m+n)).
Proof.
 induction n;intro m.
 - exists 0;now rewrite Nat.add_0_r.
 - destruct(s42_G_step n m)as(a&Ha&Ea);destruct(IHn(S m))as(b&Eb).
   exists(a+b);rewrite csteps_add,Ea,Eb;replace(S m+n)with(m+S n)by lia;reflexivity.
Qed.
Lemma s42_bridge : forall n,exists k,csteps s42_tm k(s42_Fconf 0(n+6))=Some(s42_Gconf(n+6)0).
Proof.
 intro n;destruct(s42_run_sound _ _ _ s42_bridge_check n 0)as(k&Hk&E).
 rewrite !s42_sub_den in E;unfold s42_val,s42_x6,s42_z,s42_sx,s42_x,s42_y,s42_sy,s42_next in E;cbn[e0 e1 e2]in E;repeat rewrite Nat.mul_1_l in E;repeat rewrite Nat.mul_0_l in E;repeat rewrite Nat.mul_0_r in E;repeat rewrite Nat.add_0_r in E;repeat rewrite Nat.add_0_l in E;exists k;replace(n+6)with(6+n)by lia;exact E.
Qed.
Lemma s42_suffix : forall n,exists k,csteps s42_tm k(s42_Gconf 0(n+6))=Some(s42_family(3*n+27)).
Proof.
 intro n;destruct(s42_run_sound _ _ _ s42_suffix_check n 0)as(k&Hk&E).
 rewrite !s42_sub_den in E;unfold s42_val,s42_x6,s42_z,s42_sx,s42_x,s42_y,s42_sy,s42_next in E;cbn[e0 e1 e2]in E;repeat rewrite Nat.mul_1_l in E;repeat rewrite Nat.mul_0_l in E;repeat rewrite Nat.mul_0_r in E;repeat rewrite Nat.add_0_r in E;repeat rewrite Nat.add_0_l in E;exists k;replace(n+6)with(6+n)by lia;replace(3*n+27)with(27+3*n)by lia;exact E.
Qed.
Theorem s42_return : forall n,exists k,0<k/\
 csteps s42_tm k(s42_family n)=Some(s42_family(3*n+27)).
Proof.
 intro n;destruct(s42_prefix n)as(a&Ha&Ea).
 destruct(s42_F_loop(n+6)0)as(b&Eb);rewrite Nat.add_0_l in Eb.
 destruct(s42_bridge n)as(c&Ec).
 destruct(s42_G_loop(n+6)0)as(d&Ed);rewrite Nat.add_0_l in Ed.
 destruct(s42_suffix n)as(e&Ee).
 exists(a+(b+(c+(d+e))));split;[lia|].
 rewrite csteps_add,Ea,csteps_add,Eb,csteps_add,Ec,csteps_add,Ed,Ee;reflexivity.
Qed.
Lemma s42_boot : csteps s42_tm 12565 c0=Some(s42_family 42).
Proof. vm_compute;reflexivity. Qed.
Print Assumptions s42_return.
Print Assumptions s42_boot.
