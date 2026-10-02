(** * Cube rounds over a stack of finite one-blocks.

    The seven fixed instructions act on two left counters and an arbitrary
    right suffix.  A transfer removes three from the inner counter, adds
    two to the other counter, and extends the current right block by one.
    Non-firing exits consume right blocks.  Induction on stack length
    therefore reduces D0 liveness to [cube_round_total] at the empty stack.

    D0 may have either a one-step or a three-step implementation.  Its
    common macro pushes a block or merges the first blocks, preserving the
    canonical language; every such pass fires all eight instructions.
    The final argument iterates existential positive returns and requires
    no choice principle.  All finite padding comparisons use [lift]. *)
From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
From BBB4.Counters Require Import TriReachTr CubeRoundTr WTape.
Import ListNotations.

Definition sc_ones := repeat S1.

Lemma sc_ones_add : forall a b L,
 sc_ones a ++ sc_ones b ++ L = sc_ones (a+b) ++ L.
Proof. intros. unfold sc_ones. rewrite repeat_app, app_assoc. reflexivity. Qed.
Lemma sc_ones_push : forall a L,
 sc_ones a ++ S1::L = S1::sc_ones a ++ L.
Proof. intros. unfold sc_ones. induction a; cbn; congruence. Qed.

Definition sc_B (a b : nat) (R : list Sym) : cconf :=
 (StB,(sc_ones a++S0::sc_ones b,S1,R)).
Definition sc_R (tm : TM) (c d : cconf) : Prop :=
 exists k, stepn tm k (lift c) = Some (lift d).
Lemma sc_R_steps : forall tm c d k, csteps tm k c = Some d -> sc_R tm c d.
Proof. intros. exists k. apply csteps_lift. exact H. Qed.
Lemma sc_R_same : forall tm c d, lift c = lift d -> sc_R tm c d.
Proof. intros. exists 0. cbn [stepn]. congruence. Qed.
Lemma sc_R_trans : forall tm c d e, sc_R tm c d -> sc_R tm d e -> sc_R tm c e.
Proof.
 intros tm c d e (n & Hn) (m & Hm). exists (n+m).
 rewrite stepn_add,Hn. exact Hm.
Qed.
Lemma sc_R_padL : forall tm q L h R,
 sc_R tm (q,(L,h,R)) (q,(L++[S0],h,R)).
Proof.
 intros. apply sc_R_same. unfold lift; cbn.
 rewrite lift_side_app_blank. reflexivity.
Qed.
Lemma sc_R_unpadL : forall tm q L h R,
 sc_R tm (q,(L++[S0],h,R)) (q,(L,h,R)).
Proof.
 intros. apply sc_R_same. unfold lift; cbn.
 rewrite lift_side_app_blank. reflexivity.
Qed.
Lemma sc_R_padR : forall tm q L h R,
 sc_R tm (q,(L,h,R)) (q,(L,h,R++[S0])).
Proof. intros. apply sc_R_same. symmetry. apply lift_app_blank. Qed.
Lemma sc_R_unpadR : forall tm q L h R,
 sc_R tm (q,(L,h,R++[S0])) (q,(L,h,R)).
Proof. intros. apply sc_R_same. apply lift_app_blank. Qed.

Fixpoint sc_stack (w : list nat) : list Sym :=
 match w with [] => [S0] | n::w => sc_ones (S n)++S0::sc_stack w end.
Definition sc_C a b r w := sc_B a (b+2) (sc_ones (S r)++S0::sc_stack w).
Definition sc_D p R : cconf := (StD,(sc_ones p,S0,S0::R)).
Definition sc_found tm c : Prop :=
 exists p r w, sc_R tm c (sc_D (p+2) (sc_ones (S r)++S0::sc_stack w)).
Lemma sc_found_back : forall tm c d, sc_R tm c d -> sc_found tm d -> sc_found tm c.
Proof.
 intros tm c d E (p&r&w&H). exists p,r,w. eapply sc_R_trans; eauto.
Qed.
Lemma sc_R_terminal0 : forall tm a b,
 sc_R tm (sc_B a (b+2) [S1]) (sc_C a b 0 []).
Proof.
 intros. unfold sc_C,sc_B. cbn [sc_stack sc_ones repeat app].
 eapply sc_R_trans; [apply sc_R_padR|].
 change (sc_R tm (StB,(sc_ones a++S0::sc_ones (b+2),S1,[S1;S0]))
  (StB,(sc_ones a++S0::sc_ones (b+2),S1,[S1;S0]++[S0]))).
 apply sc_R_padR.
Qed.
Lemma sc_R_terminal1 : forall tm a b,
 sc_R tm (sc_B a (b+2) [S1;S0]) (sc_C a b 0 []).
Proof. intros. apply sc_R_padR. Qed.

Section StackCube.
Variable tm : TM.
Hypothesis HA0 : tm StA S0 = Some (mkTrans S1 DL StB).
Hypothesis HA1 : tm StA S1 = Some (mkTrans S1 DR StA).
Hypothesis HB0 : tm StB S0 = Some (mkTrans S0 DL StC).
Hypothesis HB1 : tm StB S1 = Some (mkTrans S0 DL StD).
Hypothesis HC0 : tm StC S0 = Some (mkTrans S1 DR StC).
Hypothesis HC1 : tm StC S1 = Some (mkTrans S0 DR StA).
Hypothesis HD1 : tm StD S1 = Some (mkTrans S0 DL StC).

Local Ltac sc_compute :=
 repeat (cbn [csteps cstep ctape_move chd ctl t_write t_dir t_next];
  first [rewrite HA0 | rewrite HA1 | rewrite HB0 | rewrite HB1 |
         rewrite HC0 | rewrite HC1 | rewrite HD1]); reflexivity.

Lemma sc_A1_step : forall L R,
 csteps tm 1 (StA,(L,S1,R)) = Some (StA,(S1::L,chd R,ctl R)).
Proof. intros; sc_compute. Qed.
Lemma sc_A1_sweep : forall n L R,
 csteps tm n (StA,(L,chd (sc_ones n++R),ctl (sc_ones n++R))) =
 Some (StA,(sc_ones n++L,chd R,ctl R)).
Proof.
 induction n as [|n IH]; intros L R; [reflexivity|].
 change (S n) with (1+n). rewrite csteps_add.
 cbn [Nat.add sc_ones repeat app chd ctl]. rewrite sc_A1_step,IH.
 rewrite sc_ones_push. reflexivity.
Qed.
Lemma sc_A0_turn : forall L R,
 csteps tm 1 (StA,(S1::L,S0,R)) = Some (StB,(L,S1,S1::R)).
Proof. intros; sc_compute. Qed.
Lemma sc_C1_sweep : forall n L R,
 csteps tm (n+3) (StC,(L,S1,sc_ones (S n)++S0::R)) =
 Some (StB,(sc_ones n++S0::L,S1,S1::R)).
Proof.
 intros n L R.
 assert (E : csteps tm 1 (StC,(L,S1,sc_ones (S n)++S0::R)) =
  Some (StA,(S0::L,chd (sc_ones (S n)++S0::R),ctl (sc_ones (S n)++S0::R)))).
 { sc_compute. }
 replace (n+3) with (1+(S n+1)) by lia.
 rewrite csteps_add,E,csteps_add,sc_A1_sweep.
 cbn [chd ctl sc_ones repeat app]. apply sc_A0_turn.
Qed.
Lemma sc_back_step : forall L R,
 csteps tm 3 (StC,(S1::L,S1,S0::R)) = Some (StC,(L,S1,S0::S1::R)).
Proof. intros; sc_compute. Qed.
Lemma sc_back : forall n L R,
 csteps tm (3*n) (StC,(sc_ones n++L,S1,S0::R)) =
 Some (StC,(L,S1,S0::sc_ones n++R)).
Proof.
 induction n as [|n IH]; intros L R; [reflexivity|].
 replace (3*S n) with (3+3*n) by lia. rewrite csteps_add.
 cbn [sc_ones repeat app]. rewrite sc_back_step,IH,sc_ones_push. reflexivity.
Qed.
Lemma sc_back_turn : forall L R,
 csteps tm 5 (StC,(S0::L,S1,S0::R)) = Some (StC,(S1::S1::L,S1,R)).
Proof. intros; sc_compute. Qed.
Lemma sc_bounce : forall n L R,
 csteps tm (3*n+5) (StC,(sc_ones n++S0::L,S1,S0::R)) =
 Some (StC,(S1::S1::L,S1,sc_ones n++R)).
Proof.
 intros. rewrite csteps_add,sc_back,sc_back_turn. reflexivity.
Qed.
Lemma sc_B1_enter : forall L R,
 csteps tm 2 (StB,(S1::S1::L,S1,R)) = Some (StC,(L,S1,S0::S0::R)).
Proof. intros; sc_compute. Qed.
Lemma sc_transfer : forall a L R,
 csteps tm (4*a+13) (StB,(sc_ones (a+3)++S0::L,S1,R)) =
 Some (StB,(sc_ones a++S0::S1::S1::L,S1,S1::R)).
Proof.
 intros a L R. replace (a+3) with (S(S(S a))) by lia.
 replace (4*a+13) with (2+((3*S a+5)+(a+3))) by lia.
 rewrite csteps_add. cbn [sc_ones repeat app]. rewrite sc_B1_enter.
 change (csteps tm (3*S a+5+(a+3))
  (StC,(sc_ones (S a)++S0::L,S1,S0::S0::R)) =
  Some (StB,(sc_ones a++S0::S1::S1::L,S1,S1::R))).
 rewrite csteps_add,sc_bounce,sc_C1_sweep. reflexivity.
Qed.

Lemma sc_B1_one : forall L R,
 csteps tm 5 (StB,(S1::S0::L,S1,S1::R)) =
 Some (StC,(S1::S1::S1::L,S1,R)).
Proof. intros; sc_compute. Qed.
Lemma sc_C1_zero : forall L R,
 csteps tm 2 (StC,(L,S1,S0::R)) = Some (StB,(L,S0,S1::R)).
Proof. intros; sc_compute. Qed.
Lemma sc_B0_one : forall L R,
 csteps tm 1 (StB,(S1::L,S0,R)) = Some (StC,(L,S1,S0::R)).
Proof. intros; sc_compute. Qed.
Lemma sc_one_many : forall r L T,
 csteps tm (r+8) (StB,(S1::S0::L,S1,sc_ones (r+2)++S0::T)) =
 Some (StB,(sc_ones r++S0::S1::S1::S1::L,S1,S1::T)).
Proof.
 intros. replace (r+2) with (S(S r)) by lia.
 replace (r+8) with (5+(r+3)) by lia.
 rewrite csteps_add. cbn [sc_ones repeat app]. rewrite sc_B1_one.
 apply sc_C1_sweep.
Qed.
Lemma sc_two : forall b r G T,
 csteps tm (4*b+r+22)
 (StB,(S1::S1::S0::(sc_ones b++S0::G),S1,sc_ones r++S0::T)) =
 Some (StB,(sc_ones (b+r+1)++S0::S1::S1::G,S1,S1::T)).
Proof.
 intros b r G T.
 replace (4*b+r+22) with (2+(5+(2+(1+((3*(b+1)+5)+(b+r+1+3)))))) by lia.
 rewrite csteps_add,sc_B1_enter,csteps_add,sc_back_turn,
  csteps_add,sc_C1_zero,csteps_add,sc_B0_one.
 replace (b+1) with (S b) at 1 by lia.
 change (csteps tm (3*S b+5+(b+r+1+3))
  (StC,(sc_ones (S b)++S0::G,S1,S0::S1::(sc_ones r++S0::T))) =
  Some (StB,(sc_ones (b+r+1)++S0::S1::S1::G,S1,S1::T))).
 rewrite csteps_add,sc_bounce,sc_ones_push.
 change (csteps tm (b+r+1+3)
  (StC,(S1::S1::G,S1,sc_ones (S(S b))++sc_ones r++S0::T)) =
  Some (StB,(sc_ones (b+r+1)++S0::S1::S1::G,S1,S1::T))).
 rewrite sc_ones_add. replace (S(S b)+r) with (S(b+r+1)) by lia.
 apply sc_C1_sweep.
Qed.

Lemma sc_one_one : forall b q G T,
 csteps tm (4*b+q+24)
 (StB,(S1::S0::(sc_ones b++S0::G),S1,S1::S0::(sc_ones q++S0::T))) =
 Some (StB,(sc_ones (b+q+2)++S0::S1::S1::G,S1,S1::T)).
Proof.
 intros b q G T.
 replace (4*b+q+24) with (5+(2+(1+((3*(b+2)+5)+(b+q+2+3))))) by lia.
 rewrite csteps_add,sc_B1_one,csteps_add,sc_C1_zero,csteps_add,sc_B0_one.
 replace (b+2) with (S(S b)) at 1 by lia.
 change (csteps tm (3*(S(S b))+5+(b+q+2+3))
  (StC,(sc_ones (S(S b))++S0::G,S1,S0::S1::(sc_ones q++S0::T))) =
  Some (StB,(sc_ones (b+q+2)++S0::S1::S1::G,S1,S1::T))).
 rewrite csteps_add,sc_bounce,sc_ones_push.
 change (csteps tm (b+q+2+3)
  (StC,(S1::S1::G,S1,sc_ones (S(S(S b)))++sc_ones q++S0::T)) =
  Some (StB,(sc_ones (b+q+2)++S0::S1::S1::G,S1,S1::T))).
 rewrite sc_ones_add. replace (S(S(S b))+q) with (S(b+q+2)) by lia.
 apply sc_C1_sweep.
Qed.

Lemma sc_R_transfer : forall a b R,
 sc_R tm (sc_B (a+3) b R) (sc_B a (b+2) (S1::R)).
Proof.
 intros. pose proof (sc_transfer a (sc_ones b) R) as E.
 assert (Eb : S1::S1::sc_ones b = sc_ones (b+2)).
 { replace (b+2) with (S(S b)) by lia. reflexivity. }
 rewrite Eb in E. eapply sc_R_steps; exact E.
Qed.
Lemma sc_R_loop : forall k a b R,
 sc_R tm (sc_B (3*k+a) b R) (sc_B a (b+2*k) (sc_ones k++R)).
Proof.
 induction k as [|k IH]; intros a b R.
 - cbn [Nat.mul Nat.add sc_ones repeat app].
   replace (b+0) with b by lia. apply sc_R_same; reflexivity.
 - replace (3*S k+a) with ((3*k+a)+3) by lia.
   eapply sc_R_trans; [apply sc_R_transfer|].
   pose proof (IH a (b+2) (S1::R)) as E.
   rewrite sc_ones_push in E.
   replace (b+2+2*k) with (b+2*S k) in E by lia.
   exact E.
Qed.
Lemma sc_R_one_many : forall r b T,
 sc_R tm (sc_B 1 b (sc_ones (r+2)++S0::T))
   (sc_B r (b+3) (S1::T)).
Proof.
 intros. pose proof (sc_one_many r (sc_ones b) T) as E.
 assert (Eb : S1::S1::S1::sc_ones b = sc_ones (b+3)).
 { replace (b+3) with (S(S(S b))) by lia. reflexivity. }
 rewrite Eb in E. eapply sc_R_steps; exact E.
Qed.
Lemma sc_R_two : forall b r T,
 sc_R tm (sc_B 2 b (sc_ones r++S0::T))
   (sc_B (b+r+1) 2 (S1::T)).
Proof.
 intros b r T. unfold sc_B at 1.
 eapply sc_R_trans; [apply sc_R_padL|].
 pose proof (sc_two b r [] T) as E.
 cbn [app] in E.
 eapply sc_R_steps. exact E.
Qed.
Lemma sc_R_one_one : forall b q T,
 sc_R tm (sc_B 1 b (S1::S0::(sc_ones q++S0::T)))
   (sc_B (b+q+2) 2 (S1::T)).
Proof.
 intros b q T. unfold sc_B at 1.
 eapply sc_R_trans; [apply sc_R_padL|].
 pose proof (sc_one_one b q [] T) as E.
 cbn [app] in E.
 eapply sc_R_steps. exact E.
Qed.

Lemma sc_R_loop_C : forall k a b r w,
 sc_R tm (sc_C (3*k+a) b r w) (sc_C a (b+2*k) (r+k) w).
Proof.
 intros. unfold sc_C. pose proof (sc_R_loop k a (b+2)
  (sc_ones (S r)++S0::sc_stack w)) as E.
 rewrite sc_ones_add in E.
 replace (b+2+2*k) with (b+2*k+2) in E by lia.
 replace (k+S r) with (S(r+k)) in E by lia. exact E.
Qed.
Lemma sc_zero_found : forall b r w, sc_found tm (sc_C 0 b r w).
Proof.
 intros. exists b,r,w. apply sc_R_steps with (k:=1). unfold sc_C,sc_B,sc_D. cbn [sc_ones repeat app]. sc_compute.
Qed.
(** At the empty stack, the arithmetic is exactly the ternary reset map. *)
Lemma sc_terminal_found : forall a b, sc_found tm (sc_C a b 0 []).
Proof.
 apply (cube_round_total (fun a b => sc_found tm (sc_C a b 0 []))).
 - intro b. apply sc_zero_found.
 - intros k b. replace (3*k+3) with (3*(k+1)+0) by lia.
   eapply sc_found_back; [apply sc_R_loop_C|apply sc_zero_found].
 - intros b E. eapply sc_found_back.
   + unfold sc_C. cbn [sc_stack sc_ones repeat app].
     apply (sc_R_one_one (b+2) 0 []).
   + replace (b+2+0+2) with (b+4) by lia.
     eapply sc_found_back; [exact (sc_R_terminal0 tm (b+4) 0)|exact E].
 - intros b E. eapply sc_found_back.
   + unfold sc_C. cbn [sc_stack sc_ones repeat app].
     apply (sc_R_two (b+2) 1 [S0]).
   + replace (b+2+1+1) with (b+4) by lia.
     eapply sc_found_back; [exact (sc_R_terminal1 tm (b+4) 0)|exact E].
 - intros k b E. replace (3*k+4) with (3*(k+1)+1) by lia.
   eapply sc_found_back; [apply sc_R_loop_C|].
   unfold sc_C. cbn [sc_stack Nat.add].
   replace (S(k+1)) with (k+2) by lia.
   eapply sc_found_back; [apply sc_R_one_many|].
   replace (b+2*(k+1)+2+3) with ((b+2*k+5)+2) by lia.
   eapply sc_found_back; [apply sc_R_terminal1|exact E].
 - intros k b E. replace (3*k+5) with (3*(k+1)+2) by lia.
   eapply sc_found_back; [apply sc_R_loop_C|].
   unfold sc_C. cbn [sc_stack Nat.add].
   eapply sc_found_back; [apply sc_R_two|].
   replace (b+2*(k+1)+2+S(k+1)+1) with (3*k+b+7) by lia.
   eapply sc_found_back; [exact (sc_R_terminal1 tm (3*k+b+7) 0)|exact E].
Qed.

Lemma sc_R_transfer_C : forall a b r w,
 sc_R tm (sc_C (a+3) b r w) (sc_C a (b+2) (S r) w).
Proof. intros. apply sc_R_transfer. Qed.

(** No non-firing transfer can create a new right block. *)
Lemma sc_all_found : forall w a b r, sc_found tm (sc_C a b r w).
Proof.
 assert (E : forall n w, length w=n -> forall a b r, sc_found tm (sc_C a b r w)).
 { induction n as [n IH] using lt_wf_ind. intros w En.
   assert (Out : forall v, length v<=n -> forall a b,
      sc_found tm (sc_B a (b+2) (S1::sc_stack v))).
   { intros [|q v] Ev a b.
     - eapply sc_found_back; [apply sc_R_terminal1|apply sc_terminal_found].
     - change (sc_found tm (sc_C a b (S q) v)).
       apply (IH (length v)); [cbn [length] in Ev; lia|reflexivity]. }
   induction a as [a IHa] using lt_wf_ind. intros b r.
   destruct a as [|[|[|a]]].
   - apply sc_zero_found.
   - destruct r as [|r].
     + destruct w as [|q w].
       * apply sc_terminal_found.
       * eapply sc_found_back.
         -- unfold sc_C. cbn [sc_stack sc_ones repeat app].
            apply (sc_R_one_one (b+2) (S q) (sc_stack w)).
         -- exact (Out w ltac:(cbn [length] in En;lia) (b+2+S q+2) 0).
     + eapply sc_found_back.
       * unfold sc_C. replace (S(S r)) with (r+2) by lia. apply sc_R_one_many.
       * replace (b+2+3) with ((b+3)+2) by lia. apply Out. lia.
   - eapply sc_found_back.
     + unfold sc_C. apply sc_R_two.
     + exact (Out w ltac:(lia) (b+2+S r+1) 0).
   - replace (S(S(S a))) with (a+3) by lia.
     eapply sc_found_back; [apply sc_R_transfer_C|]. apply IHa. lia. }
 intros. exact (E (length w) w eq_refl a b r).
Qed.

Variable d0cost : nat.
Hypothesis HD0 : forall L R,
 csteps tm d0cost (StD,(S1::L,S0,R)) = Some (StB,(L,S1,S1::R)).

Lemma sc_D_enter : forall p R,
 sc_R tm (sc_D (p+2) R) (sc_B (p+1) 0 (S1::S0::R)).
Proof.
 intros p R. unfold sc_D. replace (p+2) with (S(p+1)) by lia.
 cbn [sc_ones repeat app].
 eapply sc_R_trans; [eapply sc_R_steps; apply HD0|].
 apply sc_R_padL.
Qed.
Lemma sc_out_return : forall w a b, exists r v,
 sc_R tm (sc_B a (b+2) (S1::sc_stack w)) (sc_C a b r v).
Proof.
 intros [|q w] a b.
 - exists 0,[]. apply sc_R_terminal1.
 - exists (S q),w. apply sc_R_same. reflexivity.
Qed.
(** The two shortest left blocks merge; longer blocks push a new block. *)
Lemma sc_D_return : forall p r w, exists a b s v,
 sc_R tm (sc_D (p+2) (sc_ones (S r)++S0::sc_stack w)) (sc_C a b s v).
Proof.
 intros [|[|p]] r w.
 - destruct (sc_out_return w (0+S r+2) 0) as (s&v&E).
   exists (0+S r+2),0,s,v. eapply sc_R_trans; [apply sc_D_enter|].
   eapply sc_R_trans; [apply (sc_R_one_one 0 (S r) (sc_stack w))|exact E].
 - exists 2,0,(S r),w. eapply sc_R_trans; [apply sc_D_enter|].
   apply (sc_R_two 0 1 (sc_ones (S r)++S0::sc_stack w)).
 - exists p,0,1,(r::w). eapply sc_R_trans; [apply sc_D_enter|].
   replace (S(S p)+1) with (p+3) by lia. apply sc_R_transfer.
Qed.

Lemma sc_fire_now : forall c, tri_reaches_fire tm (cinstr c) c.
Proof. intro c. exists 0,(lift c). split; [reflexivity|apply cinstr_lift]. Qed.
Lemma sc_fire_R : forall c d t,
 sc_R tm c d -> tri_reaches_fire tm t d -> tri_reaches_fire tm t c.
Proof.
 intros c d t (n&En) (k&e&Ek&Et). exists (n+k),e. split; [|exact Et].
 rewrite stepn_add,En. exact Ek.
Qed.
Lemma sc_fire_steps : forall c d n t,
 csteps tm n c=Some d -> tri_reaches_fire tm t d -> tri_reaches_fire tm t c.
Proof. intros. eapply sc_fire_R; [eapply sc_R_steps;exact H|exact H0]. Qed.
Lemma sc_fire_C1_A1 : forall L R,
 tri_reaches_fire tm (StA,S1) (StC,(L,S1,S1::R)).
Proof.
 intros. eapply sc_fire_steps with (n:=1) (d:=(StA,(S0::L,S1,R))).
 - sc_compute.
 - apply sc_fire_now.
Qed.
Lemma sc_fire_C1_A0 : forall L R,
 tri_reaches_fire tm (StA,S0) (StC,(L,S1,S0::R)).
Proof.
 intros. eapply sc_fire_steps with (n:=1) (d:=(StA,(S0::L,S0,R))).
 - sc_compute.
 - apply sc_fire_now.
Qed.
Lemma sc_fire_C1_B0 : forall L R,
 tri_reaches_fire tm (StB,S0) (StC,(L,S1,S0::R)).
Proof.
 intros. eapply sc_fire_steps; [apply sc_C1_zero|apply sc_fire_now].
Qed.
Lemma sc_fire_bounce_C0 : forall n L R,
 tri_reaches_fire tm (StC,S0) (StC,(sc_ones n++S0::L,S1,S0::R)).
Proof.
 intros. eapply sc_fire_steps; [apply sc_back|].
 eapply sc_fire_steps with (n:=3) (d:=(StC,(L,S0,S0::S1::sc_ones n++R))).
 - sc_compute.
 - apply sc_fire_now.
Qed.
Lemma sc_fire_B1_D1 : forall L R,
 tri_reaches_fire tm (StD,S1) (StB,(S1::L,S1,R)).
Proof.
 intros. eapply sc_fire_steps with (n:=1) (d:=(StD,(L,S1,S0::R))).
 - sc_compute.
 - apply sc_fire_now.
Qed.

Lemma sc_seven_large : forall a R t, t<>(StD,S0) ->
 tri_reaches_fire tm t (sc_B (a+3) 0 R).
Proof.
 intros a R [q h] Et. unfold sc_B. replace (a+3) with (S(S(S a))) by lia.
 cbn [sc_ones repeat app]. destruct q,h.
 - eapply sc_fire_steps; [apply sc_B1_enter|apply sc_fire_C1_A0].
 - eapply sc_fire_steps; [apply sc_B1_enter|].
   eapply sc_fire_steps; [apply (sc_bounce (S a) [])|].
   apply sc_fire_C1_A1.
 - eapply sc_fire_steps; [apply sc_B1_enter|apply sc_fire_C1_B0].
 - apply sc_fire_now.
 - eapply sc_fire_steps; [apply sc_B1_enter|]. apply (sc_fire_bounce_C0 (S a) []).
 - eapply sc_fire_steps; [apply sc_B1_enter|apply sc_fire_now].
 - contradiction.
 - apply sc_fire_B1_D1.
Qed.
Lemma sc_seven_two : forall R t, t<>(StD,S0) ->
 tri_reaches_fire tm t (sc_B 2 0 R).
Proof.
 intros R [q h] Et. unfold sc_B. cbn [sc_ones repeat app]. destruct q,h.
 - eapply sc_fire_steps; [apply sc_B1_enter|apply sc_fire_C1_A0].
 - eapply sc_fire_steps; [apply sc_B1_enter|].
   eapply sc_fire_steps; [apply sc_back_turn|].
   eapply sc_fire_steps; [apply sc_C1_zero|].
   eapply sc_fire_steps; [apply sc_B0_one|].
   eapply sc_fire_R; [apply sc_R_padL|].
   eapply sc_fire_steps; [apply (sc_bounce 1 [])|]. apply sc_fire_C1_A1.
 - eapply sc_fire_steps; [apply sc_B1_enter|apply sc_fire_C1_B0].
 - apply sc_fire_now.
 - eapply sc_fire_steps; [apply sc_B1_enter|]. apply (sc_fire_bounce_C0 0 []).
 - eapply sc_fire_steps; [apply sc_B1_enter|apply sc_fire_now].
 - contradiction.
 - apply sc_fire_B1_D1.
Qed.
Lemma sc_seven_one : forall R t, t<>(StD,S0) ->
 tri_reaches_fire tm t (sc_B 1 0 (S1::S0::R)).
Proof.
 intros R [q h] Et. unfold sc_B. cbn [sc_ones repeat app]. destruct q,h.
 - eapply sc_fire_steps; [apply sc_B1_one|apply sc_fire_C1_A0].
 - eapply sc_fire_steps; [apply sc_B1_one|].
   eapply sc_fire_steps; [apply sc_C1_zero|].
   eapply sc_fire_steps; [apply sc_B0_one|].
   eapply sc_fire_R; [apply sc_R_padL|].
   eapply sc_fire_steps; [apply (sc_bounce 2 [])|]. apply sc_fire_C1_A1.
 - eapply sc_fire_steps; [apply sc_B1_one|apply sc_fire_C1_B0].
 - apply sc_fire_now.
 - eapply sc_fire_steps with (n:=2) (d:=(StC,([],S0,[S0;S0;S1;S0]++R))).
   + sc_compute.
   + apply sc_fire_now.
 - eapply sc_fire_steps; [apply sc_B1_one|apply sc_fire_now].
 - contradiction.
 - apply sc_fire_B1_D1.
Qed.

Lemma sc_D_all_fire : forall p R t,
 tri_reaches_fire tm t (sc_D (p+2) R).
Proof.
 intros p R t. destruct (instr_eqb t (StD,S0)) eqn:E.
 - apply instr_eqb_spec in E. subst t. apply sc_fire_now.
 - assert (Et : t<>(StD,S0)).
   { intro Et. subst t. discriminate. }
   eapply sc_fire_R; [apply sc_D_enter|].
   destruct p as [|[|p]].
   + apply sc_seven_one. exact Et.
   + apply sc_seven_two. exact Et.
   + replace (S(S p)+1) with (p+3) by lia. apply sc_seven_large. exact Et.
Qed.

Lemma sc_all_fire : forall w a b r t, tri_reaches_fire tm t (sc_C a b r w).
Proof.
 intros. destruct (sc_all_found w a b r) as (p&s&v&E).
 eapply sc_fire_R; [exact E|apply sc_D_all_fire].
Qed.

Lemma sc_progress : forall w a b r, exists v x y s k,
 0<k /\ stepn tm k (lift (sc_C a b r w)) = Some (lift (sc_C x y s v)).
Proof.
 intros w a b r. destruct (sc_all_found w a b r) as (p&s&v&n&En).
 destruct (sc_D_return p s v) as (x&y&t&u&m&Em).
 assert (Hn : 0<n).
 { destruct n; [cbn [stepn sc_C sc_B sc_D lift] in En; discriminate|lia]. }
 exists u,x,y,t,(n+m). split; [lia|]. rewrite stepn_add,En. exact Em.
Qed.

Theorem stack_cube_neverqhtr :
 (exists T a b r w, stepn tm T InitES = Some (lift (sc_C a b r w))) ->
 NeverQuasiHaltsTr tm.
Proof.
 intro Boot.
 assert (Reach : forall N, exists T a b r w, N<=T /\
  stepn tm T InitES = Some (lift (sc_C a b r w))).
 { induction N as [|N IH].
   - destruct Boot as (T&a&b&r&w&E). exists T,a,b,r,w. split; [lia|exact E].
   - destruct IH as (T&a&b&r&w&HT&E).
     destruct (sc_progress w a b r) as (v&x&y&s&k&Hk&Ek).
     exists (T+k),x,y,s,v. split; [lia|]. rewrite stepn_add,E. exact Ek. }
 intros t _ N. destruct (Reach N) as (T&a&b&r&w&HT&E).
 destruct (sc_all_fire w a b r t) as (k&c&Ek&Et).
 exists (T+k). split; [lia|]. exists c. split; [|exact Et].
 rewrite stepn_add,E. exact Ek.
Qed.
End StackCube.
