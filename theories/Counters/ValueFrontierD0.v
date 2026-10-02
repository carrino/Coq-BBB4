(** * ValueFrontierD0: D0 visits in the shared period-three frontier.

    The seven common transitions admit either B0=1LA or B0=1LC.
    A run through [110] blocks reaches D0 immediately on [10].  A
    [111] turn creates such a suffix.  At a zero, the two B0 variants
    reset the frontier to the same unary blocks followed by [101] or
    [111], respectively.  A finite-word parser therefore always finds
    a D0 visit, regardless of the finite right suffix. *)
From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Counters Require Import ValueFrontierTransducer Period3WordTermination.
Import ListNotations.
Lemma vfd_Us0:forall k,vft_Us(repeat 0 k)=vft_Ps(repeat 0 k).
Proof. induction k;cbn[repeat vft_Us vft_Ps];[reflexivity|now rewrite IHk]. Qed.
Lemma vfd_Ps_snoc:forall k,
 vft_Ps(repeat 0 k)++vft_P 0=vft_Ps(repeat 0(S k)).
Proof.
 induction k;cbn[repeat vft_Ps];[now rewrite app_nil_r|].
 now rewrite <-app_assoc,IHk.
Qed.
Section Machine.
Variable tm:TM.
Variable s:Sym.
Hypothesis HA0:tm StA S0=Some(mkTrans S1 DR StB).
Hypothesis HA1:tm StA S1=Some(mkTrans S0 DL StC).
Hypothesis HB0:tm StB S0=Some(mkTrans S1 DL(match s with S0=>StA|S1=>StC end)).
Hypothesis HB1:tm StB S1=Some(mkTrans S1 DR StD).
Hypothesis HC0:tm StC S0=Some(mkTrans S1 DL StA).
Hypothesis HC1:tm StC S1=Some(mkTrans S1 DL StC).
Hypothesis HD0:tm StD S0=Some(mkTrans S1 DR StB).
Hypothesis HD1:tm StD S1=Some(mkTrans S0 DR StA).
Local Ltac vfd_compute:=
 cbn[Nat.add Nat.mul csteps cstep ctape_move chd ctl t_next t_dir t_write repeat app];
 repeat(first[rewrite HA0|rewrite HA1|rewrite HB0|rewrite HB1|rewrite HC0|rewrite HC1|rewrite HD0|rewrite HD1];
 cbn[Nat.add Nat.mul csteps cstep ctape_move chd ctl t_next t_dir t_write repeat app]);
 repeat rewrite app_nil_r;reflexivity.
Definition vfd_hit(w:list Sym):Prop:=exists k L R,
 stepn tm k(lift(StA,([],S0,w)))=Some(lift(StD,(L,S0,R))).
Lemma vfd_pad_left:forall w,
 lift(StA,([],S0,w))=lift(StA,([S0],S0,w)).
Proof.
 intro w;unfold lift,lift_tape;cbn[fst snd]. f_equal;f_equal.
 apply lpad_eqb_lift;reflexivity.
Qed.
Lemma vfd_back:forall w w' k,
 stepn tm k(lift(StA,([],S0,w)))=Some(lift(StA,([],S0,w')))->
 vfd_hit w'->vfd_hit w.
Proof.
 intros w w' k H[k'[L[R H']]]. exists(k+k'),L,R. now rewrite stepn_add,H.
Qed.
Lemma vfd_direct:forall ms R,vfd_hit(vft_Ps ms++S1::S0::R).
Proof.
 intros ms R. destruct(vft_push tm HA0 HB1 HD0 HD1 ms [] [] (S1::S0::R))as[k Hk].
 rewrite app_nil_r in Hk. cbn[vft_stack]in Hk.
 exists(k+2),(S1::S1::S0::vft_stack(rev ms)[]),R.
 rewrite vfd_pad_left. apply csteps_lift. rewrite csteps_add,Hk. vfd_compute.
Qed.
Lemma vfd_turn:forall L R,
 csteps tm 4(StA,(S0::L,S0,S0::R))=
 Some(StA,(ctl L,chd L,S1::s::S1::R)).
Proof. intros L R;destruct s;vfd_compute. Qed.
Lemma vfd_reset:forall ms R,
 exists k,stepn tm k(lift(StA,([],S0,vft_Ps ms++S0::R)))=
 Some(lift(StA,([],S0,vft_Us ms++S1::s::S1::R))).
Proof.
 intros ms R. destruct(vft_push tm HA0 HB1 HD0 HD1 ms [] [] (S0::R))as[k Hk].
 rewrite app_nil_r in Hk. cbn[vft_stack]in Hk.
 destruct(vft_pop tm HA1 HC0 HC1(rev ms)[](S1::s::S1::R))as[j Hj].
 rewrite rev_involutive in Hj.
 exists(k+(4+j)). rewrite vfd_pad_left. apply csteps_lift.
 rewrite csteps_add,Hk,csteps_add,vfd_turn. exact Hj.
Qed.
Lemma vfd_three:forall k R,vfd_hit(vft_Ps(repeat 0 k)++S1::S1::S1::R).
Proof.
 intros k R. destruct(vft_frontier tm HA0 HA1 HB1 HC0 HC1 HD0 HD1(repeat 0 k)0 R)
 as[j[Hpos Hj]].
 change(vft_Ps(repeat 0 k)++vft_Q 0++R)with(vft_Ps(repeat 0 k)++S1::S1::S1::R)in Hj.
 eapply vfd_back;[exact Hj|]. rewrite vfd_Us0.
 change(vfd_hit(vft_Ps(repeat 0 k)++vft_P 0++S1::S0::R)).
 rewrite app_assoc,vfd_Ps_snoc. apply vfd_direct.
Qed.
Lemma vfd_zero:forall k R,vfd_hit(vft_Ps(repeat 0 k)++S0::R).
Proof.
 intros k R. destruct(vfd_reset(repeat 0 k)R)as[j Hj].
 eapply vfd_back;[exact Hj|]. rewrite vfd_Us0.
 destruct s;[apply vfd_direct|apply vfd_three].
Qed.
Theorem vfd_padded:forall R k,vfd_hit(vft_Ps(repeat 0 k)++R++[S0;S0]).
Proof.
 intro R. remember(length R)as z eqn:Ez. revert R Ez.
 induction z using lt_wf_ind;intros R Ez k.
 destruct R as[|a R].
 - change(vfd_hit(vft_Ps(repeat 0 k)++S0::[S0])). apply vfd_zero.
 - destruct a.
   + change(vfd_hit(vft_Ps(repeat 0 k)++S0::(R++[S0;S0]))). apply vfd_zero.
   + destruct R as[|a R].
     * change(vfd_hit(vft_Ps(repeat 0 k)++S1::S0::[S0])). apply vfd_direct.
     * destruct a.
       -- change(vfd_hit(vft_Ps(repeat 0 k)++S1::S0::(R++[S0;S0]))). apply vfd_direct.
       -- destruct R as[|a R].
          ++ change(vfd_hit(vft_Ps(repeat 0 k)++vft_P 0++[S0])).
             rewrite app_assoc,vfd_Ps_snoc. apply vfd_zero.
          ++ destruct a.
             ** change(vfd_hit(vft_Ps(repeat 0 k)++vft_P 0++R++[S0;S0])).
                rewrite app_assoc,vfd_Ps_snoc. apply(H(length R));[cbn in Ez;lia|reflexivity].
             ** change(vfd_hit(vft_Ps(repeat 0 k)++S1::S1::S1::(R++[S0;S0]))).
                apply vfd_three.
Qed.
Theorem vfd_D0_frontier:forall R,
 exists k L R',stepn tm k(lift(StA,([],S0,R)))=Some(lift(StD,(L,S0,R'))).
Proof. intro R;rewrite pwt_pad. exact(vfd_padded R 0). Qed.
End Machine.
