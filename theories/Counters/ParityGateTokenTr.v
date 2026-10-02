(** Three-phase parity counter over repeated 100 blocks.
    The mutual carry transducers are proved for every finite suffix.
    Exact macro steps and instruction witnesses use only the eight local
    transition equations below. *)
From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Counters Require Import ValueLapTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
Import ListNotations.

Fixpoint qg_f (w : list Sym) : list Sym :=
 match w with [] => [S1;S1] | S0::x => S1::S1::x | S1::x => S1::S0::qg_u x end
with qg_u (w : list Sym) : list Sym :=
 match w with
 | [] | S0::[] => [S0;S1;S1]
 | S1::x => S1::x
 | S0::S0::x => S0::qg_f x
 | S0::S1::x => S0::S0::qg_u x
 end.
Fixpoint qg_fc (w : list Sym) : nat :=
 match w with [] | S0::_ => 3 | S1::x => 3+qg_uc x end
with qg_uc (w : list Sym) : nat :=
 match w with
 | [] | S0::[] => 8
 | S1::_ => 2
 | S0::S0::x => 5+qg_fc x
 | S0::S1::x => 4+qg_uc x
 end.
Lemma qg_f_head : forall w, exists x, qg_f w = S1::x.
Proof. intros [|[] w]; eexists; reflexivity. Qed.

Lemma qg_repeat_tail : forall (x : Sym) n R,
 repeat x n ++ x::R = x::repeat x n ++ R.
Proof. intros x n;induction n;intros R;cbn [repeat app];[reflexivity|now rewrite IHn]. Qed.

Fixpoint qg_blks (k : nat) : list Sym :=
 match k with 0 => [] | S j => S1::S0::S0::qg_blks j end.
Lemma qg_blks_tail : forall k R,
 qg_blks k ++ S1::S0::S0::R = S1::S0::S0::qg_blks k ++ R.
Proof. induction k;intros R;cbn [qg_blks app];[reflexivity|now rewrite IHk]. Qed.
Lemma qg_f_blocks : forall k w,
 qg_f (qg_blks k ++ w) = qg_blks k ++ qg_f w.
Proof. induction k;intros w;cbn [qg_blks app qg_f qg_u];[reflexivity|now rewrite IHk]. Qed.
Lemma qg_fc_blocks : forall k w,
 qg_fc (qg_blks k ++ w) = 8*k+qg_fc w.
Proof. induction k;intros w;cbn [qg_blks app qg_fc qg_uc];[lia|rewrite IHk;lia]. Qed.
Definition qg_next (w : list Sym) : list Sym :=
 match w with [] => [S1;S1] | S0::x => qg_f x | S1::x => S0::qg_u x end.
Lemma qg_u_zero : forall w, qg_u (S0::w) = S0::qg_next w.
Proof. intros [|[] x];reflexivity. Qed.
Definition qg_even k w : cconf := (StB,([],S0,qg_blks k ++ S0::S0::w)).
Definition qg_odd k w : cconf := (StB,([],S0,qg_blks k ++ S1::S1::S0::w)).

Definition qg_odd2 k w : cconf := (StB,([],S0,qg_blks k ++ S1::S0::S1::S0::w)).
Fixpoint qg_back (k:nat) : list Sym := match k with 0=>[]|S j=>S1::S1::S0::qg_back j end.
Lemma qg_back_tail : forall k R,
 qg_back k ++ S1::S1::S0::R = S1::S1::S0::qg_back k ++ R.
Proof. induction k;intros R;cbn [qg_back app];[reflexivity|now rewrite IHk]. Qed.
Definition qg_exit (port:bool) (w:list Sym) : St :=
 match w with S1::_=>StB|_=>if port then StC else StB end.
Section Parity.
Variable tm : TM.
Variable port : bool.
Hypothesis HA0 : tm StA S0 = Some (mkTrans S1 DR StB).
Hypothesis HA1 : tm StA S1 = Some (mkTrans S1 DL StD).
Hypothesis HB0 : tm StB S0 = Some (mkTrans S0 DR StC).
Hypothesis HB1 : tm StB S1 = Some (mkTrans S1 DR StA).
Hypothesis HC0 : tm StC S0 = Some (mkTrans S1 DL (if port then StC else StD)).
Hypothesis HC1 : tm StC S1 = Some (mkTrans S1 DR StA).
Hypothesis HD0 : tm StD S0 = Some (mkTrans S1 DL StB).
Hypothesis HD1 : tm StD S1 = Some (mkTrans S0 DL StD).
Local Ltac qg_compute :=
 cbn [csteps cstep ctape_move chd ctl t_next t_dir t_write];
 repeat (first [rewrite HA0|rewrite HA1|rewrite HB0|rewrite HB1|
                rewrite HC0|rewrite HC1|rewrite HD0|rewrite HD1];
         cbn [csteps cstep ctape_move chd ctl t_next t_dir t_write]);
 reflexivity.
Lemma qg_drain : forall m L R,
 csteps tm (m+1)
  (StD,(ctl (repeat S1 m ++ S0::L),chd (repeat S1 m ++ S0::L),R)) =
 Some (StB,(ctl L,chd L,S1::repeat S0 m ++ R)).
Proof.
 induction m as [|m IH];intros L R.
 - cbn [repeat app ctl chd Nat.add]. qg_compute.
 - replace (S m+1) with (1+(m+1)) by lia.
   cbn [repeat app ctl chd]. rewrite csteps_add.
   assert (H : csteps tm 1 (StD,(repeat S1 m ++ S0::L,S1,R)) =
    Some (StD,(ctl (repeat S1 m ++ S0::L),chd (repeat S1 m ++ S0::L),S0::R))) by qg_compute.
   rewrite H, IH. f_equal. f_equal. f_equal.
   now rewrite qg_repeat_tail.
Qed.
Lemma qg_exit_one : forall w, tm (qg_exit port w) S1 = Some (mkTrans S1 DR StA).
Proof. intros [|[] w];cbn [qg_exit];try exact HB1;destruct port;assumption. Qed.
Lemma qg_return : forall w m L R,
 csteps tm (m+4) (qg_exit port w,(repeat S1 m ++ S0::L,S1,S1::R)) =
 Some (StB,(ctl L,chd L,S1::repeat S0 (S m) ++ S1::R)).
Proof.
 intros w m L R. replace (m+4) with (2+(S m+1)) by lia.
 rewrite csteps_add.
 assert (H : csteps tm 2 (qg_exit port w,(repeat S1 m ++ S0::L,S1,S1::R)) =
   Some (StD,(repeat S1 m ++ S0::L,S1,S1::R))).
 { cbn [csteps cstep]. rewrite qg_exit_one. qg_compute. }
 rewrite H. apply (qg_drain (S m)).
Qed.
Lemma qg_runs : forall w,
 (forall L, csteps tm (qg_fc w) (StB,(L,S0,w)) =
  Some (qg_exit port w,(ctl L,chd L,qg_f w))) /\
 (forall m L, csteps tm (m+qg_uc w)
  (StA,(repeat S1 m ++ S0::L,chd w,ctl w)) =
  Some (StB,(ctl L,chd L,S1::repeat S0 m ++ qg_u w))).
Proof.
 fix IH 1. intro w. split.
 - intro L. destruct w as [|b x].
   + cbn [qg_fc qg_f qg_exit]. clear IH; destruct port; qg_compute.
   + destruct b.
     * cbn [qg_fc qg_f qg_exit]. clear IH; destruct port; qg_compute.
     * cbn [qg_fc qg_f qg_exit].
       replace (3+qg_uc x) with (2+(1+qg_uc x)) by lia.
       rewrite csteps_add.
       assert (H : csteps tm 2 (StB,(L,S0,S1::x)) =
         Some (StA,(S1::S0::L,chd x,ctl x))) by qg_compute.
       rewrite H. apply (proj2 (IH x) 1).
 - intros m L. destruct w as [|b x].
   + cbn [qg_uc qg_u ctl chd].
     replace (m+8) with (4+(m+4)) by lia.
     rewrite csteps_add.
     assert (H : csteps tm 4 (StA,(repeat S1 m ++ S0::L,S0,[])) =
       Some (qg_exit port [],(repeat S1 m ++ S0::L,S1,[S1;S1]))).
     { clear IH; destruct port; qg_compute. }
     rewrite H,qg_return. cbn [repeat].
     f_equal. f_equal. f_equal.
     repeat rewrite qg_repeat_tail. reflexivity.
   + destruct b.
     * destruct x as [|b x].
       -- cbn [qg_uc qg_u ctl chd].
          replace (m+8) with (4+(m+4)) by lia.
          rewrite csteps_add.
          assert (H : csteps tm 4 (StA,(repeat S1 m ++ S0::L,S0,[])) =
            Some (qg_exit port [],(repeat S1 m ++ S0::L,S1,[S1;S1]))).
     { clear IH; destruct port; qg_compute. }
          rewrite H,qg_return. cbn [repeat].
          f_equal. f_equal. f_equal.
          repeat rewrite qg_repeat_tail. reflexivity.
       -- destruct b.
          ++ cbn [qg_uc qg_u ctl chd].
             replace (m+(5+qg_fc x)) with (1+(qg_fc x+(m+4))) by lia.
             rewrite csteps_add.
             assert (H : csteps tm 1 (StA,(repeat S1 m ++ S0::L,S0,S0::x)) =
               Some (StB,(S1::repeat S1 m ++ S0::L,S0,x))) by qg_compute.
             rewrite H,csteps_add,(proj1 (IH x)). cbn [ctl chd].
             destruct (qg_f_head x) as [r Hr]. rewrite Hr,qg_return.
             cbn [repeat]. f_equal. f_equal. f_equal.
             repeat rewrite qg_repeat_tail. reflexivity.
          ++ cbn [qg_uc qg_u ctl chd].
             replace (m+(4+qg_uc x)) with (2+((S (S m))+qg_uc x)) by lia.
             rewrite csteps_add.
             assert (H : csteps tm 2 (StA,(repeat S1 m ++ S0::L,S0,S1::x)) =
               Some (StA,(S1::S1::repeat S1 m ++ S0::L,chd x,ctl x))) by qg_compute.
             rewrite H.
             change (csteps tm (S (S m)+qg_uc x)
               (StA,(repeat S1 (S (S m)) ++ S0::L,chd x,ctl x)) =
               Some (StB,(ctl L,chd L,S1::repeat S0 m ++ S0::S0::qg_u x))).
             rewrite (proj2 (IH x) (S (S m))). cbn [repeat].
             f_equal. f_equal. f_equal.
             repeat rewrite qg_repeat_tail. reflexivity.
     * cbn [qg_uc qg_u ctl chd].
       replace (m+2) with (1+(m+1)) by lia.
       rewrite csteps_add.
       assert (H : csteps tm 1 (StA,(repeat S1 m ++ S0::L,S1,x)) =
        Some (StD,(ctl (repeat S1 m ++ S0::L),chd (repeat S1 m ++ S0::L),S1::x))) by qg_compute.
       rewrite H,qg_drain. reflexivity.
Qed.
Lemma qg_f_run : forall w L,
 csteps tm (qg_fc w) (StB,(L,S0,w)) = Some (qg_exit port w,(ctl L,chd L,qg_f w)).
Proof. intros w;exact (proj1 (qg_runs w)). Qed.
Lemma qg_prefix : forall k L w,
 csteps tm (3*k) (StB,(L,S0,qg_blks k ++ w)) =
 Some (StB,(qg_back k ++ L,S0,w)).
Proof.
 induction k as [|k IH];intros L w.
 - reflexivity.
 - replace (3*S k) with (3+3*k) by lia.
   cbn [qg_blks app]. rewrite csteps_add.
   assert (H : csteps tm 3 (StB,(L,S0,S1::S0::S0::qg_blks k ++ w)) =
    Some (StB,(S1::S1::S0::L,S0,qg_blks k ++ w))) by qg_compute.
   rewrite H,IH,qg_back_tail. reflexivity.
Qed.
Lemma qg_even_run : forall k w,
 csteps tm (8*S k+3) (qg_even (S k) w) = Some (qg_odd (S k) w).
Proof.
 intros k w. pose proof (qg_f_run (qg_blks (S k) ++ S0::S0::w) []) as H.
 rewrite qg_fc_blocks,qg_f_blocks in H. exact H.
Qed.
Lemma qg_odd_run : forall k w,
 csteps tm (8*k+5) (qg_odd k w) = Some (qg_odd2 k w).
Proof.
 intros k w. pose proof (qg_f_run (qg_blks k ++ S1::S1::S0::w) []) as H.
 rewrite qg_fc_blocks,qg_f_blocks in H.
 destruct k;exact H.
Qed.
Lemma qg_odd2_run : forall k w,
 csteps tm (8*k+7+qg_uc (S0::w)) (qg_odd2 k w) =
 Some (qg_even (S k) (qg_next w)).
Proof.
 intros k w. pose proof (qg_f_run (qg_blks k ++ S1::S0::S1::S0::w) []) as H.
 rewrite qg_fc_blocks,qg_f_blocks in H.
 change (csteps tm (8*k+(3+(4+qg_uc (S0::w))))
  (StB,([],S0,qg_blks k ++ S1::S0::S1::S0::w)) =
  Some (qg_exit port (qg_blks k ++ S1::S0::S1::S0::w),
    ([],S0,qg_blks k ++ S1::S0::S0::S0::qg_u (S0::w)))) in H.
 rewrite qg_u_zero,qg_blks_tail in H.
 replace (8*k+7+qg_uc (S0::w)) with (8*k+(3+(4+qg_uc (S0::w)))) by lia.
 destruct k;exact H.
Qed.
Lemma qg_to_odd2 : forall k w,
 csteps tm (16*S k+8) (qg_even (S k) w) = Some (qg_odd2 (S k) w).
Proof.
 intros k w. replace (16*S k+8) with ((8*S k+3)+(8*S k+5)) by lia.
 rewrite csteps_add,qg_even_run. apply qg_odd_run.
Qed.
Lemma qg_lap : forall k w, 0<k ->
 csteps tm (24*k+15+qg_uc (S0::w)) (qg_even k w) =
 Some (qg_even (S k) (qg_next w)).
Proof.
 intros [|k] w Hk;[lia|].
 replace (24*S k+15+qg_uc (S0::w)) with ((16*S k+8)+(8*S k+7+qg_uc (S0::w))) by lia.
 rewrite csteps_add,qg_to_odd2. apply qg_odd2_run.
Qed.
Lemma qg_fire : forall k w t,
 exists j c, csteps tm j (qg_even (S k) w) = Some c /\ cinstr c = t.
Proof.
 intros k w [q b]. destruct q,b.
 - eexists 2,_. split.
   + unfold qg_even. cbn [qg_blks app]. qg_compute.
   + reflexivity.
 - eexists (3*S k+4),_. split.
   + unfold qg_even. rewrite csteps_add,qg_prefix.
     cbn [qg_back app]. destruct port; qg_compute.
   + reflexivity.
 - exists 0,(qg_even (S k) w). split;reflexivity.
 - eexists ((16*S k+8)+(3*S k+3)),_. split.
   + rewrite csteps_add,qg_to_odd2. unfold qg_odd2.
     rewrite csteps_add,qg_prefix. qg_compute.
   + reflexivity.
 - eexists (3*S k+1),_. split.
   + unfold qg_even. rewrite csteps_add,qg_prefix. qg_compute.
   + reflexivity.
 - eexists 1,_. split.
   + unfold qg_even. cbn [qg_blks app]. qg_compute.
   + reflexivity.
 - eexists (3*S k+7),_. split.
   + unfold qg_even. rewrite csteps_add,qg_prefix.
     cbn [qg_back app]. destruct port; qg_compute.
   + reflexivity.
 - eexists (3*S k+5),_. split.
   + unfold qg_even. rewrite csteps_add,qg_prefix.
     cbn [qg_back app]. destruct port; qg_compute.
   + reflexivity.
Qed.
End Parity.
