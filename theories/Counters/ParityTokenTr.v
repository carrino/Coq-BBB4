(** Two-phase parity counter over repeated 10 blocks.
    The mutual carry transducers are proved for every finite suffix.
    Exact macro steps and instruction witnesses use only the eight local
    transition equations below. *)
From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Counters Require Import ValueLapTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
Import ListNotations.

Fixpoint pt_f (w : list Sym) : list Sym :=
 match w with
 | [] => [S1;S1]
 | S0::x => S1::S1::x
 | S1::[] => [S1;S0;S1;S1]
 | S1::S0::x => S1::S0::pt_f x
 | S1::S1::x => S1::S0::S0::pt_u x
 end
with pt_u (w : list Sym) : list Sym :=
 match w with
 | [] | S0::[] => [S0;S1;S1]
 | S1::x => S1::x
 | S0::S0::x => S0::pt_f x
 | S0::S1::x => S0::S0::pt_u x
 end.
Fixpoint pt_fc (w : list Sym) : nat :=
 match w with
 | [] | S0::_ => 3
 | S1::[] => 9
 | S1::S0::x => 6+pt_fc x
 | S1::S1::x => 5+pt_uc x
 end
with pt_uc (w : list Sym) : nat :=
 match w with
 | [] | S0::[] => 8
 | S1::_ => 2
 | S0::S0::x => 5+pt_fc x
 | S0::S1::x => 4+pt_uc x
 end.
Lemma pt_f_head : forall w, exists x, pt_f w = S1::x.
Proof. intros [|[] [|[] w]]; eexists; reflexivity. Qed.

Lemma pt_repeat_tail : forall (x : Sym) n R,
 repeat x n ++ x::R = x::repeat x n ++ R.
Proof. intros x n;induction n;intros R;cbn [repeat app];[reflexivity|now rewrite IHn]. Qed.

Fixpoint pt_blks (k : nat) : list Sym :=
 match k with 0 => [] | S j => S1::S0::pt_blks j end.
Lemma pt_blks_tail : forall k R,
 pt_blks k ++ S1::S0::R = S1::S0::pt_blks k ++ R.
Proof. induction k;intros R;cbn [pt_blks app];[reflexivity|now rewrite IHk]. Qed.
Lemma pt_f_blocks : forall k w,
 pt_f (pt_blks k ++ w) = pt_blks k ++ pt_f w.
Proof. induction k;intros w;cbn [pt_blks app pt_f];[reflexivity|now rewrite IHk]. Qed.
Lemma pt_fc_blocks : forall k w,
 pt_fc (pt_blks k ++ w) = 6*k+pt_fc w.
Proof. induction k;intros w;cbn [pt_blks app pt_fc];[lia|rewrite IHk;lia]. Qed.
Definition pt_next (w : list Sym) : list Sym :=
 match w with [] => [S1;S1] | S0::x => pt_f x | S1::x => S0::pt_u x end.
Lemma pt_u_zero : forall w, pt_u (S0::w) = S0::pt_next w.
Proof. intros [|[] x];reflexivity. Qed.
Definition pt_even k w : cconf := (StB,([],S0,pt_blks k ++ S0::S0::w)).
Definition pt_odd k w : cconf := (StB,([],S0,pt_blks k ++ S1::S1::S0::w)).

Section Parity.
Variable tm : TM.
Hypothesis HA0 : tm StA S0 = Some (mkTrans S1 DR StB).
Hypothesis HA1 : tm StA S1 = Some (mkTrans S1 DL StD).
Hypothesis HB0 : tm StB S0 = Some (mkTrans S0 DR StC).
Hypothesis HB1 : tm StB S1 = Some (mkTrans S1 DR StA).
Hypothesis HC0 : tm StC S0 = Some (mkTrans S1 DL StD).
Hypothesis HC1 : tm StC S1 = Some (mkTrans S1 DR StB).
Hypothesis HD0 : tm StD S0 = Some (mkTrans S1 DL StB).
Hypothesis HD1 : tm StD S1 = Some (mkTrans S0 DL StD).
Local Ltac pt_compute :=
 cbn [csteps cstep ctape_move chd ctl t_next t_dir t_write];
 repeat (first [rewrite HA0|rewrite HA1|rewrite HB0|rewrite HB1|
                rewrite HC0|rewrite HC1|rewrite HD0|rewrite HD1];
         cbn [csteps cstep ctape_move chd ctl t_next t_dir t_write]);
 reflexivity.
Lemma pt_drain : forall m L R,
 csteps tm (m+1)
  (StD,(ctl (repeat S1 m ++ S0::L),chd (repeat S1 m ++ S0::L),R)) =
 Some (StB,(ctl L,chd L,S1::repeat S0 m ++ R)).
Proof.
 induction m as [|m IH];intros L R.
 - cbn [repeat app ctl chd Nat.add]. pt_compute.
 - replace (S m+1) with (1+(m+1)) by lia.
   cbn [repeat app ctl chd]. rewrite csteps_add.
   assert (H : csteps tm 1 (StD,(repeat S1 m ++ S0::L,S1,R)) =
    Some (StD,(ctl (repeat S1 m ++ S0::L),chd (repeat S1 m ++ S0::L),S0::R))) by pt_compute.
   rewrite H, IH. f_equal. f_equal. f_equal.
   now rewrite pt_repeat_tail.
Qed.
Lemma pt_return : forall m L R,
 csteps tm (m+4) (StB,(repeat S1 m ++ S0::L,S1,S1::R)) =
 Some (StB,(ctl L,chd L,S1::repeat S0 (S m) ++ S1::R)).
Proof.
 intros m L R. replace (m+4) with (2+(S m+1)) by lia.
 rewrite csteps_add.
 assert (H : csteps tm 2 (StB,(repeat S1 m ++ S0::L,S1,S1::R)) =
   Some (StD,(repeat S1 m ++ S0::L,S1,S1::R))) by pt_compute.
 rewrite H. apply (pt_drain (S m)).
Qed.
Lemma pt_runs : forall w,
 (forall L, csteps tm (pt_fc w) (StB,(L,S0,w)) =
  Some (StB,(ctl L,chd L,pt_f w))) /\
 (forall m L, csteps tm (m+pt_uc w)
  (StA,(repeat S1 m ++ S0::L,chd w,ctl w)) =
  Some (StB,(ctl L,chd L,S1::repeat S0 m ++ pt_u w))).
Proof.
 fix IH 1. intro w. split.
 - intro L. destruct w as [|b x].
   + cbn [pt_fc pt_f]. pt_compute.
   + destruct b.
     * cbn [pt_fc pt_f]. pt_compute.
     * destruct x as [|b x].
       -- cbn [pt_fc pt_f]. pt_compute.
       -- destruct b.
          ++ cbn [pt_fc pt_f].
             replace (6+pt_fc x) with (2+(pt_fc x+4)) by lia.
             rewrite csteps_add.
             assert (H : csteps tm 2 (StB,(L,S0,S1::S0::x)) =
               Some (StB,(S1::S0::L,S0,x))) by pt_compute.
             rewrite H,csteps_add,(proj1 (IH x)). cbn [ctl chd].
             destruct (pt_f_head x) as [r Hr]. rewrite Hr.
             apply (pt_return 0).
          ++ cbn [pt_fc pt_f].
             replace (5+pt_uc x) with (3+(2+pt_uc x)) by lia.
             rewrite csteps_add.
             assert (H : csteps tm 3 (StB,(L,S0,S1::S1::x)) =
               Some (StA,(S1::S1::S0::L,chd x,ctl x))) by pt_compute.
             rewrite H. apply (proj2 (IH x) 2).
 - intros m L. destruct w as [|b x].
   + cbn [pt_uc pt_u ctl chd].
     replace (m+8) with (4+(m+4)) by lia.
     rewrite csteps_add.
     assert (H : csteps tm 4 (StA,(repeat S1 m ++ S0::L,S0,[])) =
       Some (StB,(repeat S1 m ++ S0::L,S1,[S1;S1]))) by pt_compute.
     rewrite H,pt_return. cbn [repeat].
     f_equal. f_equal. f_equal.
     repeat rewrite pt_repeat_tail. reflexivity.
   + destruct b.
     * destruct x as [|b x].
       -- cbn [pt_uc pt_u ctl chd].
          replace (m+8) with (4+(m+4)) by lia.
          rewrite csteps_add.
          assert (H : csteps tm 4 (StA,(repeat S1 m ++ S0::L,S0,[])) =
            Some (StB,(repeat S1 m ++ S0::L,S1,[S1;S1]))) by pt_compute.
          rewrite H,pt_return. cbn [repeat].
          f_equal. f_equal. f_equal.
          repeat rewrite pt_repeat_tail. reflexivity.
       -- destruct b.
          ++ cbn [pt_uc pt_u ctl chd].
             replace (m+(5+pt_fc x)) with (1+(pt_fc x+(m+4))) by lia.
             rewrite csteps_add.
             assert (H : csteps tm 1 (StA,(repeat S1 m ++ S0::L,S0,S0::x)) =
               Some (StB,(S1::repeat S1 m ++ S0::L,S0,x))) by pt_compute.
             rewrite H,csteps_add,(proj1 (IH x)). cbn [ctl chd].
             destruct (pt_f_head x) as [r Hr]. rewrite Hr,pt_return.
             cbn [repeat]. f_equal. f_equal. f_equal.
             repeat rewrite pt_repeat_tail. reflexivity.
          ++ cbn [pt_uc pt_u ctl chd].
             replace (m+(4+pt_uc x)) with (2+((S (S m))+pt_uc x)) by lia.
             rewrite csteps_add.
             assert (H : csteps tm 2 (StA,(repeat S1 m ++ S0::L,S0,S1::x)) =
               Some (StA,(S1::S1::repeat S1 m ++ S0::L,chd x,ctl x))) by pt_compute.
             rewrite H.
             change (csteps tm (S (S m)+pt_uc x)
               (StA,(repeat S1 (S (S m)) ++ S0::L,chd x,ctl x)) =
               Some (StB,(ctl L,chd L,S1::repeat S0 m ++ S0::S0::pt_u x))).
             rewrite (proj2 (IH x) (S (S m))). cbn [repeat].
             f_equal. f_equal. f_equal.
             repeat rewrite pt_repeat_tail. reflexivity.
     * cbn [pt_uc pt_u ctl chd].
       replace (m+2) with (1+(m+1)) by lia.
       rewrite csteps_add.
       assert (H : csteps tm 1 (StA,(repeat S1 m ++ S0::L,S1,x)) =
        Some (StD,(ctl (repeat S1 m ++ S0::L),chd (repeat S1 m ++ S0::L),S1::x))) by pt_compute.
       rewrite H,pt_drain. reflexivity.
Qed.
Lemma pt_f_run : forall w L,
 csteps tm (pt_fc w) (StB,(L,S0,w)) = Some (StB,(ctl L,chd L,pt_f w)).
Proof. intros w;exact (proj1 (pt_runs w)). Qed.
Lemma pt_prefix : forall k L w,
 csteps tm (2*k) (StB,(L,S0,pt_blks k ++ w)) =
 Some (StB,(pt_blks k ++ L,S0,w)).
Proof.
 induction k as [|k IH];intros L w.
 - reflexivity.
 - replace (2*S k) with (2+2*k) by lia.
   cbn [pt_blks app]. rewrite csteps_add.
   assert (H : csteps tm 2 (StB,(L,S0,S1::S0::pt_blks k ++ w)) =
    Some (StB,(S1::S0::L,S0,pt_blks k ++ w))) by pt_compute.
   rewrite H,IH,pt_blks_tail. reflexivity.
Qed.
Lemma pt_even_run : forall k w,
 csteps tm (6*k+3) (pt_even k w) = Some (pt_odd k w).
Proof.
 intros k w. pose proof (pt_f_run (pt_blks k ++ S0::S0::w) []) as H.
 rewrite pt_fc_blocks,pt_f_blocks in H. exact H.
Qed.
Lemma pt_odd_run : forall k w,
 csteps tm (6*k+5+pt_uc (S0::w)) (pt_odd k w) =
 Some (pt_even (S k) (pt_next w)).
Proof.
 intros k w. pose proof (pt_f_run (pt_blks k ++ S1::S1::S0::w) []) as H.
 rewrite pt_fc_blocks,pt_f_blocks in H. cbn [pt_fc pt_f] in H.
 rewrite pt_u_zero,pt_blks_tail in H.
 replace (6*k+5+pt_uc (S0::w)) with (6*k+(5+pt_uc (S0::w))) by lia.
 exact H.
Qed.
Lemma pt_lap : forall k w,
 csteps tm (12*k+8+pt_uc (S0::w)) (pt_even k w) =
 Some (pt_even (S k) (pt_next w)).
Proof.
 intros k w. replace (12*k+8+pt_uc (S0::w)) with
  ((6*k+3)+(6*k+5+pt_uc (S0::w))) by lia.
 rewrite csteps_add,pt_even_run. apply pt_odd_run.
Qed.
Lemma pt_fire : forall k w t,
 exists j c, csteps tm j (pt_even (S k) w) = Some c /\ cinstr c = t.
Proof.
 intros k w [q b]. destruct q,b.
 - eexists ((6*S k+3)+(2*S k+3)),_. split.
   + rewrite csteps_add,pt_even_run. unfold pt_odd.
     rewrite csteps_add,pt_prefix. pt_compute.
   + reflexivity.
 - eexists (2*S k+4),_. split.
   + unfold pt_even. rewrite csteps_add,pt_prefix.
     cbn [pt_blks app]. pt_compute.
   + reflexivity.
 - exists 0,(pt_even (S k) w). split;reflexivity.
 - eexists (2*S k+3),_. split.
   + unfold pt_even. rewrite csteps_add,pt_prefix.
     cbn [pt_blks app]. pt_compute.
   + reflexivity.
 - eexists (2*S k+1),_. split.
   + unfold pt_even. rewrite csteps_add,pt_prefix. pt_compute.
   + reflexivity.
 - eexists 1,_. split.
   + unfold pt_even. cbn [pt_blks app]. pt_compute.
   + reflexivity.
 - eexists (2*S k+2),_. split.
   + unfold pt_even. rewrite csteps_add,pt_prefix. pt_compute.
   + reflexivity.
 - eexists (2*S k+5),_. split.
   + unfold pt_even. rewrite csteps_add,pt_prefix.
     cbn [pt_blks app]. pt_compute.
   + reflexivity.
Qed.
Theorem pt_neverqhtr : forall w0,
 (exists t0, stepn tm t0 InitES = Some (lift (pt_even 2 w0))) ->
 NeverQuasiHaltsTr tm.
Proof.
 intros w0 Hb.
 apply (value_lap_neverqhtr tm (list Sym) pt_next
   (fun n w => pt_even (S (S n)) w) w0).
 - exact Hb.
 - intros n w. exists (12*S (S n)+8+pt_uc (S0::w)),
     (pt_even (S (S (S n))) (pt_next w)).
   split;[apply pt_lap|]. split;[reflexivity|lia].
 - intros n w t. apply pt_fire.
Qed.
End Parity.
