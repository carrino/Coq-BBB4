(** Two-phase parity counter with a C-state carry entry.
    The mutual carry transducers are proved for every finite suffix.
    Exact macro steps and instruction witnesses use only the eight local
    transition equations below. *)
From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Counters Require Import ValueLapTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
Import ListNotations.

Fixpoint pc_f (w : list Sym) : list Sym :=
 match w with
 | [] => [S1;S1]
 | S0::x => S1::S1::x
 | S1::[] => [S1;S0;S1;S1]
 | S1::S0::x => S1::S0::pc_f x
 | S1::S1::x => S1::S0::S0::pc_u x
 end
with pc_u (w : list Sym) : list Sym :=
 match w with
 | [] | S0::[] => [S0;S1]
 | S1::x => S1::x
 | S0::S0::x => S0::S1::x
 | S0::S1::[] => [S0;S0;S1;S1]
 | S0::S1::S0::x => S0::S0::pc_f x
 | S0::S1::S1::x => S0::S0::S0::pc_u x
 end.
Fixpoint pc_fc (w : list Sym) : nat :=
 match w with
 | [] | S0::_ => 3
 | S1::[] => 9
 | S1::S0::x => 6+pc_fc x
 | S1::S1::x => 5+pc_uc x
 end
with pc_uc (w : list Sym) : nat :=
 match w with
 | [] | S0::[] | S0::S0::_ => 4
 | S1::_ => 2
 | S0::S1::[] => 10
 | S0::S1::S0::x => 7+pc_fc x
 | S0::S1::S1::x => 6+pc_uc x
 end.
Lemma pc_f_head : forall w, exists x, pc_f w = S1::x.
Proof. intros [|[] [|[] w]]; eexists; reflexivity. Qed.

Lemma pc_repeat_tail : forall (x : Sym) n R,
 repeat x n ++ x::R = x::repeat x n ++ R.
Proof. intros x n;induction n;intros R;cbn [repeat app];[reflexivity|now rewrite IHn]. Qed.

Fixpoint pc_blks (k : nat) : list Sym :=
 match k with 0 => [] | S j => S1::S0::pc_blks j end.
Lemma pc_blks_tail : forall k R,
 pc_blks k ++ S1::S0::R = S1::S0::pc_blks k ++ R.
Proof. induction k;intros R;cbn [pc_blks app];[reflexivity|now rewrite IHk]. Qed.
Lemma pc_f_blocks : forall k w,
 pc_f (pc_blks k ++ w) = pc_blks k ++ pc_f w.
Proof. induction k;intros w;cbn [pc_blks app pc_f];[reflexivity|now rewrite IHk]. Qed.
Lemma pc_fc_blocks : forall k w,
 pc_fc (pc_blks k ++ w) = 6*k+pc_fc w.
Proof. induction k;intros w;cbn [pc_blks app pc_fc];[lia|rewrite IHk;lia]. Qed.
Definition pc_next (w : list Sym) : list Sym :=
 match w with
 | [] => [S1]
 | S0::x => S1::x
 | S1::[] => [S0;S1;S1]
 | S1::S0::x => S0::pc_f x
 | S1::S1::x => S0::S0::pc_u x
 end.
Lemma pc_u_zero : forall w, pc_u (S0::w) = S0::pc_next w.
Proof. intros [|[] [|[] x]];reflexivity. Qed.
Definition pc_even k w : cconf := (StB,([],S0,pc_blks k ++ S0::S0::w)).
Definition pc_odd k w : cconf := (StB,([],S0,pc_blks k ++ S1::S1::S0::w)).

Section Parity.
Variable tm : TM.
Hypothesis HA0 : tm StA S0 = Some (mkTrans S1 DR StC).
Hypothesis HA1 : tm StA S1 = Some (mkTrans S1 DL StD).
Hypothesis HB0 : tm StB S0 = Some (mkTrans S0 DR StC).
Hypothesis HB1 : tm StB S1 = Some (mkTrans S1 DR StA).
Hypothesis HC0 : tm StC S0 = Some (mkTrans S1 DL StD).
Hypothesis HC1 : tm StC S1 = Some (mkTrans S1 DR StB).
Hypothesis HD0 : tm StD S0 = Some (mkTrans S1 DL StB).
Hypothesis HD1 : tm StD S1 = Some (mkTrans S0 DL StD).
Local Ltac pc_compute :=
 cbn [csteps cstep ctape_move chd ctl t_next t_dir t_write];
 repeat (first [rewrite HA0|rewrite HA1|rewrite HB0|rewrite HB1|
                rewrite HC0|rewrite HC1|rewrite HD0|rewrite HD1];
         cbn [csteps cstep ctape_move chd ctl t_next t_dir t_write]);
 reflexivity.
Lemma pc_drain : forall m L R,
 csteps tm (m+1)
  (StD,(ctl (repeat S1 m ++ S0::L),chd (repeat S1 m ++ S0::L),R)) =
 Some (StB,(ctl L,chd L,S1::repeat S0 m ++ R)).
Proof.
 induction m as [|m IH];intros L R.
 - cbn [repeat app ctl chd Nat.add]. pc_compute.
 - replace (S m+1) with (1+(m+1)) by lia.
   cbn [repeat app ctl chd]. rewrite csteps_add.
   assert (H : csteps tm 1 (StD,(repeat S1 m ++ S0::L,S1,R)) =
    Some (StD,(ctl (repeat S1 m ++ S0::L),chd (repeat S1 m ++ S0::L),S0::R))) by pc_compute.
   rewrite H, IH. f_equal. f_equal. f_equal.
   now rewrite pc_repeat_tail.
Qed.
Lemma pc_drain_cons : forall m L R,
 csteps tm (S m+1) (StD,(repeat S1 m ++ S0::L,S1,R)) =
 Some (StB,(ctl L,chd L,S1::repeat S0 (S m) ++ R)).
Proof. intros m;apply (pc_drain (S m)). Qed.
Lemma pc_return : forall m L R,
 csteps tm (m+4) (StB,(repeat S1 m ++ S0::L,S1,S1::R)) =
 Some (StB,(ctl L,chd L,S1::repeat S0 (S m) ++ S1::R)).
Proof.
 intros m L R. replace (m+4) with (2+(S m+1)) by lia.
 rewrite csteps_add.
 assert (H : csteps tm 2 (StB,(repeat S1 m ++ S0::L,S1,S1::R)) =
   Some (StD,(repeat S1 m ++ S0::L,S1,S1::R))) by pc_compute.
 rewrite H. apply (pc_drain (S m)).
Qed.
Lemma pc_return_cons : forall m L R,
 csteps tm (S m+4) (StB,(S1::repeat S1 m ++ S0::L,S1,S1::R)) =
 Some (StB,(ctl L,chd L,S1::repeat S0 (S (S m)) ++ S1::R)).
Proof. intros m;apply (pc_return (S m)). Qed.
Lemma pc_runs : forall w,
 (forall L, csteps tm (pc_fc w) (StB,(L,S0,w)) =
  Some (StB,(ctl L,chd L,pc_f w))) /\
 (forall m L, csteps tm (m+pc_uc w)
  (StA,(repeat S1 m ++ S0::L,chd w,ctl w)) =
  Some (StB,(ctl L,chd L,S1::repeat S0 m ++ pc_u w))).
Proof.
 fix IH 1. intro w. split.
 - intro L. destruct w as [|b x].
   + cbn [pc_fc pc_f]. pc_compute.
   + destruct b.
     * cbn [pc_fc pc_f]. pc_compute.
     * destruct x as [|b x].
       -- cbn [pc_fc pc_f]. pc_compute.
       -- destruct b.
          ++ cbn [pc_fc pc_f].
             replace (6+pc_fc x) with (2+(pc_fc x+4)) by lia.
             rewrite csteps_add.
             assert (H : csteps tm 2 (StB,(L,S0,S1::S0::x)) =
               Some (StB,(S1::S0::L,S0,x))) by pc_compute.
             rewrite H,csteps_add,(proj1 (IH x)). cbn [ctl chd].
             destruct (pc_f_head x) as [r Hr]. rewrite Hr.
             apply (pc_return 0).
          ++ cbn [pc_fc pc_f].
             replace (5+pc_uc x) with (3+(2+pc_uc x)) by lia.
             rewrite csteps_add.
             assert (H : csteps tm 3 (StB,(L,S0,S1::S1::x)) =
               Some (StA,(S1::S1::S0::L,chd x,ctl x))) by pc_compute.
             rewrite H. apply (proj2 (IH x) 2).
 - intros m L. destruct w as [|b x].
   + cbn [pc_uc pc_u ctl chd].
     replace (m+4) with (2+(S m+1)) by lia.
     rewrite csteps_add.
     assert (H : csteps tm 2 (StA,(repeat S1 m ++ S0::L,S0,[])) =
       Some (StD,(repeat S1 m ++ S0::L,S1,[S1]))) by pc_compute.
     rewrite H,pc_drain_cons. cbn [repeat].
     repeat rewrite pc_repeat_tail. reflexivity.
   + destruct b.
     * destruct x as [|b x].
       -- cbn [pc_uc pc_u ctl chd].
          replace (m+4) with (2+(S m+1)) by lia.
          rewrite csteps_add.
          assert (H : csteps tm 2 (StA,(repeat S1 m ++ S0::L,S0,[])) =
            Some (StD,(repeat S1 m ++ S0::L,S1,[S1]))) by pc_compute.
          rewrite H,pc_drain_cons. cbn [repeat].
          repeat rewrite pc_repeat_tail. reflexivity.
       -- destruct b.
          ++ cbn [pc_uc pc_u ctl chd].
             replace (m+4) with (2+(S m+1)) by lia.
             rewrite csteps_add.
             assert (H : csteps tm 2 (StA,(repeat S1 m ++ S0::L,S0,S0::x)) =
               Some (StD,(repeat S1 m ++ S0::L,S1,S1::x))) by pc_compute.
             rewrite H,pc_drain_cons. cbn [repeat].
             repeat rewrite pc_repeat_tail. reflexivity.
          ++ destruct x as [|b x].
             ** cbn [pc_uc pc_u ctl chd].
                replace (m+10) with (5+(S m+4)) by lia.
                rewrite csteps_add.
                assert (H : csteps tm 5 (StA,(repeat S1 m ++ S0::L,S0,[S1])) =
                  Some (StB,(S1::repeat S1 m ++ S0::L,S1,[S1;S1]))) by pc_compute.
                rewrite H,pc_return_cons. cbn [repeat].
                repeat rewrite pc_repeat_tail. reflexivity.
             ** destruct b.
                --- cbn [pc_uc pc_u ctl chd].
                    replace (m+(7+pc_fc x)) with (2+(pc_fc x+(S m+4))) by lia.
                    rewrite csteps_add.
                    assert (H : csteps tm 2 (StA,(repeat S1 m ++ S0::L,S0,S1::S0::x)) =
                      Some (StB,(S1::S1::repeat S1 m ++ S0::L,S0,x))) by pc_compute.
                    rewrite H,csteps_add,(proj1 (IH x)). cbn [ctl chd].
                    destruct (pc_f_head x) as [r Hr]. rewrite Hr,pc_return_cons.
                    cbn [repeat]. repeat rewrite pc_repeat_tail. reflexivity.
                --- cbn [pc_uc pc_u ctl chd].
                    replace (m+(6+pc_uc x)) with (3+(S (S (S m))+pc_uc x)) by lia.
                    rewrite csteps_add.
                    assert (H : csteps tm 3 (StA,(repeat S1 m ++ S0::L,S0,S1::S1::x)) =
                      Some (StA,(S1::S1::S1::repeat S1 m ++ S0::L,chd x,ctl x))) by pc_compute.
                    rewrite H.
                    change (csteps tm (S (S (S m))+pc_uc x)
                      (StA,(repeat S1 (S (S (S m))) ++ S0::L,chd x,ctl x)) =
                      Some (StB,(ctl L,chd L,S1::repeat S0 m ++ S0::S0::S0::pc_u x))).
                    rewrite (proj2 (IH x) (S (S (S m)))). cbn [repeat].
                    repeat rewrite pc_repeat_tail. reflexivity.
     * cbn [pc_uc pc_u ctl chd].
       replace (m+2) with (1+(m+1)) by lia.
       rewrite csteps_add.
       assert (H : csteps tm 1 (StA,(repeat S1 m ++ S0::L,S1,x)) =
        Some (StD,(ctl (repeat S1 m ++ S0::L),chd (repeat S1 m ++ S0::L),S1::x))) by pc_compute.
       rewrite H,pc_drain. reflexivity.

Qed.
Lemma pc_f_run : forall w L,
 csteps tm (pc_fc w) (StB,(L,S0,w)) = Some (StB,(ctl L,chd L,pc_f w)).
Proof. intros w;exact (proj1 (pc_runs w)). Qed.
Lemma pc_prefix : forall k L w,
 csteps tm (2*k) (StB,(L,S0,pc_blks k ++ w)) =
 Some (StB,(pc_blks k ++ L,S0,w)).
Proof.
 induction k as [|k IH];intros L w.
 - reflexivity.
 - replace (2*S k) with (2+2*k) by lia.
   cbn [pc_blks app]. rewrite csteps_add.
   assert (H : csteps tm 2 (StB,(L,S0,S1::S0::pc_blks k ++ w)) =
    Some (StB,(S1::S0::L,S0,pc_blks k ++ w))) by pc_compute.
   rewrite H,IH,pc_blks_tail. reflexivity.
Qed.
Lemma pc_even_run : forall k w,
 csteps tm (6*k+3) (pc_even k w) = Some (pc_odd k w).
Proof.
 intros k w. pose proof (pc_f_run (pc_blks k ++ S0::S0::w) []) as H.
 rewrite pc_fc_blocks,pc_f_blocks in H. exact H.
Qed.
Lemma pc_odd_run : forall k w,
 csteps tm (6*k+5+pc_uc (S0::w)) (pc_odd k w) =
 Some (pc_even (S k) (pc_next w)).
Proof.
 intros k w. pose proof (pc_f_run (pc_blks k ++ S1::S1::S0::w) []) as H.
 rewrite pc_fc_blocks,pc_f_blocks in H. cbn [pc_fc pc_f] in H.
 rewrite pc_u_zero,pc_blks_tail in H.
 replace (6*k+5+pc_uc (S0::w)) with (6*k+(5+pc_uc (S0::w))) by lia.
 exact H.
Qed.
Lemma pc_lap : forall k w,
 csteps tm (12*k+8+pc_uc (S0::w)) (pc_even k w) =
 Some (pc_even (S k) (pc_next w)).
Proof.
 intros k w. replace (12*k+8+pc_uc (S0::w)) with
  ((6*k+3)+(6*k+5+pc_uc (S0::w))) by lia.
 rewrite csteps_add,pc_even_run. apply pc_odd_run.
Qed.
Lemma pc_fire : forall k w t,
 exists j c, csteps tm j (pc_even (S k) w) = Some c /\ cinstr c = t.
Proof.
 intros k w [q b]. destruct q,b.
 - eexists ((6*S k+3)+(2*S k+3)),_. split.
   + rewrite csteps_add,pc_even_run. unfold pc_odd.
     rewrite csteps_add,pc_prefix. pc_compute.
   + reflexivity.
 - eexists (2*S k+4),_. split.
   + unfold pc_even. rewrite csteps_add,pc_prefix.
     cbn [pc_blks app]. pc_compute.
   + reflexivity.
 - exists 0,(pc_even (S k) w). split;reflexivity.
 - eexists (2*S k+3),_. split.
   + unfold pc_even. rewrite csteps_add,pc_prefix.
     cbn [pc_blks app]. pc_compute.
   + reflexivity.
 - eexists (2*S k+1),_. split.
   + unfold pc_even. rewrite csteps_add,pc_prefix. pc_compute.
   + reflexivity.
 - eexists 1,_. split.
   + unfold pc_even. cbn [pc_blks app]. pc_compute.
   + reflexivity.
 - eexists (2*S k+2),_. split.
   + unfold pc_even. rewrite csteps_add,pc_prefix. pc_compute.
   + reflexivity.
 - eexists (2*S k+5),_. split.
   + unfold pc_even. rewrite csteps_add,pc_prefix.
     cbn [pc_blks app]. pc_compute.
   + reflexivity.
Qed.
Theorem pc_neverqhtr : forall w0,
 (exists t0, stepn tm t0 InitES = Some (lift (pc_even 2 w0))) ->
 NeverQuasiHaltsTr tm.
Proof.
 intros w0 Hb.
 apply (value_lap_neverqhtr tm (list Sym) pc_next
   (fun n w => pc_even (S (S n)) w) w0).
 - exact Hb.
 - intros n w. exists (12*S (S n)+8+pc_uc (S0::w)),
     (pc_even (S (S (S n))) (pc_next w)).
   split;[apply pc_lap|]. split;[reflexivity|lia].
 - intros n w t. apply pc_fire.
Qed.
End Parity.
