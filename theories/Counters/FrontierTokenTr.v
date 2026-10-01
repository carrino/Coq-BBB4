(** * A frontier counter with a lexicographic carry ranking.

    The binary-word transducers are [MovingTokenTr.mv_f]/[mv_g].
    A three-step implementation of B0 gives the same interior carry;
    the right frontier then starts the next counter pass directly.
    A pass without D0 strictly decreases (ones, adjacent pairs of ones),
    so the rare instruction remains live. *)
From Coq Require Import Arith Lia List Bool Wellfounded Lexicographic_Product Relations.Relation_Operators.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import MovingTokenTr.
Import ListNotations.

Fixpoint fr_fcost (w : list Sym) : nat :=
  match w with
  | [] => 5
  | S0 :: t => 1 + fr_gcost t
  | S1 :: t => 2 + fr_fcost t
  end
with fr_gcost (w : list Sym) : nat :=
  match w with
  | [] | S0 :: _ => 4
  | S1 :: [] | S1 :: S0 :: [] => 12
  | S1 :: S1 :: _ => 6
  | S1 :: S0 :: S0 :: t => 8 + fr_gcost t
  | S1 :: S0 :: S1 :: t => 9 + fr_fcost t
  end.

Fixpoint fr_fmark (w : list Sym) : bool :=
  match w with [] => true | S0::t => fr_gmark t | S1::t => fr_fmark t end
with fr_gmark (w : list Sym) : bool :=
  match w with
  | [] | S0::_ | S1::[] | S1::S0::[] => true
  | S1::S1::_ => false
  | S1::S0::S0::t => fr_gmark t
  | S1::S0::S1::t => fr_fmark t
  end.

Fixpoint fr_ones (w : list Sym) : nat :=
  match w with [] => 0 | S0::t => fr_ones t | S1::t => S (fr_ones t) end.
Fixpoint fr_pairs (w : list Sym) : nat :=
  match w with
  | [] => 0
  | b::t => (match b,t with S1,S1::_ => 1 | _,_ => 0 end) + fr_pairs t
  end.

Lemma fr_rank : forall w,
  (fr_fmark w = false -> fr_ones (mv_f w) <= fr_ones w) /\
  (fr_gmark w = false ->
    fr_ones (mv_g w) < fr_ones w \/
    (fr_ones (mv_g w) = fr_ones w /\ fr_pairs (mv_g w) < fr_pairs w)).
Proof.
  fix IH 1. intro w. split; intro E.
  - destruct w as [|b t]; [discriminate|]. destruct b.
    + cbn [fr_fmark] in E. destruct (proj2 (IH t) E) as [H|[H _]];
        cbn [mv_f fr_ones]; lia.
    + cbn [fr_fmark] in E. pose proof (proj1 (IH t) E).
      cbn [mv_f fr_ones]. lia.
  - destruct w as [|b t]; [discriminate|]. destruct b; [discriminate|].
    destruct t as [|b t]; [discriminate|]. destruct b.
    + destruct t as [|b t]; [discriminate|]. destruct b.
      * cbn [fr_gmark] in E. destruct (proj2 (IH t) E) as [H|[H P]].
        -- left. cbn [mv_g fr_ones]. lia.
        -- right. cbn [mv_g fr_ones fr_pairs]. split; lia.
      * cbn [fr_gmark] in E. pose proof (proj1 (IH t) E).
        left. cbn [mv_g fr_ones]. lia.
    + right. cbn [mv_g fr_ones fr_pairs]. split; [reflexivity|lia].
Qed.

Section Frontier.
Variable tm : TM.
Hypothesis HA0 : tm StA S0 = Some (mkTrans S0 DR StB).
Hypothesis HA1 : tm StA S1 = Some (mkTrans S0 DR StA).
Hypothesis HB0 : tm StB S0 = Some (mkTrans S1 DR StC).
Hypothesis HB1 : tm StB S1 = Some (mkTrans S1 DR StA).
Hypothesis HC0 : tm StC S0 = Some (mkTrans S0 DL StD).
Hypothesis HC1 : tm StC S1 = Some (mkTrans S1 DL StC).
Hypothesis HD0 : tm StD S0 = Some (mkTrans S1 DR StA).
Hypothesis HD1 : tm StD S1 = Some (mkTrans S1 DL StB).

Local Ltac fr_compute :=
  cbn [Nat.add Nat.mul csteps cstep ctape_move chd ctl t_next t_dir t_write];
  repeat (first [rewrite HA0 | rewrite HA1 | rewrite HB0 | rewrite HB1 |
                 rewrite HC0 | rewrite HC1 | rewrite HD0 | rewrite HD1];
          cbn [Nat.add Nat.mul csteps cstep ctape_move chd ctl t_next t_dir t_write]);
  reflexivity.

Lemma fr_f_enter : forall L R,
  csteps tm 1 (StC,(L,S1,R)) = Some (StC,(ctl L,chd L,S1::R)).
Proof. intros; fr_compute. Qed.
Lemma fr_f_return : forall L R,
  csteps tm 1 (StA,(L,S1,R)) = Some (StA,(S0::L,chd R,ctl R)).
Proof. intros; fr_compute. Qed.
Lemma fr_g_base : forall L R,
  csteps tm 4 (StC,(S0::L,S0,S1::R)) =
  Some (StA,(S1::S0::S1::L,chd R,ctl R)).
Proof. intros; fr_compute. Qed.
Lemma fr_g_base_empty : forall R,
  csteps tm 4 (StC,([],S0,S1::R)) =
  Some (StA,([S1;S0;S1],chd R,ctl R)).
Proof. intros; fr_compute. Qed.
Lemma fr_g_carry : forall L R,
  csteps tm 5 (StC,(S1::S0::L,S0,S1::R)) =
  Some (StC,(ctl L,chd L,S1::S1::S0::S1::R)).
Proof. intros; fr_compute. Qed.
Lemma fr_g_carry_empty : forall R,
  csteps tm 5 (StC,([S1],S0,S1::R)) =
  Some (StC,([],S0,S1::S1::S0::S1::R)).
Proof. intros; fr_compute. Qed.
Lemma fr_g_return : forall L R,
  csteps tm 3 (StA,(L,S1,S0::S1::R)) =
  Some (StA,(S1::S0::S0::L,chd R,ctl R)).
Proof. intros; fr_compute. Qed.
Lemma fr_fg_return : forall L R,
  csteps tm 4 (StA,(L,S1,S1::S0::S1::R)) =
  Some (StA,(S1::S0::S0::S0::L,chd R,ctl R)).
Proof. intros; fr_compute. Qed.

Lemma fr_runs : forall w,
  (forall R, csteps tm (fr_fcost w) (StC,(w,S1,R)) =
     Some (StA,(mv_f w,chd R,ctl R))) /\
  (forall R, csteps tm (fr_gcost w) (StC,(w,S0,S1::R)) =
     Some (StA,(mv_g w,chd R,ctl R))).
Proof.
  fix IH 1. intro w. split.
  - intro R. destruct w as [|b t].
    + change (fr_fcost []) with (1+4). rewrite csteps_add, fr_f_enter.
      cbn [ctl chd]. apply fr_g_base_empty.
    + destruct b.
      * change (fr_fcost (S0::t)) with (1+fr_gcost t).
        rewrite csteps_add, fr_f_enter. cbn [ctl chd mv_f]. apply (proj2 (IH t)).
      * change (fr_fcost (S1::t)) with (2+fr_fcost t).
        replace (2+fr_fcost t) with (1+(fr_fcost t+1)) by lia.
        rewrite csteps_add, fr_f_enter. cbn [ctl chd].
        rewrite csteps_add, (proj1 (IH t)). apply fr_f_return.
  - intro R. destruct w as [|b t].
    + apply fr_g_base_empty.
    + destruct b.
      * apply fr_g_base.
      * destruct t as [|b t].
        -- change (fr_gcost [S1]) with (5+(4+3)).
           rewrite csteps_add, fr_g_carry_empty, csteps_add, fr_g_base_empty.
           apply fr_g_return.
        -- destruct b.
           ++ destruct t as [|b t].
              ** change (fr_gcost [S1;S0]) with (5+(4+3)).
                 rewrite csteps_add, fr_g_carry. cbn [ctl chd].
                 rewrite csteps_add, fr_g_base_empty. apply fr_g_return.
              ** destruct b.
                 --- change (fr_gcost (S1::S0::S0::t)) with (8+fr_gcost t).
                     replace (8+fr_gcost t) with (5+(fr_gcost t+3)) by lia.
                     rewrite csteps_add, fr_g_carry. cbn [ctl chd].
                     rewrite csteps_add, (proj2 (IH t)). apply fr_g_return.
                 --- change (fr_gcost (S1::S0::S1::t)) with (9+fr_fcost t).
                     replace (9+fr_fcost t) with (5+(fr_fcost t+4)) by lia.
                     rewrite csteps_add, fr_g_carry. cbn [ctl chd].
                     rewrite csteps_add, (proj1 (IH t)). apply fr_fg_return.
           ++ cbn [fr_gcost mv_g]. fr_compute.
Qed.

Definition fr_hits (q : St) (s : Sym) (c : cconf) : Prop :=
  exists j L R, csteps tm j c = Some (q,(L,s,R)).

Lemma fr_hits_prefix : forall q s c d k,
  csteps tm k c = Some d -> fr_hits q s d -> fr_hits q s c.
Proof.
  intros q s c d k H (j & L & R & Hj). exists (k+j), L, R.
  rewrite csteps_add, H. exact Hj.
Qed.

Lemma fr_g_base_hit : forall L R,
  fr_hits StD S0 (StC,(S0::L,S0,S1::R)).
Proof. intros. exists 1, L, (S0::S1::R). fr_compute. Qed.
Lemma fr_g_empty_hit : forall R,
  fr_hits StD S0 (StC,([],S0,S1::R)).
Proof. intros. exists 1, [], (S0::S1::R). fr_compute. Qed.

Lemma fr_marks_sound : forall w,
  (forall R, fr_fmark w = true -> fr_hits StD S0 (StC,(w,S1,R))) /\
  (forall R, fr_gmark w = true -> fr_hits StD S0 (StC,(w,S0,S1::R))).
Proof.
  fix IH 1. intro w. split; intros R E.
  - eapply fr_hits_prefix; [apply fr_f_enter|].
    destruct w as [|b t]; cbn [ctl chd].
    + apply fr_g_empty_hit.
    + destruct b.
      * apply (proj2 (IH t)). exact E.
      * apply (proj1 (IH t)). exact E.
  - destruct w as [|b t].
    + apply fr_g_empty_hit.
    + destruct b.
      * apply fr_g_base_hit.
      * destruct t as [|b t].
        -- eapply fr_hits_prefix; [apply fr_g_carry_empty|apply fr_g_empty_hit].
        -- destruct b.
           ++ eapply fr_hits_prefix; [apply fr_g_carry|].
              destruct t as [|b t]; cbn [ctl chd].
              ** apply fr_g_empty_hit.
              ** destruct b.
                 --- apply (proj2 (IH t)). exact E.
                 --- apply (proj1 (IH t)). exact E.
           ++ discriminate.
Qed.

Lemma fr_g_b1 : forall w R, fr_hits StB S1 (StC,(w,S0,S1::R)).
Proof.
  fix IH 1. intros w R. destruct w as [|b t].
  - exists 3, [S0;S1], R. fr_compute.
  - destruct b.
    + exists 3, (S0::S1::t), R. fr_compute.
    + destruct t as [|b t].
      * eapply fr_hits_prefix; [apply fr_g_carry_empty|].
        exists 3, [S0;S1], (S1::S0::S1::R). fr_compute.
      * destruct b.
        -- eapply fr_hits_prefix; [apply fr_g_carry|].
           destruct t as [|b t]; cbn [ctl chd].
           ++ exists 3, [S0;S1], (S1::S0::S1::R). fr_compute.
           ++ destruct b.
              ** apply IH.
              ** eapply fr_hits_prefix; [apply (proj1 (fr_runs t))|].
                 exists 3, (S0::S0::S0::mv_f t), R. fr_compute.
        -- exists 2, t, (S1::S0::S1::R). fr_compute.
Qed.

Definition fr_anchor (w : list Sym) : cconf := (StC,(S1::S0::w,S1,[S0])).

Lemma fr_middle : forall w,
  csteps tm (2+fr_gcost w) (fr_anchor w) = Some (StA,(mv_g w,S1,[S0])).
Proof.
  intro w. rewrite csteps_add. unfold fr_anchor.
  assert (E : csteps tm 2 (StC,(S1::S0::w,S1,[S0])) =
    Some (StC,(w,S0,[S1;S1;S0]))) by fr_compute.
  rewrite E. apply (proj2 (fr_runs w)).
Qed.

Lemma fr_frontier : forall L,
  csteps tm 6 (StA,(L,S1,[S0])) = Some (StC,(S1::S0::L,S1,[S0])).
Proof. intros; fr_compute. Qed.

Lemma fr_lap : forall w,
  csteps tm (fr_gcost w+8) (fr_anchor w) = Some (fr_anchor (mv_g w)).
Proof.
  intro w. replace (fr_gcost w+8) with ((2+fr_gcost w)+6) by lia.
  rewrite csteps_add, fr_middle. apply fr_frontier.
Qed.

Lemma fr_d0 : forall w, fr_hits StD S0 (fr_anchor w).
Proof.
  apply (well_founded_induction
    (wf_inverse_image (list Sym) (nat*nat)
      (slexprod nat nat lt lt) (fun w => (fr_ones w,fr_pairs w))
      (wf_slexprod nat nat lt lt lt_wf lt_wf))).
  intros w IH. destruct (fr_gmark w) eqn:E.
  - eapply fr_hits_prefix with (k:=2).
    + unfold fr_anchor. fr_compute.
    + apply (proj2 (fr_marks_sound w)). exact E.
  - eapply fr_hits_prefix; [apply fr_lap|]. apply IH.
    change (slexprod nat nat lt lt (fr_ones (mv_g w),fr_pairs (mv_g w))
      (fr_ones w,fr_pairs w)).
    destruct (proj2 (fr_rank w) E) as [H|[H P]].
    + apply left_slex. exact H.
    + rewrite H. apply right_slex. exact P.
Qed.

Lemma fr_all_hits : forall w q s, fr_hits q s (fr_anchor w).
Proof.
  intros w q s. destruct q,s.
  - eapply fr_hits_prefix; [apply fr_middle|]. eexists 1. eexists. eexists. fr_compute.
  - exists (2+fr_gcost w), (mv_g w), [S0]. apply fr_middle.
  - eapply fr_hits_prefix; [apply fr_middle|]. eexists 2. eexists. eexists. fr_compute.
  - eapply fr_hits_prefix with (k:=2).
    + unfold fr_anchor. fr_compute.
    + apply fr_g_b1.
  - eapply fr_hits_prefix; [apply fr_middle|]. eexists 3. eexists. eexists. fr_compute.
  - exists 0, (S1::S0::w), [S0]. reflexivity.
  - apply fr_d0.
  - eapply fr_hits_prefix; [apply fr_middle|]. eexists 4. eexists. eexists. fr_compute.
Qed.

End Frontier.
