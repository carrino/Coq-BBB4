(** * A total binary-word transducer with two carry ports.

    [mv_f] describes the counter half of a bouncer whose low end moves
    one cell per lap.  Its companion [mv_g] handles entry on a zero.
    Both are total on arbitrary finite binary words; no numeration or
    canonical-word invariant is required.  A parameterized macro for
    C1 also accepts implementations which take several machine steps. *)
From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement CTape.
Import ListNotations.

Fixpoint mv_f (w : list Sym) : list Sym :=
  match w with
  | [] => [S1;S0;S1]
  | S0 :: t => mv_g t
  | S1 :: t => S0 :: mv_f t
  end
with mv_g (w : list Sym) : list Sym :=
  match w with
  | [] => [S1;S0;S1]
  | S0 :: t => S1 :: S0 :: S1 :: t
  | S1 :: [] => [S1;S0;S0;S1;S0;S1]
  | S1 :: S1 :: t => S1 :: S0 :: S0 :: S1 :: t
  | S1 :: S0 :: [] => [S1;S0;S0;S1;S0;S1]
  | S1 :: S0 :: S0 :: t => S1 :: S0 :: S0 :: mv_g t
  | S1 :: S0 :: S1 :: t => S1 :: S0 :: S0 :: S0 :: mv_f t
  end.

Fixpoint mv_fcost (k : nat) (w : list Sym) {struct w} : nat :=
  match w with
  | [] => k + 4
  | S0 :: t => k + mv_gcost k t
  | S1 :: t => k + mv_fcost k t + 1
  end
with mv_gcost (k : nat) (w : list Sym) {struct w} : nat :=
  match w with
  | [] | S0 :: _ => 4
  | S1 :: [] | S1 :: S0 :: [] => 10
  | S1 :: S1 :: _ => 6
  | S1 :: S0 :: S0 :: t => 6 + mv_gcost k t
  | S1 :: S0 :: S1 :: t => 7 + mv_fcost k t
  end.

Section MovingTokens.
Variable tm : TM.
Variable kc : nat.
Hypothesis HA0 : tm StA S0 = Some (mkTrans S0 DR StB).
Hypothesis HA1 : tm StA S1 = Some (mkTrans S0 DR StA).
Hypothesis HB0 : tm StB S0 = Some (mkTrans S1 DL StC).
Hypothesis HB1 : tm StB S1 = Some (mkTrans S1 DR StA).
Hypothesis HC0 : tm StC S0 = Some (mkTrans S0 DL StD).
Hypothesis HD0 : tm StD S0 = Some (mkTrans S1 DR StA).
Hypothesis HD1 : tm StD S1 = Some (mkTrans S1 DL StB).
Hypothesis HC1 : forall L R,
  csteps tm kc (StC,(L,S1,S1::R)) =
  Some (StC,(ctl L,chd L,S1::S1::R)).

Local Ltac mv_compute :=
  cbn [csteps cstep ctape_move chd ctl t_next t_dir t_write];
  repeat (first [rewrite HA0 | rewrite HA1 | rewrite HB0 | rewrite HB1 |
                 rewrite HC0 | rewrite HD0 | rewrite HD1];
          cbn [csteps cstep ctape_move chd ctl t_next t_dir t_write]);
  reflexivity.

Lemma mv_f_return : forall L R,
  csteps tm 1 (StA,(L,S1,S1::R)) = Some (StA,(S0::L,S1,R)).
Proof. intros; mv_compute. Qed.

Lemma mv_g_base : forall L R,
  csteps tm 4 (StC,(S0::L,S0,S1::R)) =
  Some (StA,(S1::S0::S1::L,chd R,ctl R)).
Proof. intros; mv_compute. Qed.

Lemma mv_g_base_empty : forall R,
  csteps tm 4 (StC,([],S0,S1::R)) =
  Some (StA,([S1;S0;S1],chd R,ctl R)).
Proof. intros; mv_compute. Qed.

Lemma mv_g_carry : forall L R,
  csteps tm 3 (StC,(S1::S0::L,S0,S1::R)) =
  Some (StC,(ctl L,chd L,S1::S1::S0::S1::R)).
Proof. intros; mv_compute. Qed.

Lemma mv_g_carry_empty : forall R,
  csteps tm 3 (StC,([S1],S0,S1::R)) =
  Some (StC,([],S0,S1::S1::S0::S1::R)).
Proof. intros; mv_compute. Qed.

Lemma mv_g_return : forall L R,
  csteps tm 3 (StA,(L,S1,S0::S1::R)) =
  Some (StA,(S1::S0::S0::L,chd R,ctl R)).
Proof. intros; mv_compute. Qed.

Lemma mv_fg_return : forall L R,
  csteps tm 4 (StA,(L,S1,S1::S0::S1::R)) =
  Some (StA,(S1::S0::S0::S0::L,chd R,ctl R)).
Proof. intros; mv_compute. Qed.

(** Simultaneous structural induction.  The recursive carry consumes
    three cells; all return windows are constant and leave the far
    right tail opaque. *)
Lemma mv_runs : forall w,
  (forall R, csteps tm (mv_fcost kc w) (StC,(w,S1,S1::R)) =
     Some (StA,(mv_f w,S1,R))) /\
  (forall R, csteps tm (mv_gcost kc w) (StC,(w,S0,S1::R)) =
     Some (StA,(mv_g w,chd R,ctl R))).
Proof.
  fix IH 1. intro w. split.
  - intro R. destruct w as [|b t].
    + cbn [mv_fcost mv_f]. rewrite csteps_add, HC1.
      cbn [ctl chd]. apply mv_g_base_empty.
    + destruct b.
      * cbn [mv_fcost mv_f]. rewrite csteps_add, HC1.
        cbn [ctl chd]. apply (proj2 (IH t)).
      * cbn [mv_fcost mv_f].
        replace (kc + mv_fcost kc t + 1) with (kc + (mv_fcost kc t + 1)) by lia.
        rewrite csteps_add, HC1. cbn [ctl chd].
        rewrite csteps_add, (proj1 (IH t)). apply mv_f_return.
  - intro R. destruct w as [|b t].
    + apply mv_g_base_empty.
    + destruct b.
      * apply mv_g_base.
      * destruct t as [|b t].
        -- change (csteps tm (3+(4+3)) (StC,([S1],S0,S1::R)) =
             Some (StA,([S1;S0;S0;S1;S0;S1],chd R,ctl R))).
           rewrite csteps_add, mv_g_carry_empty, csteps_add, mv_g_base_empty.
           apply mv_g_return.
        -- destruct b.
           ++ destruct t as [|b t].
              ** change (csteps tm (3+(4+3)) (StC,([S1;S0],S0,S1::R)) =
                   Some (StA,([S1;S0;S0;S1;S0;S1],chd R,ctl R))).
                 rewrite csteps_add, mv_g_carry. cbn [ctl chd].
                 rewrite csteps_add, mv_g_base_empty. apply mv_g_return.
              ** destruct b.
                 --- cbn [mv_gcost mv_g].
                     replace (6 + mv_gcost kc t) with (3+(mv_gcost kc t+3)) by lia.
                     rewrite csteps_add, mv_g_carry. cbn [ctl chd].
                     rewrite csteps_add, (proj2 (IH t)). apply mv_g_return.
                 --- cbn [mv_gcost mv_g].
                     replace (7 + mv_fcost kc t) with (3+(mv_fcost kc t+4)) by lia.
                     rewrite csteps_add, mv_g_carry. cbn [ctl chd].
                     rewrite csteps_add, (proj1 (IH t)). apply mv_fg_return.
           ++ cbn [mv_gcost mv_g]. mv_compute.
Qed.

Lemma mv_f_run : forall w R,
  csteps tm (mv_fcost kc w) (StC,(w,S1,S1::R)) =
  Some (StA,(mv_f w,S1,R)).
Proof. intros w; exact (proj1 (mv_runs w)). Qed.

Lemma mv_g_run : forall w R,
  csteps tm (mv_gcost kc w) (StC,(w,S0,S1::R)) =
  Some (StA,(mv_g w,chd R,ctl R)).
Proof. intros w; exact (proj2 (mv_runs w)). Qed.

End MovingTokens.
