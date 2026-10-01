(** Transition-level closeout batch AST_04: a token transducer beside a
    periodic bouncer.  Each lap visits every instruction and advances an
    arbitrary token word; no positional value or canonical-word invariant
    is needed.  Collected by tools/closeouttr/gen_closeout_tr.py. *)
From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Census Require Import Deferred_Defs.
From BBB4.CloseoutTr Require Import CloseoutKitTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
From BBB4.Counters Require Import WTape ValueLapTr MutualTokenTr TokenSweepTr.
Import ListNotations.

(* spec 0RB0RA_1LC1RA_0LD0LC_1LA1LB *)
Definition r_AST_04_0000 : list (option Trans) :=
  [t0RB;t0RA;t1LC;t1RA;t0LD;t0LC;t1LA;t1LB].

Local Definition tm := row_to_tm r_AST_04_0000.
Local Definition anchor (n : nat) (w : list mt_digit) : cconf :=
  (StC, (mt_encode w, S1, rep [S1;S1;S0] (2*n+1) ++ [S1])).
Local Definition middle (n : nat) (w : list mt_digit) : cconf :=
  (StA, (mt_encode (mt_succ w), S1, rep [S1;S0;S1] (2*n+2))).

Local Lemma token_phase : forall w R,
  csteps tm (12+6*mt_depth w) (StC,(mt_encode w,S1,R)) =
  Some (StB,(mt_encode (mt_succ w),S1,R)).
Proof. apply (mt_token_phase tm StA StB StC StD); reflexivity. Qed.

Local Lemma sweep_finish : forall n X,
  csteps tm (12*n+12)
    (StB,(X,S1,rep [S1;S1;S0] (2*n+1) ++ [S1])) =
  Some (StA,(X,S1,rep [S1;S0;S1] (2*n+2))).
Proof. apply token_sweep_finish; reflexivity. Qed.

Local Lemma sweeps : forall n Y,
  csteps tm (24*n+38) (StA,(S0::Y,S1,rep [S1;S0;S1] (2*n+2))) =
  Some (StC,(S0::Y,S1,rep [S1;S1;S0] (2*n+3) ++ [S1])).
Proof. apply token_sweeps; reflexivity. Qed.

Local Lemma first_phase : forall n w,
  csteps tm (12*n+24+6*mt_depth w) (anchor n w) = Some (middle n w).
Proof.
  intros n w. unfold anchor, middle.
  replace (12*n+24+6*mt_depth w) with ((12+6*mt_depth w)+(12*n+12)) by lia.
  rewrite csteps_add, token_phase. apply sweep_finish.
Qed.

Local Lemma lap : forall n w,
  csteps tm (36*n+62+6*mt_depth w) (anchor n w) =
  Some (anchor (S n) (mt_succ w)).
Proof.
  intros n w.
  replace (36*n+62+6*mt_depth w) with
    ((12*n+24+6*mt_depth w)+(24*n+38)) by lia.
  rewrite csteps_add, first_phase. unfold middle, anchor.
  destruct (mt_succ_head w) as (Y & HY). rewrite HY, sweeps.
  replace (2*S n+1) with (2*n+3) by lia. reflexivity.
Qed.

Local Lemma fire : forall n w t,
  exists k c, csteps tm k (anchor n w) = Some c /\ cinstr c = t.
Proof.
  intros n w t.
  destruct (instr_eqb t (StC,S1)) eqn:E.
  - apply instr_eqb_spec in E. subst t.
    exists 0, (anchor n w). split; reflexivity.
  - assert (Hne : t <> (StC,S1)).
    { intro H; subst t. discriminate E. }
    assert (Hfire : forall k L t, t <> (StC,S1) ->
      exists j c, csteps tm j (StA,(L,S1,rep [S1;S0;S1] (S k))) =
      Some c /\ cinstr c = t).
    { apply token_sweep_fire; reflexivity. }
    destruct (Hfire (2*n+1) (mt_encode (mt_succ w)) t Hne)
      as (j & c & Hj & Ht).
    exists ((12*n+24+6*mt_depth w)+j), c. split; [|exact Ht].
    rewrite csteps_add, first_phase. unfold middle.
    replace (2*n+2) with (S (2*n+1)) by lia. exact Hj.
Qed.

Lemma cv_AST_04_0000 : coversTr (row_to_tm r_AST_04_0000).
Proof.
  apply coversTr_nqh.
  apply (value_lap_neverqhtr tm (list mt_digit) mt_succ anchor []).
  - exists 13.
    assert (H : csteps tm 13 c0 = Some (StC,([S0],S1,[S1;S1;S0;S1])))
      by reflexivity.
    rewrite <- lift_c0, (csteps_lift _ _ _ _ H).
    f_equal. apply ceqb_lift. reflexivity.
  - intros n w. exists (36*n+62+6*mt_depth w), (anchor (S n) (mt_succ w)).
    split; [apply lap|]. split; [reflexivity|lia].
  - exact fire.
Qed.

Definition cbtrows_AST_04 : list (list (option Trans)) := [r_AST_04_0000].

Lemma cbt_AST_04_covers : Forall coversTr (map row_to_tm cbtrows_AST_04).
Proof. exact (Forall_cons _ cv_AST_04_0000 (Forall_nil _)). Qed.
