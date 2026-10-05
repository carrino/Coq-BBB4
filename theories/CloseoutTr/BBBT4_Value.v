(** * BBBT4_Value: the proof of [BBBT4_statement] -- BBB_tr(4) = 32,779,478.

    The CLAIM lives in BBBT4_Spec.v: [BBBT4_statement := BBBT4_is
    champion_score], stated census-free.  THIS file proves it.  Two
    inputs meet here:

    - the UPPER bound: [bbbt4_bound : forall tm, QHBoundTr B_tr tm]
      (CloseoutFinalTr.v: the 96-unit census walk [census_tr] chained
      with [closeout_tr_complete], every one of the 10,924 deferred rows
      boarded).  [B_tr] is the census's decimal literal; [B_tr_champion]
      equates it with the spec's [champion_score] through the binary
      numerals, never building the unary one.

    - the LOWER bound: [champion_attains_tr] (BBBT4_Champion.v): the
      state-level champion's last entry into [StD], at configuration
      index 32,779,477, is the last fire of instruction [(StD, S0)].

    Box only, like CloseoutFinalTr.v (it loads the census walk's .vo).
    `make proof-tr-all` builds the whole chain from a fresh clone and
    compiles this file last.

    [Print Assumptions BBBT4_value] below. *)
From Coq Require Import Arith Lia NArith.
From BBB4 Require Import BBB4_Statement BBBT4_Statement BBB4_Spec BBBT4_Spec
  BBBT4_Champion.
From BBB4.CensusTr Require Import TNF_QHTr RunTr.
From BBB4.Counters Require Import BlankTailTr.
From BBB4.CloseoutTr Require Import CloseoutFinalTr.

(** The census's bound is the spec's number: [B_tr] is [Nat.of_num_uint]
    of the decimal digits 32779478, and [of_uint_N] turns it into
    [N.to_nat] of the binary numeral, which is [champion_score]. *)
Lemma B_tr_champion : B_tr = champion_score.
Proof.
  unfold B_tr, champion_score. cbv [Nat.of_num_uint]. rewrite of_uint_N.
  apply f_equal. reflexivity.
Qed.

(** ** The value: BBB_tr(4) = 32,779,478

    ATTAINED by the champion, and MAXIMAL because any attained score
    [S s] is bounded by [bbbt4_bound]'s [QHBoundTr]. *)
Theorem BBBT4_value : BBBT4_statement.
Proof.
  split.
  - exists tm_champion. exact champion_attains_tr.
  - intros tm B' (t & s & Hq & Hs).
    rewrite <- Hs, <- B_tr_champion. exact (bbbt4_bound tm t s Hq).
Qed.

Print Assumptions BBBT4_value.
