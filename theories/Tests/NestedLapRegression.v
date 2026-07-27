(** Regression test: re-derive the hand-authored IXP board's OVERFLOW branch
    through the generic [NestedLap.nested_overflow], instead of its own
    hand-written composition.  If this proves the same statement, the generic
    theorem really does capture what the 163 IXP boards do. *)
From Coq Require Import Arith Lia List PArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape MonoCounter ILCounter JpCounter
                                  IXPGadgets NestedLap.
From BBB4.Machines.Counters Require Import IXP_0RB0RB_0LC1RD_1RB1LC_0LA0RB.
Import ListNotations.

Notation tm  := tm_0RB0RB_0LC1RD_1RB1LC_0LA0RB.
Notation Cc  := Cc_0RB0RB_0LC1RD_1RB1LC_0LA0RB.
Notation Cin := Cin_0RB0RB_0LC1RD_1RB1LC_0LA0RB.

(** The inner interior lap, in [NestedLap]'s shape. *)
Lemma Hin_test : forall v i q0, cview v = (i, Some q0) ->
  exists n, 0 < n /\ csteps tm n (Cin v) = Some (Cin (Pos.succ v)).
Proof.
  intros v i q0 E.
  destruct (lap_inner_0RB0RB_0LC1RD_1RB1LC_0LA0RB v i q0 E)
    as (n & c' & H1 & H2 & H3).
  exists n. split; [exact H3 | rewrite H1, H2; reflexivity].
Qed.

(** The SAME statement the board proves by hand as [lap_ov_...], now via the
    generic composition. *)
Lemma lap_ov_via_nested : forall p j', cview p = (S j', None) ->
  exists n c', csteps tm n (Cc p) = Some c'
          /\ lift c' = lift (Cc (Pos.succ p)) /\ 0 < n.
Proof.
  intros p j' Ecv.
  destruct (cview_none_I p j' Ecv) as (HIp & HIs).
  pose proof (cview_none_shape p j' Ecv) as Hp.
  apply (nested_overflow tm Cc Cin Hin_test p (pow2 j')).
  - (* boot *)
    destruct (boot_ov_0RB0RB_0LC1RD_1RB1LC_0LA0RB j') as (m1 & c1 & Hb & Hc1 & Hm1).
    exists m1. split; [exact Hm1|].
    unfold Cc_0RB0RB_0LC1RD_1RB1LC_0LA0RB. rewrite HIp. rewrite Hb, Hc1.
    reflexivity.
  - (* inner lands at [fill (pow2 j')], which IS [p] -- exit from there *)
    destruct (exit_ov_0RB0RB_0LC1RD_1RB1LC_0LA0RB j') as (m3 & c3 & Hx & Hc3 & _).
    exists m3, c3. split.
    + rewrite <- Hp. unfold Cin_0RB0RB_0LC1RD_1RB1LC_0LA0RB. rewrite HIp. exact Hx.
    + subst c3. unfold Cc_0RB0RB_0LC1RD_1RB1LC_0LA0RB. rewrite HIs.
      rewrite <- app_assoc. cbn [app].
      change (rep [S1;S0] (S j') ++ S1 :: S1 :: S0 :: nil)
        with (rep [S1;S0] (S j') ++ [S1] ++ [S1] ++ [S0]).
      rewrite !app_assoc.
      rewrite lift_lblank_0RB0RB_0LC1RD_1RB1LC_0LA0RB.
      rewrite pair_rot.
      reflexivity.
Qed.

(* [Print Assumptions lap_ov_via_nested] = functional_extensionality_dep only. *)
