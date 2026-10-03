(** * Counters.TwoLevelTr: the two-level binary mirror counter (SCOPING_INSTR 7.4.LE11)

    LE10's "two-level binary mirror counters" share one abstract dynamics.
    At the junction the right side holds a binary counter [y] (LSB nearest,
    row-specific cells), the left side [xc u ++ 1 :: xc v]: a binary counter
    [u] (cells [00] / [10]), one SEPARATOR cell, and a digit string [v] read
    one cell out of step.  One macro step ([astep]) increments [y], then:

    - [u] has a 0 digit: [u] is incremented;
    - [u] is all 1s, [v = []]: [u] widens to [0^(|u|+1)];
    - [u] is all 1s, [v = 1 :: v1]: [u] and the separator move to the
      right ([y := 1^|u| 0 ++ y+1]), [v := v1];
    - [u] is all 1s, [v = 0 :: v1]: [u := 0^(|u|+1)], [v := v1];
    - [y] all 1s (and then [v = []]): the walk enters the left one cell out
      of step; the right resets to [0^(w+1)] ([u] odd) or [0^w] ([u]
      even) and [u] less its low digit becomes [v].

    [Inv] keeps the orbit in these cases: in an era ([v = []]) the left
    count [val u + 2^|u|] is at most [val y]; in a pass the right deficit is
    at least the left one.  [reach_good] finds, from any state, a step whose
    left walk passes a [10] digit or the separator onto a [0] cell, and
    [reach_good2] one whose [y] is odd.  The board [two_level_neverqhtr]
    takes the row's macro lemma (its cells) and fire witnesses from those
    two kinds of state.

    Axiom footprint: [functional_extensionality_dep], via [CTape.lift]. *)
From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Counters Require Import WTape NestCountTr LoopRunTr LoopMirrorTr.
From BBB4.Checkers Require Import WrapTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
Import ListNotations.

(** ** The abstract state and its step *)

Definition xc (u : list bool) : list Sym := bcells [S0; S0] [S1; S0] u.

Definition ast : Type := (list bool * list bool * list bool)%type.

Definition allt (l : list bool) : bool := forallb (fun b => b) l.

Definition astep (s : ast) : ast :=
  let '(u, v, y) := s in
  if allt y then
    match u with
    | [] => ([], [], repeat false (S (length y)))
    | true :: u1 => ([], u1 ++ [true], repeat false (S (length y)))
    | false :: u1 => ([false], u1 ++ [true], repeat false (length y))
    end
  else if allt u then
    match v with
    | [] => (repeat false (S (length u)), [], binc y)
    | true :: v1 => ([], v1, repeat true (length u) ++ false :: binc y)
    | false :: v1 => (repeat false (S (length u)), v1, binc y)
    end
  else (binc u, v, binc y).

(** ** List facts *)

Lemma allt_repeat : forall k, allt (repeat true k) = true.
Proof. induction k as [|k IH]; [reflexivity|]. exact IH. Qed.

Lemma allt_int : forall k r, allt (repeat true k ++ false :: r) = false.
Proof. induction k as [|k IH]; intros r; [reflexivity|]. apply IH. Qed.

Lemma allt_dec : forall l, (allt l = true /\ l = repeat true (length l)) \/
  (allt l = false /\ exists k r, l = repeat true k ++ false :: r).
Proof.
  intros l. destruct (ttdecomp l) as [(k & r & ->) | (k & ->)].
  - right. split; [apply allt_int | exists k, r; reflexivity].
  - left. split; [apply allt_repeat | rewrite repeat_length; reflexivity].
Qed.

Lemma xc_ff : forall k r, xc (repeat false k ++ r) = rep [S0; S0] k ++ xc r.
Proof. intros. apply bcells_ff. Qed.
Lemma xc_tt : forall k r, xc (repeat true k ++ r) = rep [S1; S0] k ++ xc r.
Proof. intros. apply bcells_tt. Qed.
Lemma xc_t : forall r, xc (true :: r) = S1 :: S0 :: xc r.
Proof. reflexivity. Qed.
Lemma xc_f : forall r, xc (false :: r) = S0 :: S0 :: xc r.
Proof. reflexivity. Qed.
Lemma xc_nil : xc [] = [].
Proof. reflexivity. Qed.
Lemma xc_all : forall k, xc (repeat true k) = rep [S1; S0] k.
Proof. intros. apply bcells_alltrue. Qed.
Lemma xc_none : forall k, xc (repeat false k) = rep [S0; S0] k.
Proof. intros. apply bcells_allfalse. Qed.
Lemma xc_app : forall a b, xc (a ++ b) = xc a ++ xc b.
Proof. intros. apply flat_map_app. Qed.

(** ** The invariant *)

Fixpoint val (l : list bool) : nat :=
  match l with [] => 0 | b :: r => (if b then 1 else 0) + 2 * val r end.

Lemma val_lt : forall l, val l < 2 ^ length l.
Proof. induction l as [|[|] l IH]; cbn [val length]; rewrite ?Nat.pow_succ_r', ?Nat.pow_0_r; lia. Qed.

Lemma val_binc : forall l, val (binc l) = S (val l).
Proof. induction l as [|[|] l IH]; cbn [binc val]; lia. Qed.

Lemma len_binc : forall l, allt l = false -> length (binc l) = length l.
Proof.
  induction l as [|[|] l IH]; intros H; [discriminate | | reflexivity].
  cbn [binc length]. rewrite IH; [reflexivity | exact H].
Qed.

Lemma binc_nonnil : forall l, binc l <> [].
Proof. intros [|[|] l]; discriminate. Qed.

Lemma val_app : forall a b, val (a ++ b) = val a + 2 ^ length a * val b.
Proof.
  induction a as [|x a IH]; intros b; cbn [val app length]; [rewrite Nat.pow_0_r; lia|].
  rewrite IH, Nat.pow_succ_r'. destruct x; lia.
Qed.

Lemma val_rt : forall k, val (repeat true k) + 1 = 2 ^ k.
Proof. induction k as [|k IH]; cbn [val repeat]; rewrite ?Nat.pow_succ_r', ?Nat.pow_0_r; lia. Qed.

Lemma val_rf : forall k, val (repeat false k) = 0.
Proof. induction k as [|k IH]; cbn [val repeat]; lia. Qed.

Lemma allt_full : forall l, allt l = true -> val l + 1 = 2 ^ length l.
Proof.
  intros l H. destruct (allt_dec l) as [[_ E] | [H' _]]; [| congruence].
  rewrite E, repeat_length. apply val_rt.
Qed.

Lemma allt_short : forall l, allt l = false -> val l + 2 <= 2 ^ length l.
Proof. intros l H. pose proof (val_lt (binc l)). rewrite val_binc, len_binc in H0 by exact H. lia. Qed.

Lemma pow_pos : forall n, 1 <= 2 ^ n.
Proof. intros n. pose proof (Nat.pow_nonzero 2 n ltac:(lia)). lia. Qed.

Definition Inv (s : ast) : Prop :=
  let '(u, v, y) := s in
  (v = [] /\ val u + 2 ^ length u <= val y /\ (u = [] -> allt y = false)) \/
  (v <> [] /\ last v false = true /\
   2 ^ (length u + S (length v)) + val y + 1 <= 2 ^ length y + val (u ++ true :: v)).

Lemma Inv_side : forall u v y, Inv (u, v, y) -> allt y = true -> v = [].
Proof.
  intros u v y [(Hv & _) | (_ & _ & H)] Hy; [exact Hv|].
  pose proof (allt_full y Hy). pose proof (val_lt (u ++ true :: v)).
  rewrite app_length in H1. cbn [length] in H1. lia.
Qed.

Lemma val_snoc_t : forall l, val (l ++ [true]) = val l + 2 ^ length l.
Proof. intros l. rewrite val_app. cbn [val]. lia. Qed.

Lemma val_rt_app : forall k l, val (repeat true k ++ l) + 1 = 2 ^ k + 2 ^ k * val l.
Proof. intros k l. rewrite val_app, repeat_length. pose proof (val_rt k). lia. Qed.

Lemma Inv_step : forall s, Inv s -> Inv (astep s).
Proof.
  intros [[u v] y] HI. pose proof (Inv_side u v y HI) as Hs.
  destruct (allt_dec y) as [[Hy Ey] | [Hy _]].
  - specialize (Hs Hy). subst v. cbn [astep]. rewrite Hy.
    destruct HI as [(_ & H1 & H2) | (H & _)]; [| congruence].
    pose proof (allt_full y Hy) as Hf.
    destruct u as [|[|] u1].
    + exfalso. specialize (H2 eq_refl). congruence.
    + right. split; [destruct u1; discriminate|]. split; [apply last_last|].
      cbn [app]. rewrite app_length, repeat_length, val_rf. cbn [val length] in *.
      rewrite val_snoc_t. rewrite Nat.pow_succ_r' in H1.
      replace (0 + S (length u1 + 1)) with (S (S (length u1))) by lia.
      rewrite !Nat.pow_succ_r'. lia.
    + right. split; [destruct u1; discriminate|]. split; [apply last_last|].
      cbn [app]. rewrite app_length, repeat_length, val_rf. cbn [val length] in *.
      rewrite val_snoc_t. rewrite Nat.pow_succ_r' in H1.
      assert (Hlt : S (length u1) < length y).
      { apply (Nat.pow_lt_mono_r_iff 2); [lia|]. rewrite Nat.pow_succ_r'. lia. }
      assert (Hle : 2 ^ S (S (length u1)) <= 2 ^ length y) by (apply Nat.pow_le_mono_r; lia).
      replace (1 + S (length u1 + 1)) with (S (S (S (length u1)))) by lia.
      rewrite !Nat.pow_succ_r' in *. lia.
  - cbn [astep]. rewrite Hy. pose proof (allt_short y Hy) as Hys.
    pose proof (len_binc y Hy) as Hlb. pose proof (val_binc y) as Hvb.
    destruct (allt_dec u) as [[Hu Eu] | [Hu _]]; rewrite Hu.
    + pose proof (allt_full u Hu) as Hf. destruct v as [|[|] v1].
      * left. split; [reflexivity|]. split; [|discriminate].
        rewrite val_rf, repeat_length, Nat.pow_succ_r'.
        destruct HI as [(_ & H1 & _) | (H & _)]; [lia | congruence].
      * destruct HI as [(H & _) | (_ & Hl & H)]; [discriminate|].
        pose proof (val_rt_app (length u) (false :: binc y)) as Hy'.
        cbn [val] in Hy'. pose proof (pow_pos (length u)).
        destruct v1 as [|b v1'].
        -- left. split; [reflexivity|]. split; [cbn [val length]; rewrite Nat.pow_0_r; rewrite Hvb in Hy'; nia|].
           intros _. apply allt_int.
        -- right. split; [discriminate|]. split; [exact Hl|].
           rewrite Eu in H at 2.
           pose proof (val_rt_app (length u) (true :: true :: b :: v1')) as Hx.
           cbn [app]. rewrite app_length, repeat_length. cbn [length val] in *.
           pose proof (val_lt (b :: v1')) as Hb. cbn [length val] in Hb.
           rewrite Hlb, Hvb in *. rewrite Nat.pow_add_r in *. rewrite !Nat.pow_succ_r' in *. rewrite Nat.pow_0_r in *.
           remember ((if b then 1 else 0) + 2 * val v1') as bb.
           remember (2 ^ length u) as K. remember (2 ^ length v1') as P. remember (2 ^ length y) as Y.
           remember (val (repeat true (length u) ++ true :: true :: b :: v1')) as V2.
           remember (val (repeat true (length u) ++ false :: binc y)) as V1.
           destruct (Nat.le_exists_sub (bb + 1) (2 * P) ltac:(lia)) as (E & HE & _).
           replace (K * (2 * (2 * (2 * P)))) with (4 * (K * (E + (bb + 1)))) in H
             by (rewrite <- HE; ring).
           assert (H2 : 4 * (K * E) + val y + 2 <= Y) by lia.
           assert (H3 : K * (2 * (4 * (K * E) + val y + 2)) <= K * (2 * Y))
             by (apply Nat.mul_le_mono_l; lia).
           assert (H4 : E <= K * (K * E)) by nia.
           replace (2 * (2 * P)) with (2 * (E + (bb + 1))) by lia.
           replace (2 ^ (length u + S (length y))) with (K * (2 * Y))
             by (subst K Y; rewrite Nat.pow_add_r, Nat.pow_succ_r'; reflexivity).
           lia.
      * destruct HI as [(H & _) | (_ & Hl & H)]; [discriminate|].
        destruct v1 as [|b v1']; [discriminate|].
        right. split; [discriminate|]. split; [exact Hl|].
        rewrite Eu in H at 2.
        pose proof (val_rt_app (length u) (true :: false :: b :: v1')) as Hx.
        rewrite val_app, repeat_length, val_rf. cbn [length val] in *.
        rewrite Nat.pow_add_r in *. rewrite !Nat.pow_succ_r' in *. rewrite Hlb, Hvb. nia.
    + destruct v as [|b v1].
      * left. split; [reflexivity|].
        destruct HI as [(_ & H1 & _) | (H & _)]; [| congruence].
        split; [rewrite val_binc, len_binc by exact Hu; lia|].
        intros H. exfalso. exact (binc_nonnil u H).
      * destruct HI as [(H & _) | (_ & Hl & H)]; [discriminate|].
        right. split; [discriminate|]. split; [exact Hl|].
        rewrite val_app, !val_binc, len_binc, Hlb by exact Hu. rewrite val_app in H. lia.
Qed.

Lemma iter_inv : forall n s, Inv s -> Inv (Nat.iter n astep s).
Proof.
  induction n as [|n IH]; intros s H; [exact H|].
  cbn [Nat.iter nat_rect]. apply Inv_step. apply IH, H.
Qed.

(** ** Steps in which every instruction fires *)

Definition good (s : ast) : Prop :=
  let '(u, v, y) := s in allt y = false /\
  ((exists j r, u = true :: repeat true j ++ false :: r) \/
   (allt u = true /\ (v = [] \/ exists v1, v = false :: v1))).

Lemma allt_f : forall l, allt (false :: l) = false.
Proof. reflexivity. Qed.

Lemma F_ones : forall v u y, Inv (u, v, y) -> allt u = true -> allt y = false ->
  exists n, good (Nat.iter n astep (u, v, y)).
Proof.
  induction v as [|[|] v1 IH]; intros u y HI Hu Hy.
  - exists 0. cbn. split; [exact Hy|]. right. split; [exact Hu | left; reflexivity].
  - destruct (IH [] (repeat true (length u) ++ false :: binc y)) as (n & Hn).
    + pose proof (Inv_step _ HI) as H. cbn [astep] in H. rewrite Hy, Hu in H. exact H.
    + reflexivity.
    + apply allt_int.
    + exists (S n). rewrite Nat.iter_succ_r. cbn [astep]. rewrite Hy, Hu. exact Hn.
  - exists 0. cbn. split; [exact Hy|]. right. split; [exact Hu | right; exists v1; reflexivity].
Qed.

Lemma Inv_len : forall u y, Inv (u, [], y) -> length u < length y.
Proof.
  intros u y [(_ & H & _) | (H & _)]; [|congruence].
  pose proof (val_lt y). apply (Nat.pow_lt_mono_r_iff 2); lia.
Qed.

Lemma reach_good : forall s, Inv s -> exists n, good (Nat.iter n astep s).
Proof.
  intros [[u v] y] HI.
  destruct (allt_dec y) as [[Hy Ey] | [Hy _]].
  - pose proof (Inv_side u v y HI Hy) as ->.
    pose proof (Inv_len u y HI) as Hl.
    destruct u as [|[|] u1].
    + exfalso. destruct HI as [(_ & _ & H) | (H & _)]; [|congruence].
      specialize (H eq_refl). congruence.
    + destruct (F_ones (u1 ++ [true]) [] (repeat false (S (length y)))) as (n & Hn).
      * pose proof (Inv_step _ HI) as H. cbn [astep] in H. rewrite Hy in H. exact H.
      * reflexivity.
      * reflexivity.
      * exists (S n). rewrite Nat.iter_succ_r. cbn [astep]. rewrite Hy. exact Hn.
    + cbn [length] in Hl. destruct (length y) as [|[|w]] eqn:Ew; [lia | lia |].
      destruct (F_ones (u1 ++ [true]) [true] (binc (repeat false (length y)))) as (n & Hn).
      * pose proof (Inv_step _ (Inv_step _ HI)) as H. cbn [astep] in H. rewrite Hy in H.
        rewrite Ew in H |- *. cbn [allt forallb repeat binc andb] in H |- *. exact H.
      * reflexivity.
      * rewrite Ew. reflexivity.
      * exists (S (S n)). rewrite !Nat.iter_succ_r. cbn [astep]. rewrite Hy.
        rewrite Ew in Hn |- *. exact Hn.
  - destruct (allt_dec u) as [[Hu _] | [Hu (j & r & Eu)]];
      [apply F_ones; assumption|].
    destruct j as [|j].
    + cbn in Eu. subst u.
      assert (HI1 := Inv_step _ HI). cbn [astep] in HI1. rewrite Hy in HI1. cbn [allt forallb andb binc] in HI1.
      destruct (allt_dec (binc y)) as [[Hy1 _] | [Hy1 _]].
      * pose proof (Inv_side _ _ _ HI1 Hy1) as ->.
        destruct (F_ones (r ++ [true]) [] (repeat false (S (length (binc y))))) as (n & Hn).
        -- pose proof (Inv_step _ HI1) as H. cbn [astep] in H. rewrite Hy1 in H. exact H.
        -- reflexivity.
        -- reflexivity.
        -- exists (S (S n)). rewrite !Nat.iter_succ_r. cbn [astep]. rewrite Hy. cbn [allt forallb andb binc].
           cbn [astep]. rewrite Hy1. exact Hn.
      * destruct (allt_dec r) as [[Hr _] | [Hr (i & r' & Er)]].
        -- destruct (F_ones v (true :: r) (binc y) HI1 Hr Hy1) as (n & Hn).
           exists (S n). rewrite Nat.iter_succ_r. cbn [astep]. rewrite Hy. exact Hn.
        -- exists 1. cbn [Nat.iter nat_rect astep]. rewrite Hy. cbn [allt forallb andb binc].
           split; [exact Hy1|]. left. exists i, r'. rewrite Er. reflexivity.
    + exists 0. cbn [Nat.iter nat_rect]. split; [exact Hy|]. left. exists j, r. exact Eu.
Qed.


(** an era start: the left is [1], the right has a 0 and a 1 digit *)
Lemma val_pos : forall l, existsb (fun b => b) l = true -> 1 <= val l.
Proof. induction l as [|[|] l IH]; cbn; intros H; [discriminate | lia | specialize (IH H); lia]. Qed.

Lemma Inv_start : forall y, allt y = false -> existsb (fun b => b) y = true -> Inv ([], [], y).
Proof.
  intros y H1 H2. left. split; [reflexivity|]. split; [|intros _; exact H1].
  pose proof (val_pos y H2). cbn [val length]. rewrite Nat.pow_0_r. lia.
Qed.

(** a step from which the right counter is odd *)
Definition good2 (s : ast) : Prop := let '(u, v, y) := s in hd false y = true.

Lemma reach_good2 : forall s, Inv s -> exists n, good2 (Nat.iter n astep s).
Proof.
  intros s HI. destruct (reach_good s HI) as (n & Hn).
  remember (Nat.iter n astep s) as s1 eqn:E. destruct s1 as [[u v] y].
  destruct Hn as (Hy & Hg).
  destruct y as [|[|] y']; [discriminate| exists n; rewrite <- E; reflexivity |].
  exists (S n). rewrite Nat.iter_succ. rewrite <- E. cbn [astep]. rewrite Hy.
  destruct Hg as [(j & r & ->) | (Hu & [-> | (v1 & ->)])].
  - change (true :: repeat true j ++ false :: r) with (repeat true (S j) ++ false :: r).
    rewrite allt_int. reflexivity.
  - rewrite Hu. reflexivity.
  - rewrite Hu. reflexivity.
Qed.

(** ** The board *)
Section Board.
Variable tm0 : TM.
Local Notation tm := (tm_wrap_trs tm0 []).
Variable enc : ast -> cconf.
Hypothesis Hmacro : forall u v y, (allt y = true -> v = []) ->
  Reach1 tm (enc (u, v, y)) (enc (astep (u, v, y))).
Hypothesis Hfire : forall t, (forall s, good s -> Fires tm (enc s) t) \/
                             (forall s, good2 s -> Fires tm (enc s) t).
Variable s0 : ast.
Hypothesis Hs0 : Inv s0.

Lemma macro_inv : forall s, Inv s -> Reach1 tm (enc s) (enc (astep s)).
Proof. intros [[u v] y] H. apply Hmacro. apply (Inv_side u v y H). Qed.

Lemma iter_reach : forall n s, Inv s -> Reach0 tm (enc s) (enc (Nat.iter n astep s)).
Proof.
  induction n as [|n IH]; intros s H; [apply reach0_refl|].
  rewrite Nat.iter_succ_r. eapply reach0_trans; [apply reach1_0, macro_inv, H|].
  apply IH, Inv_step, H.
Qed.

Definition Cf (i : nat) : cconf := enc (Nat.iter i astep s0).

Lemma lap : forall i, Reach1 tm (Cf i) (Cf (S i)).
Proof. intros i. unfold Cf. cbn [Nat.iter nat_rect]. apply macro_inv, iter_inv, Hs0. Qed.

Lemma fires : forall t, ~ In t [] -> forall i, Fires tm (Cf i) t.
Proof.
  intros t _ i. unfold Cf. pose proof (iter_inv i s0 Hs0) as HI.
  destruct (Hfire t) as [H | H].
  - destruct (reach_good _ HI) as (n & Hn).
    eapply fire_back; [apply (iter_reach n _ HI)|]. apply H, Hn.
  - destruct (reach_good2 _ HI) as (n & Hn).
    eapply fire_back; [apply (iter_reach n _ HI)|]. apply H, Hn.
Qed.

Theorem two_level_neverqhtr : forall b,
  stepn tm b InitES = Some (lift (enc s0)) -> NeverQuasiHaltsTr tm0.
Proof. intros b Hb. exact (boardS_neverqhtr _ [] Cf lap fires b Hb). Qed.
End Board.
