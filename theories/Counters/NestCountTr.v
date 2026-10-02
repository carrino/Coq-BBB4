(** * Counters.NestCountTr: counters whose arms run a whole INNER COUNT
    (SCOPING_INSTR 7.4.LE8).

    LE4-LE6 left a residue of binary counters whose carry or refill costs
    [2^k] or [3^k] for a carry over [k] digits ("carry cost doubles
    (nested)", "the fill counts"): to carry over [k] ones the machine
    shifts its frame and counts a second binary counter of [k - 1] digits
    from zero to all ones (once or twice), then shifts back.  No single
    segment program states such an arm, but the arm needs no cost formula:
    every lap obligation asks for [exists m].  So an arm is a COMPOSITION of
    reachability facts on concrete configurations, and an inner count is a
    lemma by induction on its width:

      carry  :  forall k Y, P O^k Z Y  ->+  P Z^k O Y
      count  :  forall k Y, P Z^k Y    ->*  P O^k Y          ([count_from_carry])

    ([count (k+1)] is [count k] on [Z Y], the carry, [count k] on [O Y]).
    The inner carry is in turn an ordinary arm family, or (a counter whose
    carry counts ITSELF one level down) a composition proved by strong
    induction on the width.

    This file holds the generic pieces:

    - [Reach0] / [Reach1]: reachability on lifted configurations (zero or
      more / one or more steps) and their composition;
    - [armfam_r] / [armfam_l]: a [LadderNest] arm family (threshold, stride,
      one repeated word on the counter side, an opaque tail beyond it) as a
      [Reach1] fact for EVERY count and tail; [fire_of_nfire_r] / [_l] the
      same for a fire witness, and [fire_back] pulls a fire back along a
      [Reach0];
    - [count_from_carry];
    - [BoardBinTr]: a binary increment counter over two digit words, LSB at
      the head, whose interior and top arms are ANY [Reach1] facts (so they
      may run inner counts), live because every instruction fires from every
      anchor with enough low ones and such anchors recur; never-QH and QH
      closers as in [LadderCheckZeckDTr].

    Nothing landed is modified.  Axiom footprint: [functional_extensionality_dep],
    via [CTape.lift]. *)
From Coq Require Import Arith Lia Bool List PArith FunctionalExtensionality.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape ClosureTr.
From BBB4.Counters Require Import WTape LapCertGlueLift.
From BBB4.Checkers Require Import WrapTr LapDecider LadderKernel LadderFam LadderCheck LadderCheckTr LadderNest LadderCheckNestTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
From BBB4.Counters Require Import LapGlueTr.
From BBB4.CensusTr Require Import TNF_QHTr QHConveyorTr.
Import ListNotations.

(** ** 1. Reachability on lifted configurations *)

Section Reach.
Variable tm : TM.

Definition Reach0 (c c' : cconf) : Prop :=
  exists m, stepn tm m (lift c) = Some (lift c').

Definition Reach1 (c c' : cconf) : Prop :=
  exists m, 0 < m /\ stepn tm m (lift c) = Some (lift c').

Lemma reach0_refl : forall c, Reach0 c c.
Proof. intros c. exists 0. reflexivity. Qed.

Lemma reach0_lift : forall c c', lift c = lift c' -> Reach0 c c'.
Proof. intros c c' H. exists 0. cbn. rewrite H. reflexivity. Qed.

Lemma reach0_trans : forall a b c, Reach0 a b -> Reach0 b c -> Reach0 a c.
Proof.
  intros a b c (m1 & H1) (m2 & H2). exists (m1 + m2).
  rewrite stepn_add, H1. exact H2.
Qed.

Lemma reach1_0 : forall a b, Reach1 a b -> Reach0 a b.
Proof. intros a b (m & _ & H). exists m. exact H. Qed.

Lemma reach10 : forall a b c, Reach1 a b -> Reach0 b c -> Reach1 a c.
Proof.
  intros a b c (m1 & Hm & H1) (m2 & H2). exists (m1 + m2). split; [lia|].
  rewrite stepn_add, H1. exact H2.
Qed.

Lemma reach01 : forall a b c, Reach0 a b -> Reach1 b c -> Reach1 a c.
Proof.
  intros a b c (m1 & H1) (m2 & Hm & H2). exists (m1 + m2). split; [lia|].
  rewrite stepn_add, H1. exact H2.
Qed.

Lemma reach1_lift_l : forall a a' b, lift a = lift a' -> Reach1 a' b -> Reach1 a b.
Proof. intros a a' b H (m & Hm & H1). exists m. rewrite H. split; assumption. Qed.

Lemma reach1_lift_r : forall a b b', lift b = lift b' -> Reach1 a b' -> Reach1 a b.
Proof. intros a b b' H (m & Hm & H1). exists m. rewrite H. split; assumption. Qed.

Lemma reach1_csteps : forall a b, Reach1 a b ->
  exists m c', 0 < m /\ csteps tm m a = Some c' /\ lift c' = lift b.
Proof.
  intros a b (m & Hm & H).
  destruct (stepn_csteps_at tm m a (lift b) H) as (c' & Hc & Hl).
  exists m, c'. split; [exact Hm | split; assumption].
Qed.

Definition Fires (c : cconf) (t : Instr) : Prop :=
  exists k c', csteps tm k c = Some c' /\ cinstr c' = t.

Lemma fire_back : forall a b t, Reach0 a b -> Fires b t -> Fires a t.
Proof.
  intros a b t (m & Hm) (k & c' & Hk & Ht).
  assert (Hs : stepn tm (m + k) (lift a) = Some (lift c')).
  { rewrite stepn_add, Hm. apply csteps_lift. exact Hk. }
  destruct (stepn_csteps_at tm (m + k) a (lift c') Hs) as (c'' & Hc'' & Hl).
  exists (m + k), c''. split; [exact Hc''|].
  rewrite <- cinstr_lift, Hl, cinstr_lift. exact Ht.
Qed.

Lemma fire_lift : forall a b t, lift a = lift b -> Fires b t -> Fires a t.
Proof. intros a b t H. apply fire_back, reach0_lift, H. Qed.

(** ** 2. Arm families as [Reach1] facts for every count and tail *)

Lemma reachL_reach1 : forall el er c c' XL XR j,
  ReachL tm el er c c' -> (el = true -> XL = []) -> (er = true -> XR = []) ->
  Reach1 (cden XL XR j c) (cden XL XR j c').
Proof.
  intros el er c c' XL XR j H HL HR.
  destruct (H XL XR j HL HR) as (m & c'' & Hm & Hc & Hl).
  exists m. split; [exact Hm|]. rewrite <- Hl. apply csteps_lift. exact Hc.
Qed.

Lemma sden_blk_rep : forall P w r s W X j,
  sden X j (blk (P ++ rep w r) w s W) = P ++ rep w (r + s * j) ++ W ++ X.
Proof.
  intros. rewrite blk_den, rep_add, <- !app_assoc. reflexivity.
Qed.

(** the counter on the RIGHT of the head *)
Lemma armfam_r : forall el er N0 st (AR : nat -> LRule)
    q1 L1 h1 P1 w1 W1 q2 L2 h2 P2 w2 W2,
  0 < st ->
  (forall r, r < N0 + st -> ReachL tm el er (lr_lhs (AR r)) (lr_rhs (AR r))) ->
  (forall r, r < N0 + st ->
     lr_lhs (AR r) = mkC q1 (sflat L1) h1 (blk (P1 ++ rep w1 r) w1 (astride N0 st r) W1)) ->
  (forall r, r < N0 + st ->
     lr_rhs (AR r) = mkC q2 (sflat L2) h2 (blk (P2 ++ rep w2 r) w2 (astride N0 st r) W2)) ->
  forall k X, (er = true -> X = []) ->
  Reach1 (q1, (L1, h1, P1 ++ rep w1 k ++ W1 ++ X))
         (q2, (L2, h2, P2 ++ rep w2 k ++ W2 ++ X)).
Proof.
  intros el er N0 st AR q1 L1 h1 P1 w1 W1 q2 L2 h2 P2 w2 W2 Hst HS HL HR k X HX.
  set (r := aoff N0 st k).
  assert (Hr : r < N0 + st) by (apply arm_index_lt; exact Hst).
  assert (Hk : r + astride N0 st r * acnt N0 st k = k) by (apply arm_index; exact Hst).
  pose proof (reachL_reach1 el er _ _ [] X (acnt N0 st k) (HS r Hr) (fun _ => eq_refl) HX) as H.
  rewrite (HL r Hr), (HR r Hr) in H. unfold cden in H; cbn [c_st c_l c_h c_r] in H.
  rewrite !sden_flat, !sden_blk_rep, !app_nil_r, Hk in H. exact H.
Qed.

(** the counter on the LEFT of the head *)
Lemma armfam_l : forall el er N0 st (AR : nat -> LRule)
    q1 R1 h1 P1 w1 W1 q2 R2 h2 P2 w2 W2,
  0 < st ->
  (forall r, r < N0 + st -> ReachL tm el er (lr_lhs (AR r)) (lr_rhs (AR r))) ->
  (forall r, r < N0 + st ->
     lr_lhs (AR r) = mkC q1 (blk (P1 ++ rep w1 r) w1 (astride N0 st r) W1) h1 (sflat R1)) ->
  (forall r, r < N0 + st ->
     lr_rhs (AR r) = mkC q2 (blk (P2 ++ rep w2 r) w2 (astride N0 st r) W2) h2 (sflat R2)) ->
  forall k X, (el = true -> X = []) ->
  Reach1 (q1, (P1 ++ rep w1 k ++ W1 ++ X, h1, R1))
         (q2, (P2 ++ rep w2 k ++ W2 ++ X, h2, R2)).
Proof.
  intros el er N0 st AR q1 R1 h1 P1 w1 W1 q2 R2 h2 P2 w2 W2 Hst HS HL HR k X HX.
  set (r := aoff N0 st k).
  assert (Hr : r < N0 + st) by (apply arm_index_lt; exact Hst).
  assert (Hk : r + astride N0 st r * acnt N0 st k = k) by (apply arm_index; exact Hst).
  pose proof (reachL_reach1 el er _ _ X [] (acnt N0 st k) (HS r Hr) HX (fun _ => eq_refl)) as H.
  rewrite (HL r Hr), (HR r Hr) in H. unfold cden in H; cbn [c_st c_l c_h c_r] in H.
  rewrite !sden_flat, !sden_blk_rep, !app_nil_r, Hk in H. exact H.
Qed.

(** one arm with no repeated word *)
Lemma arm1_r : forall el er A q1 L1 h1 R1 q2 L2 h2 R2,
  ReachL tm el er (lr_lhs A) (lr_rhs A) ->
  lr_lhs A = mkC q1 (sflat L1) h1 (sflat R1) ->
  lr_rhs A = mkC q2 (sflat L2) h2 (sflat R2) ->
  forall X, (er = true -> X = []) ->
  Reach1 (q1, (L1, h1, R1 ++ X)) (q2, (L2, h2, R2 ++ X)).
Proof.
  intros el er A q1 L1 h1 R1 q2 L2 h2 R2 HS HL HR X HX.
  pose proof (reachL_reach1 el er _ _ [] X 0 HS (fun _ => eq_refl) HX) as H.
  rewrite HL, HR in H. unfold cden in H; cbn [c_st c_l c_h c_r] in H.
  rewrite !sden_flat, !app_nil_r in H. exact H.
Qed.

Lemma arm1_l : forall el er A q1 L1 h1 R1 q2 L2 h2 R2,
  ReachL tm el er (lr_lhs A) (lr_rhs A) ->
  lr_lhs A = mkC q1 (sflat L1) h1 (sflat R1) ->
  lr_rhs A = mkC q2 (sflat L2) h2 (sflat R2) ->
  forall X, (el = true -> X = []) ->
  Reach1 (q1, (L1 ++ X, h1, R1)) (q2, (L2 ++ X, h2, R2)).
Proof.
  intros el er A q1 L1 h1 R1 q2 L2 h2 R2 HS HL HR X HX.
  pose proof (reachL_reach1 el er _ _ X [] 0 HS HX (fun _ => eq_refl)) as H.
  rewrite HL, HR in H. unfold cden in H; cbn [c_st c_l c_h c_r] in H.
  rewrite !sden_flat, !app_nil_r in H. exact H.
Qed.

(** fire witnesses read from a [LadderNest] program, for every count and tail *)
Lemma fire_of_nfire_r : forall el er rs N0 st (sg : nat -> list nseg) (vl : nat -> list lstep)
    (lhs : nat -> sconf) q1 L1 h1 P1 w1 W1 t,
  0 < st ->
  Forall (RuleSound tm false false) rs ->
  (forall r, r < N0 + st -> nfire tm el er rs (sg r) (vl r) (lhs r) = Some t) ->
  (forall r, r < N0 + st ->
     lhs r = mkC q1 (sflat L1) h1 (blk (P1 ++ rep w1 r) w1 (astride N0 st r) W1)) ->
  forall k X, (er = true -> X = []) ->
  Fires (q1, (L1, h1, P1 ++ rep w1 k ++ W1 ++ X)) t.
Proof.
  intros el er rs N0 st sg vl lhs q1 L1 h1 P1 w1 W1 t Hst Hrs HF HL k X HX.
  set (r := aoff N0 st k).
  assert (Hr : r < N0 + st) by (apply arm_index_lt; exact Hst).
  assert (Hk : r + astride N0 st r * acnt N0 st k = k) by (apply arm_index; exact Hst).
  destruct (nfire_sound tm el er rs (sg r) (vl r) (lhs r) t Hrs (HF r Hr)
              [] X (acnt N0 st k) (fun _ => eq_refl) HX) as (m & c' & Hc & Ht).
  rewrite (HL r Hr) in Hc. unfold cden in Hc; cbn [c_st c_l c_h c_r] in Hc.
  rewrite !sden_flat, !sden_blk_rep, !app_nil_r, Hk in Hc.
  exists m, c'. split; assumption.
Qed.

Lemma fire_of_nfire_l : forall el er rs N0 st (sg : nat -> list nseg) (vl : nat -> list lstep)
    (lhs : nat -> sconf) q1 R1 h1 P1 w1 W1 t,
  0 < st ->
  Forall (RuleSound tm false false) rs ->
  (forall r, r < N0 + st -> nfire tm el er rs (sg r) (vl r) (lhs r) = Some t) ->
  (forall r, r < N0 + st ->
     lhs r = mkC q1 (blk (P1 ++ rep w1 r) w1 (astride N0 st r) W1) h1 (sflat R1)) ->
  forall k X, (el = true -> X = []) ->
  Fires (q1, (P1 ++ rep w1 k ++ W1 ++ X, h1, R1)) t.
Proof.
  intros el er rs N0 st sg vl lhs q1 R1 h1 P1 w1 W1 t Hst Hrs HF HL k X HX.
  set (r := aoff N0 st k).
  assert (Hr : r < N0 + st) by (apply arm_index_lt; exact Hst).
  assert (Hk : r + astride N0 st r * acnt N0 st k = k) by (apply arm_index; exact Hst).
  destruct (nfire_sound tm el er rs (sg r) (vl r) (lhs r) t Hrs (HF r Hr)
              X [] (acnt N0 st k) HX (fun _ => eq_refl)) as (m & c' & Hc & Ht).
  rewrite (HL r Hr) in Hc. unfold cden in Hc; cbn [c_st c_l c_h c_r] in Hc.
  rewrite !sden_flat, !sden_blk_rep, !app_nil_r, Hk in Hc.
  exists m, c'. split; assumption.
Qed.

(** ** 3. An inner count from its carry *)

Section Count.
Variable mk : list Sym -> cconf.
Variables Z O : list Sym.
Hypothesis Hcar : forall k Y, Reach1 (mk (rep O k ++ Z ++ Y)) (mk (rep Z k ++ O ++ Y)).

Lemma rep_S_r : forall (u : list Sym) k, rep u (S k) = rep u k ++ u.
Proof. intros u k. replace (S k) with (k + 1) by lia. rewrite rep_add. cbn. rewrite app_nil_r. reflexivity. Qed.

Lemma count_from_carry : forall k Y, Reach0 (mk (rep Z k ++ Y)) (mk (rep O k ++ Y)).
Proof.
  induction k as [|k IH]; intros Y; [apply reach0_refl|].
  rewrite !rep_S_r, <- !app_assoc.
  apply (reach0_trans _ (mk (rep O k ++ Z ++ Y))); [exact (IH (Z ++ Y))|].
  apply (reach0_trans _ (mk (rep Z k ++ O ++ Y))); [apply reach1_0, Hcar|].
  exact (IH (O ++ Y)).
Qed.

End Count.

End Reach.

(** ** 4. A binary increment counter whose arms are [Reach1] facts *)

Fixpoint binc (x : list bool) : list bool :=
  match x with
  | [] => [true]
  | false :: r => true :: r
  | true :: r => false :: binc r
  end.

Fixpoint biter (x : list bool) (n : nat) : list bool :=
  match n with O => x | S n' => biter (binc x) n' end.

Lemma biter_add : forall n1 n2 x, biter x (n1 + n2) = biter (biter x n1) n2.
Proof. induction n1 as [|n1 IH]; intros n2 x; [reflexivity | apply IH]. Qed.

Lemma biter_S : forall n x, biter x (S n) = binc (biter x n).
Proof.
  intros n x. replace (S n) with (n + 1) by lia. rewrite biter_add. reflexivity.
Qed.

Lemma binc_int : forall k r, binc (repeat true k ++ false :: r) = repeat false k ++ true :: r.
Proof. induction k as [|k IH]; intros r; [reflexivity|]. cbn. rewrite IH. reflexivity. Qed.

Lemma binc_top : forall k, binc (repeat true k) = repeat false k ++ [true].
Proof. induction k as [|k IH]; [reflexivity|]. cbn. rewrite IH. reflexivity. Qed.

Lemma ttdecomp : forall x,
  (exists k r, x = repeat true k ++ false :: r) \/ (exists k, x = repeat true k).
Proof.
  induction x as [|[|] x IH].
  - right. exists 0. reflexivity.
  - destruct IH as [(k & r & ->) | (k & ->)].
    + left. exists (S k), r. reflexivity.
    + right. exists (S k). reflexivity.
  - left. exists 0, x. reflexivity.
Qed.

Lemma biter_low : forall y n,
  biter (false :: y) (2 * n) = false :: biter y n
  /\ biter (false :: y) (2 * n + 1) = true :: biter y n.
Proof.
  intros y n. induction n as [|n [IH1 IH2]]; [split; reflexivity|].
  assert (E1 : biter (false :: y) (2 * S n) = false :: biter y (S n)).
  { replace (2 * S n) with (S (2 * n + 1)) by lia.
    rewrite biter_S, IH2, biter_S. reflexivity. }
  split; [exact E1|].
  replace (2 * S n + 1) with (S (2 * S n)) by lia. rewrite biter_S, E1. reflexivity.
Qed.

Lemma low_count : forall K r, biter (repeat false K ++ r) (2 ^ K - 1) = repeat true K ++ r.
Proof.
  induction K as [|K IH]; intros r; [reflexivity|].
  replace (2 ^ S K - 1) with (2 * (2 ^ K - 1) + 1)
    by (rewrite Nat.pow_succ_r'; pose proof (Nat.pow_nonzero 2 K ltac:(lia)); lia).
  cbn [repeat app]. rewrite (proj2 (biter_low _ _)), IH. reflexivity.
Qed.

Lemma reach_ones : forall K x, exists j r, biter x j = repeat true K ++ r.
Proof.
  induction K as [|K IH]; intros x; [exists 0, x; reflexivity|].
  destruct (IH x) as (j1 & r1 & H1).
  destruct r1 as [|[|] r'].
  - exists (j1 + 1 + (2 ^ K - 1)), [].
    rewrite !biter_add, H1, app_nil_r. cbn [biter]. rewrite binc_top, low_count, app_nil_r.
    replace (S K) with (K + 1) by lia. rewrite repeat_app. reflexivity.
  - exists j1, r'. rewrite H1. replace (S K) with (K + 1) by lia.
    rewrite repeat_app, <- app_assoc. reflexivity.
  - exists (j1 + 1 + (2 ^ K - 1)), r'.
    rewrite !biter_add, H1. cbn [biter]. rewrite binc_int, low_count.
    replace (S K) with (K + 1) by lia. rewrite repeat_app, <- app_assoc. reflexivity.
Qed.

Section BoardBinTr.

Variable tm0   : TM.
Variable pins  : list Instr.
Local Notation tm := (tm_wrap_trs tm0 pins).

Variable mk    : list Sym -> cconf.   (** the anchor, from the counter side's cells *)
Variables Z O T : list Sym.            (** digit words 0, 1 (LSB nearest the head), terminator *)
Variable x0    : list bool.

Definition bcells (x : list bool) : list Sym := flat_map (fun b : bool => if b then O else Z) x.
Definition bcfg (x : list bool) : cconf := mk (bcells x ++ T).

Hypothesis Hint : forall k r,
  Reach1 tm (bcfg (repeat true k ++ false :: r)) (bcfg (repeat false k ++ true :: r)).
Hypothesis Htop : forall k,
  Reach1 tm (bcfg (repeat true k)) (bcfg (repeat false k ++ [true])).
Hypothesis Hfire : forall t, ~ In t pins -> exists K, forall r,
  Fires tm (bcfg (repeat true K ++ r)) t.

Local Notation Cf := (fun n => bcfg (biter x0 n)).

Lemma lapB : forall x, Reach1 tm (bcfg x) (bcfg (binc x)).
Proof.
  intros x. destruct (ttdecomp x) as [(k & r & ->) | (k & ->)].
  - rewrite binc_int. apply Hint.
  - rewrite binc_top. apply Htop.
Qed.

Lemma lapB_n : forall n, exists m c',
  csteps tm m (Cf n) = Some c' /\ lift c' = lift (Cf (S n)) /\ 0 < m.
Proof.
  intros n. destruct (reach1_csteps tm _ _ (lapB (biter x0 n))) as (m & c' & Hm & Hc & Hl).
  exists m, c'. cbn beta. rewrite biter_S. split; [exact Hc | split; [exact Hl | exact Hm]].
Qed.

Lemma fireB : forall t N, ~ In t pins ->
  exists n k c', N <= n /\ csteps tm k (Cf n) = Some c' /\ cinstr c' = t.
Proof.
  intros t N Hnp.
  destruct (Hfire t Hnp) as (K & HK).
  destruct (reach_ones K (biter x0 N)) as (j & r & Hj).
  destruct (HK r) as (k & c' & Hc & Ht).
  exists (N + j), k, c'. split; [lia|]. cbn beta. rewrite biter_add, Hj.
  split; assumption.
Qed.

Theorem boardB_neverqhtr : forall s0,
  stepn tm s0 InitES = Some (lift (bcfg x0)) ->
  NeverQuasiHaltsTr tm0.
Proof.
  intros s0 Hboot.
  apply (glue_neverqhtrN tm0 pins Cf).
  - exists s0. exact Hboot.
  - exact lapB_n.
  - intros t Hnp N. exact (fireB t N Hnp).
Qed.

Lemma reachB : forall d n,
  exists Tm, stepn tm Tm (lift (Cf n)) = Some (lift (Cf (n + d))).
Proof.
  induction d; intros n.
  - exists 0. rewrite Nat.add_0_r. reflexivity.
  - destruct (IHd n) as (Tm & HT).
    destruct (lapB_n (n + d)) as (m & c' & Hm & Hl & _).
    exists (Tm + m). rewrite stepn_add, HT.
    replace (n + S d) with (S (n + d)) by lia.
    rewrite <- Hl. apply csteps_lift. exact Hm.
Qed.

Lemma fire_everyB : forall t, ~ In t pins -> forall n,
  exists k c', csteps tm k (Cf n) = Some c' /\ cinstr c' = t.
Proof.
  intros t Hnp n.
  destruct (fireB t n Hnp) as (m & k & c' & Hm & Hk & Hc').
  destruct (reachB (m - n) n) as (Tm & HT).
  replace (n + (m - n)) with m in HT by lia.
  assert (Hs : stepn tm (Tm + k) (lift (Cf n)) = Some (lift c')).
  { rewrite stepn_add, HT. apply csteps_lift. exact Hk. }
  destruct (stepn_csteps_at tm (Tm + k) (Cf n) (lift c') Hs) as (c'' & Hc'' & Hl').
  exists (Tm + k), c''. split; [exact Hc''|].
  rewrite <- cinstr_lift, Hl', cinstr_lift. exact Hc'.
Qed.

Theorem boardB_qhtr : forall s0 Bd,
  stepn tm0 s0 InitES = Some (lift (bcfg x0)) ->
  existsb (fun tg => cfires tm0 CTape.c0 s0 tg) pins = true ->
  (s0 <=? Bd) = true ->
  NonHalt tm0 /\ QHBoundTr Bd tm0 /\ QuasiHaltsTr tm0.
Proof.
  intros s0 Bd Hboot Hwit Hle.
  apply (lap_qh_stage tm0 pins (fun p => Cf (Nat.pred (Pos.to_nat p)))
           1%positive s0 Bd).
  - exact Hboot.
  - intros p _.
    destruct (lapB_n (Nat.pred (Pos.to_nat p))) as (m & c' & Hrun & Hl & Hm).
    exists m, c'. split; [exact Hrun | split; [|exact Hm]].
    rewrite Hl, Pos2Nat.inj_succ.
    replace (S (Nat.pred (Pos.to_nat p))) with (Pos.to_nat p)
      by (pose proof (Pos2Nat.is_pos p); lia).
    reflexivity.
  - intros t Hnp p _. exact (fire_everyB t Hnp (Nat.pred (Pos.to_nat p))).
  - exact Hwit.
  - exact Hle.
Qed.

End BoardBinTr.

(** ** 5. Configurations from cell lists, blank padding, and the board's
    hypotheses from one carry lemma *)

Definition cfgR (q : St) (L : list Sym) (l : list Sym) : cconf := (q, (L, chd l, ctl l)).
Definition cfgL (q : St) (l : list Sym) (R : list Sym) : cconf := (q, (ctl l, chd l, R)).

Lemma lift_side_pad0 : forall l, lift_side (l ++ [S0]) = lift_side l.
Proof.
  intros l. apply functional_extensionality. intros n. unfold lift_side, nthb.
  revert n. induction l as [|a l IH]; intros [|n]; cbn; try reflexivity.
  - destruct n; reflexivity.
  - apply IH.
Qed.

Lemma lift_side_padn : forall m l, lift_side (l ++ repeat S0 m) = lift_side l.
Proof.
  induction m as [|m IH]; intros l; [rewrite app_nil_r; reflexivity|].
  change (repeat S0 (S m)) with ([S0] ++ repeat S0 m).
  rewrite app_assoc, IH. apply lift_side_pad0.
Qed.

Lemma lift_cfgR_padn : forall m q L l, lift (cfgR q L (l ++ repeat S0 m)) = lift (cfgR q L l).
Proof.
  intros m q L l. unfold cfgR, lift, lift_tape; cbn [fst snd].
  destruct l as [|a l].
  - destruct m as [|m]; [reflexivity|]. cbn [app repeat chd ctl].
    rewrite <- (app_nil_l (repeat S0 m)), lift_side_padn. reflexivity.
  - cbn [app chd ctl]. rewrite lift_side_padn. reflexivity.
Qed.

Lemma lift_cfgL_padn : forall m q l R, lift (cfgL q (l ++ repeat S0 m) R) = lift (cfgL q l R).
Proof.
  intros m q l R. unfold cfgL, lift, lift_tape; cbn [fst snd].
  destruct l as [|a l].
  - destruct m as [|m]; [reflexivity|]. cbn [app repeat chd ctl].
    rewrite <- (app_nil_l (repeat S0 m)), lift_side_padn. reflexivity.
  - cbn [app chd ctl]. rewrite lift_side_padn. reflexivity.
Qed.

(** the far side padded with blanks *)
Lemma lift_fixR_padn : forall m q L h R, lift (q, (L, h, R ++ repeat S0 m)) = lift (q, (L, h, R)).
Proof. intros. unfold lift, lift_tape; cbn [fst snd]. rewrite lift_side_padn. reflexivity. Qed.

Lemma lift_fixL_padn : forall m q L h R, lift (q, (L ++ repeat S0 m, h, R)) = lift (q, (L, h, R)).
Proof. intros. unfold lift, lift_tape; cbn [fst snd]. rewrite lift_side_padn. reflexivity. Qed.

Section BinGlue.
Variable tm : TM.
Variable mk : list Sym -> cconf.
Variables Z O T : list Sym.

Lemma bcells_tt : forall k r, bcells Z O (repeat true k ++ r) = rep O k ++ bcells Z O r.
Proof.
  induction k as [|k IH]; intros r; [reflexivity|].
  cbn [repeat app]. unfold bcells in *. cbn [flat_map]. rewrite IH. cbn [rep]. rewrite <- app_assoc. reflexivity.
Qed.

Lemma bcells_ff : forall k r, bcells Z O (repeat false k ++ r) = rep Z k ++ bcells Z O r.
Proof.
  induction k as [|k IH]; intros r; [reflexivity|].
  cbn [repeat app]. unfold bcells in *. cbn [flat_map]. rewrite IH. cbn [rep]. rewrite <- app_assoc. reflexivity.
Qed.

Hypothesis Hcarry : forall k X, Reach1 tm (mk (rep O k ++ Z ++ X)) (mk (rep Z k ++ O ++ X)).

Lemma bin_int_of_carry : forall k r,
  Reach1 tm (bcfg mk Z O T (repeat true k ++ false :: r)) (bcfg mk Z O T (repeat false k ++ true :: r)).
Proof.
  intros k r. unfold bcfg. rewrite bcells_tt, bcells_ff.
  unfold bcells; cbn [flat_map]. fold (bcells Z O r). rewrite <- !app_assoc. apply Hcarry.
Qed.

Hypothesis HZ : forall l, lift (mk (l ++ Z ++ T)) = lift (mk (l ++ T)).

Lemma bin_top_of_carry : forall k,
  Reach1 tm (bcfg mk Z O T (repeat true k)) (bcfg mk Z O T (repeat false k ++ [true])).
Proof.
  intros k. unfold bcfg.
  rewrite <- (app_nil_r (repeat true k)), bcells_tt, bcells_ff. cbn [bcells flat_map].
  rewrite !app_nil_r.
  apply (reach1_lift_l tm _ (mk (rep O k ++ Z ++ T))); [symmetry; apply HZ|].
  rewrite <- app_assoc. apply Hcarry.
Qed.

Lemma bin_fire_of_carry : forall K t,
  (forall n X, Fires tm (mk (rep O (K + n) ++ Z ++ X)) t) ->
  forall r, Fires tm (bcfg mk Z O T (repeat true K ++ r)) t.
Proof.
  intros K t HF r. unfold bcfg.
  destruct (ttdecomp r) as [(j & r' & ->) | (j & ->)].
  - rewrite app_assoc, <- repeat_app, bcells_tt. unfold bcells; cbn [flat_map].
    fold (bcells Z O r'). rewrite <- !app_assoc. apply HF.
  - rewrite <- repeat_app, <- (app_nil_r (repeat true (K + j))), bcells_tt.
    cbn [bcells flat_map]. rewrite app_nil_r.
    apply (fire_lift tm _ (mk (rep O (K + j) ++ Z ++ T))); [symmetry; apply HZ|].
    apply HF.
Qed.

(** the plain binary successor at the top, from the carry over blank zeros *)
Lemma ovf_of_carry : forall k,
  Reach1 tm (mk (rep O k ++ O ++ T)) (mk (rep Z (k + 1) ++ O ++ T)).
Proof.
  intros k. rewrite app_assoc, <- rep_S_r.
  apply (reach1_lift_l tm _ (mk (rep O (S k) ++ Z ++ T))); [symmetry; apply HZ|].
  replace (k + 1) with (S k) by lia. apply Hcarry.
Qed.

Lemma fire_ovf_of_carry : forall K t,
  (forall n X, Fires tm (mk (rep O (K + n) ++ Z ++ X)) t) ->
  forall n, Fires tm (mk (rep O (K + n) ++ O ++ T)) t.
Proof.
  intros K t HF n. rewrite app_assoc, <- rep_S_r.
  apply (fire_lift tm _ (mk (rep O (S (K + n)) ++ Z ++ T))); [symmetry; apply HZ|].
  replace (S (K + n)) with (K + S n) by lia. apply HF.
Qed.

End BinGlue.

(** ** 6. A counter closed by whole COUNTS: one lap is a full count of the
    width and one overflow

    [Cf i = mk (Z^(L0 + i d) W T)]: the low digits count from zero to all
    ones ([Hcount], e.g. [count_from_carry]) and the overflow writes zeros
    [d] digits wider ([Hovf]; the plain binary successor is [W = O],
    [d = 1]).  Every lap passes an overflow, so the fires are read from
    the overflow configurations alone ([Hfire]).  Any of the three may run
    inner counts. *)

Section BoardCountTr.

Variable tm0   : TM.
Variable pins  : list Instr.
Local Notation tm := (tm_wrap_trs tm0 pins).

Variable mk    : list Sym -> cconf.
Variables Z O W T : list Sym.
Variables d L0 : nat.

Hypothesis Hcount : forall k Y, Reach0 tm (mk (rep Z k ++ Y)) (mk (rep O k ++ Y)).
Hypothesis Hovf : forall n,
  Reach1 tm (mk (rep O (L0 + n) ++ W ++ T)) (mk (rep Z (L0 + n + d) ++ W ++ T)).
Hypothesis Hfire : forall t, ~ In t pins -> forall n,
  Fires tm (mk (rep O (L0 + n) ++ W ++ T)) t.

Definition ccfg (i : nat) : cconf := mk (rep Z (L0 + i * d) ++ W ++ T).

Lemma lapC : forall i, Reach1 tm (ccfg i) (ccfg (S i)).
Proof.
  intros i. unfold ccfg.
  apply (reach01 tm _ (mk (rep O (L0 + i * d) ++ W ++ T))); [apply Hcount|].
  replace (L0 + S i * d) with (L0 + i * d + d) by lia. apply Hovf.
Qed.

Lemma lapC_n : forall i, exists m c',
  csteps tm m (ccfg i) = Some c' /\ lift c' = lift (ccfg (S i)) /\ 0 < m.
Proof.
  intros i. destruct (reach1_csteps tm _ _ (lapC i)) as (m & c' & Hm & Hc & Hl).
  exists m, c'. split; [exact Hc | split; [exact Hl | exact Hm]].
Qed.

Lemma fireC : forall t, ~ In t pins -> forall i, Fires tm (ccfg i) t.
Proof.
  intros t Hnp i. unfold ccfg.
  apply (fire_back tm _ (mk (rep O (L0 + i * d) ++ W ++ T))); [apply Hcount|].
  apply Hfire, Hnp.
Qed.

Theorem boardC_neverqhtr : forall s0,
  stepn tm s0 InitES = Some (lift (ccfg 0)) ->
  NeverQuasiHaltsTr tm0.
Proof.
  intros s0 Hboot.
  apply (glue_neverqhtrN tm0 pins ccfg).
  - exists s0. exact Hboot.
  - exact lapC_n.
  - intros t Hnp N. destruct (fireC t Hnp N) as (k & c' & Hc & Ht).
    exists N, k, c'. split; [lia | split; assumption].
Qed.

Lemma reachC : forall dd i,
  exists Tm, stepn tm Tm (lift (ccfg i)) = Some (lift (ccfg (i + dd))).
Proof.
  induction dd; intros i.
  - exists 0. rewrite Nat.add_0_r. reflexivity.
  - destruct (IHdd i) as (Tm & HT).
    destruct (lapC (i + dd)) as (m & _ & Hm).
    exists (Tm + m). rewrite stepn_add, HT.
    replace (i + S dd) with (S (i + dd)) by lia. exact Hm.
Qed.

Theorem boardC_qhtr : forall s0 Bd,
  stepn tm0 s0 InitES = Some (lift (ccfg 0)) ->
  existsb (fun tg => cfires tm0 CTape.c0 s0 tg) pins = true ->
  (s0 <=? Bd) = true ->
  NonHalt tm0 /\ QHBoundTr Bd tm0 /\ QuasiHaltsTr tm0.
Proof.
  intros s0 Bd Hboot Hwit Hle.
  apply (lap_qh_stage tm0 pins (fun p => ccfg (Nat.pred (Pos.to_nat p)))
           1%positive s0 Bd).
  - exact Hboot.
  - intros p _.
    destruct (lapC_n (Nat.pred (Pos.to_nat p))) as (m & c' & Hrun & Hl & Hm).
    exists m, c'. split; [exact Hrun | split; [|exact Hm]].
    rewrite Hl, Pos2Nat.inj_succ.
    replace (S (Nat.pred (Pos.to_nat p))) with (Pos.to_nat p)
      by (pose proof (Pos2Nat.is_pos p); lia).
    reflexivity.
  - intros t Hnp p _. exact (fireC t Hnp (Nat.pred (Pos.to_nat p))).
  - exact Hwit.
  - exact Hle.
Qed.

End BoardCountTr.
