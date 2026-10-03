(** * Counters.TopMapTr: a binary counter whose TOP transitions are an
    arbitrary map (SCOPING_INSTR 7.4.LE9).

    The phased boards of LE9 ([PhBinCountTr], [RunPhCountTr],
    [LadderCheckTankPhTr]) all have the same skeleton: a binary counter [x]
    (LSB at the head) counts up inside its width, and at its top something
    else happens that depends on a small state beside the counter (a run
    length [m], a phase [p]).  This board takes that "something else" as a
    MAP [G p k m = (x', m', p')] and its liveness as a hypothesis on the
    MACRO dynamics [(k, m, p) |-> (length x', m', p')], which a row proves
    by hand (an induction on the run, the width, the phase).

    Configurations: [tcfg (x, m, p) = base (bcells x ++ tail p m)].
    Hypotheses ([Reach1] facts, any [LadderNest] arm family): one carry
    (against any tail), one top transition per abstract state satisfying an
    invariant [Inv k m p] that [G] preserves; the fires are read off the
    tops of the macro states satisfying a predicate per instruction, which
    the macro dynamics revisit.
    Never-QH and QH closers.

    Nothing landed is modified.  Axiom footprint: [functional_extensionality_dep],
    via [CTape.lift]. *)
From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape ClosureTr.
From BBB4.Counters Require Import WTape LapCertGlueLift.
From BBB4.Checkers Require Import WrapTr LapDecider LadderKernel LadderCheckTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
From BBB4.Counters Require Import NestCountTr PhBinCountTr.
From BBB4.CensusTr Require Import TNF_QHTr QHConveyorTr.
Import ListNotations.

Section TopMap.

Variable tm0  : TM.
Variable pins : list Instr.
Local Notation tm := (tm_wrap_trs tm0 pins).

Variable base : list Sym -> cconf.
Variables Z O : list Sym.
Variable tail : nat -> nat -> list Sym.          (** phase, run *)
Variable G    : nat -> nat -> nat -> list bool * nat * nat.   (** phase, width, run *)
Variable Inv  : nat -> nat -> nat -> Prop.        (** width, run, phase *)

Definition TSt : Type := (list bool * nat * nat)%type.

Definition tcfg (s : TSt) : cconf := let '(x, m, p) := s in base (bcells Z O x ++ tail p m).

Definition tsucc (s : TSt) : TSt :=
  let '(x, m, p) := s in if alltrue x then G p (length x) m else (binc x, m, p).

Fixpoint titer (s : TSt) (n : nat) : TSt :=
  match n with 0 => s | S n' => titer (tsucc s) n' end.

Lemma titer_add : forall n1 n2 s, titer s (n1 + n2) = titer (titer s n1) n2.
Proof. induction n1 as [|n1 IH]; intros n2 s; [reflexivity | apply IH]. Qed.

Definition TInv (s : TSt) : Prop := let '(x, m, p) := s in Inv (length x) m p.

(** the macro dynamics, top to top *)
Definition macro (a : nat * nat * nat) : nat * nat * nat :=
  let '(k, m, p) := a in let '(x', m', p') := G p k m in (length x', m', p').

Fixpoint miter (a : nat * nat * nat) (n : nat) : nat * nat * nat :=
  match n with 0 => a | S n' => miter (macro a) n' end.

Lemma miter_add : forall n1 n2 a, miter a (n1 + n2) = miter (miter a n1) n2.
Proof. induction n1 as [|n1 IH]; intros n2 a; [reflexivity | apply IH]. Qed.

Hypothesis Hcarry : forall k X,
  Reach1 tm (base (rep O k ++ Z ++ X)) (base (rep Z k ++ O ++ X)).
Hypothesis Htop : forall p k m, Inv k m p ->
  Reach1 tm (base (rep O k ++ tail p m)) (tcfg (G p k m)).
Hypothesis HGinv : forall p k m, Inv k m p -> TInv (G p k m).
(** each instruction fires from the tops of the macro states satisfying a
    predicate [Q], which the macro dynamics revisit *)
Hypothesis Hfire : forall t, ~ In t pins -> exists Q : nat -> nat -> nat -> Prop,
  (forall k m p, Q k m p -> Inv k m p -> Fires tm (base (rep O k ++ tail p m)) t) /\
  (forall k m p, Inv k m p -> exists n, let '(k', m', p') := miter (k, m, p) n in Q k' m' p').

Lemma tsucc_inv : forall s, TInv s -> TInv (tsucc s).
Proof.
  intros [[x m] p] Hi. cbn [tsucc TInv] in *.
  destruct (alltrue x) eqn:E.
  - rewrite (alltrue_eq x E), repeat_length in Hi. apply HGinv, Hi.
  - destruct (binc_val x E) as [_ H2]. cbn. rewrite H2. exact Hi.
Qed.

Lemma titer_inv : forall n s, TInv s -> TInv (titer s n).
Proof. induction n as [|n IH]; intros s Hs; [exact Hs|]. apply IH, tsucc_inv, Hs. Qed.

Lemma tstep : forall s, TInv s -> Reach1 tm (tcfg s) (tcfg (tsucc s)).
Proof.
  intros [[x m] p] Hi. cbn [tsucc TInv] in *.
  destruct (alltrue x) eqn:E.
  - rewrite (alltrue_eq x E) in Hi |- *. rewrite repeat_length in Hi |- *.
    unfold tcfg at 1. rewrite bcells_rep_true. apply Htop, Hi.
  - destruct (ttdecomp x) as [(k & r & ->) | (k & ->)].
    2:{ rewrite alltrue_repeat in E. discriminate. }
    rewrite binc_int. unfold tcfg.
    rewrite !bcells_tt, !bcells_ff.
    change (bcells Z O (false :: r)) with (Z ++ bcells Z O r).
    change (bcells Z O (true :: r)) with (O ++ bcells Z O r).
    rewrite <- !app_assoc. apply Hcarry.
Qed.

(** the top of the current width is reached, the run and phase unchanged *)
Lemma top_reached : forall v x m p, 2 ^ length x - bval x <= v ->
  exists n, titer (x, m, p) n = (repeat true (length x), m, p).
Proof.
  induction v as [|v IH]; intros x m p Hv.
  - pose proof (bval_lt x). lia.
  - destruct (alltrue x) eqn:E.
    + exists 0. cbn. rewrite <- (alltrue_eq x E). reflexivity.
    + destruct (binc_val x E) as [H1 H2].
      destruct (IH (binc x) m p) as (n & Hn); [rewrite H1, H2; lia|].
      exists (S n). cbn [titer tsucc]. rewrite E, Hn, H2. reflexivity.
Qed.

(** from a top, the next top is the macro step *)
Lemma top_next : forall k m p, exists n, 0 < n /\
  titer (repeat true k, m, p) n =
    (let '(k', m', p') := macro (k, m, p) in (repeat true k', m', p')).
Proof.
  intros k m p. cbn [macro].
  destruct (G p k m) as [[x' m'] p'] eqn:EG.
  destruct (top_reached (2 ^ length x' - bval x') x' m' p' (le_n _)) as (n & Hn).
  exists (S n). split; [lia|]. cbn [titer tsucc]. rewrite alltrue_repeat, repeat_length, EG. exact Hn.
Qed.

Lemma top_miter : forall j k m p, exists n,
  titer (repeat true k, m, p) n =
    (let '(k', m', p') := miter (k, m, p) j in (repeat true k', m', p')).
Proof.
  induction j as [|j IH]; intros k m p.
  - exists 0. reflexivity.
  - destruct (top_next k m p) as (n1 & _ & Hn1).
    cbn [miter]. destruct (macro (k, m, p)) as [[k' m'] p'] eqn:Em.
    destruct (IH k' m' p') as (n2 & Hn2).
    exists (n1 + n2). rewrite titer_add, Hn1. exact Hn2.
Qed.

Variable x0 : list bool.
Variables m0 p0 : nat.
Hypothesis Hinv0 : TInv (x0, m0, p0).

Definition tCf (n : nat) : cconf := tcfg (titer (x0, m0, p0) n).

Lemma tCf_lap : forall n, exists k c',
  csteps tm k (tCf n) = Some c' /\ lift c' = lift (tCf (S n)) /\ 0 < k.
Proof.
  intros n.
  pose proof (titer_inv n (x0, m0, p0) Hinv0) as Hi.
  destruct (reach1_csteps tm _ _ (tstep _ Hi)) as (k & c' & Hk & Hc & Hl).
  exists k, c'. unfold tCf. replace (S n) with (n + 1) by lia. rewrite titer_add.
  split; [exact Hc | split; [exact Hl | exact Hk]].
Qed.

Lemma tCf_fire : forall t N, ~ In t pins ->
  exists n k c', N <= n /\ csteps tm k (tCf n) = Some c' /\ cinstr c' = t.
Proof.
  intros t N Hnp.
  destruct (Hfire t Hnp) as (Q & Hf & Hr).
  pose proof (titer_inv N (x0, m0, p0) Hinv0) as HiN.
  destruct (titer (x0, m0, p0) N) as [[x m] p] eqn:EN.
  destruct (top_reached (2 ^ length x - bval x) x m p (le_n _)) as (n1 & Hn1).
  destruct (Hr (length x) m p HiN) as (j & Hj).
  destruct (top_miter j (length x) m p) as (n2 & Hn2).
  destruct (miter (length x, m, p) j) as [[k' m'] p'] eqn:Em.
  (* the invariant at that top *)
  assert (Hit : TInv (titer (x0, m0, p0) (N + n1 + n2))) by (apply titer_inv, Hinv0).
  rewrite !titer_add, EN, Hn1, Hn2 in Hit. cbn [TInv] in Hit. rewrite repeat_length in Hit.
  destruct (Hf k' m' p' Hj Hit) as (k & c' & Hc & Hct).
  exists (N + n1 + n2), k, c'. split; [lia|].
  unfold tCf. rewrite !titer_add, EN, Hn1, Hn2. cbn [tcfg]. rewrite bcells_rep_true.
  split; assumption.
Qed.

Theorem topmap_neverqhtr : forall t0,
  stepn tm t0 InitES = Some (lift (tcfg (x0, m0, p0))) ->
  NeverQuasiHaltsTr tm0.
Proof.
  intros t0 Hboot.
  apply (glue_neverqhtrN tm0 pins tCf).
  - exists t0. exact Hboot.
  - exact tCf_lap.
  - intros t Hnp N. exact (tCf_fire t N Hnp).
Qed.

Lemma tCf_reach : forall d n,
  exists Tm, stepn tm Tm (lift (tCf n)) = Some (lift (tCf (n + d))).
Proof.
  induction d; intros n.
  - exists 0. rewrite Nat.add_0_r. reflexivity.
  - destruct (IHd n) as (Tm & HT).
    destruct (tCf_lap (n + d)) as (m & c' & Hm & Hl & _).
    exists (Tm + m). rewrite stepn_add, HT.
    replace (n + S d) with (S (n + d)) by lia.
    rewrite <- Hl. apply csteps_lift. exact Hm.
Qed.

Lemma tCf_fire_every : forall t, ~ In t pins -> forall n,
  exists k c', csteps tm k (tCf n) = Some c' /\ cinstr c' = t.
Proof.
  intros t Hnp n.
  destruct (tCf_fire t n Hnp) as (m & k & c' & Hm & Hk & Hc').
  destruct (tCf_reach (m - n) n) as (Tm & HT).
  replace (n + (m - n)) with m in HT by lia.
  assert (Hs : stepn tm (Tm + k) (lift (tCf n)) = Some (lift c')).
  { rewrite stepn_add, HT. apply csteps_lift. exact Hk. }
  destruct (stepn_csteps_at tm (Tm + k) (tCf n) (lift c') Hs) as (c'' & Hc'' & Hl').
  exists (Tm + k), c''. split; [exact Hc''|].
  rewrite <- cinstr_lift, Hl', cinstr_lift. exact Hc'.
Qed.

Theorem topmap_qhtr : forall t0 B,
  stepn tm0 t0 InitES = Some (lift (tcfg (x0, m0, p0))) ->
  existsb (fun tg => cfires tm0 CTape.c0 t0 tg) pins = true ->
  (t0 <=? B) = true ->
  NonHalt tm0 /\ QHBoundTr B tm0 /\ QuasiHaltsTr tm0.
Proof.
  intros t0 B Hboot Hwit Hle.
  apply (lap_qh_stage tm0 pins (fun p => tCf (Nat.pred (Pos.to_nat p)))
           1%positive t0 B).
  - exact Hboot.
  - intros p _.
    destruct (tCf_lap (Nat.pred (Pos.to_nat p))) as (m & c' & Hrun & Hl & Hm).
    exists m, c'. split; [exact Hrun | split; [|exact Hm]].
    rewrite Hl, Pos2Nat.inj_succ.
    replace (S (Nat.pred (Pos.to_nat p))) with (Pos.to_nat p)
      by (pose proof (Pos2Nat.is_pos p); lia).
    reflexivity.
  - intros t Hnp p _. exact (tCf_fire_every t Hnp (Nat.pred (Pos.to_nat p))).
  - exact Hwit.
  - exact Hle.
Qed.

End TopMap.
