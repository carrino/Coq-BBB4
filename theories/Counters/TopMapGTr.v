(** * Counters.TopMapGTr: [TopMapTr] with the configuration an arbitrary
    function of the abstract state (SCOPING_INSTR 7.4.LE9).

    [TopMapTr] spells the counter on one side, [base (bcells x ++ tail p m)];
    a MIRRORED counter holds [x] on both sides of the head, so here the
    configuration is any [C x m p] and the carry is a hypothesis on [C]
    directly ([1^k 0 r -> 0^k 1 r], for every [r] the invariant allows),
    which a row proves by composing one-sided arms.  Everything else is
    [TopMapTr]'s.

    The phased boards of LE9 ([PhBinCountTr], [RunPhCountTr],
    [LadderCheckTankPhTr]) all have the same skeleton: a binary counter [x]
    (LSB at the head) counts up inside its width, and at its top something
    else happens that depends on a small state beside the counter (a run
    length [m], a phase [p]).  This board takes that "something else" as a
    MAP [G p k m = (x', m', p')] and its liveness as a hypothesis on the
    MACRO dynamics [(k, m, p) |-> (length x', m', p')], which a row proves
    by hand (an induction on the run, the width, the phase).

    Configurations: [gcfg (x, m, p) = C x m p].
    Hypotheses ([Reach1] facts): the carry, one top transition per abstract state satisfying an
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

Section TopMapG.

Variable tm0  : TM.
Variable pins : list Instr.
Local Notation tm := (tm_wrap_trs tm0 pins).

Variable C    : list bool -> nat -> nat -> cconf.   (** counter, run, phase *)
Variable G    : nat -> nat -> nat -> list bool * nat * nat.   (** phase, width, run *)
Variable Inv  : nat -> nat -> nat -> Prop.        (** width, run, phase *)

Definition GSt : Type := (list bool * nat * nat)%type.

Definition gcfg (s : GSt) : cconf := let '(x, m, p) := s in C x m p.

Definition gsucc (s : GSt) : GSt :=
  let '(x, m, p) := s in if alltrue x then G p (length x) m else (binc x, m, p).

Fixpoint giter (s : GSt) (n : nat) : GSt :=
  match n with 0 => s | S n' => giter (gsucc s) n' end.

Lemma giter_add : forall n1 n2 s, giter s (n1 + n2) = giter (giter s n1) n2.
Proof. induction n1 as [|n1 IH]; intros n2 s; [reflexivity | apply IH]. Qed.

Definition GInv (s : GSt) : Prop := let '(x, m, p) := s in Inv (length x) m p.

(** the macro dynamics, top to top *)
Definition gmacro (a : nat * nat * nat) : nat * nat * nat :=
  let '(k, m, p) := a in let '(x', m', p') := G p k m in (length x', m', p').

Fixpoint gmiter (a : nat * nat * nat) (n : nat) : nat * nat * nat :=
  match n with 0 => a | S n' => gmiter (gmacro a) n' end.

Lemma gmiter_add : forall n1 n2 a, gmiter a (n1 + n2) = gmiter (gmiter a n1) n2.
Proof. induction n1 as [|n1 IH]; intros n2 a; [reflexivity | apply IH]. Qed.

Hypothesis Hcarry : forall k r m p, Inv (k + S (length r)) m p ->
  Reach1 tm (C (repeat true k ++ false :: r) m p) (C (repeat false k ++ true :: r) m p).
Hypothesis Htop : forall p k m, Inv k m p ->
  Reach1 tm (C (repeat true k) m p) (gcfg (G p k m)).
Hypothesis HGinv : forall p k m, Inv k m p -> GInv (G p k m).
(** each instruction fires from the tops of the macro states satisfying a
    predicate [Q], which the macro dynamics revisit *)
Hypothesis Hfire : forall t, ~ In t pins -> exists Q : nat -> nat -> nat -> Prop,
  (forall k m p, Q k m p -> Inv k m p -> Fires tm (C (repeat true k) m p) t) /\
  (forall k m p, Inv k m p -> exists n, let '(k', m', p') := gmiter (k, m, p) n in Q k' m' p').

Lemma gsucc_inv : forall s, GInv s -> GInv (gsucc s).
Proof.
  intros [[x m] p] Hi. cbn [gsucc GInv] in *.
  destruct (alltrue x) eqn:E.
  - rewrite (alltrue_eq x E), repeat_length in Hi. apply HGinv, Hi.
  - destruct (binc_val x E) as [_ H2]. cbn. rewrite H2. exact Hi.
Qed.

Lemma giter_inv : forall n s, GInv s -> GInv (giter s n).
Proof. induction n as [|n IH]; intros s Hs; [exact Hs|]. apply IH, gsucc_inv, Hs. Qed.

Lemma gstep : forall s, GInv s -> Reach1 tm (gcfg s) (gcfg (gsucc s)).
Proof.
  intros [[x m] p] Hi. cbn [gsucc GInv] in *.
  destruct (alltrue x) eqn:E.
  - rewrite (alltrue_eq x E) in Hi |- *. rewrite repeat_length in Hi |- *.
    apply Htop, Hi.
  - destruct (ttdecomp x) as [(k & r & ->) | (k & ->)].
    2:{ rewrite alltrue_repeat in E. discriminate. }
    rewrite binc_int. apply Hcarry.
    rewrite app_length, repeat_length in Hi. exact Hi.
Qed.

(** the top of the current width is reached, the run and phase unchanged *)
Lemma gtop_reached : forall v x m p, 2 ^ length x - bval x <= v ->
  exists n, giter (x, m, p) n = (repeat true (length x), m, p).
Proof.
  induction v as [|v IH]; intros x m p Hv.
  - pose proof (bval_lt x). lia.
  - destruct (alltrue x) eqn:E.
    + exists 0. cbn. rewrite <- (alltrue_eq x E). reflexivity.
    + destruct (binc_val x E) as [H1 H2].
      destruct (IH (binc x) m p) as (n & Hn); [rewrite H1, H2; lia|].
      exists (S n). cbn [giter gsucc]. rewrite E, Hn, H2. reflexivity.
Qed.

(** from a top, the next top is the gmacro step *)
Lemma gtop_next : forall k m p, exists n, 0 < n /\
  giter (repeat true k, m, p) n =
    (let '(k', m', p') := gmacro (k, m, p) in (repeat true k', m', p')).
Proof.
  intros k m p. cbn [gmacro].
  destruct (G p k m) as [[x' m'] p'] eqn:EG.
  destruct (gtop_reached (2 ^ length x' - bval x') x' m' p' (le_n _)) as (n & Hn).
  exists (S n). split; [lia|]. cbn [giter gsucc]. rewrite alltrue_repeat, repeat_length, EG. exact Hn.
Qed.

Lemma top_gmiter : forall j k m p, exists n,
  giter (repeat true k, m, p) n =
    (let '(k', m', p') := gmiter (k, m, p) j in (repeat true k', m', p')).
Proof.
  induction j as [|j IH]; intros k m p.
  - exists 0. reflexivity.
  - destruct (gtop_next k m p) as (n1 & _ & Hn1).
    cbn [gmiter]. destruct (gmacro (k, m, p)) as [[k' m'] p'] eqn:Em.
    destruct (IH k' m' p') as (n2 & Hn2).
    exists (n1 + n2). rewrite giter_add, Hn1. exact Hn2.
Qed.

Variable x0 : list bool.
Variables m0 p0 : nat.
Hypothesis Hinv0 : GInv (x0, m0, p0).

Definition gCf (n : nat) : cconf := gcfg (giter (x0, m0, p0) n).

Lemma gCf_lap : forall n, exists k c',
  csteps tm k (gCf n) = Some c' /\ lift c' = lift (gCf (S n)) /\ 0 < k.
Proof.
  intros n.
  pose proof (giter_inv n (x0, m0, p0) Hinv0) as Hi.
  destruct (reach1_csteps tm _ _ (gstep _ Hi)) as (k & c' & Hk & Hc & Hl).
  exists k, c'. unfold gCf. replace (S n) with (n + 1) by lia. rewrite giter_add.
  split; [exact Hc | split; [exact Hl | exact Hk]].
Qed.

Lemma gCf_fire : forall t N, ~ In t pins ->
  exists n k c', N <= n /\ csteps tm k (gCf n) = Some c' /\ cinstr c' = t.
Proof.
  intros t N Hnp.
  destruct (Hfire t Hnp) as (Q & Hf & Hr).
  pose proof (giter_inv N (x0, m0, p0) Hinv0) as HiN.
  destruct (giter (x0, m0, p0) N) as [[x m] p] eqn:EN.
  destruct (gtop_reached (2 ^ length x - bval x) x m p (le_n _)) as (n1 & Hn1).
  destruct (Hr (length x) m p HiN) as (j & Hj).
  destruct (top_gmiter j (length x) m p) as (n2 & Hn2).
  destruct (gmiter (length x, m, p) j) as [[k' m'] p'] eqn:Em.
  (* the invariant at that top *)
  assert (Hit : GInv (giter (x0, m0, p0) (N + n1 + n2))) by (apply giter_inv, Hinv0).
  rewrite !giter_add, EN, Hn1, Hn2 in Hit. cbn [GInv] in Hit. rewrite repeat_length in Hit.
  destruct (Hf k' m' p' Hj Hit) as (k & c' & Hc & Hct).
  exists (N + n1 + n2), k, c'. split; [lia|].
  unfold gCf. rewrite !giter_add, EN, Hn1, Hn2. cbn [gcfg].
  split; assumption.
Qed.

Theorem topmapg_neverqhtr : forall t0,
  stepn tm t0 InitES = Some (lift (gcfg (x0, m0, p0))) ->
  NeverQuasiHaltsTr tm0.
Proof.
  intros t0 Hboot.
  apply (glue_neverqhtrN tm0 pins gCf).
  - exists t0. exact Hboot.
  - exact gCf_lap.
  - intros t Hnp N. exact (gCf_fire t N Hnp).
Qed.

Lemma gCf_reach : forall d n,
  exists Tm, stepn tm Tm (lift (gCf n)) = Some (lift (gCf (n + d))).
Proof.
  induction d; intros n.
  - exists 0. rewrite Nat.add_0_r. reflexivity.
  - destruct (IHd n) as (Tm & HT).
    destruct (gCf_lap (n + d)) as (m & c' & Hm & Hl & _).
    exists (Tm + m). rewrite stepn_add, HT.
    replace (n + S d) with (S (n + d)) by lia.
    rewrite <- Hl. apply csteps_lift. exact Hm.
Qed.

Lemma gCf_fire_every : forall t, ~ In t pins -> forall n,
  exists k c', csteps tm k (gCf n) = Some c' /\ cinstr c' = t.
Proof.
  intros t Hnp n.
  destruct (gCf_fire t n Hnp) as (m & k & c' & Hm & Hk & Hc').
  destruct (gCf_reach (m - n) n) as (Tm & HT).
  replace (n + (m - n)) with m in HT by lia.
  assert (Hs : stepn tm (Tm + k) (lift (gCf n)) = Some (lift c')).
  { rewrite stepn_add, HT. apply csteps_lift. exact Hk. }
  destruct (stepn_csteps_at tm (Tm + k) (gCf n) (lift c') Hs) as (c'' & Hc'' & Hl').
  exists (Tm + k), c''. split; [exact Hc''|].
  rewrite <- cinstr_lift, Hl', cinstr_lift. exact Hc'.
Qed.

Theorem topmapg_qhtr : forall t0 B,
  stepn tm0 t0 InitES = Some (lift (gcfg (x0, m0, p0))) ->
  existsb (fun tg => cfires tm0 CTape.c0 t0 tg) pins = true ->
  (t0 <=? B) = true ->
  NonHalt tm0 /\ QHBoundTr B tm0 /\ QuasiHaltsTr tm0.
Proof.
  intros t0 B Hboot Hwit Hle.
  apply (lap_qh_stage tm0 pins (fun p => gCf (Nat.pred (Pos.to_nat p)))
           1%positive t0 B).
  - exact Hboot.
  - intros p _.
    destruct (gCf_lap (Nat.pred (Pos.to_nat p))) as (m & c' & Hrun & Hl & Hm).
    exists m, c'. split; [exact Hrun | split; [|exact Hm]].
    rewrite Hl, Pos2Nat.inj_succ.
    replace (S (Nat.pred (Pos.to_nat p))) with (Pos.to_nat p)
      by (pose proof (Pos2Nat.is_pos p); lia).
    reflexivity.
  - intros t Hnp p _. exact (gCf_fire_every t Hnp (Nat.pred (Pos.to_nat p))).
  - exact Hwit.
  - exact Hle.
Qed.

End TopMapG.
