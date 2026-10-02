(** * Counters.PhBinCountTr: a binary counter with PHASES, each phase its
    own anchor (SCOPING_INSTR 7.4.LE9).

    LE7's "mixed-digit" rows ([0RB1LD_1LC1RB_1RA1LA_1LB0LC] and two
    conjugates) are a plain binary counter over two 3-cell words, LSB at the
    head, read at TWO anchors that differ by one cell of the far side: phase
    A counts [x] up to its top and FILLS to phase B with [x = 1 0^k] one
    digit wider, the anchor one cell further in; B counts and fills back to
    A with [x = 0 1 0^k].  [LadderFam] has one far side per family, so no
    landed counter states it.

    The board is generic: [mk p] builds phase [p]'s configuration from the
    counter side's cells, [pcfg p x = mk p (bcells x ++ T p)], and the
    hypotheses are [Reach1] facts (any [LadderNest] arm family or
    composition): one carry per phase (an interior increment for every
    tail), one fill per phase from every width [>= Kmin] to the next phase
    at the digits [fz p k].  Liveness: within a phase the binary value rises
    to the top, the fills recur and the phases cycle; each instruction is
    read off the fills of one phase.  Never-QH and QH closers.

    Nothing landed is modified.  Axiom footprint: [functional_extensionality_dep],
    via [CTape.lift]. *)
From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape ClosureTr.
From BBB4.Counters Require Import WTape LapCertGlueLift.
From BBB4.Checkers Require Import WrapTr LapDecider LadderKernel LadderCheckTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
From BBB4.Counters Require Import NestCountTr.
From BBB4.CensusTr Require Import TNF_QHTr QHConveyorTr.
Import ListNotations.

(** ** 1. The binary value *)

Fixpoint bval (x : list bool) : nat :=
  match x with
  | [] => 0
  | b :: r => (if b then 1 else 0) + 2 * bval r
  end.

Definition alltrue (x : list bool) : bool := forallb (fun b => b) x.

Lemma bval_lt : forall x, bval x < 2 ^ length x.
Proof.
  induction x as [|b r IH]; cbn [bval length]; [simpl; lia|].
  rewrite Nat.pow_succ_r'. destruct b; simpl; lia.
Qed.

Lemma binc_val : forall x, alltrue x = false ->
  bval (binc x) = S (bval x) /\ length (binc x) = length x.
Proof.
  induction x as [|b r IH]; intros H; [discriminate|].
  destruct b; simpl in *.
  - destruct (IH H) as [H1 H2]. rewrite H1, H2. split; lia.
  - split; lia.
Qed.

Lemma alltrue_repeat : forall k, alltrue (repeat true k) = true.
Proof. induction k as [|k IH]; [reflexivity|]. exact IH. Qed.

Lemma alltrue_eq : forall x, alltrue x = true -> x = repeat true (length x).
Proof.
  induction x as [|b r IH]; intros H; [reflexivity|].
  cbn [alltrue forallb] in H. apply andb_prop in H as [Hb Hr].
  subst b. cbn [length repeat]. f_equal. apply IH, Hr.
Qed.

Lemma alltrue_int : forall k r, alltrue (repeat true k ++ false :: r) = false.
Proof. induction k as [|k IH]; intros r; [reflexivity|]. exact (IH r). Qed.

(** ** 2. The board *)

Section PhBin.

Variable tm0  : TM.
Variable pins : list Instr.
Local Notation tm := (tm_wrap_trs tm0 pins).

Variable P    : nat.
Variable mk   : nat -> list Sym -> cconf.
Variables Z O : list Sym.
Variable T    : nat -> list Sym.
Variable zpre : nat -> list bool.     (** a fill's low digits *)
Variable zcut : nat -> nat.           (** ... then [k - zcut p] zeros *)
Variable Kmin : nat.

Definition fz (p k : nat) : list bool := zpre p ++ repeat false (k - zcut p).

Definition nxtB (p : nat) : nat := if S p =? P then 0 else S p.

Definition pbcfg (p : nat) (x : list bool) : cconf := mk p (bcells Z O x ++ T p).

Definition BSt : Type := (list bool * nat)%type.

Definition bsucc (s : BSt) : BSt :=
  let '(x, p) := s in
  if alltrue x then (fz p (length x), nxtB p) else (binc x, p).

Fixpoint biterP (s : BSt) (n : nat) : BSt :=
  match n with 0 => s | S n' => biterP (bsucc s) n' end.

Lemma biterP_add : forall n1 n2 s, biterP s (n1 + n2) = biterP (biterP s n1) n2.
Proof. induction n1 as [|n1 IH]; intros n2 s; [reflexivity | apply IH]. Qed.

Definition BInv (s : BSt) : Prop := let '(x, p) := s in Kmin <= length x /\ p < P.

Hypothesis HP : 0 < P.
Hypothesis Hcarry : forall p k X, p < P ->
  Reach1 tm (mk p (rep O k ++ Z ++ X)) (mk p (rep Z k ++ O ++ X)).
Hypothesis Hfill : forall p k, p < P -> Kmin <= k ->
  Reach1 tm (mk p (rep O k ++ T p))
            (mk (nxtB p) (bcells Z O (zpre p) ++ rep Z (k - zcut p) ++ T (nxtB p))).
Hypothesis Hzcut : forall p, p < P -> zcut p <= length (zpre p).
Hypothesis Hfire : forall t, ~ In t pins -> exists p, p < P /\
  forall k, Kmin <= k -> Fires tm (mk p (rep O k ++ T p)) t.

Lemma bcells_app : forall a b, bcells Z O (a ++ b) = bcells Z O a ++ bcells Z O b.
Proof. intros a b. unfold bcells. apply flat_map_app. Qed.

Lemma bcells_rep_false : forall k, bcells Z O (repeat false k) = rep Z k.
Proof.
  intros k. rewrite <- (app_nil_r (repeat false k)), bcells_ff. cbn. apply app_nil_r.
Qed.

Lemma Hfzlen : forall p k, p < P -> Kmin <= k -> Kmin <= length (fz p k).
Proof.
  intros p k Hp Hk. unfold fz. rewrite app_length, repeat_length.
  pose proof (Hzcut p Hp). lia.
Qed.

Lemma nxtB_lt : forall p, p < P -> nxtB p < P.
Proof. intros p Hp. unfold nxtB. destruct (Nat.eqb_spec (S p) P); lia. Qed.

Lemma bsucc_inv : forall s, BInv s -> BInv (bsucc s).
Proof.
  intros [x p] [Hl Hp]. cbn [bsucc].
  destruct (alltrue x) eqn:E.
  - split; [apply Hfzlen; assumption | apply nxtB_lt, Hp].
  - destruct (binc_val x E) as [_ H2]. cbn. rewrite H2. split; assumption.
Qed.

Lemma biterP_inv : forall n s, BInv s -> BInv (biterP s n).
Proof. induction n as [|n IH]; intros s Hs; [exact Hs|]. apply IH, bsucc_inv, Hs. Qed.

Lemma bcells_rep_true : forall k, bcells Z O (repeat true k) = rep O k.
Proof.
  intros k. rewrite <- (app_nil_r (repeat true k)), bcells_tt. cbn. apply app_nil_r.
Qed.

(** one lap *)
Lemma bstep : forall s, BInv s ->
  Reach1 tm (let '(x, p) := s in pbcfg p x) (let '(x, p) := bsucc s in pbcfg p x).
Proof.
  intros [x p] [Hl Hp]. cbn [bsucc].
  destruct (alltrue x) eqn:E.
  - rewrite (alltrue_eq x E) at 1. unfold pbcfg at 1 2. rewrite bcells_rep_true.
    unfold fz. rewrite bcells_app, bcells_rep_false, <- app_assoc.
    apply Hfill; [exact Hp|].
    rewrite (alltrue_eq x E) in Hl. rewrite repeat_length in Hl. exact Hl.
  - destruct (ttdecomp x) as [(k & r & ->) | (k & ->)].
    2:{ rewrite alltrue_repeat in E. discriminate. }
    rewrite binc_int. unfold pbcfg.
    rewrite !bcells_tt, !bcells_ff.
    change (bcells Z O (false :: r)) with (Z ++ bcells Z O r).
    change (bcells Z O (true :: r)) with (O ++ bcells Z O r).
    rewrite <- !app_assoc. apply Hcarry, Hp.
Qed.

(** the top recurs within a phase *)
Lemma top_reached : forall v x p, BInv (x, p) -> 2 ^ length x - bval x <= v ->
  exists n, alltrue (fst (biterP (x, p) n)) = true /\ snd (biterP (x, p) n) = p
            /\ BInv (biterP (x, p) n).
Proof.
  induction v as [|v IH]; intros x p Hs Hv.
  - pose proof (bval_lt x). lia.
  - destruct (alltrue x) eqn:E.
    + exists 0. cbn. split; [exact E | split; [reflexivity | exact Hs]].
    + destruct (binc_val x E) as [H1 H2].
      assert (Hi : BInv (binc x, p)) by (destruct Hs; split; [rewrite H2|]; assumption).
      destruct (IH (binc x) p Hi) as (n & Hn).
      * rewrite H1, H2. lia.
      * exists (S n). cbn [biterP bsucc]. rewrite E. exact Hn.
Qed.

Fixpoint nxtB_iter (d p : nat) : nat :=
  match d with 0 => p | S d' => nxtB_iter d' (nxtB p) end.

Lemma top_phase : forall d s, BInv s ->
  exists n, alltrue (fst (biterP s n)) = true /\ snd (biterP s n) = nxtB_iter d (snd s)
            /\ BInv (biterP s n).
Proof.
  induction d as [|d IH]; intros [x p] Hs.
  - destruct (top_reached (2 ^ length x - bval x) x p Hs (le_n _)) as (n & Hn).
    exists n. exact Hn.
  - destruct (top_reached (2 ^ length x - bval x) x p Hs (le_n _)) as (n1 & Ht1 & Hp1 & Hi1).
    pose proof (bsucc_inv _ Hi1) as Hi2.
    destruct (IH (bsucc (biterP (x, p) n1)) Hi2) as (n2 & Ht2 & Hp2 & Hi3).
    exists (n1 + S n2). rewrite biterP_add. cbn [biterP].
    split; [exact Ht2|]. split; [|exact Hi3].
    rewrite Hp2. destruct (biterP (x, p) n1) as [y q] eqn:Ey. cbn [fst snd] in Ht1, Hp1.
    cbn [bsucc snd nxtB_iter]. rewrite Ht1, Hp1. reflexivity.
Qed.

Lemma nxtB_iter_mod : forall d p, p < P -> nxtB_iter d p = (p + d) mod P.
Proof.
  induction d as [|d IH]; intros p Hp.
  - rewrite Nat.add_0_r, Nat.mod_small by exact Hp. reflexivity.
  - cbn [nxtB_iter]. rewrite IH by (apply nxtB_lt, Hp).
    unfold nxtB. destruct (Nat.eqb_spec (S p) P) as [E|E].
    + rewrite <- E. replace (p + S d) with (d + 1 * S p) by lia.
      rewrite Nat.Div0.mod_add. reflexivity.
    + replace (p + S d) with (S p + d) by lia. reflexivity.
Qed.

Theorem top_cofinal : forall s N pt, BInv s -> pt < P ->
  exists n, N <= n /\ alltrue (fst (biterP s n)) = true /\ snd (biterP s n) = pt
            /\ BInv (biterP s n).
Proof.
  intros s N pt Hs Hpt.
  pose proof (biterP_inv N s Hs) as HsN.
  destruct (biterP s N) as [x p] eqn:EN.
  assert (Hp : p < P) by exact (proj2 HsN).
  destruct (top_phase (pt + P - p) (x, p) HsN) as (n & Ht & Hph & Hi).
  exists (N + n). rewrite biterP_add, EN. split; [lia|]. split; [exact Ht|]. split; [|exact Hi].
  rewrite Hph. cbn [snd]. rewrite nxtB_iter_mod by exact Hp.
  replace (p + (pt + P - p)) with (pt + 1 * P) by lia.
  rewrite Nat.Div0.mod_add, Nat.mod_small by lia. reflexivity.
Qed.

Variable x0 : list bool.
Variable p0 : nat.
Hypothesis Hinv0 : BInv (x0, p0).

Definition bCf (n : nat) : cconf := let '(x, p) := biterP (x0, p0) n in pbcfg p x.

Lemma bCf_lap : forall n, exists m c',
  csteps tm m (bCf n) = Some c' /\ lift c' = lift (bCf (S n)) /\ 0 < m.
Proof.
  intros n.
  pose proof (biterP_inv n (x0, p0) Hinv0) as Hi.
  pose proof (bstep _ Hi) as H.
  destruct (reach1_csteps tm _ _ H) as (m & c' & Hm & Hc & Hl).
  exists m, c'. unfold bCf. replace (S n) with (n + 1) by lia. rewrite biterP_add.
  cbn [biterP]. split; [exact Hc | split; [exact Hl | exact Hm]].
Qed.

Lemma bCf_fire : forall t N, ~ In t pins ->
  exists n k c', N <= n /\ csteps tm k (bCf n) = Some c' /\ cinstr c' = t.
Proof.
  intros t N Hnp.
  destruct (Hfire t Hnp) as (pt & Hpt & Hf).
  destruct (top_cofinal (x0, p0) N pt Hinv0 Hpt) as (n & HN & Ht & Hph & Hi).
  exists n. unfold bCf.
  destruct (biterP (x0, p0) n) as [x p] eqn:E. cbn [fst snd] in Ht, Hph. subst p.
  rewrite (alltrue_eq x Ht). destruct Hi as [Hl _].
  unfold pbcfg. rewrite bcells_rep_true.
  destruct (Hf (length x) Hl) as (k & c' & Hc & Hct).
  exists k, c'. split; [exact HN | split; assumption].
Qed.

Theorem phbin_neverqhtr : forall t0,
  stepn tm t0 InitES = Some (lift (pbcfg p0 x0)) ->
  NeverQuasiHaltsTr tm0.
Proof.
  intros t0 Hboot.
  apply (glue_neverqhtrN tm0 pins bCf).
  - exists t0. exact Hboot.
  - exact bCf_lap.
  - intros t Hnp N. exact (bCf_fire t N Hnp).
Qed.

Lemma bCf_reach : forall d n,
  exists Tm, stepn tm Tm (lift (bCf n)) = Some (lift (bCf (n + d))).
Proof.
  induction d; intros n.
  - exists 0. rewrite Nat.add_0_r. reflexivity.
  - destruct (IHd n) as (Tm & HT).
    destruct (bCf_lap (n + d)) as (m & c' & Hm & Hl & _).
    exists (Tm + m). rewrite stepn_add, HT.
    replace (n + S d) with (S (n + d)) by lia.
    rewrite <- Hl. apply csteps_lift. exact Hm.
Qed.

Lemma bCf_fire_every : forall t, ~ In t pins -> forall n,
  exists k c', csteps tm k (bCf n) = Some c' /\ cinstr c' = t.
Proof.
  intros t Hnp n.
  destruct (bCf_fire t n Hnp) as (m & k & c' & Hm & Hk & Hc').
  destruct (bCf_reach (m - n) n) as (Tm & HT).
  replace (n + (m - n)) with m in HT by lia.
  assert (Hs : stepn tm (Tm + k) (lift (bCf n)) = Some (lift c')).
  { rewrite stepn_add, HT. apply csteps_lift. exact Hk. }
  destruct (stepn_csteps_at tm (Tm + k) (bCf n) (lift c') Hs) as (c'' & Hc'' & Hl').
  exists (Tm + k), c''. split; [exact Hc''|].
  rewrite <- cinstr_lift, Hl', cinstr_lift. exact Hc'.
Qed.

Theorem phbin_qhtr : forall t0 B,
  stepn tm0 t0 InitES = Some (lift (pbcfg p0 x0)) ->
  existsb (fun tg => cfires tm0 CTape.c0 t0 tg) pins = true ->
  (t0 <=? B) = true ->
  NonHalt tm0 /\ QHBoundTr B tm0 /\ QuasiHaltsTr tm0.
Proof.
  intros t0 B Hboot Hwit Hle.
  apply (lap_qh_stage tm0 pins (fun p => bCf (Nat.pred (Pos.to_nat p)))
           1%positive t0 B).
  - exact Hboot.
  - intros p _.
    destruct (bCf_lap (Nat.pred (Pos.to_nat p))) as (m & c' & Hrun & Hl & Hm).
    exists m, c'. split; [exact Hrun | split; [|exact Hm]].
    rewrite Hl, Pos2Nat.inj_succ.
    replace (S (Nat.pred (Pos.to_nat p))) with (Pos.to_nat p)
      by (pose proof (Pos2Nat.is_pos p); lia).
    reflexivity.
  - intros t Hnp p _. exact (bCf_fire_every t Hnp (Nat.pred (Pos.to_nat p))).
  - exact Hwit.
  - exact Hle.
Qed.

End PhBin.
