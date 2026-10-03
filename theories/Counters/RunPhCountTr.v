(** * Counters.RunPhCountTr: a binary counter beside a marker RUN, the run
    lengthening as the counter narrows, with PHASES between refills
    (SCOPING_INSTR 7.4.LE9).

    [0RB1LA_1LC1RD_1RB0LD_1RB0LA] (LE7's "tail grows") reads, from its
    anchor, [x ++ M ++ R^m ++ suf_p]: a binary counter [x] (LSB at the head)
    over two words, a marker [M], a run of [m] words [R] and a far-end
    suffix of phase [p]:

      (x, m, p)          -> (x + 1, m, p)                x not all-top
      (top^(k+1), m, p)  -> (0^k, m + 1, p)              the top digit joins the run
      ([], m, p)         -> (0^(ca_p + m) ++ zt_p, 0, p + 1 mod P)   the refill

    LE4's marker run ([LadderCheckRun2Tr]) with a phase index: here the
    suffix alternates [[]] / [[1]] and the two refills differ.  The board is
    generic, every arm a [Reach1] fact (any [LadderNest] arm family): one
    carry, one narrowing (both against any tail), one refill per phase.
    Liveness: within a phase [(length x, value)] runs down lexicographically
    to the empty counter; the refills recur and the phases cycle; each
    instruction is read off one phase's refills.  Never-QH and QH closers.

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

Section RunPh.

Variable tm0  : TM.
Variable pins : list Instr.
Local Notation tm := (tm_wrap_trs tm0 pins).

Variable P    : nat.
Variable mk   : list Sym -> cconf.
Variables Z O M R : list Sym.
Variable suf  : nat -> list Sym.
Variable ca   : nat -> nat.
Variable zt   : nat -> list bool.

Definition rcfg (x : list bool) (m p : nat) : cconf :=
  mk (bcells Z O x ++ M ++ rep R m ++ suf p).

Definition RSt : Type := (list bool * nat * nat)%type.

Definition rsucc (s : RSt) : RSt :=
  let '(x, m, p) := s in
  match x with
  | [] => (repeat false (ca p + m) ++ zt p, 0, nxtB P p)
  | _ => if alltrue x then (repeat false (pred (length x)), S m, p) else (binc x, m, p)
  end.

Fixpoint riter (s : RSt) (n : nat) : RSt :=
  match n with 0 => s | S n' => riter (rsucc s) n' end.

Lemma riter_add : forall n1 n2 s, riter s (n1 + n2) = riter (riter s n1) n2.
Proof. induction n1 as [|n1 IH]; intros n2 s; [reflexivity | apply IH]. Qed.

Definition RInv (s : RSt) : Prop := let '(_, _, p) := s in p < P.

Hypothesis HP : 0 < P.
Hypothesis Hcarry : forall k X,
  Reach1 tm (mk (rep O k ++ Z ++ X)) (mk (rep Z k ++ O ++ X)).
Hypothesis Hnarrow : forall k X,
  Reach1 tm (mk (rep O k ++ O ++ M ++ X)) (mk (rep Z k ++ M ++ R ++ X)).
Hypothesis Hrefill : forall p m, p < P ->
  Reach1 tm (mk (M ++ rep R m ++ suf p))
            (mk (rep Z (ca p + m) ++ bcells Z O (zt p) ++ M ++ suf (nxtB P p))).
Hypothesis Hfire : forall t, ~ In t pins -> exists p, p < P /\
  forall m, Fires tm (mk (M ++ rep R m ++ suf p)) t.

Lemma rsucc_inv : forall s, RInv s -> RInv (rsucc s).
Proof.
  intros [[x m] p] Hp. cbn [RInv] in Hp. destruct x as [|b r]; cbn [rsucc RInv].
  - apply nxtB_lt; assumption.
  - destruct (alltrue (b :: r)); exact Hp.
Qed.

Lemma riter_inv : forall n s, RInv s -> RInv (riter s n).
Proof. induction n as [|n IH]; intros s Hs; [exact Hs|]. apply IH, rsucc_inv, Hs. Qed.

Lemma runph_step : forall x m p, p < P ->
  Reach1 tm (rcfg x m p) (let '(x', m', p') := rsucc (x, m, p) in rcfg x' m' p').
Proof.
  intros x m p Hp. destruct x as [|b r] eqn:Ex.
  - cbn [rsucc]. unfold rcfg. rewrite bcells_app, bcells_rep_false.
    change (bcells Z O []) with (@nil Sym). change (rep R 0) with (@nil Sym).
    rewrite <- !app_assoc. cbn [app]. apply (Hrefill p m Hp).
  - cbn [rsucc]. destruct (alltrue (b :: r)) eqn:E.
    + pose proof (alltrue_eq _ E) as Hx. cbn [length] in Hx.
      cbn [length pred]. unfold rcfg. rewrite Hx.
      rewrite bcells_rep_true, bcells_rep_false.
      replace (rep O (S (length r))) with (rep O (length r) ++ O) by (symmetry; apply rep_S_r).
      change (rep R (S m)) with (R ++ rep R m). rewrite <- !app_assoc.
      exact (Hnarrow (length r) (rep R m ++ suf p)).
    + destruct (ttdecomp (b :: r)) as [(k & r' & Ex') | (k & Ex')].
      2:{ rewrite Ex', alltrue_repeat in E. discriminate. }
      rewrite Ex', binc_int. unfold rcfg.
      rewrite !bcells_tt, !bcells_ff.
      change (bcells Z O (false :: r')) with (Z ++ bcells Z O r').
      change (bcells Z O (true :: r')) with (O ++ bcells Z O r').
      rewrite <- !app_assoc. apply Hcarry.
Qed.

(** within a phase the empty counter is reached *)
Lemma empty_reached : forall l v x m p, length x <= l -> 2 ^ length x - bval x <= v -> p < P ->
  exists n, fst (fst (riter (x, m, p) n)) = [] /\ snd (riter (x, m, p) n) = p.
Proof.
  induction l as [|l IHl]; intros v x m p Hl Hv Hp.
  - destruct x; [|cbn in Hl; lia]. exists 0. split; reflexivity.
  - revert x m Hl Hv. induction v as [|v IHv]; intros x m Hl Hv.
    + pose proof (bval_lt x). lia.
    + destruct x as [|b r]; [exists 0; split; reflexivity|].
      destruct (alltrue (b :: r)) eqn:E.
      * assert (Hlen : length (repeat false (pred (length (b :: r)))) <= l)
          by (rewrite repeat_length; cbn [length pred] in *; lia).
        destruct (IHl _ _ (S m) p Hlen (le_n _) Hp) as (n & Hn).
        exists (S n). cbn [riter rsucc]. rewrite E. exact Hn.
      * destruct (binc_val (b :: r) E) as [H1 H2].
        destruct (IHv (binc (b :: r)) m) as (n & Hn).
        -- rewrite H2. exact Hl.
        -- rewrite H1, H2. lia.
        -- exists (S n). cbn [riter rsucc]. rewrite E. exact Hn.
Qed.

Lemma empty_reached_s : forall s, RInv s ->
  exists n, fst (fst (riter s n)) = [] /\ snd (riter s n) = snd s.
Proof.
  intros [[x m] p] Hp.
  exact (empty_reached (length x) (2 ^ length x - bval x) x m p (le_n _) (le_n _) Hp).
Qed.

Fixpoint nxt_iterR (d p : nat) : nat :=
  match d with 0 => p | S d' => nxt_iterR d' (nxtB P p) end.

Lemma empty_phase : forall d s, RInv s ->
  exists n, fst (fst (riter s n)) = [] /\ snd (riter s n) = nxt_iterR d (snd s).
Proof.
  induction d as [|d IH]; intros s Hs.
  - exact (empty_reached_s s Hs).
  - destruct (empty_reached_s s Hs) as (n1 & He1 & Hp1).
    pose proof (riter_inv n1 s Hs) as Hi1.
    pose proof (rsucc_inv _ Hi1) as Hi2.
    destruct (IH (rsucc (riter s n1)) Hi2) as (n2 & He2 & Hp2).
    exists (n1 + S n2). rewrite riter_add. cbn [riter].
    split; [exact He2|]. rewrite Hp2.
    destruct (riter s n1) as [[y m'] q] eqn:Ey. cbn [fst snd] in He1, Hp1. subst y q.
    reflexivity.
Qed.

Lemma nxt_iterR_mod : forall d p, p < P -> nxt_iterR d p = (p + d) mod P.
Proof.
  induction d as [|d IH]; intros p Hp.
  - rewrite Nat.add_0_r, Nat.mod_small by exact Hp. reflexivity.
  - cbn [nxt_iterR]. rewrite IH by (apply nxtB_lt; assumption).
    unfold nxtB. destruct (Nat.eqb_spec (S p) P) as [E|E].
    + rewrite <- E. replace (p + S d) with (d + 1 * S p) by lia.
      rewrite Nat.Div0.mod_add. reflexivity.
    + replace (p + S d) with (S p + d) by lia. reflexivity.
Qed.

Theorem empty_cofinal : forall s N pt, RInv s -> pt < P ->
  exists n, N <= n /\ fst (fst (riter s n)) = [] /\ snd (riter s n) = pt.
Proof.
  intros s N pt Hs Hpt.
  pose proof (riter_inv N s Hs) as HsN.
  destruct (riter s N) as [[x m] p] eqn:EN.
  assert (Hp : p < P) by exact HsN.
  destruct (empty_phase (pt + P - p) (x, m, p) HsN) as (n & He & Hph).
  exists (N + n). rewrite riter_add, EN. split; [lia|]. split; [exact He|].
  rewrite Hph. cbn [snd]. rewrite nxt_iterR_mod by exact Hp.
  replace (p + (pt + P - p)) with (pt + 1 * P) by lia.
  rewrite Nat.Div0.mod_add, Nat.mod_small by lia. reflexivity.
Qed.

Variable x0 : list bool.
Variables m0 p0 : nat.
Hypothesis Hp0 : p0 < P.

Definition rCf (n : nat) : cconf := let '(x, m, p) := riter (x0, m0, p0) n in rcfg x m p.

Lemma rCf_lap : forall n, exists k c',
  csteps tm k (rCf n) = Some c' /\ lift c' = lift (rCf (S n)) /\ 0 < k.
Proof.
  intros n.
  pose proof (riter_inv n (x0, m0, p0) Hp0) as Hi.
  unfold rCf. replace (S n) with (n + 1) by lia. rewrite riter_add. cbn [riter].
  destruct (riter (x0, m0, p0) n) as [[x m] p] eqn:E.
  pose proof (runph_step x m p Hi) as H.
  destruct (reach1_csteps tm _ _ H) as (k & c' & Hk & Hc & Hl).
  exists k, c'. split; [exact Hc | split; [|exact Hk]].
  rewrite Hl. destruct (rsucc (x, m, p)) as [[x' m'] p']. reflexivity.
Qed.

Lemma rCf_fire : forall t N, ~ In t pins ->
  exists n k c', N <= n /\ csteps tm k (rCf n) = Some c' /\ cinstr c' = t.
Proof.
  intros t N Hnp.
  destruct (Hfire t Hnp) as (pt & Hpt & Hf).
  destruct (empty_cofinal (x0, m0, p0) N pt Hp0 Hpt) as (n & HN & He & Hph).
  exists n. unfold rCf.
  destruct (riter (x0, m0, p0) n) as [[x m] p] eqn:E. cbn [fst snd] in He, Hph. subst x p.
  unfold rcfg. cbn [bcells flat_map app].
  destruct (Hf m) as (k & c' & Hc & Hct).
  exists k, c'. split; [exact HN | split; assumption].
Qed.

Theorem runph_neverqhtr : forall t0,
  stepn tm t0 InitES = Some (lift (rcfg x0 m0 p0)) ->
  NeverQuasiHaltsTr tm0.
Proof.
  intros t0 Hboot.
  apply (glue_neverqhtrN tm0 pins rCf).
  - exists t0. exact Hboot.
  - exact rCf_lap.
  - intros t Hnp N. exact (rCf_fire t N Hnp).
Qed.

Lemma rCf_reach : forall d n,
  exists Tm, stepn tm Tm (lift (rCf n)) = Some (lift (rCf (n + d))).
Proof.
  induction d; intros n.
  - exists 0. rewrite Nat.add_0_r. reflexivity.
  - destruct (IHd n) as (Tm & HT).
    destruct (rCf_lap (n + d)) as (m & c' & Hm & Hl & _).
    exists (Tm + m). rewrite stepn_add, HT.
    replace (n + S d) with (S (n + d)) by lia.
    rewrite <- Hl. apply csteps_lift. exact Hm.
Qed.

Lemma rCf_fire_every : forall t, ~ In t pins -> forall n,
  exists k c', csteps tm k (rCf n) = Some c' /\ cinstr c' = t.
Proof.
  intros t Hnp n.
  destruct (rCf_fire t n Hnp) as (m & k & c' & Hm & Hk & Hc').
  destruct (rCf_reach (m - n) n) as (Tm & HT).
  replace (n + (m - n)) with m in HT by lia.
  assert (Hs : stepn tm (Tm + k) (lift (rCf n)) = Some (lift c')).
  { rewrite stepn_add, HT. apply csteps_lift. exact Hk. }
  destruct (stepn_csteps_at tm (Tm + k) (rCf n) (lift c') Hs) as (c'' & Hc'' & Hl').
  exists (Tm + k), c''. split; [exact Hc''|].
  rewrite <- cinstr_lift, Hl', cinstr_lift. exact Hc'.
Qed.

Theorem runph_qhtr : forall t0 B,
  stepn tm0 t0 InitES = Some (lift (rcfg x0 m0 p0)) ->
  existsb (fun tg => cfires tm0 CTape.c0 t0 tg) pins = true ->
  (t0 <=? B) = true ->
  NonHalt tm0 /\ QHBoundTr B tm0 /\ QuasiHaltsTr tm0.
Proof.
  intros t0 B Hboot Hwit Hle.
  apply (lap_qh_stage tm0 pins (fun p => rCf (Nat.pred (Pos.to_nat p)))
           1%positive t0 B).
  - exact Hboot.
  - intros p _.
    destruct (rCf_lap (Nat.pred (Pos.to_nat p))) as (m & c' & Hrun & Hl & Hm).
    exists m, c'. split; [exact Hrun | split; [|exact Hm]].
    rewrite Hl, Pos2Nat.inj_succ.
    replace (S (Nat.pred (Pos.to_nat p))) with (Pos.to_nat p)
      by (pose proof (Pos2Nat.is_pos p); lia).
    reflexivity.
  - intros t Hnp p _. exact (rCf_fire_every t Hnp (Nat.pred (Pos.to_nat p))).
  - exact Hwit.
  - exact Hle.
Qed.

End RunPh.
