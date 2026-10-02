(** * Checkers.LadderCheckZeckDwTr: the Zeckendorf countdown whose bottom
    WIDENS by more than one digit (SCOPING_INSTR 7.4.LE6).

    [LadderCheckZeckDTr] with one change: at [x = 0] the counter refills to
    the largest string [dw] digits wider than [LadderCheckZeckDTr]'s, i.e.
    [false^m -> alt (m + dw)] on token lists (LE6's survey: 21 rows whose
    tape grows two cells per factor phi^2, [dw = 1]).  The interior and end
    classes, the cells and the liveness measure are [LadderCheckZeckDTr]'s;
    only the bottom's right-hand side changes, to
    [BR dw u = PR ((u + dw) mod 2) ++ B^((u + dw) / 2)].

    Nothing landed is modified.  Axiom footprint: [functional_extensionality_dep],
    via [CTape.lift]. *)
From Coq Require Import Arith Lia Bool List PArith Wf_nat.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape ClosureTr.
From BBB4.Counters Require Import WTape LapCertGlueLift.
From BBB4.Checkers Require Import WrapTr LapDecider LadderKernel LadderFam LadderCheck LadderCheckTr LadderNest LadderCheckNestTr TCyclerQHTr.
From BBB4.Checkers Require Import LadderCheckZeckDTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
From BBB4.Counters Require Import LapGlueTr.
From BBB4.CensusTr Require Import TNF_QHTr QHConveyorTr.
Import ListNotations.

(** ** 1. The step with a wider bottom *)

Definition dstepw (dw : nat) (t : list bool) : list bool :=
  match after1 t with Some _ => dstep t | None => alt (lz t + dw) end.

Fixpoint diterw (dw : nat) (t : list bool) (n : nat) : list bool :=
  match n with O => t | S n' => diterw dw (dstepw dw t) n' end.

Lemma diterw_add : forall dw n1 n2 t, diterw dw t (n1 + n2) = diterw dw (diterw dw t n1) n2.
Proof. intros dw. induction n1 as [|n1 IH]; intros n2 t; [reflexivity | apply IH]. Qed.

Definition BRt (dw u : nat) : list bool :=
  PRt ((u + dw) mod 2) ++ repeat true ((u + dw) / 2).

Lemma dstepw_int : forall dw u k r, u < 2 ->
  dstepw dw (PLt u ++ repeat false (2 * k) ++ true :: r)
  = PRt u ++ repeat true k ++ false :: r.
Proof.
  intros dw u k r Hu. unfold dstepw.
  rewrite PLt_ff, after_ff by exact Hu. cbn [after1].
  rewrite <- PLt_ff by exact Hu. apply dstep_int, Hu.
Qed.

Lemma dstepw_bot : forall dw u k, u < 2 ->
  dstepw dw (PLt u ++ repeat false (2 * k)) = BRt dw u ++ repeat true k.
Proof.
  intros dw u k Hu. unfold dstepw.
  pose proof (PLt_ff u k [] Hu) as H. rewrite !app_nil_r in H. rewrite H.
  rewrite <- (app_nil_r (repeat false (u + 2 * k))), after_ff, lz_ff. cbn [after1 lz].
  replace (u + 2 * k + 0 + dw) with ((u + dw) mod 2 + 2 * (k + (u + dw) / 2)).
  - rewrite alt_split by (apply Nat.mod_upper_bound; lia).
    unfold BRt. rewrite <- app_assoc, <- repeat_app. f_equal. f_equal. lia.
  - pose proof (Nat.div_mod_eq (u + dw) 2). lia.
Qed.

Lemma dstepw_nonempty : forall dw t, dstepw dw t <> [].
Proof.
  intros dw t. unfold dstepw. destruct (after1 t); [apply dstep_nonempty|].
  destruct (split_n (lz t + dw)) as (u & k & Hu & ->).
  rewrite alt_split by exact Hu. destruct u as [|[|u]]; cbn; discriminate.
Qed.

Lemma diterw_nonempty : forall dw n t, t <> [] -> diterw dw t n <> [].
Proof.
  intros dw. induction n as [|n IH]; intros t Ht; [exact Ht|]. cbn. apply IH, dstepw_nonempty.
Qed.

Lemma botw_reach : forall dw t, t <> [] -> exists j, after1 (diterw dw t j) = None.
Proof.
  intros dw t. remember (bval (tdig t)) as v eqn:Ev. revert t Ev.
  induction v as [v IH] using lt_wf_ind. intros t Ev Ht.
  destruct (after1 t) as [r|] eqn:Ea.
  - assert (Hs : dstepw dw t = dstep t) by (unfold dstepw; rewrite Ea; reflexivity).
    destruct (IH (bval (tdig (dstepw dw t)))) with (t := dstepw dw t) as (j & Hj).
    + rewrite Ev, Hs. exact (dstep_dec t r Ea).
    + reflexivity.
    + apply dstepw_nonempty.
    + exists (S j). exact Hj.
  - exists 0. exact Ea.
Qed.

Lemma botsw_cofinal : forall dw t0 N, t0 <> [] ->
  exists n, N <= n /\
    exists u k, u < 2 /\ (u = 0 -> 0 < k) /\ diterw dw t0 n = PLt u ++ repeat false (2 * k).
Proof.
  intros dw t0 N H0.
  destruct (botw_reach dw (diterw dw t0 N) (diterw_nonempty dw N t0 H0)) as (j & Hj).
  exists (N + j). split; [lia|]. rewrite diterw_add.
  destruct (dclass (diterw dw (diterw dw t0 N) j) (diterw_nonempty dw j _ (diterw_nonempty dw N t0 H0)))
    as [(u & k & r & Hu & He) | Hb]; [|exact Hb].
  exfalso. rewrite He, PLt_ff, after_ff in Hj by exact Hu. discriminate.
Qed.

Section CellsDw.
Variable F : Fam.
Variables A B T : list Sym.

Definition zdBR (dw u : nat) : list Sym := tcells A B (BRt dw u).

Lemma zd_botw_r : forall dw u k m st,
  zdcells F A B T (BRt dw u ++ repeat true (k + st * m))
    = sden [] m (zdside F (zdBR dw u) B k st T).
Proof.
  intros dw u k m st. rewrite zdside_den. unfold zdcells, zdBR.
  rewrite !tcells_app, tcells_tt.
  rewrite <- !app_assoc, !app_nil_r. reflexivity.
Qed.
End CellsDw.

(** ** 2. The board *)

Section BoardZDwTr.

Variable tm0   : TM.
Variable pins  : list Instr.
Local Notation tm := (tm_wrap_trs tm0 pins).

Variable F     : Fam.
Variables A B T : list Sym.
Variable AI    : nat -> nat -> LRule.   (** interior: kind, index *)
Variable N0i sti : nat.
Variable AE    : nat -> nat -> LRule.   (** end: kind, index *)
Variable N0e ste : nat.
Variable AB    : nat -> nat -> LRule.   (** bottom: kind, index *)
Variable N0b stb : nat.
Variable rsv   : list LRule.
Variable vsegs : nat -> nat -> Instr -> list nseg.
Variable visI  : nat -> nat -> Instr -> list lstep.
Variable dw    : nat.         (** the bottom widens by [dw + 1] digits *)
Variable t0    : list bool.

Hypothesis Ht0 : t0 <> [].

Hypothesis Hsti : 0 < sti.
Hypothesis HAIS : forall i r, i < 2 -> r < N0i + sti ->
  ReachL tm (negb (fm_left F)) (fm_left F) (lr_lhs (AI i r)) (lr_rhs (AI i r)).
Hypothesis HAIL : forall i r, i < 2 -> r < N0i + sti ->
  lr_lhs (AI i r) = cls_conf F (zdside F (zdPL A i) (A ++ A) r (astride N0i sti r) B).
Hypothesis HAIR : forall i r, i < 2 -> r < N0i + sti ->
  lr_rhs (AI i r) = cls_conf F (zdside F (zdPR A B i) B r (astride N0i sti r) A).

Hypothesis Hste : 0 < ste.
Hypothesis HAES : forall i r, i < 2 -> r < N0e + ste ->
  ReachL tm true true (lr_lhs (AE i r)) (lr_rhs (AE i r)).
Hypothesis HAEL : forall i r, i < 2 -> r < N0e + ste ->
  lr_lhs (AE i r) = cls_conf F (zdside F (zdPL A i) (A ++ A) r (astride N0e ste r) (B ++ T)).
Hypothesis HAER : forall i r, i < 2 -> r < N0e + ste ->
  lr_rhs (AE i r) = cls_conf F (zdside F (zdPR A B i) B r (astride N0e ste r) (A ++ T)).

Hypothesis Hstb : 0 < stb.
Hypothesis HN0b : 0 < N0b.
Hypothesis HABS : forall i r, i < 2 -> r < N0b + stb -> (i = 0 -> 0 < r) ->
  ReachL tm true true (lr_lhs (AB i r)) (lr_rhs (AB i r)).
Hypothesis HABL : forall i r, i < 2 -> r < N0b + stb -> (i = 0 -> 0 < r) ->
  lr_lhs (AB i r) = cls_conf F (zdside F (zdPL A i) (A ++ A) r (astride N0b stb r) T).
Hypothesis HABR : forall i r, i < 2 -> r < N0b + stb -> (i = 0 -> 0 < r) ->
  lr_rhs (AB i r) = cls_conf F (zdside F (zdBR A B dw i) B r (astride N0b stb r) T).

Hypothesis Hrsv : Forall (RuleSound tm false false) rsv.
Hypothesis Hfire : forall i r t, ~ In t pins -> i < 2 -> r < N0b + stb ->
  (i = 0 -> 0 < r) ->
  nfire tm true true rsv (vsegs i r t) (visI i r t) (lr_lhs (AB i r)) = Some t.

Local Notation Cf := (fun n => zdcfg F A B T (diterw dw t0 n)).

(** the bottom arm serving a bottom list, and its configuration *)
Lemma bot_armZDw : forall i k, i < 2 -> (i = 0 -> 0 < k) ->
  let r := aoff N0b stb k in
  r < N0b + stb /\ (i = 0 -> 0 < r)
  /\ zdcfg F A B T (PLt i ++ repeat false (2 * k))
     = cden [] [] (acnt N0b stb k) (lr_lhs (AB i r)).
Proof.
  intros i k Hi Hk0 r.
  assert (Hrlt : r < N0b + stb) by (apply arm_index_lt; exact Hstb).
  assert (Hr0 : i = 0 -> 0 < r).
  { intros ->. apply arm_index_pos; [exact HN0b | exact (Hk0 eq_refl)]. }
  assert (Hk : r + astride N0b stb r * acnt N0b stb k = k)
    by (apply arm_index; exact Hstb).
  split; [exact Hrlt | split; [exact Hr0|]].
  rewrite (HABL i r Hi Hrlt Hr0).
  assert (Hc : zdcells F A B T (PLt i ++ repeat false (2 * k))
                 = sden [] (acnt N0b stb k) (zdside F (zdPL A i) (A ++ A) r (astride N0b stb r) T)).
  { rewrite <- Hk at 1. apply zd_bot_l. exact Hi. }
  pose proof (cden_zd F A B T _ [] _ _ Hc) as H.
  rewrite tailL_nil, tailR_nil in H. symmetry. exact H.
Qed.

Lemma board_armZDw : forall t, t <> [] ->
  exists Ar el er X n,
    ReachL tm el er (lr_lhs Ar) (lr_rhs Ar)
    /\ (el = true -> tailL F X = []) /\ (er = true -> tailR F X = [])
    /\ zdcfg F A B T t = cden (tailL F X) (tailR F X) n (lr_lhs Ar)
    /\ zdcfg F A B T (dstepw dw t) = cden (tailL F X) (tailR F X) n (lr_rhs Ar).
Proof.
  intros t Ht.
  destruct (dclass t Ht) as [(i & k & r0 & Hi & ->) | (i & k & Hi & Hk0 & ->)].
  - destruct r0 as [|b r1].
    + (* the end *)
      remember (aoff N0e ste k) as r eqn:Er.
      assert (Hrlt : r < N0e + ste) by (subst r; apply arm_index_lt; exact Hste).
      assert (Hk : r + astride N0e ste r * acnt N0e ste k = k)
        by (subst r; apply arm_index; exact Hste).
      exists (AE i r), true, true, [], (acnt N0e ste k).
      split; [|split; [|split; [|split]]].
      * exact (HAES i r Hi Hrlt).
      * intros _; apply tailL_nil.
      * intros _; apply tailR_nil.
      * rewrite (HAEL i r Hi Hrlt). symmetry. apply cden_zd.
        rewrite <- Hk at 1. apply zd_end_l. exact Hi.
      * rewrite dstepw_int by exact Hi. rewrite (HAER i r Hi Hrlt). symmetry.
        apply cden_zd. rewrite <- Hk at 1. apply zd_end_r. exact Hi.
    + (* the interior *)
      remember (aoff N0i sti k) as r eqn:Er.
      assert (Hrlt : r < N0i + sti) by (subst r; apply arm_index_lt; exact Hsti).
      assert (Hk : r + astride N0i sti r * acnt N0i sti k = k)
        by (subst r; apply arm_index; exact Hsti).
      exists (AI i r), (negb (fm_left F)), (fm_left F),
        (tcells A B (b :: r1) ++ T), (acnt N0i sti k).
      split; [|split; [|split; [|split]]].
      * exact (HAIS i r Hi Hrlt).
      * intros He. unfold tailL. destruct (fm_left F); [discriminate|reflexivity].
      * intros He. unfold tailR. rewrite He. reflexivity.
      * rewrite (HAIL i r Hi Hrlt). symmetry. apply cden_zd.
        rewrite <- Hk at 1. apply zd_int_l. exact Hi.
      * rewrite dstepw_int by exact Hi. rewrite (HAIR i r Hi Hrlt). symmetry.
        apply cden_zd. rewrite <- Hk at 1. apply zd_int_r. exact Hi.
  - (* the bottom *)
    destruct (bot_armZDw i k Hi Hk0) as (Hrlt & Hr0 & Hden).
    set (r := aoff N0b stb k) in *.
    assert (Hk : r + astride N0b stb r * acnt N0b stb k = k)
      by (apply arm_index; exact Hstb).
    exists (AB i r), true, true, [], (acnt N0b stb k).
    split; [|split; [|split; [|split]]].
    + exact (HABS i r Hi Hrlt Hr0).
    + intros _; apply tailL_nil.
    + intros _; apply tailR_nil.
    + rewrite tailL_nil, tailR_nil. exact Hden.
    + rewrite dstepw_bot by exact Hi. rewrite (HABR i r Hi Hrlt Hr0). symmetry.
      apply cden_zd. rewrite <- Hk at 1. apply zd_botw_r.
Qed.

Lemma lapZDw : forall n, exists m c',
  0 < m /\ csteps tm m (Cf n) = Some c' /\ lift c' = lift (Cf (S n)).
Proof.
  intros n.
  destruct (board_armZDw _ (diterw_nonempty dw n t0 Ht0))
    as (Ar & el & er & X & k & HA & HL & HR & Hl & Hr).
  destruct (HA _ _ k HL HR) as (m & c' & Hm & Hc' & Hlc).
  exists m, c'. split; [exact Hm|]. split.
  - cbn beta. rewrite Hl. exact Hc'.
  - rewrite Hlc, <- Hr. cbn beta.
    replace (S n) with (n + 1) by lia. rewrite diterw_add. reflexivity.
Qed.

Lemma fireZDw : forall t N, ~ In t pins ->
  exists n k c', N <= n /\ csteps tm k (Cf n) = Some c' /\ cinstr c' = t.
Proof.
  intros t N Hnp.
  destruct (botsw_cofinal dw t0 N Ht0) as (n & HN & (i & k & Hi & Hk0 & Hx)).
  exists n. cbn beta. rewrite Hx.
  destruct (bot_armZDw i k Hi Hk0) as (Hrlt & Hr0 & Hden).
  set (r := aoff N0b stb k) in *.
  destruct (nfire_sound tm true true rsv (vsegs i r t) (visI i r t)
              (lr_lhs (AB i r)) t Hrsv (Hfire i r t Hnp Hi Hrlt Hr0)
              [] [] (acnt N0b stb k)
              (fun _ => eq_refl) (fun _ => eq_refl)) as (k' & c' & Hc' & Ht).
  exists k', c'. rewrite Hden. split; [exact HN | split; [exact Hc' | exact Ht]].
Qed.

Theorem boardZDw_neverqhtr : forall s0,
  stepn tm s0 InitES = Some (lift (zdcfg F A B T t0)) ->
  NeverQuasiHaltsTr tm0.
Proof.
  intros s0 Hboot.
  apply (glue_neverqhtrN tm0 pins Cf).
  - exists s0. exact Hboot.
  - intros n. destruct (lapZDw n) as (m & c' & Hm & Hrun & Hl).
    exists m, c'. split; [exact Hrun | split; [exact Hl | exact Hm]].
  - intros t Hnp N. exact (fireZDw t N Hnp).
Qed.

Lemma reachZDw : forall d n,
  exists Tm, stepn tm Tm (lift (Cf n)) = Some (lift (Cf (n + d))).
Proof.
  induction d; intros n.
  - exists 0. rewrite Nat.add_0_r. reflexivity.
  - destruct (IHd n) as (Tm & HT).
    destruct (lapZDw (n + d)) as (m & c' & _ & Hm & Hl).
    exists (Tm + m). rewrite stepn_add, HT.
    replace (n + S d) with (S (n + d)) by lia.
    rewrite <- Hl. apply csteps_lift. exact Hm.
Qed.

Lemma fire_everyZDw : forall t, ~ In t pins -> forall n,
  exists k c', csteps tm k (Cf n) = Some c' /\ cinstr c' = t.
Proof.
  intros t Hnp n.
  destruct (fireZDw t n Hnp) as (m & k & c' & Hm & Hk & Hc').
  destruct (reachZDw (m - n) n) as (Tm & HT).
  replace (n + (m - n)) with m in HT by lia.
  assert (Hs : stepn tm (Tm + k) (lift (Cf n)) = Some (lift c')).
  { rewrite stepn_add, HT. apply csteps_lift. exact Hk. }
  destruct (stepn_csteps_at tm (Tm + k) (Cf n) (lift c') Hs) as (c'' & Hc'' & Hl').
  exists (Tm + k), c''. split; [exact Hc''|].
  rewrite <- cinstr_lift, Hl', cinstr_lift. exact Hc'.
Qed.

Theorem boardZDw_qhtr : forall s0 Bd,
  stepn tm0 s0 InitES = Some (lift (zdcfg F A B T t0)) ->
  existsb (fun tg => cfires tm0 CTape.c0 s0 tg) pins = true ->
  (s0 <=? Bd) = true ->
  NonHalt tm0 /\ QHBoundTr Bd tm0 /\ QuasiHaltsTr tm0.
Proof.
  intros s0 Bd Hboot Hwit Hle.
  apply (lap_qh_stage tm0 pins (fun p => Cf (Nat.pred (Pos.to_nat p)))
           1%positive s0 Bd).
  - exact Hboot.
  - intros p _.
    destruct (lapZDw (Nat.pred (Pos.to_nat p))) as (m & c' & Hm & Hrun & Hl).
    exists m, c'. split; [exact Hrun | split; [|exact Hm]].
    rewrite Hl, Pos2Nat.inj_succ.
    replace (S (Nat.pred (Pos.to_nat p))) with (Pos.to_nat p)
      by (pose proof (Pos2Nat.is_pos p); lia).
    reflexivity.
  - intros t Hnp p _. exact (fire_everyZDw t Hnp (Nat.pred (Pos.to_nat p))).
  - exact Hwit.
  - exact Hle.
Qed.

End BoardZDwTr.
