(** * Checkers.LadderCheckZeckUTr: the Zeckendorf count UP inside a fixed
    width, overflowing to zero wider (SCOPING_INSTR 7.4.LE8).

    LE6's "Zeckendorf beside a run" rows (survey ratio phi per cell, still
    open after [LadderCheckZeckDTr]): read from the head, the tape is a
    Zeckendorf string over the token words [A] ([0]) and [B] ([10]) that
    keeps its HIGH ZERO digits on the tape.  It counts UP through every
    string of its width (the carry eats the top [A]s: LE6's "run that
    shortens at each top") and from the largest string of the width the
    machine writes a fixed string some digits wider: the zero string
    ([w = []]), or the successor [0^i 1] padded by zero digits.  On token
    lists ([false] = [0], [true] = [10]) this is [LadderCheckZeckDTr]'s step
    run BACKWARDS, with a new overflow:

      ustep (alt i ++ false :: rho) = false^i ++ true :: rho
      ustep (alt i)                 = false^(i + a) ++ w

    for a fixed [a] and token list [w] that add an EVEN number of digits
    ([a + |tdig w| = 1 + 2 dh]).

    ([alt (2k) = false :: true^k], [alt (2k+1) = true^(k+1)]).  With
    [i = u + 2k] every class is one side over the words [B] and [AA]
    ([PR 0 = A], [PR 1 = B], [PL 0 = []], [PL 1 = A]):

    - interior: [PR u B^k A X  ->  PL u (AA)^k B X], [X] opaque;
    - end:      [PR ue B^k A T ->  PL ue (AA)^k B T];
    - overflow: [PR u0 B^k T   ->  PL p (AA)^(k + c) W T]
                ([u0 + a = p + 2 c], [W] the cells of [w]).

    The digit count [length (tdig t)] is fixed by interior and end steps
    and grows by [2 dh] at an overflow, so its parity is invariant: an
    overflow list is always of kind [u0] and an end list of kind
    [ue = 1 - u0], and only those arms are asked for.

    Liveness: the binary value of the digit string RISES at every interior
    and end step ([LadderCheckZeckDTr.dstep_dec] read backwards) and stays
    below [2 ^ (digit count)], so overflows recur; the fires are read from
    the overflow arms.

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

(** ** 1. Token lists and the count up *)

Fixpoint ltt (t : list bool) : nat :=
  match t with true :: r => S (ltt r) | _ => 0 end.

Fixpoint dropt (t : list bool) : list bool :=
  match t with true :: r => dropt r | _ => t end.

Definition uafter (t : list bool) : list bool :=
  dropt (match t with false :: r => r | _ => t end).

Definition uidx (t : list bool) : nat :=
  match t with false :: r => 2 * ltt r | _ => 2 * ltt t - 1 end.

Section Step.
Variable a : nat.
Variable w : list bool.

Definition ustep (t : list bool) : list bool :=
  match uafter t with
  | false :: rho => repeat false (uidx t) ++ true :: rho
  | _ => repeat false (uidx t + a) ++ w
  end.

Fixpoint uiter (t : list bool) (n : nat) : list bool :=
  match n with O => t | S n' => uiter (ustep t) n' end.

Lemma uiter_add : forall n1 n2 t, uiter t (n1 + n2) = uiter (uiter t n1) n2.
Proof. induction n1 as [|n1 IH]; intros n2 t; [reflexivity | apply IH]. Qed.

Lemma ltt_tt : forall k r, ltt (repeat true k ++ false :: r) = k.
Proof. induction k as [|k IH]; intros r; [reflexivity|]. cbn. rewrite IH. reflexivity. Qed.

Lemma ltt_tt0 : forall k, ltt (repeat true k) = k.
Proof. induction k as [|k IH]; [reflexivity|]. cbn. rewrite IH. reflexivity. Qed.

Lemma dropt_tt : forall k r, dropt (repeat true k ++ r) = dropt r.
Proof. induction k as [|k IH]; intros r; [reflexivity|]. cbn. apply IH. Qed.

Lemma ustep_int : forall u k r, u < 2 ->
  ustep (PRt u ++ repeat true k ++ false :: r)
  = PLt u ++ repeat false (2 * k) ++ true :: r.
Proof.
  intros [|[|u]] k r Hu; [| |lia].
  - unfold ustep, uafter, uidx. cbn [PRt Nat.eqb app].
    rewrite dropt_tt, ltt_tt. reflexivity.
  - unfold ustep, uafter, uidx. cbn [PRt Nat.eqb app].
    change (true :: repeat true k ++ false :: r) with (repeat true (S k) ++ false :: r).
    rewrite dropt_tt, ltt_tt. cbn [dropt PLt Nat.eqb].
    replace (2 * S k - 1) with (S (2 * k)) by lia. reflexivity.
Qed.

Lemma ustep_ovf : forall u k, u < 2 ->
  ustep (PRt u ++ repeat true k) = repeat false (u + 2 * k + a) ++ w.
Proof.
  intros [|[|u]] k Hu; [| |lia].
  - unfold ustep, uafter, uidx. cbn [PRt Nat.eqb app].
    rewrite <- (app_nil_r (repeat true k)), dropt_tt, app_nil_r, ltt_tt0. reflexivity.
  - unfold ustep, uafter, uidx. cbn [PRt Nat.eqb app].
    change (true :: repeat true k) with (repeat true (S k)).
    rewrite <- (app_nil_r (repeat true (S k))), dropt_tt, app_nil_r, ltt_tt0.
    cbn [dropt]. do 2 f_equal. lia.
Qed.

Lemma dropt_decomp : forall s,
  s = repeat true (ltt s) ++ dropt s
  /\ (dropt s = [] \/ exists rho, dropt s = false :: rho).
Proof.
  induction s as [|[|] s IH]; cbn [ltt dropt repeat app].
  - split; [reflexivity | left; reflexivity].
  - destruct IH as [IH1 IH2]. split; [f_equal; exact IH1 | exact IH2].
  - split; [reflexivity | right; exists s; reflexivity].
Qed.

(** every nonempty token list is in exactly one class *)
Lemma uclass : forall t, t <> [] ->
  (exists u k r, u < 2 /\ t = PRt u ++ repeat true k ++ false :: r)
  \/ (exists u k, u < 2 /\ t = PRt u ++ repeat true k).
Proof.
  intros [|b s] Ht; [congruence|].
  destruct (dropt_decomp s) as [Hs [He | (rho & He)]].
  - right. exists (if b then 1 else 0), (ltt s). split; [destruct b; lia|].
    destruct b; cbn [PRt Nat.eqb app]; rewrite Hs at 1; rewrite He, app_nil_r; reflexivity.
  - left. exists (if b then 1 else 0), (ltt s), rho. split; [destruct b; lia|].
    destruct b; cbn [PRt Nat.eqb app]; rewrite Hs at 1; rewrite He; reflexivity.
Qed.

(** ** 2. The digit count and its parity *)

Lemma tdig_len_app : forall x y, length (tdig (x ++ y)) = length (tdig x) + length (tdig y).
Proof. intros x y. rewrite tdig_app. apply app_length. Qed.

Lemma tdig_len_ff : forall n, length (tdig (repeat false n)) = n.
Proof. intros n. rewrite tdig_ff. apply repeat_length. Qed.

Lemma tdig_len_PR : forall u, u < 2 -> length (tdig (PRt u)) = S u.
Proof. intros [|[|u]] Hu; [reflexivity|reflexivity|lia]. Qed.

Lemma tdig_len_PL : forall u, u < 2 -> length (tdig (PLt u)) = u.
Proof. intros [|[|u]] Hu; [reflexivity|reflexivity|lia]. Qed.

Lemma tdig_len_cons : forall b r, length (tdig (b :: r)) = (if b then 2 else 1) + length (tdig r).
Proof. intros [|] r; reflexivity. Qed.

Definition uinv (u0 : nat) (t : list bool) : Prop :=
  t <> [] /\ exists n, length (tdig t) = u0 + 1 + 2 * n.

Lemma ustep_int_len : forall u k r, u < 2 ->
  length (tdig (ustep (PRt u ++ repeat true k ++ false :: r)))
  = length (tdig (PRt u ++ repeat true k ++ false :: r)).
Proof.
  intros u k r Hu. rewrite ustep_int by exact Hu.
  rewrite !tdig_len_app, !tdig_len_cons, tdig_len_PR, tdig_len_PL, tdig_len_ff, tdig_tt_len
    by exact Hu.
  lia.
Qed.

(** an overflow list is of kind [u0], an end list of kind [1 - u0] *)
Lemma uinv_ovf_kind : forall u0 u k, u0 < 2 -> u < 2 ->
  uinv u0 (PRt u ++ repeat true k) -> u = u0.
Proof.
  intros u0 u k Hu0 Hu [_ (n & Hn)].
  rewrite tdig_len_app, tdig_len_PR, tdig_tt_len in Hn by exact Hu. lia.
Qed.

Lemma uinv_end_kind : forall u0 u k, u0 < 2 -> u < 2 ->
  uinv u0 (PRt u ++ repeat true k ++ [false]) -> u = 1 - u0.
Proof.
  intros u0 u k Hu0 Hu [_ (n & Hn)].
  rewrite !tdig_len_app, tdig_len_PR, tdig_tt_len in Hn by exact Hu. cbn in Hn. lia.
Qed.

Lemma ustep_inc : forall u k r, u < 2 ->
  bval (tdig (PRt u ++ repeat true k ++ false :: r))
  < bval (tdig (ustep (PRt u ++ repeat true k ++ false :: r))).
Proof.
  intros u k r Hu. rewrite ustep_int by exact Hu.
  rewrite <- (dstep_int u k r Hu).
  apply (dstep_dec _ r).
  rewrite PLt_ff, after_ff by exact Hu. reflexivity.
Qed.

Definition uisovf (t : list bool) : bool :=
  match uafter t with false :: _ => false | _ => true end.

Lemma uafter_int : forall u k r, u < 2 -> uafter (PRt u ++ repeat true k ++ false :: r) = false :: r.
Proof.
  intros [|[|u]] k r Hu; [| |lia]; unfold uafter; cbn [PRt Nat.eqb app].
  - apply dropt_tt.
  - change (true :: repeat true k ++ false :: r) with (repeat true (S k) ++ false :: r).
    apply dropt_tt.
Qed.

Variable dh : nat.
Hypothesis Hdh : a + length (tdig w) = 1 + 2 * dh.

Lemma ustep_nonempty : forall t, ustep t <> [].
Proof.
  intros t. unfold ustep.
  assert (Hr : forall n, 0 < n + length (tdig w) -> repeat false n ++ w <> []).
  { intros [|n] Hn; [|discriminate]. destruct w; [cbn in Hn; lia | discriminate]. }
  destruct (uafter t) as [|[|] rho].
  - apply Hr. lia.
  - apply Hr. lia.
  - destruct (uidx t); cbn; discriminate.
Qed.

Lemma uinv_step : forall u0 t, u0 < 2 -> uinv u0 t -> uinv u0 (ustep t).
Proof.
  intros u0 t Hu0 [Ht (n & Hn)]. split; [apply ustep_nonempty|].
  destruct (uclass t Ht) as [(u & k & r & Hu & ->) | (u & k & Hu & ->)].
  - exists n. rewrite ustep_int_len by exact Hu. exact Hn.
  - exists (n + dh). rewrite ustep_ovf by exact Hu. rewrite tdig_len_app, tdig_len_ff.
    rewrite tdig_len_app, tdig_len_PR, tdig_tt_len in Hn by exact Hu. lia.
Qed.

Lemma uinv_iter : forall u0 n t, u0 < 2 -> uinv u0 t -> uinv u0 (uiter t n).
Proof.
  intros u0. induction n as [|n IH]; intros t Hu0 Ht; [exact Ht|].
  cbn. apply IH; [exact Hu0|]. apply uinv_step; assumption.
Qed.



(** ** 3. Overflows recur: the binary value of the digits rises *)



Lemma ovf_reach : forall t, t <> [] -> exists j, uisovf (uiter t j) = true.
Proof.
  intros t Ht.
  remember (2 ^ length (tdig t) - bval (tdig t)) as v eqn:Ev.
  revert t Ev Ht.
  induction v as [v IH] using lt_wf_ind. intros t Ev Ht.
  destruct (uclass t Ht) as [(u & k & r & Hu & Et) | (u & k & Hu & Et)].
  - assert (Hlt := ustep_inc u k r Hu).
    assert (Hlen := ustep_int_len u k r Hu).
    rewrite <- Et in Hlt, Hlen.
    assert (Hb : bval (tdig (ustep t)) < 2 ^ length (tdig (ustep t))).
    { apply bval_lt. intros d Hd. unfold tdig in Hd. apply in_flat_map in Hd as (b & _ & Hd).
      destruct b; simpl in Hd; repeat (destruct Hd as [Hd|Hd]; [subst d; lia|]); contradiction. }
    destruct (IH (2 ^ length (tdig (ustep t)) - bval (tdig (ustep t))))
      with (t := ustep t) as (j & Hj).
    + rewrite Ev, Hlen. rewrite Hlen in Hb. lia.
    + reflexivity.
    + apply ustep_nonempty.
    + exists (S j). exact Hj.
  - exists 0. cbn [uiter]. unfold uisovf.
    rewrite Et. destruct u as [|[|u]]; [| |lia]; unfold uafter; cbn [PRt Nat.eqb app].
    + rewrite <- (app_nil_r (repeat true k)), dropt_tt. reflexivity.
    + change (true :: repeat true k) with (repeat true (S k)).
      rewrite <- (app_nil_r (repeat true (S k))), dropt_tt. reflexivity.
Qed.

Lemma ovfs_cofinal : forall u0 t0 N, u0 < 2 -> uinv u0 t0 ->
  exists n, N <= n /\ exists k, uiter t0 n = PRt u0 ++ repeat true k.
Proof.
  intros u0 t0 N Hu0 H0.
  assert (HN := uinv_iter u0 N t0 Hu0 H0).
  destruct (ovf_reach (uiter t0 N) (proj1 HN)) as (j & Hj).
  exists (N + j). split; [lia|]. rewrite uiter_add.
  assert (Hj' := uinv_iter u0 j _ Hu0 HN).
  destruct (uclass _ (proj1 Hj')) as [(u & k & r & Hu & He) | (u & k & Hu & He)].
  - exfalso. unfold uisovf in Hj. rewrite He, uafter_int in Hj by exact Hu. discriminate.
  - exists k. rewrite He in Hj' |- *.
    rewrite (uinv_ovf_kind u0 u k Hu0 Hu Hj'). reflexivity.
Qed.

End Step.

(** ** 4. Cells *)

Section CellsU.
Variable F : Fam.
Variables A B T : list Sym.

Lemma zu_ovf_l : forall p K m st w, p < 2 ->
  zdcells F A B T (PLt p ++ repeat false (2 * (K + st * m)) ++ w)
    = sden [] m (zdside F (zdPL A p) (A ++ A) K st (tcells A B w ++ T)).
Proof.
  intros p K m st w Hp. rewrite zdside_den. unfold zdcells.
  rewrite !tcells_app, tcells_PL, tcells_ff by exact Hp.
  rewrite <- !app_assoc, app_nil_r. reflexivity.
Qed.
End CellsU.

(** ** 5. The board *)

Section BoardZUTr.

Variable tm0   : TM.
Variable pins  : list Instr.
Local Notation tm := (tm_wrap_trs tm0 pins).

Variable F     : Fam.
Variables A B T : list Sym.
Variable u0 : nat.             (** the overflow kind *)
Variables a po co dh : nat.    (** overflow [alt i -> false^(i + a) ++ w], [u0 + a = po + 2 co] *)
Variable w : list bool.
Variable AI    : nat -> nat -> LRule.   (** interior: kind, index *)
Variable N0i sti : nat.
Variable AE    : nat -> LRule.          (** end (kind [1 - u0]): index *)
Variable N0e ste : nat.
Variable AB    : nat -> LRule.          (** overflow (kind [u0]): index *)
Variable N0b stb : nat.
Variable rsv   : list LRule.
Variable vsegs : nat -> Instr -> list nseg.
Variable visI  : nat -> Instr -> list lstep.
Variable t0    : list bool.

Hypothesis Hu0 : u0 < 2.
Hypothesis Hp : po < 2.
Hypothesis Hpc : u0 + a = po + 2 * co.
Hypothesis Hdh : a + length (tdig w) = 1 + 2 * dh.
Hypothesis Ht0 : uinv u0 t0.

Hypothesis Hsti : 0 < sti.
Hypothesis HAIS : forall i r, i < 2 -> r < N0i + sti ->
  ReachL tm (negb (fm_left F)) (fm_left F) (lr_lhs (AI i r)) (lr_rhs (AI i r)).
Hypothesis HAIL : forall i r, i < 2 -> r < N0i + sti ->
  lr_lhs (AI i r) = cls_conf F (zdside F (zdPR A B i) B r (astride N0i sti r) A).
Hypothesis HAIR : forall i r, i < 2 -> r < N0i + sti ->
  lr_rhs (AI i r) = cls_conf F (zdside F (zdPL A i) (A ++ A) r (astride N0i sti r) B).

Hypothesis Hste : 0 < ste.
Hypothesis HAES : forall r, r < N0e + ste ->
  ReachL tm true true (lr_lhs (AE r)) (lr_rhs (AE r)).
Hypothesis HAEL : forall r, r < N0e + ste ->
  lr_lhs (AE r) = cls_conf F (zdside F (zdPR A B (1 - u0)) B r (astride N0e ste r) (A ++ T)).
Hypothesis HAER : forall r, r < N0e + ste ->
  lr_rhs (AE r) = cls_conf F (zdside F (zdPL A (1 - u0)) (A ++ A) r (astride N0e ste r) (B ++ T)).

Hypothesis Hstb : 0 < stb.
Hypothesis HABS : forall r, r < N0b + stb ->
  ReachL tm true true (lr_lhs (AB r)) (lr_rhs (AB r)).
Hypothesis HABL : forall r, r < N0b + stb ->
  lr_lhs (AB r) = cls_conf F (zdside F (zdPR A B u0) B r (astride N0b stb r) T).
Hypothesis HABR : forall r, r < N0b + stb ->
  lr_rhs (AB r) = cls_conf F (zdside F (zdPL A po) (A ++ A) (r + co)
                                        (astride N0b stb r) (tcells A B w ++ T)).

Hypothesis Hrsv : Forall (RuleSound tm false false) rsv.
Hypothesis Hfire : forall r t, ~ In t pins -> r < N0b + stb ->
  nfire tm true true rsv (vsegs r t) (visI r t) (lr_lhs (AB r)) = Some t.

Local Notation Cf := (fun n => zdcfg F A B T (uiter a w t0 n)).

(** the overflow arm serving an overflow list, and its configuration *)
Lemma ovf_armZU : forall k,
  let r := aoff N0b stb k in
  r < N0b + stb
  /\ zdcfg F A B T (PRt u0 ++ repeat true k)
     = cden [] [] (acnt N0b stb k) (lr_lhs (AB r)).
Proof.
  intros k r.
  assert (Hrlt : r < N0b + stb) by (apply arm_index_lt; exact Hstb).
  assert (Hk : r + astride N0b stb r * acnt N0b stb k = k)
    by (apply arm_index; exact Hstb).
  split; [exact Hrlt|].
  rewrite (HABL r Hrlt).
  assert (Hc : zdcells F A B T (PRt u0 ++ repeat true k)
                 = sden [] (acnt N0b stb k) (zdside F (zdPR A B u0) B r (astride N0b stb r) T)).
  { rewrite <- Hk at 1. apply zd_bot_r. exact Hu0. }
  pose proof (cden_zd F A B T _ [] _ _ Hc) as H.
  rewrite tailL_nil, tailR_nil in H. symmetry. exact H.
Qed.

Lemma board_armZU : forall t, uinv u0 t ->
  exists Ar el er X n,
    ReachL tm el er (lr_lhs Ar) (lr_rhs Ar)
    /\ (el = true -> tailL F X = []) /\ (er = true -> tailR F X = [])
    /\ zdcfg F A B T t = cden (tailL F X) (tailR F X) n (lr_lhs Ar)
    /\ zdcfg F A B T (ustep a w t) = cden (tailL F X) (tailR F X) n (lr_rhs Ar).
Proof.
  intros t Hinv.
  destruct (uclass t (proj1 Hinv)) as [(i & k & r0 & Hi & Et) | (i & k & Hi & Et)].
  - destruct r0 as [|b r1].
    + (* the end *)
      assert (Hie : i = 1 - u0) by (apply (uinv_end_kind u0 i k Hu0 Hi); rewrite <- Et; exact Hinv).
      subst t i.
      remember (aoff N0e ste k) as r eqn:Er.
      assert (Hrlt : r < N0e + ste) by (subst r; apply arm_index_lt; exact Hste).
      assert (Hk : r + astride N0e ste r * acnt N0e ste k = k)
        by (subst r; apply arm_index; exact Hste).
      exists (AE r), true, true, [], (acnt N0e ste k).
      split; [|split; [|split; [|split]]].
      * exact (HAES r Hrlt).
      * intros _; apply tailL_nil.
      * intros _; apply tailR_nil.
      * rewrite (HAEL r Hrlt). symmetry. apply cden_zd.
        rewrite <- Hk at 1. apply zd_end_r. exact Hi.
      * rewrite ustep_int by exact Hi. rewrite (HAER r Hrlt). symmetry.
        apply cden_zd. rewrite <- Hk at 1. apply zd_end_l. exact Hi.
    + (* the interior *)
      subst t.
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
        rewrite <- Hk at 1. apply zd_int_r. exact Hi.
      * rewrite ustep_int by exact Hi. rewrite (HAIR i r Hi Hrlt). symmetry.
        apply cden_zd. rewrite <- Hk at 1. apply zd_int_l. exact Hi.
  - (* the overflow *)
    assert (Hio : i = u0) by (apply (uinv_ovf_kind u0 i k Hu0 Hi); rewrite <- Et; exact Hinv).
    subst t i.
    destruct (ovf_armZU k) as (Hrlt & Hden).
    set (r := aoff N0b stb k) in *.
    assert (Hk : r + astride N0b stb r * acnt N0b stb k = k)
      by (apply arm_index; exact Hstb).
    exists (AB r), true, true, [], (acnt N0b stb k).
    split; [|split; [|split; [|split]]].
    + exact (HABS r Hrlt).
    + intros _; apply tailL_nil.
    + intros _; apply tailR_nil.
    + rewrite tailL_nil, tailR_nil. exact Hden.
    + rewrite ustep_ovf by exact Hu0. rewrite (HABR r Hrlt). symmetry.
      apply cden_zd.
      replace (u0 + 2 * k + a)
        with (po + 2 * ((r + co) + astride N0b stb r * acnt N0b stb k))
        by (rewrite <- Hk at 2; lia).
      rewrite <- PLt_ff by exact Hp.
      apply zu_ovf_l. exact Hp.
Qed.

Lemma lapZU : forall n, exists m c',
  0 < m /\ csteps tm m (Cf n) = Some c' /\ lift c' = lift (Cf (S n)).
Proof.
  intros n.
  destruct (board_armZU _ (uinv_iter a w dh Hdh u0 n t0 Hu0 Ht0))
    as (Ar & el & er & X & k & HA & HL & HR & Hl & Hr).
  destruct (HA _ _ k HL HR) as (m & c' & Hm & Hc' & Hlc).
  exists m, c'. split; [exact Hm|]. split.
  - cbn beta. rewrite Hl. exact Hc'.
  - rewrite Hlc, <- Hr. cbn beta.
    replace (S n) with (n + 1) by lia. rewrite uiter_add. reflexivity.
Qed.

Lemma fireZU : forall t N, ~ In t pins ->
  exists n k c', N <= n /\ csteps tm k (Cf n) = Some c' /\ cinstr c' = t.
Proof.
  intros t N Hnp.
  destruct (ovfs_cofinal a w dh Hdh u0 t0 N Hu0 Ht0) as (n & HN & (k & Hx)).
  exists n. cbn beta. rewrite Hx.
  destruct (ovf_armZU k) as (Hrlt & Hden).
  set (r := aoff N0b stb k) in *.
  destruct (nfire_sound tm true true rsv (vsegs r t) (visI r t)
              (lr_lhs (AB r)) t Hrsv (Hfire r t Hnp Hrlt)
              [] [] (acnt N0b stb k)
              (fun _ => eq_refl) (fun _ => eq_refl)) as (k' & c' & Hc' & Ht).
  exists k', c'. rewrite Hden. split; [exact HN | split; [exact Hc' | exact Ht]].
Qed.

Theorem boardZU_neverqhtr : forall s0,
  stepn tm s0 InitES = Some (lift (zdcfg F A B T t0)) ->
  NeverQuasiHaltsTr tm0.
Proof.
  intros s0 Hboot.
  apply (glue_neverqhtrN tm0 pins Cf).
  - exists s0. exact Hboot.
  - intros n. destruct (lapZU n) as (m & c' & Hm & Hrun & Hl).
    exists m, c'. split; [exact Hrun | split; [exact Hl | exact Hm]].
  - intros t Hnp N. exact (fireZU t N Hnp).
Qed.

Lemma reachZU : forall d n,
  exists Tm, stepn tm Tm (lift (Cf n)) = Some (lift (Cf (n + d))).
Proof.
  induction d; intros n.
  - exists 0. rewrite Nat.add_0_r. reflexivity.
  - destruct (IHd n) as (Tm & HT).
    destruct (lapZU (n + d)) as (m & c' & _ & Hm & Hl).
    exists (Tm + m). rewrite stepn_add, HT.
    replace (n + S d) with (S (n + d)) by lia.
    rewrite <- Hl. apply csteps_lift. exact Hm.
Qed.

Lemma fire_everyZU : forall t, ~ In t pins -> forall n,
  exists k c', csteps tm k (Cf n) = Some c' /\ cinstr c' = t.
Proof.
  intros t Hnp n.
  destruct (fireZU t n Hnp) as (m & k & c' & Hm & Hk & Hc').
  destruct (reachZU (m - n) n) as (Tm & HT).
  replace (n + (m - n)) with m in HT by lia.
  assert (Hs : stepn tm (Tm + k) (lift (Cf n)) = Some (lift c')).
  { rewrite stepn_add, HT. apply csteps_lift. exact Hk. }
  destruct (stepn_csteps_at tm (Tm + k) (Cf n) (lift c') Hs) as (c'' & Hc'' & Hl').
  exists (Tm + k), c''. split; [exact Hc''|].
  rewrite <- cinstr_lift, Hl', cinstr_lift. exact Hc'.
Qed.

Theorem boardZU_qhtr : forall s0 Bd,
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
    destruct (lapZU (Nat.pred (Pos.to_nat p))) as (m & c' & Hm & Hrun & Hl).
    exists m, c'. split; [exact Hrun | split; [|exact Hm]].
    rewrite Hl, Pos2Nat.inj_succ.
    replace (S (Nat.pred (Pos.to_nat p))) with (Pos.to_nat p)
      by (pose proof (Pos2Nat.is_pos p); lia).
    reflexivity.
  - intros t Hnp p _. exact (fire_everyZU t Hnp (Nat.pred (Pos.to_nat p))).
  - exact Hwit.
  - exact Hle.
Qed.

End BoardZUTr.
