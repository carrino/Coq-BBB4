(** * Checkers.LadderCheckZeckDTr: the Zeckendorf COUNTDOWN over two token
    words (SCOPING_INSTR 7.4.LE6).

    LE6's survey finds ~140 open rows whose tape grows one cell per factor
    phi of time.  LE4's [LadderCheckZeck2Tr] reads 20 of them (an increment,
    each one written [11]); 75 more count DOWN.  Read from the head, a
    Zeckendorf string (LSB first, every [1] followed by a [0]) is a list of
    tokens [0] and [10]; the tape is that list with [0 -> A] and [10 -> B]
    for two cell words [A], [B] (mostly [A = 1], [B = 01]: the complement of
    the one-cell code).  So the state is a TOKEN LIST [tau : list bool]
    ([false] = [0], [true] = [10]) and every token list is a Zeckendorf
    string; the configuration is [fm_pre F ++ tcells tau ++ T].

    One step is [x -> x - 1] inside a width and, at [x = 0], the largest
    string of the next width:

      dstep (false^i :: true :: rho) = alt i ++ false :: rho
      dstep (false^m)                = alt m

    with [alt (2k) = false :: true^k] and [alt (2k+1) = true^(k+1)].  With
    [i = u + 2k] ([u < 2]) every class is one symbolic side over the words
    [AA] (left) and [B] (right), [PL 0 = []], [PL 1 = A], [PR 0 = A],
    [PR 1 = B]:

    - interior: [PL u (AA)^k B X  ->  PR u B^k A X], [X] opaque;
    - end:      [PL u (AA)^k B T  ->  PR u B^k A T];
    - bottom:   [PL u (AA)^k T    ->  PR u B^k T]   ([u = 0 -> 0 < k]).

    Liveness: the binary value of the digit string falls at every interior
    and end step (the lowest one becomes a zero and the digits below it are
    worth less), so bottoms recur; the fires are read from the bottom arms.

    Nothing landed is modified.  Axiom footprint: [functional_extensionality_dep],
    via [CTape.lift]. *)
From Coq Require Import Arith Lia Bool List PArith Wf_nat.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape ClosureTr.
From BBB4.Counters Require Import WTape LapCertGlueLift.
From BBB4.Checkers Require Import WrapTr LapDecider LadderKernel LadderFam LadderCheck LadderCheckTr LadderNest LadderCheckNestTr TCyclerQHTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
From BBB4.Counters Require Import LapGlueTr.
From BBB4.CensusTr Require Import TNF_QHTr QHConveyorTr.
Import ListNotations.

(** ** 1. Token lists and the countdown *)

Fixpoint lz (t : list bool) : nat :=
  match t with false :: r => S (lz r) | _ => 0 end.

Fixpoint after1 (t : list bool) : option (list bool) :=
  match t with false :: r => after1 r | true :: r => Some r | [] => None end.

Fixpoint alt (i : nat) : list bool :=
  match i with
  | 0 => [false]
  | 1 => [true]
  | S (S j) => match alt j with b :: r => b :: true :: r | [] => [] end
  end.

Definition dstep (t : list bool) : list bool :=
  alt (lz t) ++ match after1 t with Some r => false :: r | None => [] end.

Fixpoint diter (t : list bool) (n : nat) : list bool :=
  match n with O => t | S n' => diter (dstep t) n' end.

Lemma diter_add : forall n1 n2 t, diter t (n1 + n2) = diter (diter t n1) n2.
Proof. induction n1 as [|n1 IH]; intros n2 t; [reflexivity | apply IH]. Qed.

Definition PLt (u : nat) : list bool := if u =? 0 then [] else [false].
Definition PRt (u : nat) : list bool := if u =? 0 then [false] else [true].

Lemma alt_split : forall u k, u < 2 -> alt (u + 2 * k) = PRt u ++ repeat true k.
Proof.
  intros u k Hu. induction k as [|k IH].
  - destruct u as [|[|u]]; [reflexivity|reflexivity|lia].
  - replace (u + 2 * S k) with (S (S (u + 2 * k))) by lia.
    cbn [alt]. rewrite IH.
    destruct u as [|[|u]]; [reflexivity|reflexivity|lia].
Qed.

Lemma lz_ff : forall n r, lz (repeat false n ++ r) = n + lz r.
Proof. induction n as [|n IH]; intros r; [reflexivity|]. cbn. rewrite IH. reflexivity. Qed.

Lemma after_ff : forall n r, after1 (repeat false n ++ r) = after1 r.
Proof. induction n as [|n IH]; intros r; [reflexivity|]. cbn. apply IH. Qed.

Lemma PLt_ff : forall u k r, u < 2 ->
  PLt u ++ repeat false (2 * k) ++ r = repeat false (u + 2 * k) ++ r.
Proof.
  intros [|[|u]] k r Hu; [reflexivity| |lia]. reflexivity.
Qed.

Lemma dstep_int : forall u k r, u < 2 ->
  dstep (PLt u ++ repeat false (2 * k) ++ true :: r)
  = PRt u ++ repeat true k ++ false :: r.
Proof.
  intros u k r Hu. rewrite PLt_ff by exact Hu. unfold dstep.
  rewrite lz_ff, after_ff. cbn [lz after1]. rewrite Nat.add_0_r, alt_split by exact Hu.
  rewrite <- app_assoc. reflexivity.
Qed.

Lemma dstep_bot : forall u k, u < 2 ->
  dstep (PLt u ++ repeat false (2 * k)) = PRt u ++ repeat true k.
Proof.
  intros u k Hu. pose proof (PLt_ff u k [] Hu) as H. rewrite !app_nil_r in H.
  rewrite H. unfold dstep.
  rewrite <- (app_nil_r (repeat false (u + 2 * k))), lz_ff, after_ff.
  cbn [lz after1]. rewrite Nat.add_0_r, alt_split by exact Hu. apply app_nil_r.
Qed.

(** every nonempty token list is in exactly one class *)
Lemma ff_decomp : forall t,
  t = repeat false (lz t) ++ match after1 t with Some r => true :: r | None => [] end.
Proof.
  induction t as [|[|] t IH]; [reflexivity|reflexivity|].
  cbn [lz after1 repeat app]. f_equal. exact IH.
Qed.

Lemma split_n : forall n, exists u k, u < 2 /\ n = u + 2 * k.
Proof.
  intros n. exists (n mod 2), (n / 2). split.
  - apply Nat.mod_upper_bound; lia.
  - pose proof (Nat.div_mod_eq n 2). lia.
Qed.

Lemma dclass : forall t, t <> [] ->
  (exists u k r, u < 2 /\ t = PLt u ++ repeat false (2 * k) ++ true :: r)
  \/ (exists u k, u < 2 /\ (u = 0 -> 0 < k) /\ t = PLt u ++ repeat false (2 * k)).
Proof.
  intros t Ht. rewrite (ff_decomp t).
  destruct (split_n (lz t)) as (u & k & Hu & Hn). rewrite Hn.
  destruct (after1 t) as [r|] eqn:Ea.
  - left. exists u, k, r. split; [exact Hu|]. rewrite PLt_ff by exact Hu. reflexivity.
  - right. exists u, k. split; [exact Hu|]. split.
    + intros ->. destruct k as [|k]; [|lia].
      exfalso. apply Ht. rewrite (ff_decomp t), Ea, Hn. reflexivity.
    + rewrite app_nil_r. pose proof (PLt_ff u k [] Hu) as H.
      rewrite !app_nil_r in H. symmetry. exact H.
Qed.

(** ** 2. Bottoms recur: the binary value of the digits falls *)

Definition tdig (t : list bool) : list nat :=
  flat_map (fun b : bool => if b then [1;0] else [0]) t.

Fixpoint bval (l : list nat) : nat :=
  match l with [] => 0 | d :: r => d + 2 * bval r end.

Lemma bval_app : forall p q, bval (p ++ q) = bval p + 2 ^ length p * bval q.
Proof.
  induction p as [|d p IH]; intros q; cbn [app bval length]; [simpl; lia|].
  rewrite IH, Nat.pow_succ_r'. nia.
Qed.

Lemma bval_lt : forall l, (forall d, In d l -> d <= 1) -> bval l < 2 ^ length l.
Proof.
  induction l as [|d l IH]; intros H; cbn [bval length]; [simpl; lia|].
  rewrite Nat.pow_succ_r'.
  assert (d <= 1) by (apply H; left; reflexivity).
  assert (bval l < 2 ^ length l) by (apply IH; intros e He; apply H; right; exact He).
  lia.
Qed.

Lemma tdig_last : forall t, t <> [] ->
  exists D, tdig t = D ++ [0] /\ forall d, In d D -> d <= 1.
Proof.
  induction t as [|b t IH]; intros Ht; [congruence|].
  destruct t as [|b' t'].
  - exists (if b then [1] else []). split; [destruct b; reflexivity|].
    intros d Hd. destruct b; simpl in Hd;
      repeat (destruct Hd as [Hd|Hd]; [subst d; lia|]); contradiction.
  - destruct (IH ltac:(discriminate)) as (D & HD & Hb).
    exists ((if b then [1;0] else [0]) ++ D). split.
    + change (tdig (b :: b' :: t')) with ((if b then [1;0] else [0]) ++ tdig (b' :: t')).
      rewrite HD, app_assoc. reflexivity.
    + intros d Hd. apply in_app_or in Hd as [Hd|Hd]; [|exact (Hb d Hd)].
      destruct b; simpl in Hd;
        repeat (destruct Hd as [Hd|Hd]; [subst d; lia|]); contradiction.
Qed.

Lemma tdig_app : forall a b, tdig (a ++ b) = tdig a ++ tdig b.
Proof. intros a b. unfold tdig. apply flat_map_app. Qed.

Lemma tdig_ff : forall n, tdig (repeat false n) = repeat 0 n.
Proof. induction n as [|n IH]; [reflexivity|]. cbn. rewrite <- IH. reflexivity. Qed.

Lemma bval_zeros : forall n q, bval (repeat 0 n ++ q) = 2 ^ n * bval q.
Proof.
  induction n as [|n IH]; intros q; cbn [repeat app bval]; [simpl; lia|].
  rewrite IH, Nat.pow_succ_r'. nia.
Qed.

Lemma tdig_tt_len : forall k, length (tdig (repeat true k)) = 2 * k.
Proof.
  induction k as [|k IH]; [reflexivity|].
  change (tdig (repeat true (S k))) with ([1;0] ++ tdig (repeat true k)).
  rewrite app_length, IH. cbn [length]. lia.
Qed.

Lemma tdig_alt_len : forall i, length (tdig (alt i)) = S i.
Proof.
  intros i. destruct (split_n i) as (u & k & Hu & ->).
  rewrite alt_split by exact Hu. rewrite tdig_app, app_length, tdig_tt_len.
  destruct u as [|[|u]]; cbn; lia.
Qed.

Lemma dstep_dec : forall t r, after1 t = Some r ->
  bval (tdig (dstep t)) < bval (tdig t).
Proof.
  intros t r Ha.
  assert (Ht : t = repeat false (lz t) ++ true :: r)
    by (rewrite (ff_decomp t) at 1; rewrite Ha; reflexivity).
  unfold dstep. rewrite Ha.
  set (i := lz t) in *.
  destruct (tdig_last (alt i)) as (D & HD & Hb).
  { destruct (split_n i) as (u & k & Hu & Hi). rewrite Hi, alt_split by exact Hu.
    destruct u as [|[|u]]; cbn; discriminate. }
  pose proof (tdig_alt_len i) as Hl. rewrite HD, app_length in Hl. cbn in Hl.
  assert (HDl : length D = i) by lia.
  assert (Et : bval (tdig t) = bval (tdig (repeat false i ++ true :: r)))
    by (do 2 f_equal; exact Ht).
  rewrite Et. rewrite !tdig_app, HD, tdig_ff.
  change (tdig (true :: r)) with ([1;0] ++ tdig r).
  change (tdig (false :: r)) with ([0] ++ tdig r).
  rewrite bval_zeros, <- !app_assoc, bval_app, HDl.
  cbn [app bval].
  pose proof (bval_lt D Hb) as HbD. rewrite HDl in HbD.
  nia.
Qed.

Lemma dstep_nonempty : forall t, dstep t <> [].
Proof.
  intros t. unfold dstep. destruct (split_n (lz t)) as (u & k & Hu & ->).
  rewrite alt_split by exact Hu. destruct u as [|[|u]]; cbn; discriminate.
Qed.

Lemma bot_reach : forall t, t <> [] -> exists j, after1 (diter t j) = None.
Proof.
  intros t. remember (bval (tdig t)) as v eqn:Ev. revert t Ev.
  induction v as [v IH] using lt_wf_ind. intros t Ev Ht.
  destruct (after1 t) as [r|] eqn:Ea.
  - destruct (IH (bval (tdig (dstep t)))) with (t := dstep t) as (j & Hj).
    + rewrite Ev. exact (dstep_dec t r Ea).
    + reflexivity.
    + apply dstep_nonempty.
    + exists (S j). exact Hj.
  - exists 0. exact Ea.
Qed.

Lemma diter_nonempty : forall n t, t <> [] -> diter t n <> [].
Proof.
  induction n as [|n IH]; intros t Ht; [exact Ht|]. cbn. apply IH, dstep_nonempty.
Qed.

Lemma bots_cofinal : forall t0 N, t0 <> [] ->
  exists n, N <= n /\
    exists u k, u < 2 /\ (u = 0 -> 0 < k) /\ diter t0 n = PLt u ++ repeat false (2 * k).
Proof.
  intros t0 N H0.
  destruct (bot_reach (diter t0 N) (diter_nonempty N t0 H0)) as (j & Hj).
  exists (N + j). split; [lia|]. rewrite diter_add.
  destruct (dclass (diter (diter t0 N) j) (diter_nonempty j _ (diter_nonempty N t0 H0)))
    as [(u & k & r & Hu & He) | Hb]; [|exact Hb].
  exfalso. rewrite He, PLt_ff, after_ff in Hj by exact Hu. discriminate.
Qed.

(** ** 3. Cells, sides, configurations *)

Section CellsD.

Variable F : Fam.
Variables A B T : list Sym.   (** the token words and the terminator, in cells *)

Definition tcells (t : list bool) : list Sym := flat_map (fun b : bool => if b then B else A) t.

Definition zdPL (u : nat) : list Sym := if u =? 0 then [] else A.
Definition zdPR (u : nat) : list Sym := if u =? 0 then A else B.

Definition zdcells (t : list bool) : list Sym := fm_pre F ++ tcells t ++ T.

Definition zdcfg (t : list bool) : cconf :=
  if fm_left F
  then (fm_st F, (zdcells t, fm_hs F, fm_other F))
  else (fm_st F, (fm_other F, fm_hs F, zdcells t)).

Definition zdside (P w : list Sym) (r s : nat) (W : list Sym) : sside :=
  blk (fm_pre F ++ P ++ rep w r) w s W.

Lemma zdside_den : forall P w r s W X m,
  sden X m (zdside P w r s W) = fm_pre F ++ P ++ rep w (r + s * m) ++ W ++ X.
Proof.
  intros P w r s W X m. unfold zdside. rewrite blk_den, rep_add, !app_assoc. reflexivity.
Qed.

Lemma cden_zd : forall sd X n t,
  zdcells t = sden X n sd ->
  cden (tailL F X) (tailR F X) n (cls_conf F sd) = zdcfg t.
Proof.
  intros sd X n t H.
  unfold cden, cls_conf, zdcfg, tailL, tailR.
  destruct (fm_left F); simpl; rewrite sden_flat, app_nil_r, <- H; reflexivity.
Qed.

Lemma tcells_app : forall a b, tcells (a ++ b) = tcells a ++ tcells b.
Proof. intros a b. unfold tcells. apply flat_map_app. Qed.

Lemma tcells_ff : forall k, tcells (repeat false (2 * k)) = rep (A ++ A) k.
Proof.
  induction k as [|k IH]; [reflexivity|].
  replace (2 * S k) with (S (S (2 * k))) by lia.
  cbn [repeat rep]. rewrite <- IH. cbn [tcells flat_map]. rewrite app_assoc. reflexivity.
Qed.

Lemma tcells_tt : forall k, tcells (repeat true k) = rep B k.
Proof.
  induction k as [|k IH]; [reflexivity|]. cbn [repeat rep]. rewrite <- IH. reflexivity.
Qed.

Lemma tcells_PL : forall u, u < 2 -> tcells (PLt u) = zdPL u.
Proof. intros [|[|u]] Hu; [reflexivity| |lia]. cbn. apply app_nil_r. Qed.

Lemma tcells_PR : forall u, u < 2 -> tcells (PRt u) = zdPR u.
Proof. intros [|[|u]] Hu; [| |lia]; cbn; apply app_nil_r. Qed.

Lemma zd_int_l : forall u k r m st, u < 2 ->
  zdcells (PLt u ++ repeat false (2 * (k + st * m)) ++ true :: r)
    = sden (tcells r ++ T) m (zdside (zdPL u) (A ++ A) k st B).
Proof.
  intros u k r m st Hu. rewrite zdside_den. unfold zdcells.
  rewrite !tcells_app, tcells_PL, tcells_ff by exact Hu.
  change (tcells (true :: r)) with (B ++ tcells r).
  rewrite <- !app_assoc. reflexivity.
Qed.

Lemma zd_int_r : forall u k r m st, u < 2 ->
  zdcells (PRt u ++ repeat true (k + st * m) ++ false :: r)
    = sden (tcells r ++ T) m (zdside (zdPR u) B k st A).
Proof.
  intros u k r m st Hu. rewrite zdside_den. unfold zdcells.
  rewrite !tcells_app, tcells_PR, tcells_tt by exact Hu.
  change (tcells (false :: r)) with (A ++ tcells r).
  rewrite <- !app_assoc. reflexivity.
Qed.

Lemma zd_end_l : forall u k m st, u < 2 ->
  zdcells (PLt u ++ repeat false (2 * (k + st * m)) ++ [true])
    = sden [] m (zdside (zdPL u) (A ++ A) k st (B ++ T)).
Proof.
  intros u k m st Hu. rewrite zdside_den. unfold zdcells.
  rewrite !tcells_app, tcells_PL, tcells_ff by exact Hu.
  change (tcells [true]) with (B ++ []).
  rewrite <- !app_assoc, !app_nil_r. reflexivity.
Qed.

Lemma zd_end_r : forall u k m st, u < 2 ->
  zdcells (PRt u ++ repeat true (k + st * m) ++ [false])
    = sden [] m (zdside (zdPR u) B k st (A ++ T)).
Proof.
  intros u k m st Hu. rewrite zdside_den. unfold zdcells.
  rewrite !tcells_app, tcells_PR, tcells_tt by exact Hu.
  change (tcells [false]) with (A ++ []).
  rewrite <- !app_assoc, !app_nil_r. reflexivity.
Qed.

Lemma zd_bot_l : forall u k m st, u < 2 ->
  zdcells (PLt u ++ repeat false (2 * (k + st * m)))
    = sden [] m (zdside (zdPL u) (A ++ A) k st T).
Proof.
  intros u k m st Hu. rewrite zdside_den. unfold zdcells.
  rewrite !tcells_app, tcells_PL, tcells_ff by exact Hu.
  rewrite <- !app_assoc, !app_nil_r. reflexivity.
Qed.

Lemma zd_bot_r : forall u k m st, u < 2 ->
  zdcells (PRt u ++ repeat true (k + st * m))
    = sden [] m (zdside (zdPR u) B k st T).
Proof.
  intros u k m st Hu. rewrite zdside_den. unfold zdcells.
  rewrite !tcells_app, tcells_PR, tcells_tt by exact Hu.
  rewrite <- !app_assoc, !app_nil_r. reflexivity.
Qed.

End CellsD.

(** ** 4. The board *)

Section BoardZDTr.

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
  lr_rhs (AB i r) = cls_conf F (zdside F (zdPR A B i) B r (astride N0b stb r) T).

Hypothesis Hrsv : Forall (RuleSound tm false false) rsv.
Hypothesis Hfire : forall i r t, ~ In t pins -> i < 2 -> r < N0b + stb ->
  (i = 0 -> 0 < r) ->
  nfire tm true true rsv (vsegs i r t) (visI i r t) (lr_lhs (AB i r)) = Some t.

Local Notation Cf := (fun n => zdcfg F A B T (diter t0 n)).

(** the bottom arm serving a bottom list, and its configuration *)
Lemma bot_armZD : forall i k, i < 2 -> (i = 0 -> 0 < k) ->
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

Lemma board_armZD : forall t, t <> [] ->
  exists Ar el er X n,
    ReachL tm el er (lr_lhs Ar) (lr_rhs Ar)
    /\ (el = true -> tailL F X = []) /\ (er = true -> tailR F X = [])
    /\ zdcfg F A B T t = cden (tailL F X) (tailR F X) n (lr_lhs Ar)
    /\ zdcfg F A B T (dstep t) = cden (tailL F X) (tailR F X) n (lr_rhs Ar).
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
      * rewrite dstep_int by exact Hi. rewrite (HAER i r Hi Hrlt). symmetry.
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
      * rewrite dstep_int by exact Hi. rewrite (HAIR i r Hi Hrlt). symmetry.
        apply cden_zd. rewrite <- Hk at 1. apply zd_int_r. exact Hi.
  - (* the bottom *)
    destruct (bot_armZD i k Hi Hk0) as (Hrlt & Hr0 & Hden).
    set (r := aoff N0b stb k) in *.
    assert (Hk : r + astride N0b stb r * acnt N0b stb k = k)
      by (apply arm_index; exact Hstb).
    exists (AB i r), true, true, [], (acnt N0b stb k).
    split; [|split; [|split; [|split]]].
    + exact (HABS i r Hi Hrlt Hr0).
    + intros _; apply tailL_nil.
    + intros _; apply tailR_nil.
    + rewrite tailL_nil, tailR_nil. exact Hden.
    + rewrite dstep_bot by exact Hi. rewrite (HABR i r Hi Hrlt Hr0). symmetry.
      apply cden_zd. rewrite <- Hk at 1. apply zd_bot_r. exact Hi.
Qed.

Lemma lapZD : forall n, exists m c',
  0 < m /\ csteps tm m (Cf n) = Some c' /\ lift c' = lift (Cf (S n)).
Proof.
  intros n.
  destruct (board_armZD _ (diter_nonempty n t0 Ht0))
    as (Ar & el & er & X & k & HA & HL & HR & Hl & Hr).
  destruct (HA _ _ k HL HR) as (m & c' & Hm & Hc' & Hlc).
  exists m, c'. split; [exact Hm|]. split.
  - cbn beta. rewrite Hl. exact Hc'.
  - rewrite Hlc, <- Hr. cbn beta.
    replace (S n) with (n + 1) by lia. rewrite diter_add. reflexivity.
Qed.

Lemma fireZD : forall t N, ~ In t pins ->
  exists n k c', N <= n /\ csteps tm k (Cf n) = Some c' /\ cinstr c' = t.
Proof.
  intros t N Hnp.
  destruct (bots_cofinal t0 N Ht0) as (n & HN & (i & k & Hi & Hk0 & Hx)).
  exists n. cbn beta. rewrite Hx.
  destruct (bot_armZD i k Hi Hk0) as (Hrlt & Hr0 & Hden).
  set (r := aoff N0b stb k) in *.
  destruct (nfire_sound tm true true rsv (vsegs i r t) (visI i r t)
              (lr_lhs (AB i r)) t Hrsv (Hfire i r t Hnp Hi Hrlt Hr0)
              [] [] (acnt N0b stb k)
              (fun _ => eq_refl) (fun _ => eq_refl)) as (k' & c' & Hc' & Ht).
  exists k', c'. rewrite Hden. split; [exact HN | split; [exact Hc' | exact Ht]].
Qed.

Theorem boardZD_neverqhtr : forall s0,
  stepn tm s0 InitES = Some (lift (zdcfg F A B T t0)) ->
  NeverQuasiHaltsTr tm0.
Proof.
  intros s0 Hboot.
  apply (glue_neverqhtrN tm0 pins Cf).
  - exists s0. exact Hboot.
  - intros n. destruct (lapZD n) as (m & c' & Hm & Hrun & Hl).
    exists m, c'. split; [exact Hrun | split; [exact Hl | exact Hm]].
  - intros t Hnp N. exact (fireZD t N Hnp).
Qed.

Lemma reachZD : forall d n,
  exists Tm, stepn tm Tm (lift (Cf n)) = Some (lift (Cf (n + d))).
Proof.
  induction d; intros n.
  - exists 0. rewrite Nat.add_0_r. reflexivity.
  - destruct (IHd n) as (Tm & HT).
    destruct (lapZD (n + d)) as (m & c' & _ & Hm & Hl).
    exists (Tm + m). rewrite stepn_add, HT.
    replace (n + S d) with (S (n + d)) by lia.
    rewrite <- Hl. apply csteps_lift. exact Hm.
Qed.

Lemma fire_everyZD : forall t, ~ In t pins -> forall n,
  exists k c', csteps tm k (Cf n) = Some c' /\ cinstr c' = t.
Proof.
  intros t Hnp n.
  destruct (fireZD t n Hnp) as (m & k & c' & Hm & Hk & Hc').
  destruct (reachZD (m - n) n) as (Tm & HT).
  replace (n + (m - n)) with m in HT by lia.
  assert (Hs : stepn tm (Tm + k) (lift (Cf n)) = Some (lift c')).
  { rewrite stepn_add, HT. apply csteps_lift. exact Hk. }
  destruct (stepn_csteps_at tm (Tm + k) (Cf n) (lift c') Hs) as (c'' & Hc'' & Hl').
  exists (Tm + k), c''. split; [exact Hc''|].
  rewrite <- cinstr_lift, Hl', cinstr_lift. exact Hc'.
Qed.

Theorem boardZD_qhtr : forall s0 Bd,
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
    destruct (lapZD (Nat.pred (Pos.to_nat p))) as (m & c' & Hm & Hrun & Hl).
    exists m, c'. split; [exact Hrun | split; [|exact Hm]].
    rewrite Hl, Pos2Nat.inj_succ.
    replace (S (Nat.pred (Pos.to_nat p))) with (Pos.to_nat p)
      by (pose proof (Pos2Nat.is_pos p); lia).
    reflexivity.
  - intros t Hnp p _. exact (fire_everyZD t Hnp (Nat.pred (Pos.to_nat p))).
  - exact Hwit.
  - exact Hle.
Qed.

End BoardZDTr.
