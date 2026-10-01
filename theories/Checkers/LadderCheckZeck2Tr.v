(** * Checkers.LadderCheckZeck2Tr: the Zeckendorf counter over TWO-CELL tokens
    (SCOPING_INSTR 7.4.LE4).

    LE2's five "constant, fibonacci weights" rows
    ([0RB1LD_1LA1RC_1LA1RB_0RC0LD], ...) count in Zeckendorf, but the tape
    is not [flat_map dig x]: cell [i] is [x_i OR x_(i-1)], so every [1] of
    [x] is written across two cells as [11] and the ones sit at a moving
    cell offset ([0000 11], [11 00 11], [0 11 0 11], [00 11 11]).  Read
    from the head, a Zeckendorf string splits uniquely into the tokens [0]
    and [10] (every [1] is followed by a [0]), and the tape is the token
    string with [0 -> 0] and [10 -> 11].  That is [zc] below: a two-state
    transducer of the digits, not a digit-word code.

    The numeration is [LadderCheckZeckTr]'s, unchanged: [zinc], [zok],
    [zdec], the bound and the cofinal tops are imported.  Only the cells
    change.  The configuration at value [x] is
    [fm_pre F ++ zc (x ++ [0]) ++ T]: the [0] closes the last token, and
    [T] is the terminator in cells.  Under [zc] each class of the
    Zeckendorf checker is again one symbolic side over a two-cell word:

    - interior: [U i (11)^k 0 X   -> U0 i (00)^k 11 X], [X] opaque;
    - end:      [U i (11)^k 0 T   -> U0 i (00)^k 11 T];
    - top:      [U i (11)^k T     -> U0 i (00)^k 00 T];

    with [U 0 = 0], [U 1 = 11], [U0 0 = []], [U0 1 = 0] (the two kinds of
    the alternating prefix).  Liveness is [LadderCheckZeckTr]'s.

    Nothing landed is modified.  Axiom footprint: [functional_extensionality_dep],
    via [CTape.lift]. *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape ClosureTr.
From BBB4.Counters Require Import WTape LapCertGlueLift.
From BBB4.Checkers Require Import WrapTr LapDecider LadderKernel LadderFam LadderCheck LadderCheckTr LadderNest LadderCheckNestTr TCyclerQHTr.
From BBB4.Checkers Require Import LadderCheckZeckTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
From BBB4.Counters Require Import LapGlueTr.
From BBB4.CensusTr Require Import TNF_QHTr QHConveyorTr.
Import ListNotations.

(** ** 1. The two-cell code *)

Fixpoint zc (x : list nat) : list Sym :=
  match x with
  | [] => []
  | 0 :: r => S0 :: zc r
  | _ :: r => S1 :: S1 :: match r with [] => [] | _ :: r' => zc r' end
  end.

Definition zU (i : nat) : list Sym := if i =? 0 then [S0] else [S1;S1].
Definition zU0 (i : nat) : list Sym := if i =? 0 then [] else [S0].

Lemma zc_10 : forall k b, zc (wrep [1;0] k ++ b) = rep [S1;S1] k ++ zc b.
Proof.
  induction k as [|k IH]; intros b; [reflexivity|].
  cbn [wrep app zc rep]. rewrite IH. reflexivity.
Qed.

Lemma wrep_rot01 : forall k b, wrep [0;1] k ++ 0 :: b = 0 :: (wrep [1;0] k ++ b).
Proof.
  induction k as [|k IH]; intros b; [reflexivity|].
  cbn [wrep app]. rewrite IH. reflexivity.
Qed.

(** a class prefix closed by a [0]: [u (01)^k 0] *)
Lemma zc_cls : forall i k b, i < 2 ->
  zc (zu i ++ wrep [0;1] k ++ 0 :: b) = zU i ++ rep [S1;S1] k ++ zc b.
Proof.
  intros [|[|i]] k b Hi; [| |lia]; cbn [zu zU Nat.eqb app].
  - rewrite wrep_rot01. cbn [zc]. rewrite zc_10. reflexivity.
  - rewrite wrep_rot01.
    change (zc (1 :: 0 :: wrep [1;0] k ++ b)) with (S1 :: S1 :: zc (wrep [1;0] k ++ b)).
    rewrite zc_10. reflexivity.
Qed.

Lemma zc_00 : forall k b, zc (wrep [0;0] k ++ b) = rep [S0;S0] k ++ zc b.
Proof.
  induction k as [|k IH]; intros b; [reflexivity|].
  cbn [wrep app zc rep]. rewrite IH. reflexivity.
Qed.

Lemma zc_zcls : forall i k b, i < 2 ->
  zc (zu0 i ++ wrep [0;0] k ++ b) = zU0 i ++ rep [S0;S0] k ++ zc b.
Proof.
  intros [|[|i]] k b Hi; [| |lia]; cbn [zu0 zU0 Nat.eqb app].
  - apply zc_00.
  - cbn [zc]. rewrite zc_00. reflexivity.
Qed.

(** ** 2. Cells, sides, configurations *)

Section Cells2.

Variable F : Fam.
Variable T : list Sym.   (** the terminator, in cells *)

Definition z2cells (x : list nat) : list Sym := fm_pre F ++ zc (x ++ [0]) ++ T.

Definition z2cfg (x : list nat) : cconf :=
  if fm_left F
  then (fm_st F, (z2cells x, fm_hs F, fm_other F))
  else (fm_st F, (fm_other F, fm_hs F, z2cells x)).

(** [P w^r] then a block of [w] at stride [s], then [W] *)
Definition z2side (P w : list Sym) (r s : nat) (W : list Sym) : sside :=
  blk (fm_pre F ++ P ++ rep w r) w s W.

Lemma z2side_den : forall P w r s W X m,
  sden X m (z2side P w r s W) = fm_pre F ++ P ++ rep w (r + s * m) ++ W ++ X.
Proof.
  intros P w r s W X m. unfold z2side. rewrite blk_den, rep_add, !app_assoc. reflexivity.
Qed.

Lemma cden_z2 : forall sd X n x,
  z2cells x = sden X n sd ->
  cden (tailL F X) (tailR F X) n (cls_conf F sd) = z2cfg x.
Proof.
  intros sd X n x H.
  unfold cden, cls_conf, z2cfg, tailL, tailR.
  destruct (fm_left F); simpl; rewrite sden_flat, app_nil_r, <- H; reflexivity.
Qed.

(** the cells of each class, and of its successor *)
Lemma z2_int_l : forall i k r0 m st, i < 2 ->
  z2cells (zu i ++ wrep [0;1] (k + st * m) ++ 0 :: 0 :: r0)
    = sden (zc (r0 ++ [0]) ++ T) m (z2side (zU i) [S1;S1] k st [S0]).
Proof.
  intros i k r0 m st Hi. rewrite z2side_den. unfold z2cells.
  rewrite <- !app_assoc. cbn [app]. rewrite zc_cls by exact Hi.
  cbn [zc]. rewrite <- !app_assoc. reflexivity.
Qed.

Lemma z2_int_r : forall i k r0 m st, i < 2 ->
  z2cells (zu0 i ++ wrep [0;0] (k + st * m) ++ 1 :: 0 :: r0)
    = sden (zc (r0 ++ [0]) ++ T) m (z2side (zU0 i) [S0;S0] k st [S1;S1]).
Proof.
  intros i k r0 m st Hi. rewrite z2side_den. unfold z2cells.
  rewrite <- !app_assoc. cbn [app]. rewrite zc_zcls by exact Hi.
  cbn [zc]. rewrite <- !app_assoc. reflexivity.
Qed.

Lemma z2_end_l : forall i k m st, i < 2 ->
  z2cells (zu i ++ wrep [0;1] (k + st * m) ++ [0])
    = sden [] m (z2side (zU i) [S1;S1] k st ([S0] ++ T)).
Proof.
  intros i k m st Hi. rewrite z2side_den. unfold z2cells.
  rewrite <- !app_assoc. cbn [app]. rewrite zc_cls by exact Hi.
  cbn [zc]. rewrite <- !app_assoc, app_nil_r. reflexivity.
Qed.

Lemma z2_end_r : forall i k m st, i < 2 ->
  z2cells (zu0 i ++ wrep [0;0] (k + st * m) ++ [1])
    = sden [] m (z2side (zU0 i) [S0;S0] k st ([S1;S1] ++ T)).
Proof.
  intros i k m st Hi. rewrite z2side_den. unfold z2cells.
  rewrite <- !app_assoc. cbn [app]. rewrite zc_zcls by exact Hi.
  cbn [zc]. rewrite <- !app_assoc, app_nil_r. reflexivity.
Qed.

Lemma z2_top_l : forall i k m st, i < 2 ->
  z2cells (zu i ++ wrep [0;1] (k + st * m))
    = sden [] m (z2side (zU i) [S1;S1] k st T).
Proof.
  intros i k m st Hi. rewrite z2side_den. unfold z2cells.
  rewrite <- !app_assoc. rewrite zc_cls by exact Hi.
  cbn [zc]. rewrite <- !app_assoc, app_nil_r. reflexivity.
Qed.

Lemma z2_top_r : forall i k m st, i < 2 ->
  z2cells (zu0 i ++ wrep [0;0] (k + st * m) ++ [0])
    = sden [] m (z2side (zU0 i) [S0;S0] k st ([S0;S0] ++ T)).
Proof.
  intros i k m st Hi. rewrite z2side_den. unfold z2cells.
  rewrite <- !app_assoc. cbn [app]. rewrite zc_zcls by exact Hi.
  cbn [zc]. rewrite <- !app_assoc, app_nil_r. reflexivity.
Qed.

End Cells2.

(** ** 3. The board *)

Section BoardZ2Tr.

Variable tm0   : TM.
Variable pins  : list Instr.
Local Notation tm := (tm_wrap_trs tm0 pins).

Variable F     : Fam.
Variable T     : list Sym.
Variable AI    : nat -> nat -> LRule.   (** interior: kind, index *)
Variable N0i sti : nat.
Variable AE    : nat -> nat -> LRule.   (** end: kind, index *)
Variable N0e ste : nat.
Variable AT    : nat -> nat -> LRule.   (** top: kind, index *)
Variable N0t stt : nat.
Variable rsv   : list LRule.
Variable vsegs : nat -> nat -> Instr -> list nseg.
Variable visI  : nat -> nat -> Instr -> list lstep.
Variable x0    : list nat.

Hypothesis Hz0 : zok x0 = true.
Hypothesis Hl0 : 0 < length x0.

Hypothesis Hsti : 0 < sti.
Hypothesis HAIS : forall i r, i < 2 -> r < N0i + sti ->
  ReachL tm (negb (fm_left F)) (fm_left F) (lr_lhs (AI i r)) (lr_rhs (AI i r)).
Hypothesis HAIL : forall i r, i < 2 -> r < N0i + sti ->
  lr_lhs (AI i r) = cls_conf F (z2side F (zU i) [S1;S1] r (astride N0i sti r) [S0]).
Hypothesis HAIR : forall i r, i < 2 -> r < N0i + sti ->
  lr_rhs (AI i r) = cls_conf F (z2side F (zU0 i) [S0;S0] r (astride N0i sti r) [S1;S1]).

Hypothesis Hste : 0 < ste.
Hypothesis HAES : forall i r, i < 2 -> r < N0e + ste ->
  ReachL tm true true (lr_lhs (AE i r)) (lr_rhs (AE i r)).
Hypothesis HAEL : forall i r, i < 2 -> r < N0e + ste ->
  lr_lhs (AE i r) = cls_conf F (z2side F (zU i) [S1;S1] r (astride N0e ste r) ([S0] ++ T)).
Hypothesis HAER : forall i r, i < 2 -> r < N0e + ste ->
  lr_rhs (AE i r) = cls_conf F (z2side F (zU0 i) [S0;S0] r (astride N0e ste r) ([S1;S1] ++ T)).

Hypothesis Hstt : 0 < stt.
Hypothesis HN0t : 0 < N0t.
Hypothesis HATS : forall i r, i < 2 -> r < N0t + stt -> (i = 0 -> 0 < r) ->
  ReachL tm true true (lr_lhs (AT i r)) (lr_rhs (AT i r)).
Hypothesis HATL : forall i r, i < 2 -> r < N0t + stt -> (i = 0 -> 0 < r) ->
  lr_lhs (AT i r) = cls_conf F (z2side F (zU i) [S1;S1] r (astride N0t stt r) T).
Hypothesis HATR : forall i r, i < 2 -> r < N0t + stt -> (i = 0 -> 0 < r) ->
  lr_rhs (AT i r) = cls_conf F (z2side F (zU0 i) [S0;S0] r (astride N0t stt r) ([S0;S0] ++ T)).

Hypothesis Hrsv : Forall (RuleSound tm false false) rsv.
Hypothesis Hfire : forall i r t, ~ In t pins -> i < 2 -> r < N0t + stt ->
  (i = 0 -> 0 < r) ->
  nfire tm true true rsv (vsegs i r t) (visI i r t) (lr_lhs (AT i r)) = Some t.

Local Notation Cf := (fun n => z2cfg F T (ziter x0 n)).

(** the top arm serving a top string, and its configuration *)
Lemma top_armZ2 : forall i k, i < 2 -> 0 < length (zu i ++ wrep [0;1] k) ->
  let r := aoff N0t stt k in
  r < N0t + stt /\ (i = 0 -> 0 < r)
  /\ z2cfg F T (zu i ++ wrep [0;1] k)
     = cden [] [] (acnt N0t stt k) (lr_lhs (AT i r)).
Proof.
  intros i k Hi Hl r.
  assert (Hrlt : r < N0t + stt) by (apply arm_index_lt; exact Hstt).
  assert (Hr0 : i = 0 -> 0 < r).
  { intros ->. apply arm_index_pos; [exact HN0t|].
    cbn [zu Nat.eqb app] in Hl. rewrite wrep_length in Hl. cbn in Hl. lia. }
  assert (Hk : r + astride N0t stt r * acnt N0t stt k = k)
    by (apply arm_index; exact Hstt).
  split; [exact Hrlt | split; [exact Hr0|]].
  rewrite (HATL i r Hi Hrlt Hr0).
  assert (Hc : z2cells F T (zu i ++ wrep [0;1] k)
                 = sden [] (acnt N0t stt k) (z2side F (zU i) [S1;S1] r (astride N0t stt r) T)).
  { rewrite <- Hk at 1. apply z2_top_l. exact Hi. }
  pose proof (cden_z2 F T _ [] _ _ Hc) as H.
  rewrite tailL_nil, tailR_nil in H. symmetry. exact H.
Qed.

Lemma board_armZ2 : forall x, ZInv x ->
  exists A el er X n,
    ReachL tm el er (lr_lhs A) (lr_rhs A)
    /\ (el = true -> tailL F X = []) /\ (er = true -> tailR F X = [])
    /\ z2cfg F T x = cden (tailL F X) (tailR F X) n (lr_lhs A)
    /\ z2cfg F T (zinc x) = cden (tailL F X) (tailR F X) n (lr_rhs A).
Proof.
  intros x (Hz & Hl).
  destruct (zdec x Hz) as (i & k & s & Hi & Hxe & [Hs | [Hs | (r0 & Hs)]]); subst s.
  - (* the top *)
    rewrite app_nil_r in Hxe. subst x.
    destruct (top_armZ2 i k Hi Hl) as (Hrlt & Hr0 & Hden).
    set (r := aoff N0t stt k) in *.
    assert (Hk : r + astride N0t stt r * acnt N0t stt k = k)
      by (apply arm_index; exact Hstt).
    exists (AT i r), true, true, [], (acnt N0t stt k).
    split; [|split; [|split; [|split]]].
    + exact (HATS i r Hi Hrlt Hr0).
    + intros _; apply tailL_nil.
    + intros _; apply tailR_nil.
    + rewrite tailL_nil, tailR_nil. exact Hden.
    + rewrite zstep_top by exact Hi. rewrite (HATR i r Hi Hrlt Hr0). symmetry.
      apply cden_z2. rewrite <- Hk at 1. apply z2_top_r. exact Hi.
  - (* the end *)
    subst x.
    remember (aoff N0e ste k) as r eqn:Er.
    assert (Hrlt : r < N0e + ste) by (subst r; apply arm_index_lt; exact Hste).
    assert (Hk : r + astride N0e ste r * acnt N0e ste k = k)
      by (subst r; apply arm_index; exact Hste).
    exists (AE i r), true, true, [], (acnt N0e ste k).
    split; [|split; [|split; [|split]]].
    + exact (HAES i r Hi Hrlt).
    + intros _; apply tailL_nil.
    + intros _; apply tailR_nil.
    + rewrite (HAEL i r Hi Hrlt). symmetry. apply cden_z2.
      rewrite <- Hk at 1. apply z2_end_l. exact Hi.
    + rewrite (proj1 (zstep_end i k Hi)), (HAER i r Hi Hrlt). symmetry.
      apply cden_z2. rewrite <- Hk at 1. apply z2_end_r. exact Hi.
  - (* the interior *)
    subst x.
    remember (aoff N0i sti k) as r eqn:Er.
    assert (Hrlt : r < N0i + sti) by (subst r; apply arm_index_lt; exact Hsti).
    assert (Hk : r + astride N0i sti r * acnt N0i sti k = k)
      by (subst r; apply arm_index; exact Hsti).
    exists (AI i r), (negb (fm_left F)), (fm_left F), (zc (r0 ++ [0]) ++ T), (acnt N0i sti k).
    split; [|split; [|split; [|split]]].
    + exact (HAIS i r Hi Hrlt).
    + intros He. unfold tailL. destruct (fm_left F); [discriminate|reflexivity].
    + intros He. unfold tailR. rewrite He. reflexivity.
    + rewrite (HAIL i r Hi Hrlt). symmetry. apply cden_z2.
      rewrite <- Hk at 1. apply z2_int_l. exact Hi.
    + rewrite (proj1 (zstep_int i k r0 Hi)), (HAIR i r Hi Hrlt). symmetry.
      apply cden_z2. rewrite <- Hk at 1. apply z2_int_r. exact Hi.
Qed.

Lemma zinv0Z2 : ZInv x0.
Proof. split; assumption. Qed.

Lemma lapZ2 : forall n, exists m c',
  0 < m /\ csteps tm m (Cf n) = Some c' /\ lift c' = lift (Cf (S n)).
Proof.
  intros n.
  destruct (board_armZ2 _ (ziter_inv n x0 zinv0Z2))
    as (A & el & er & X & k & HA & HL & HR & Hl & Hr).
  destruct (HA _ _ k HL HR) as (m & c' & Hm & Hc' & Hlc).
  exists m, c'. split; [exact Hm|]. split.
  - cbn beta. rewrite Hl. exact Hc'.
  - rewrite Hlc, <- Hr. cbn beta.
    replace (S n) with (n + 1) by lia. rewrite ziter_add. reflexivity.
Qed.

Lemma fireZ2 : forall t N, ~ In t pins ->
  exists n k c', N <= n /\ csteps tm k (Cf n) = Some c' /\ cinstr c' = t.
Proof.
  intros t N Hnp.
  destruct (ztops_cofinal x0 N zinv0Z2) as (n & HN & (i & k & Hi & Hx) & (_ & Hl)).
  exists n. cbn beta. rewrite Hx. rewrite Hx in Hl.
  destruct (top_armZ2 i k Hi Hl) as (Hrlt & Hr0 & Hden).
  set (r := aoff N0t stt k) in *.
  destruct (nfire_sound tm true true rsv (vsegs i r t) (visI i r t)
              (lr_lhs (AT i r)) t Hrsv (Hfire i r t Hnp Hi Hrlt Hr0)
              [] [] (acnt N0t stt k)
              (fun _ => eq_refl) (fun _ => eq_refl)) as (k' & c' & Hc' & Ht).
  exists k', c'. rewrite Hden. split; [exact HN | split; [exact Hc' | exact Ht]].
Qed.

Theorem boardZ2_neverqhtr : forall t0,
  stepn tm t0 InitES = Some (lift (z2cfg F T x0)) ->
  NeverQuasiHaltsTr tm0.
Proof.
  intros t0 Hboot.
  apply (glue_neverqhtrN tm0 pins Cf).
  - exists t0. exact Hboot.
  - intros n. destruct (lapZ2 n) as (m & c' & Hm & Hrun & Hl).
    exists m, c'. split; [exact Hrun | split; [exact Hl | exact Hm]].
  - intros t Hnp N. exact (fireZ2 t N Hnp).
Qed.

Lemma reachZ2 : forall d n,
  exists Tm, stepn tm Tm (lift (Cf n)) = Some (lift (Cf (n + d))).
Proof.
  induction d; intros n.
  - exists 0. rewrite Nat.add_0_r. reflexivity.
  - destruct (IHd n) as (Tm & HT).
    destruct (lapZ2 (n + d)) as (m & c' & _ & Hm & Hl).
    exists (Tm + m). rewrite stepn_add, HT.
    replace (n + S d) with (S (n + d)) by lia.
    rewrite <- Hl. apply csteps_lift. exact Hm.
Qed.

Lemma fire_everyZ2 : forall t, ~ In t pins -> forall n,
  exists k c', csteps tm k (Cf n) = Some c' /\ cinstr c' = t.
Proof.
  intros t Hnp n.
  destruct (fireZ2 t n Hnp) as (m & k & c' & Hm & Hk & Hc').
  destruct (reachZ2 (m - n) n) as (Tm & HT).
  replace (n + (m - n)) with m in HT by lia.
  assert (Hs : stepn tm (Tm + k) (lift (Cf n)) = Some (lift c')).
  { rewrite stepn_add, HT. apply csteps_lift. exact Hk. }
  destruct (stepn_csteps_at tm (Tm + k) (Cf n) (lift c') Hs) as (c'' & Hc'' & Hl').
  exists (Tm + k), c''. split; [exact Hc''|].
  rewrite <- cinstr_lift, Hl', cinstr_lift. exact Hc'.
Qed.

Theorem boardZ2_qhtr : forall t0 B,
  stepn tm0 t0 InitES = Some (lift (z2cfg F T x0)) ->
  existsb (fun tg => cfires tm0 CTape.c0 t0 tg) pins = true ->
  (t0 <=? B) = true ->
  NonHalt tm0 /\ QHBoundTr B tm0 /\ QuasiHaltsTr tm0.
Proof.
  intros t0 B Hboot Hwit Hle.
  apply (lap_qh_stage tm0 pins (fun p => Cf (Nat.pred (Pos.to_nat p)))
           1%positive t0 B).
  - exact Hboot.
  - intros p _.
    destruct (lapZ2 (Nat.pred (Pos.to_nat p))) as (m & c' & Hm & Hrun & Hl).
    exists m, c'. split; [exact Hrun | split; [|exact Hm]].
    rewrite Hl, Pos2Nat.inj_succ.
    replace (S (Nat.pred (Pos.to_nat p))) with (Pos.to_nat p)
      by (pose proof (Pos2Nat.is_pos p); lia).
    reflexivity.
  - intros t Hnp p _. exact (fire_everyZ2 t Hnp (Nat.pred (Pos.to_nat p))).
  - exact Hwit.
  - exact Hle.
Qed.

End BoardZ2Tr.
