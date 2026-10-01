(** * Checkers.LadderCheckRun2Tr: terminator-run counters with a MARKER
    between the digits and the run (SCOPING_INSTR 7.4.LE4).

    [LadderCheckRunTr] states [pre x T^m suf]: the top of [x] narrows it by a
    digit and lengthens the run, an empty [x] refills.  Its narrowing is
    [t^j T X -> 0^(j-1) T T X], so the word after [x] must BE the run word.
    LE4's rows ([0RB0LC_1LC0RD_1LA1LD_0LA1RB]: [A0 x 01 (11)^m 1], [x] over
    [10] / [11]) put a different word [M] there, and their run can be empty:

      (x, m)       -> (x + 1, m)                 while x is not all top;
      (top^j, m)   -> (0^(j-1), m + 1)  (j >= 1)  the top narrows x;
      ([], m)      -> (0^(m + a), c)             an empty x refills.

    The cells are [pre ++ x ++ M ++ T^m ++ suf]; [M = T] with [m >= 1] is
    [LadderCheckRunTr] again.  So this file is that one with [M] added
    (every name suffixed [M]) and two changes: the invariant drops
    [1 <= m] (the run may be empty, so the refill arms are indexed from 0),
    and the narrowing is [t^j M X -> 0^(j-1) M T X].  LE4's positional
    finder reads these rows as a counter whose FILL costs about twice as
    much at each width: the narrowings and the refill are that fill.

    Three arm classes, all [LadderNest.ReachL] programs:
    - interior: [t^n d X -> 0^n (d+1) X], [X] opaque;
    - narrowing: [t^j M X -> 0^(j-1) M T X], [X] opaque, [j >= 1];
    - refill: [M T^m suf -> 0^(m+a) M T^c suf], both tails known empty.

    Nothing landed is modified.  Axiom footprint: [functional_extensionality_dep],
    via [CTape.lift]. *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape ClosureTr.
From BBB4.Counters Require Import WTape LapCertGlueLift.
From BBB4.Checkers Require Import WrapTr LapDecider LadderKernel LadderFam LadderCheck LadderCheckTr LadderNest LadderCheckNestTr TCyclerQHTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
From BBB4.Counters Require Import LapGlueTr.
From BBB4.CensusTr Require Import TNF_QHTr QHConveyorTr.
Import ListNotations.

(** ** 1. The counter *)

Section RunM.

Variable F : Fam.
Variable M T suf : list Sym.
Variable a c : nat.

Local Notation b := (fm_b F).

Fixpoint incM (x : list nat) : list nat :=
  match x with
  | [] => []
  | d :: t => if d =? b - 1 then 0 :: incM t else S d :: t
  end.

Definition alltopM (x : list nat) : bool := forallb (Nat.eqb (b - 1)) x.

Definition RStM : Type := (list nat * nat)%type.

Definition rsuccM (s : RStM) : RStM :=
  let '(x, m) := s in
  match x with
  | [] => (repeat 0 (m + a), c)
  | _ :: _ => if alltopM x then (repeat 0 (length x - 1), S m) else (incM x, m)
  end.

Fixpoint riterM (s : RStM) (n : nat) : RStM :=
  match n with
  | O => s
  | S n' => riterM (rsuccM s) n'
  end.

Lemma riter_addM : forall n1 n2 s, riterM s (n1 + n2) = riterM (riterM s n1) n2.
Proof. induction n1 as [|n1 IH]; intros n2 s; [reflexivity | apply IH]. Qed.

Definition rcellsM (x : list nat) (m : nat) : list Sym :=
  fm_pre F ++ flat_map (dig F) x ++ M ++ rep T m ++ suf.

Definition rcfgM (s : RStM) : cconf :=
  let '(x, m) := s in
  if fm_left F
  then (fm_st F, (rcellsM x m, fm_hs F, fm_other F))
  else (fm_st F, (fm_other F, fm_hs F, rcellsM x m)).

Lemma rcfg_clsM : forall sd X n x m,
  rcellsM x m = sden X n sd ->
  cden (tailL F X) (tailR F X) n (cls_conf F sd) = rcfgM (x, m).
Proof.
  intros sd X n x m H.
  unfold cden, cls_conf, rcfgM, tailL, tailR.
  destruct (fm_left F); simpl; rewrite sden_flat, app_nil_r, <- H; reflexivity.
Qed.

(** *** The odometer carry, and the value it adds one to *)

Lemma inc_classM : forall n d rest, d < b - 1 ->
  incM (repeat (b - 1) n ++ d :: rest) = repeat 0 n ++ S d :: rest.
Proof.
  induction n as [|n IH]; intros d rest Hd; cbn [repeat app incM].
  - destruct (Nat.eqb_spec d (b - 1)); [lia | reflexivity].
  - rewrite Nat.eqb_refl, IH by exact Hd. reflexivity.
Qed.

Lemma alltop_repeatM : forall n, alltopM (repeat (b - 1) n) = true.
Proof.
  induction n as [|n IH]; [reflexivity|]. cbn [repeat alltopM forallb].
  rewrite Nat.eqb_refl. exact IH.
Qed.

Lemma alltop_classM : forall n d rest, d <> b - 1 ->
  alltopM (repeat (b - 1) n ++ d :: rest) = false.
Proof.
  induction n as [|n IH]; intros d rest Hd; cbn [repeat app alltopM forallb].
  - destruct (Nat.eqb_spec (b - 1) d); [lia | reflexivity].
  - rewrite Nat.eqb_refl. apply IH. exact Hd.
Qed.

Hypothesis Hb : 1 < b.

Lemma inc_valM : forall x, Forall (fun d => d < b) x -> alltopM x = false ->
  val_pos b (incM x) = S (val_pos b x).
Proof.
  induction x as [|d t IH]; intros Hx Ht; [discriminate|].
  inversion Hx as [|? ? Hd Htl]; subst.
  cbn [incM alltopM forallb] in *.
  destruct (Nat.eqb_spec d (b - 1)) as [E|E].
  - subst d. rewrite Nat.eqb_refl in Ht. cbn [andb] in Ht.
    cbn [val_pos]. rewrite (IH Htl Ht). nia.
  - cbn [val_pos]. lia.
Qed.

Lemma inc_lenM : forall x, length (incM x) = length x.
Proof.
  induction x as [|d t IH]; [reflexivity|]. cbn [incM].
  destruct (d =? b - 1); cbn [length]; [rewrite IH|]; reflexivity.
Qed.

Lemma inc_bndM : forall x, Forall (fun d => d < b) x -> alltopM x = false ->
  Forall (fun d => d < b) (incM x).
Proof.
  induction x as [|d t IH]; intros Hx Ht; [constructor|].
  inversion Hx as [|? ? Hd Htl]; subst.
  cbn [incM alltopM forallb] in *.
  destruct (Nat.eqb_spec d (b - 1)) as [E|E].
  - subst d. rewrite Nat.eqb_refl in Ht. constructor; [lia | apply IH; assumption].
  - constructor; [lia | exact Htl].
Qed.

Lemma repeat0_bndM : forall n, Forall (fun d => d < b) (repeat 0 n).
Proof.
  intros n. apply Forall_forall. intros y Hy. apply repeat_spec in Hy. lia.
Qed.

(** *** Refills recur *)

Definition RInvM (s : RStM) : Prop :=
  let '(x, m) := s in Forall (fun d => d < b) x.

Lemma rsucc_invM : forall s, RInvM s -> RInvM (rsuccM s).
Proof.
  intros [x m] Hx. destruct x as [|d t]; cbn [rsuccM].
  - apply repeat0_bndM.
  - destruct (alltopM (d :: t)) eqn:E.
    + apply repeat0_bndM.
    + apply inc_bndM; assumption.
Qed.

Lemma riter_invM : forall n s, RInvM s -> RInvM (riterM s n).
Proof.
  induction n as [|n IH]; intros s Hs; [exact Hs|]. apply IH, rsucc_invM, Hs.
Qed.

Lemma refill_reachedM : forall k v s, RInvM s ->
  length (fst s) <= k ->
  Nat.pow b (length (fst s)) - val_pos b (fst s) <= v ->
  exists n, fst (riterM s n) = [].
Proof.
  induction k as [|k IHk]; intros v [x m] Hs Hk Hv; cbn [fst] in *.
  - destruct x; [exists 0; reflexivity | cbn in Hk; lia].
  - revert x m Hs Hk Hv. induction v as [|v IHv]; intros x m Hs Hk Hv.
    + exfalso. pose proof (val_pos_lt b x Hb Hs). lia.
    + destruct x as [|d t]; [exists 0; reflexivity|]. cbn [length] in Hk, Hv.
      destruct (alltopM (d :: t)) eqn:E.
      * (* the narrowing: one digit fewer *)
        destruct (IHk (Nat.pow b (length t)) (rsuccM (d :: t, m)) (rsucc_invM _ Hs))
          as (n & Hn).
        -- cbn [rsuccM]. rewrite E. cbn [fst length]. rewrite repeat_length. lia.
        -- cbn [rsuccM]. rewrite E. cbn [fst length]. rewrite repeat_length.
           replace (S (length t) - 1) with (length t) by lia. lia.
        -- exists (S n). exact Hn.
      * (* inside the length: the value rises by one *)
        assert (Hi : RInvM (incM (d :: t), m)) by (apply inc_bndM; assumption).
        destruct (IHv (incM (d :: t)) m Hi) as (n & Hn).
        -- rewrite inc_lenM. cbn [length] in *. exact Hk.
        -- rewrite inc_lenM, inc_valM by assumption. cbn [length] in *. lia.
        -- exists (S n). cbn [riterM rsuccM]. rewrite E. exact Hn.
Qed.

Theorem refill_cofinalM : forall s N, RInvM s ->
  exists n, N <= n /\ fst (riterM s n) = [] /\ RInvM (riterM s n).
Proof.
  intros s N Hs.
  pose proof (riter_invM N s Hs) as HsN.
  destruct (refill_reachedM (length (fst (riterM s N)))
              (Nat.pow b (length (fst (riterM s N))) - val_pos b (fst (riterM s N)))
              (riterM s N) HsN ltac:(lia) ltac:(lia)) as (n & Hn).
  exists (N + n). rewrite riter_addM.
  split; [lia | split; [exact Hn | apply riter_invM, HsN]].
Qed.

(** *** The cells of each class *)

Lemma rcells_intM : forall t r st n d rest m,
  rcellsM (repeat t (r + st * n) ++ d :: rest) m
    = sden (flat_map (dig F) rest ++ M ++ rep T m ++ suf) n
        (cls_side F [] t r st [d]).
Proof.
  intros t r st n d rest m. unfold rcellsM, cls_side.
  rewrite blk_den, flat_map_app, flat_map_repeat_nil.
  cbn [flat_map app]. rewrite app_nil_r, rep_add, !app_assoc. reflexivity.
Qed.

Lemma rcells_topM : forall t r st n m,
  rcellsM (repeat t (r + st * n)) m
    = sden (rep T m ++ suf) n
        (blk (fm_pre F ++ rep (dig F t) r) (dig F t) st M).
Proof.
  intros t r st n m. unfold rcellsM.
  rewrite blk_den, flat_map_repeat_nil, rep_add.
  rewrite !app_assoc. reflexivity.
Qed.

Lemma rcells_narM : forall t r st n m,
  rcellsM (repeat t (r + st * n)) (S m)
    = sden (rep T m ++ suf) n
        (blk (fm_pre F ++ rep (dig F t) r) (dig F t) st (M ++ T)).
Proof.
  intros t r st n m. unfold rcellsM.
  rewrite blk_den, flat_map_repeat_nil, rep_add. cbn [rep].
  rewrite !app_assoc. reflexivity.
Qed.

Lemma rcells_refillM : forall r st n,
  rcellsM [] (r + st * n)
    = sden [] n (blk (fm_pre F ++ M ++ rep T r) T st suf).
Proof.
  intros r st n. unfold rcellsM.
  rewrite blk_den, rep_add. cbn [flat_map].
  rewrite ?app_nil_r, !app_assoc, ?app_nil_r. reflexivity.
Qed.

Lemma rcells_refilledM : forall f1 st n f2,
  rcellsM (repeat 0 (f1 + st * n + f2)) c
    = sden [] n (blk (fm_pre F ++ rep (dig F 0) f1) (dig F 0) st
                   (rep (dig F 0) f2 ++ M ++ rep T c ++ suf)).
Proof.
  intros f1 st n f2. unfold rcellsM.
  rewrite blk_den, flat_map_repeat_nil, !rep_add, !app_nil_r, !app_assoc.
  reflexivity.
Qed.

Lemma rsucc_consM : forall x m, x <> [] ->
  rsuccM (x, m) = if alltopM x then (repeat 0 (length x - 1), S m) else (incM x, m).
Proof. intros [|d t] m H; [congruence | reflexivity]. Qed.

End RunM.

(** ** 2. The board *)

Section BoardRTrM.

Variable tm0   : TM.
Variable pins  : list Instr.
Local Notation tm := (tm_wrap_trs tm0 pins).

Variable F     : Fam.
Variable M T suf : list Sym.
Variable a c   : nat.
Variable AI    : nat -> nat -> LRule.   (** interior: digit, index *)
Variable N0i sti : nat.
Variable AN    : nat -> LRule.          (** narrowing: index *)
Variable N0n stn : nat.
Variable AR    : nat -> LRule.          (** refill: index *)
Variable N0r str : nat.
Variable fm1 fm2 : nat -> nat.
Variable rsv   : list LRule.
Variable vsegs : nat -> Instr -> list nseg.
Variable visI  : nat -> Instr -> list lstep.
Variable x0    : list nat.
Variable m0    : nat.

Local Notation b := (fm_b F).

Hypothesis Hb    : 1 < b.
Hypothesis Hbnd0 : Forall (fun d => d < b) x0.

Hypothesis Hsti : 0 < sti.
Hypothesis HAIS : forall d r, d < b - 1 -> r < N0i + sti ->
  ReachL tm (negb (fm_left F)) (fm_left F) (lr_lhs (AI d r)) (lr_rhs (AI d r)).
Hypothesis HAIL : forall d r, d < b - 1 -> r < N0i + sti ->
  lr_lhs (AI d r) = cls_conf F (cls_side F [] (b - 1) r (astride N0i sti r) [d]).
Hypothesis HAIR : forall d r, d < b - 1 -> r < N0i + sti ->
  lr_rhs (AI d r) = cls_conf F (cls_side F [] 0 r (astride N0i sti r) [S d]).

Hypothesis Hstn : 0 < stn.
Hypothesis HN0n : 0 < N0n.
Hypothesis HANS : forall r, 0 < r -> r < N0n + stn ->
  ReachL tm (negb (fm_left F)) (fm_left F) (lr_lhs (AN r)) (lr_rhs (AN r)).
Hypothesis HANL : forall r, 0 < r -> r < N0n + stn ->
  lr_lhs (AN r) = cls_conf F (blk (fm_pre F ++ rep (dig F (b - 1)) r)
                                (dig F (b - 1)) (astride N0n stn r) M).
Hypothesis HANR : forall r, 0 < r -> r < N0n + stn ->
  lr_rhs (AN r) = cls_conf F (blk (fm_pre F ++ rep (dig F 0) (r - 1))
                                (dig F 0) (astride N0n stn r) (M ++ T)).

Hypothesis Hstr : 0 < str.
Hypothesis HARS : forall r, r < N0r + str ->
  ReachL tm true true (lr_lhs (AR r)) (lr_rhs (AR r)).
Hypothesis HARL : forall r, r < N0r + str ->
  lr_lhs (AR r) = cls_conf F (blk (fm_pre F ++ M ++ rep T r) T (astride N0r str r) suf).
Hypothesis HARR : forall r, r < N0r + str ->
  lr_rhs (AR r) = cls_conf F (blk (fm_pre F ++ rep (dig F 0) (fm1 r)) (dig F 0)
                                (astride N0r str r)
                                (rep (dig F 0) (fm2 r) ++ M ++ rep T c ++ suf)).
Hypothesis Hfm : forall r, r < N0r + str -> fm1 r + fm2 r = r + a.

Hypothesis Hrsv : Forall (RuleSound tm false false) rsv.
Hypothesis Hfire : forall r t, ~ In t pins -> r < N0r + str ->
  nfire tm true true rsv (vsegs r t) (visI r t) (lr_lhs (AR r)) = Some t.

Local Notation Cf := (fun n => rcfgM F M T suf (riterM F a c (x0, m0) n)).

Lemma rinv0M : RInvM F (x0, m0).
Proof. exact Hbnd0. Qed.

Lemma board_armRM : forall s, RInvM F s ->
  exists A el er X n,
    ReachL tm el er (lr_lhs A) (lr_rhs A)
    /\ (el = true -> tailL F X = []) /\ (er = true -> tailR F X = [])
    /\ rcfgM F M T suf s = cden (tailL F X) (tailR F X) n (lr_lhs A)
    /\ rcfgM F M T suf (rsuccM F a c s) = cden (tailL F X) (tailR F X) n (lr_rhs A).
Proof.
  intros [x m] Hx.
  destruct x as [|d0 t0] eqn:Ex.
  - (* the refill *)
    remember (aoff N0r str m) as r eqn:Er.
    assert (Hrlt : r < N0r + str) by (subst r; apply arm_index_lt; assumption).
    assert (Hk : r + astride N0r str r * acnt N0r str m = m)
      by (subst r; apply arm_index; assumption).
    exists (AR r), true, true, [], (acnt N0r str m).
    split; [|split; [|split; [|split]]].
    + exact (HARS r Hrlt).
    + intros _; apply tailL_nil.
    + intros _; apply tailR_nil.
    + rewrite (HARL r Hrlt). symmetry. apply rcfg_clsM.
      rewrite <- Hk at 1. apply rcells_refillM.
    + rewrite (HARR r Hrlt). symmetry. cbn [rsuccM]. apply rcfg_clsM.
      pose proof (Hfm r Hrlt).
      rewrite <- (rcells_refilledM F M T suf c (fm1 r) (astride N0r str r)
                    (acnt N0r str m) (fm2 r)).
      f_equal. f_equal. lia.
  - rewrite <- Ex. assert (Hne : x <> []) by (subst x; discriminate).
    rewrite <- Ex in Hx.
    destruct (digs_decomp (b - 1) x) as [Htop | (n & d & rest & Hxe & Hd)].
    + (* the narrowing *)
      set (j := length x) in Htop.
      assert (Hj : 0 < j) by (unfold j; subst x; cbn; lia).
      remember (aoff N0n stn j) as r eqn:Er.
      assert (Hr0 : 0 < r) by (subst r; apply arm_index_pos; assumption).
      assert (Hrlt : r < N0n + stn) by (subst r; apply arm_index_lt; assumption).
      assert (Hk : r + astride N0n stn r * acnt N0n stn j = j)
        by (subst r; apply arm_index; assumption).
      exists (AN r), (negb (fm_left F)), (fm_left F), (rep T m ++ suf), (acnt N0n stn j).
      split; [|split; [|split; [|split]]].
      * exact (HANS r Hr0 Hrlt).
      * intros He. unfold tailL. destruct (fm_left F); [discriminate|reflexivity].
      * intros He. unfold tailR. rewrite He. reflexivity.
      * rewrite (HANL r Hr0 Hrlt). symmetry. apply rcfg_clsM.
        rewrite Htop, <- Hk at 1. apply rcells_topM.
      * rewrite (HANR r Hr0 Hrlt). symmetry.
        rewrite (rsucc_consM F a c x m Hne).
        rewrite Htop at 1. rewrite (alltop_repeatM F).
        apply rcfg_clsM. fold j.
        replace (j - 1) with ((r - 1) + astride N0n stn r * acnt N0n stn j) by lia.
        apply rcells_narM.
    + (* the interior *)
      rewrite Hxe in Hx.
      apply Forall_app in Hx as [_ Hrest'].
      inversion Hrest' as [|? ? Hdb Hrest].
      assert (Hdlt : d < b - 1) by lia.
      remember (aoff N0i sti n) as r eqn:Er.
      assert (Hrlt : r < N0i + sti) by (subst r; apply arm_index_lt; assumption).
      assert (Hn : r + astride N0i sti r * acnt N0i sti n = n)
        by (subst r; apply arm_index; assumption).
      exists (AI d r), (negb (fm_left F)), (fm_left F),
             (flat_map (dig F) rest ++ M ++ rep T m ++ suf), (acnt N0i sti n).
      split; [|split; [|split; [|split]]].
      * exact (HAIS d r Hdlt Hrlt).
      * intros He. unfold tailL. destruct (fm_left F); [discriminate|reflexivity].
      * intros He. unfold tailR. rewrite He. reflexivity.
      * rewrite (HAIL d r Hdlt Hrlt). symmetry. apply rcfg_clsM.
        rewrite Hxe, <- Hn at 1. apply rcells_intM.
      * rewrite (HAIR d r Hdlt Hrlt). symmetry.
        rewrite (rsucc_consM F a c x m Hne), Hxe.
        rewrite (alltop_classM F n d rest Hd), (inc_classM F n d rest Hdlt).
        apply rcfg_clsM. rewrite <- Hn at 1. apply rcells_intM.
Qed.

Lemma lapRM : forall n, exists m c',
  0 < m /\ csteps tm m (Cf n) = Some c' /\ lift c' = lift (Cf (S n)).
Proof.
  intros n.
  pose proof (riter_invM F a c Hb n (x0, m0) rinv0M) as Hi.
  destruct (board_armRM _ Hi) as (A & el & er & X & k & HA & HL & HR & Hl & Hr).
  destruct (HA _ _ k HL HR) as (m & c' & Hm & Hc' & Hlc).
  exists m, c'. split; [exact Hm|]. split.
  - cbn beta. rewrite Hl. exact Hc'.
  - rewrite Hlc, <- Hr. cbn beta.
    replace (S n) with (n + 1) by lia. rewrite riter_addM. reflexivity.
Qed.

Lemma fireRM : forall t N, ~ In t pins ->
  exists n k c', N <= n /\ csteps tm k (Cf n) = Some c' /\ cinstr c' = t.
Proof.
  intros t N Hnp.
  destruct (refill_cofinalM F a c Hb (x0, m0) N rinv0M) as (n & HN & Hx & Hi).
  exists n.
  destruct (riterM F a c (x0, m0) n) as [x m] eqn:Eit.
  cbn [fst] in Hx. subst x.
  remember (aoff N0r str m) as r eqn:Er.
  assert (Hrlt : r < N0r + str) by (subst r; apply arm_index_lt; assumption).
  assert (Hk : r + astride N0r str r * acnt N0r str m = m)
    by (subst r; apply arm_index; assumption).
  assert (Hden : rcfgM F M T suf ([], m)
                 = cden [] [] (acnt N0r str m) (lr_lhs (AR r))).
  { rewrite (HARL r Hrlt).
    rewrite <- (rcfg_clsM F M T suf
                  (blk (fm_pre F ++ M ++ rep T r) T (astride N0r str r) suf)
                  [] (acnt N0r str m) [] m).
    - unfold tailL, tailR; destruct (fm_left F); reflexivity.
    - rewrite <- Hk at 1. apply rcells_refillM. }
  destruct (nfire_sound tm true true rsv (vsegs r t) (visI r t)
              (lr_lhs (AR r)) t Hrsv (Hfire r t Hnp Hrlt)
              [] [] (acnt N0r str m)
              (fun _ => eq_refl) (fun _ => eq_refl)) as (k & c' & Hc' & Ht).
  exists k, c'. cbn beta. rewrite ?Eit, Hden.
  split; [exact HN | split; [exact Hc' | exact Ht]].
Qed.

Theorem boardR_neverqhtrM : forall t0,
  stepn tm t0 InitES = Some (lift (rcfgM F M T suf (x0, m0))) ->
  NeverQuasiHaltsTr tm0.
Proof.
  intros t0 Hboot.
  apply (glue_neverqhtrN tm0 pins Cf).
  - exists t0. exact Hboot.
  - intros n. destruct (lapRM n) as (m & c' & Hm & Hrun & Hl).
    exists m, c'. split; [exact Hrun | split; [exact Hl | exact Hm]].
  - intros t Hnp N. exact (fireRM t N Hnp).
Qed.

Lemma reachRM : forall d n,
  exists Tm, stepn tm Tm (lift (Cf n)) = Some (lift (Cf (n + d))).
Proof.
  induction d; intros n.
  - exists 0. rewrite Nat.add_0_r. reflexivity.
  - destruct (IHd n) as (Tm & HT).
    destruct (lapRM (n + d)) as (m & c' & _ & Hm & Hl).
    exists (Tm + m). rewrite stepn_add, HT.
    replace (n + S d) with (S (n + d)) by lia.
    rewrite <- Hl. apply csteps_lift. exact Hm.
Qed.

Lemma fire_everyRM : forall t, ~ In t pins -> forall n,
  exists k c', csteps tm k (Cf n) = Some c' /\ cinstr c' = t.
Proof.
  intros t Hnp n.
  destruct (fireRM t n Hnp) as (m & k & c' & Hm & Hk & Hc').
  destruct (reachRM (m - n) n) as (Tm & HT).
  replace (n + (m - n)) with m in HT by lia.
  assert (Hs : stepn tm (Tm + k) (lift (Cf n)) = Some (lift c')).
  { rewrite stepn_add, HT. apply csteps_lift. exact Hk. }
  destruct (stepn_csteps_at tm (Tm + k) (Cf n) (lift c') Hs) as (c'' & Hc'' & Hl').
  exists (Tm + k), c''. split; [exact Hc''|].
  rewrite <- cinstr_lift, Hl', cinstr_lift. exact Hc'.
Qed.

Theorem boardR_qhtrM : forall t0 B,
  stepn tm0 t0 InitES = Some (lift (rcfgM F M T suf (x0, m0))) ->
  existsb (fun tg => cfires tm0 CTape.c0 t0 tg) pins = true ->
  (t0 <=? B) = true ->
  NonHalt tm0 /\ QHBoundTr B tm0 /\ QuasiHaltsTr tm0.
Proof.
  intros t0 B Hboot Hwit Hle.
  apply (lap_qh_stage tm0 pins (fun p => Cf (Nat.pred (Pos.to_nat p)))
           1%positive t0 B).
  - exact Hboot.
  - intros p _.
    destruct (lapRM (Nat.pred (Pos.to_nat p))) as (m & c' & Hm & Hrun & Hl).
    exists m, c'. split; [exact Hrun | split; [|exact Hm]].
    rewrite Hl, Pos2Nat.inj_succ.
    replace (S (Nat.pred (Pos.to_nat p))) with (Pos.to_nat p)
      by (pose proof (Pos2Nat.is_pos p); lia).
    reflexivity.
  - intros t Hnp p _. exact (fire_everyRM t Hnp (Nat.pred (Pos.to_nat p))).
  - exact Hwit.
  - exact Hle.
Qed.

End BoardRTrM.
