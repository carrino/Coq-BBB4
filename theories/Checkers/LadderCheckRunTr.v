(** * Checkers.LadderCheckRunTr: counters whose terminator is a RUN that
    grows as the counter laps (SCOPING_INSTR 7.4.LE3).

    LE2 read [0RB1LA_1RC0LA_0LD1RB_1LB0RC] as a two-phase family whose fills
    run [+2, -1] and whose landing terminator ([0101]) is off a digit-word
    boundary.  At its anchor the machine actually spells

      [B1] x (01)^m        with x a binary string over the words 11 / 10,

    and the laps are

      (x, m)        -> (x + 1, m)                  while x is not all top;
      (top^j, m)    -> (0^(j-1), m + 1)   (j >= 1)  the top NARROWS x and
                                                    lengthens the run;
      ([], m)       -> (0^(m + a), c)              an empty x refills.

    [LadderFam] has no field for a run terminator (its [Fill] widening is a
    [nat] and its terminators are words), so the family here is a [Fam] for
    the digits, the near-head prefix and the anchor, plus the run word [T],
    the end word [suf] and the refill law [(a, c)].  The successor [rsucc]
    is total and digit-wise ([inc] is the odometer carry).  Liveness: the
    length of [x] falls at each narrowing and inside a length the value
    rises, so an empty [x] -- a REFILL -- recurs ([refill_cofinal]), and the
    fires are witnessed from the refill arms' anchors.

    Three arm classes, all [LadderNest.ReachL] programs:
    - interior: [t^n d X -> 0^n (d+1) X], [X] opaque (the rest of x, the run
      and [suf]), one arm per digit and index;
    - narrowing: [t^j T X -> 0^(j-1) T T X], [X] opaque, one arm per index
      ([j >= 1]);
    - refill: [T^m suf -> 0^(m+a) T^c suf], both tails known empty, one arm
      per index ([m >= 1]).

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

Section Run.

Variable F : Fam.
Variable T suf : list Sym.
Variable a c : nat.

Local Notation b := (fm_b F).

Fixpoint inc (x : list nat) : list nat :=
  match x with
  | [] => []
  | d :: t => if d =? b - 1 then 0 :: inc t else S d :: t
  end.

Definition alltop (x : list nat) : bool := forallb (Nat.eqb (b - 1)) x.

Definition RSt : Type := (list nat * nat)%type.

Definition rsucc (s : RSt) : RSt :=
  let '(x, m) := s in
  match x with
  | [] => (repeat 0 (m + a), c)
  | _ :: _ => if alltop x then (repeat 0 (length x - 1), S m) else (inc x, m)
  end.

Fixpoint riter (s : RSt) (n : nat) : RSt :=
  match n with
  | O => s
  | S n' => riter (rsucc s) n'
  end.

Lemma riter_add : forall n1 n2 s, riter s (n1 + n2) = riter (riter s n1) n2.
Proof. induction n1 as [|n1 IH]; intros n2 s; [reflexivity | apply IH]. Qed.

Definition rcells (x : list nat) (m : nat) : list Sym :=
  fm_pre F ++ flat_map (dig F) x ++ rep T m ++ suf.

Definition rcfg (s : RSt) : cconf :=
  let '(x, m) := s in
  if fm_left F
  then (fm_st F, (rcells x m, fm_hs F, fm_other F))
  else (fm_st F, (fm_other F, fm_hs F, rcells x m)).

Lemma rcfg_cls : forall sd X n x m,
  rcells x m = sden X n sd ->
  cden (tailL F X) (tailR F X) n (cls_conf F sd) = rcfg (x, m).
Proof.
  intros sd X n x m H.
  unfold cden, cls_conf, rcfg, tailL, tailR.
  destruct (fm_left F); simpl; rewrite sden_flat, app_nil_r, <- H; reflexivity.
Qed.

(** *** The odometer carry, and the value it adds one to *)

Lemma inc_class : forall n d rest, d < b - 1 ->
  inc (repeat (b - 1) n ++ d :: rest) = repeat 0 n ++ S d :: rest.
Proof.
  induction n as [|n IH]; intros d rest Hd; cbn [repeat app inc].
  - destruct (Nat.eqb_spec d (b - 1)); [lia | reflexivity].
  - rewrite Nat.eqb_refl, IH by exact Hd. reflexivity.
Qed.

Lemma alltop_repeat : forall n, alltop (repeat (b - 1) n) = true.
Proof.
  induction n as [|n IH]; [reflexivity|]. cbn [repeat alltop forallb].
  rewrite Nat.eqb_refl. exact IH.
Qed.

Lemma alltop_class : forall n d rest, d <> b - 1 ->
  alltop (repeat (b - 1) n ++ d :: rest) = false.
Proof.
  induction n as [|n IH]; intros d rest Hd; cbn [repeat app alltop forallb].
  - destruct (Nat.eqb_spec (b - 1) d); [lia | reflexivity].
  - rewrite Nat.eqb_refl. apply IH. exact Hd.
Qed.

Hypothesis Hb : 1 < b.

Lemma inc_val : forall x, Forall (fun d => d < b) x -> alltop x = false ->
  val_pos b (inc x) = S (val_pos b x).
Proof.
  induction x as [|d t IH]; intros Hx Ht; [discriminate|].
  inversion Hx as [|? ? Hd Htl]; subst.
  cbn [inc alltop forallb] in *.
  destruct (Nat.eqb_spec d (b - 1)) as [E|E].
  - subst d. rewrite Nat.eqb_refl in Ht. cbn [andb] in Ht.
    cbn [val_pos]. rewrite (IH Htl Ht). nia.
  - cbn [val_pos]. lia.
Qed.

Lemma inc_len : forall x, length (inc x) = length x.
Proof.
  induction x as [|d t IH]; [reflexivity|]. cbn [inc].
  destruct (d =? b - 1); cbn [length]; [rewrite IH|]; reflexivity.
Qed.

Lemma inc_bnd : forall x, Forall (fun d => d < b) x -> alltop x = false ->
  Forall (fun d => d < b) (inc x).
Proof.
  induction x as [|d t IH]; intros Hx Ht; [constructor|].
  inversion Hx as [|? ? Hd Htl]; subst.
  cbn [inc alltop forallb] in *.
  destruct (Nat.eqb_spec d (b - 1)) as [E|E].
  - subst d. rewrite Nat.eqb_refl in Ht. constructor; [lia | apply IH; assumption].
  - constructor; [lia | exact Htl].
Qed.

Lemma repeat0_bnd : forall n, Forall (fun d => d < b) (repeat 0 n).
Proof.
  intros n. apply Forall_forall. intros y Hy. apply repeat_spec in Hy. lia.
Qed.

(** *** Refills recur *)

Hypothesis Hc : 1 <= c.

Definition RInv (s : RSt) : Prop :=
  let '(x, m) := s in Forall (fun d => d < b) x /\ 1 <= m.

Lemma rsucc_inv : forall s, RInv s -> RInv (rsucc s).
Proof.
  intros [x m] (Hx & Hm). destruct x as [|d t]; cbn [rsucc].
  - split; [apply repeat0_bnd | exact Hc].
  - destruct (alltop (d :: t)) eqn:E.
    + split; [apply repeat0_bnd | lia].
    + split; [apply inc_bnd; assumption | exact Hm].
Qed.

Lemma riter_inv : forall n s, RInv s -> RInv (riter s n).
Proof.
  induction n as [|n IH]; intros s Hs; [exact Hs|]. apply IH, rsucc_inv, Hs.
Qed.

Lemma refill_reached : forall k v s, RInv s ->
  length (fst s) <= k ->
  Nat.pow b (length (fst s)) - val_pos b (fst s) <= v ->
  exists n, fst (riter s n) = [].
Proof.
  induction k as [|k IHk]; intros v [x m] Hs Hk Hv; cbn [fst] in *.
  - destruct x; [exists 0; reflexivity | cbn in Hk; lia].
  - revert x m Hs Hk Hv. induction v as [|v IHv]; intros x m Hs Hk Hv.
    + exfalso. destruct Hs as (Hx & _).
      pose proof (val_pos_lt b x Hb Hx). lia.
    + destruct x as [|d t]; [exists 0; reflexivity|]. cbn [length] in Hk, Hv.
      destruct (alltop (d :: t)) eqn:E.
      * (* the narrowing: one digit fewer *)
        destruct (IHk (Nat.pow b (length t)) (rsucc (d :: t, m)) (rsucc_inv _ Hs))
          as (n & Hn).
        -- cbn [rsucc]. rewrite E. cbn [fst length]. rewrite repeat_length. lia.
        -- cbn [rsucc]. rewrite E. cbn [fst length]. rewrite repeat_length.
           replace (S (length t) - 1) with (length t) by lia. lia.
        -- exists (S n). exact Hn.
      * (* inside the length: the value rises by one *)
        destruct Hs as (Hx & Hm).
        assert (Hi : RInv (inc (d :: t), m))
          by (split; [apply inc_bnd; assumption | exact Hm]).
        destruct (IHv (inc (d :: t)) m Hi) as (n & Hn).
        -- rewrite inc_len. cbn [length] in *. exact Hk.
        -- rewrite inc_len, inc_val by assumption. cbn [length] in *. lia.
        -- exists (S n). cbn [riter rsucc]. rewrite E. exact Hn.
Qed.

Theorem refill_cofinal : forall s N, RInv s ->
  exists n, N <= n /\ fst (riter s n) = [] /\ RInv (riter s n).
Proof.
  intros s N Hs.
  pose proof (riter_inv N s Hs) as HsN.
  destruct (refill_reached (length (fst (riter s N)))
              (Nat.pow b (length (fst (riter s N))) - val_pos b (fst (riter s N)))
              (riter s N) HsN ltac:(lia) ltac:(lia)) as (n & Hn).
  exists (N + n). rewrite riter_add.
  split; [lia | split; [exact Hn | apply riter_inv, HsN]].
Qed.

(** *** The cells of each class *)

Lemma rcells_int : forall t r st n d rest m,
  rcells (repeat t (r + st * n) ++ d :: rest) m
    = sden (flat_map (dig F) rest ++ rep T m ++ suf) n
        (cls_side F [] t r st [d]).
Proof.
  intros t r st n d rest m. unfold rcells, cls_side.
  rewrite blk_den, flat_map_app, flat_map_repeat_nil.
  cbn [flat_map app]. rewrite app_nil_r, rep_add, !app_assoc. reflexivity.
Qed.

Lemma rcells_top : forall t r st n m,
  rcells (repeat t (r + st * n)) (S m)
    = sden (rep T m ++ suf) n
        (blk (fm_pre F ++ rep (dig F t) r) (dig F t) st T).
Proof.
  intros t r st n m. unfold rcells.
  rewrite blk_den, flat_map_repeat_nil, rep_add. cbn [rep].
  rewrite !app_assoc. reflexivity.
Qed.

Lemma rcells_nar : forall t r st n m,
  rcells (repeat t (r + st * n)) (S (S m))
    = sden (rep T m ++ suf) n
        (blk (fm_pre F ++ rep (dig F t) r) (dig F t) st (T ++ T)).
Proof.
  intros t r st n m. unfold rcells.
  rewrite blk_den, flat_map_repeat_nil, rep_add. cbn [rep].
  rewrite !app_assoc. reflexivity.
Qed.

Lemma rcells_refill : forall r st n,
  rcells [] (r + st * n)
    = sden [] n (blk (fm_pre F ++ rep T r) T st suf).
Proof.
  intros r st n. unfold rcells.
  rewrite blk_den, rep_add. cbn [flat_map].
  rewrite ?app_nil_r, !app_assoc, ?app_nil_r. reflexivity.
Qed.

Lemma rcells_refilled : forall f1 st n f2,
  rcells (repeat 0 (f1 + st * n + f2)) c
    = sden [] n (blk (fm_pre F ++ rep (dig F 0) f1) (dig F 0) st
                   (rep (dig F 0) f2 ++ rep T c ++ suf)).
Proof.
  intros f1 st n f2. unfold rcells.
  rewrite blk_den, flat_map_repeat_nil, !rep_add, !app_nil_r, !app_assoc.
  reflexivity.
Qed.

Lemma rsucc_cons : forall x m, x <> [] ->
  rsucc (x, m) = if alltop x then (repeat 0 (length x - 1), S m) else (inc x, m).
Proof. intros [|d t] m H; [congruence | reflexivity]. Qed.

End Run.

(** ** 2. The board *)

Section BoardRTr.

Variable tm0   : TM.
Variable pins  : list Instr.
Local Notation tm := (tm_wrap_trs tm0 pins).

Variable F     : Fam.
Variable T suf : list Sym.
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
Hypothesis Hc    : 1 <= c.
Hypothesis Hbnd0 : Forall (fun d => d < b) x0.
Hypothesis Hm0   : 1 <= m0.

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
                                (dig F (b - 1)) (astride N0n stn r) T).
Hypothesis HANR : forall r, 0 < r -> r < N0n + stn ->
  lr_rhs (AN r) = cls_conf F (blk (fm_pre F ++ rep (dig F 0) (r - 1))
                                (dig F 0) (astride N0n stn r) (T ++ T)).

Hypothesis Hstr : 0 < str.
Hypothesis HN0r : 0 < N0r.
Hypothesis HARS : forall r, 0 < r -> r < N0r + str ->
  ReachL tm true true (lr_lhs (AR r)) (lr_rhs (AR r)).
Hypothesis HARL : forall r, 0 < r -> r < N0r + str ->
  lr_lhs (AR r) = cls_conf F (blk (fm_pre F ++ rep T r) T (astride N0r str r) suf).
Hypothesis HARR : forall r, 0 < r -> r < N0r + str ->
  lr_rhs (AR r) = cls_conf F (blk (fm_pre F ++ rep (dig F 0) (fm1 r)) (dig F 0)
                                (astride N0r str r)
                                (rep (dig F 0) (fm2 r) ++ rep T c ++ suf)).
Hypothesis Hfm : forall r, 0 < r -> r < N0r + str -> fm1 r + fm2 r = r + a.

Hypothesis Hrsv : Forall (RuleSound tm false false) rsv.
Hypothesis Hfire : forall r t, ~ In t pins -> 0 < r -> r < N0r + str ->
  nfire tm true true rsv (vsegs r t) (visI r t) (lr_lhs (AR r)) = Some t.

Local Notation Cf := (fun n => rcfg F T suf (riter F a c (x0, m0) n)).

Lemma rinv0 : RInv F (x0, m0).
Proof. split; assumption. Qed.

Lemma board_armR : forall s, RInv F s ->
  exists A el er X n,
    ReachL tm el er (lr_lhs A) (lr_rhs A)
    /\ (el = true -> tailL F X = []) /\ (er = true -> tailR F X = [])
    /\ rcfg F T suf s = cden (tailL F X) (tailR F X) n (lr_lhs A)
    /\ rcfg F T suf (rsucc F a c s) = cden (tailL F X) (tailR F X) n (lr_rhs A).
Proof.
  intros [x m] (Hx & Hm).
  destruct x as [|d0 t0] eqn:Ex.
  - (* the refill *)
    remember (aoff N0r str m) as r eqn:Er.
    assert (Hr0 : 0 < r) by (subst r; apply arm_index_pos; lia).
    assert (Hrlt : r < N0r + str) by (subst r; apply arm_index_lt; assumption).
    assert (Hk : r + astride N0r str r * acnt N0r str m = m)
      by (subst r; apply arm_index; assumption).
    exists (AR r), true, true, [], (acnt N0r str m).
    split; [|split; [|split; [|split]]].
    + exact (HARS r Hr0 Hrlt).
    + intros _; apply tailL_nil.
    + intros _; apply tailR_nil.
    + rewrite (HARL r Hr0 Hrlt). symmetry. apply rcfg_cls.
      rewrite <- Hk at 1. apply rcells_refill.
    + rewrite (HARR r Hr0 Hrlt). symmetry. cbn [rsucc]. apply rcfg_cls.
      pose proof (Hfm r Hr0 Hrlt).
      rewrite <- (rcells_refilled F T suf c (fm1 r) (astride N0r str r)
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
      destruct m as [|m']; [lia|].
      exists (AN r), (negb (fm_left F)), (fm_left F), (rep T m' ++ suf), (acnt N0n stn j).
      split; [|split; [|split; [|split]]].
      * exact (HANS r Hr0 Hrlt).
      * intros He. unfold tailL. destruct (fm_left F); [discriminate|reflexivity].
      * intros He. unfold tailR. rewrite He. reflexivity.
      * rewrite (HANL r Hr0 Hrlt). symmetry. apply rcfg_cls.
        rewrite Htop, <- Hk at 1. apply rcells_top.
      * rewrite (HANR r Hr0 Hrlt). symmetry.
        rewrite (rsucc_cons F a c x (S m') Hne).
        rewrite Htop at 1. rewrite (alltop_repeat F).
        apply rcfg_cls. fold j.
        replace (j - 1) with ((r - 1) + astride N0n stn r * acnt N0n stn j) by lia.
        apply rcells_nar.
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
             (flat_map (dig F) rest ++ rep T m ++ suf), (acnt N0i sti n).
      split; [|split; [|split; [|split]]].
      * exact (HAIS d r Hdlt Hrlt).
      * intros He. unfold tailL. destruct (fm_left F); [discriminate|reflexivity].
      * intros He. unfold tailR. rewrite He. reflexivity.
      * rewrite (HAIL d r Hdlt Hrlt). symmetry. apply rcfg_cls.
        rewrite Hxe, <- Hn at 1. apply rcells_int.
      * rewrite (HAIR d r Hdlt Hrlt). symmetry.
        rewrite (rsucc_cons F a c x m Hne), Hxe.
        rewrite (alltop_class F n d rest Hd), (inc_class F n d rest Hdlt).
        apply rcfg_cls. rewrite <- Hn at 1. apply rcells_int.
Qed.

Lemma lapR : forall n, exists m c',
  0 < m /\ csteps tm m (Cf n) = Some c' /\ lift c' = lift (Cf (S n)).
Proof.
  intros n.
  pose proof (riter_inv F a c Hb Hc n (x0, m0) rinv0) as Hi.
  destruct (board_armR _ Hi) as (A & el & er & X & k & HA & HL & HR & Hl & Hr).
  destruct (HA _ _ k HL HR) as (m & c' & Hm & Hc' & Hlc).
  exists m, c'. split; [exact Hm|]. split.
  - cbn beta. rewrite Hl. exact Hc'.
  - rewrite Hlc, <- Hr. cbn beta.
    replace (S n) with (n + 1) by lia. rewrite riter_add. reflexivity.
Qed.

Lemma fireR : forall t N, ~ In t pins ->
  exists n k c', N <= n /\ csteps tm k (Cf n) = Some c' /\ cinstr c' = t.
Proof.
  intros t N Hnp.
  destruct (refill_cofinal F a c Hb Hc (x0, m0) N rinv0) as (n & HN & Hx & Hi).
  exists n.
  destruct (riter F a c (x0, m0) n) as [x m] eqn:Eit.
  cbn [fst] in Hx. subst x. destruct Hi as (_ & Hm).
  remember (aoff N0r str m) as r eqn:Er.
  assert (Hr0 : 0 < r) by (subst r; apply arm_index_pos; lia).
  assert (Hrlt : r < N0r + str) by (subst r; apply arm_index_lt; assumption).
  assert (Hk : r + astride N0r str r * acnt N0r str m = m)
    by (subst r; apply arm_index; assumption).
  assert (Hden : rcfg F T suf ([], m)
                 = cden [] [] (acnt N0r str m) (lr_lhs (AR r))).
  { rewrite (HARL r Hr0 Hrlt).
    rewrite <- (rcfg_cls F T suf
                  (blk (fm_pre F ++ rep T r) T (astride N0r str r) suf)
                  [] (acnt N0r str m) [] m).
    - unfold tailL, tailR; destruct (fm_left F); reflexivity.
    - rewrite <- Hk at 1. apply rcells_refill. }
  destruct (nfire_sound tm true true rsv (vsegs r t) (visI r t)
              (lr_lhs (AR r)) t Hrsv (Hfire r t Hnp Hr0 Hrlt)
              [] [] (acnt N0r str m)
              (fun _ => eq_refl) (fun _ => eq_refl)) as (k & c' & Hc' & Ht).
  exists k, c'. cbn beta. rewrite ?Eit, Hden.
  split; [exact HN | split; [exact Hc' | exact Ht]].
Qed.

Theorem boardR_neverqhtr : forall t0,
  stepn tm t0 InitES = Some (lift (rcfg F T suf (x0, m0))) ->
  NeverQuasiHaltsTr tm0.
Proof.
  intros t0 Hboot.
  apply (glue_neverqhtrN tm0 pins Cf).
  - exists t0. exact Hboot.
  - intros n. destruct (lapR n) as (m & c' & Hm & Hrun & Hl).
    exists m, c'. split; [exact Hrun | split; [exact Hl | exact Hm]].
  - intros t Hnp N. exact (fireR t N Hnp).
Qed.

Lemma reachR : forall d n,
  exists Tm, stepn tm Tm (lift (Cf n)) = Some (lift (Cf (n + d))).
Proof.
  induction d; intros n.
  - exists 0. rewrite Nat.add_0_r. reflexivity.
  - destruct (IHd n) as (Tm & HT).
    destruct (lapR (n + d)) as (m & c' & _ & Hm & Hl).
    exists (Tm + m). rewrite stepn_add, HT.
    replace (n + S d) with (S (n + d)) by lia.
    rewrite <- Hl. apply csteps_lift. exact Hm.
Qed.

Lemma fire_everyR : forall t, ~ In t pins -> forall n,
  exists k c', csteps tm k (Cf n) = Some c' /\ cinstr c' = t.
Proof.
  intros t Hnp n.
  destruct (fireR t n Hnp) as (m & k & c' & Hm & Hk & Hc').
  destruct (reachR (m - n) n) as (Tm & HT).
  replace (n + (m - n)) with m in HT by lia.
  assert (Hs : stepn tm (Tm + k) (lift (Cf n)) = Some (lift c')).
  { rewrite stepn_add, HT. apply csteps_lift. exact Hk. }
  destruct (stepn_csteps_at tm (Tm + k) (Cf n) (lift c') Hs) as (c'' & Hc'' & Hl').
  exists (Tm + k), c''. split; [exact Hc''|].
  rewrite <- cinstr_lift, Hl', cinstr_lift. exact Hc'.
Qed.

Theorem boardR_qhtr : forall t0 B,
  stepn tm0 t0 InitES = Some (lift (rcfg F T suf (x0, m0))) ->
  existsb (fun tg => cfires tm0 CTape.c0 t0 tg) pins = true ->
  (t0 <=? B) = true ->
  NonHalt tm0 /\ QHBoundTr B tm0 /\ QuasiHaltsTr tm0.
Proof.
  intros t0 B Hboot Hwit Hle.
  apply (lap_qh_stage tm0 pins (fun p => Cf (Nat.pred (Pos.to_nat p)))
           1%positive t0 B).
  - exact Hboot.
  - intros p _.
    destruct (lapR (Nat.pred (Pos.to_nat p))) as (m & c' & Hm & Hrun & Hl).
    exists m, c'. split; [exact Hrun | split; [|exact Hm]].
    rewrite Hl, Pos2Nat.inj_succ.
    replace (S (Nat.pred (Pos.to_nat p))) with (Pos.to_nat p)
      by (pose proof (Pos2Nat.is_pos p); lia).
    reflexivity.
  - intros t Hnp p _. exact (fire_everyR t Hnp (Nat.pred (Pos.to_nat p))).
  - exact Hwit.
  - exact Hle.
Qed.

End BoardRTr.
