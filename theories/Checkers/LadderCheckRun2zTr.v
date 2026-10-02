(** * Checkers.LadderCheckRun2zTr: [LadderCheckRun2Tr] with a refill that
    ends in a fixed digit string (SCOPING_INSTR 7.4.LE6).

    LE6's binary COUNTDOWNS with a marker run ([0RB1LA_1LC1RD_0RA1LD_1RB0LA]:
    [A0 x 0 (11)^m], [x] over [11] / [10] counting down) are
    [LadderCheckRun2Tr]'s counter with the two digit words swapped, except
    for the refill: an empty [x] refills to [1^m 0] in the machine's words,
    i.e. [0^m 1] in the swapped ones -- the top digit's last cell is the blank
    beyond the tape.  So the one change is the refill law

      ([], m) -> (0^(m + a) ++ z, c)      for a fixed string [z] of digits

    ([z = []] is [LadderCheckRun2Tr]).  The invariant needs [z]'s digits
    below the base; the liveness (length, then value) is unchanged, since a
    refill is where it starts again.  Every name is [LadderCheckRun2Tr]'s
    with the suffix [Z] for [M].

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

Section RunZ.

Variable F : Fam.
Variable M T suf : list Sym.
Variable a c : nat.
Variable z : list nat.     (** the refill's top digits *)

Local Notation b := (fm_b F).

Fixpoint incZ (x : list nat) : list nat :=
  match x with
  | [] => []
  | d :: t => if d =? b - 1 then 0 :: incZ t else S d :: t
  end.

Definition alltopZ (x : list nat) : bool := forallb (Nat.eqb (b - 1)) x.

Definition RStZ : Type := (list nat * nat)%type.

Definition rsuccZ (s : RStZ) : RStZ :=
  let '(x, m) := s in
  match x with
  | [] => (repeat 0 (m + a) ++ z, c)
  | _ :: _ => if alltopZ x then (repeat 0 (length x - 1), S m) else (incZ x, m)
  end.

Fixpoint riterZ (s : RStZ) (n : nat) : RStZ :=
  match n with
  | O => s
  | S n' => riterZ (rsuccZ s) n'
  end.

Lemma riter_addZ : forall n1 n2 s, riterZ s (n1 + n2) = riterZ (riterZ s n1) n2.
Proof. induction n1 as [|n1 IH]; intros n2 s; [reflexivity | apply IH]. Qed.

Definition rcellsZ (x : list nat) (m : nat) : list Sym :=
  fm_pre F ++ flat_map (dig F) x ++ M ++ rep T m ++ suf.

Definition rcfgZ (s : RStZ) : cconf :=
  let '(x, m) := s in
  if fm_left F
  then (fm_st F, (rcellsZ x m, fm_hs F, fm_other F))
  else (fm_st F, (fm_other F, fm_hs F, rcellsZ x m)).

Lemma rcfg_clsZ : forall sd X n x m,
  rcellsZ x m = sden X n sd ->
  cden (tailL F X) (tailR F X) n (cls_conf F sd) = rcfgZ (x, m).
Proof.
  intros sd X n x m H.
  unfold cden, cls_conf, rcfgZ, tailL, tailR.
  destruct (fm_left F); simpl; rewrite sden_flat, app_nil_r, <- H; reflexivity.
Qed.

(** *** The odometer carry, and the value it adds one to *)

Lemma inc_classZ : forall n d rest, d < b - 1 ->
  incZ (repeat (b - 1) n ++ d :: rest) = repeat 0 n ++ S d :: rest.
Proof.
  induction n as [|n IH]; intros d rest Hd; cbn [repeat app incZ].
  - destruct (Nat.eqb_spec d (b - 1)); [lia | reflexivity].
  - rewrite Nat.eqb_refl, IH by exact Hd. reflexivity.
Qed.

Lemma alltop_repeatZ : forall n, alltopZ (repeat (b - 1) n) = true.
Proof.
  induction n as [|n IH]; [reflexivity|]. cbn [repeat alltopZ forallb].
  rewrite Nat.eqb_refl. exact IH.
Qed.

Lemma alltop_classZ : forall n d rest, d <> b - 1 ->
  alltopZ (repeat (b - 1) n ++ d :: rest) = false.
Proof.
  induction n as [|n IH]; intros d rest Hd; cbn [repeat app alltopZ forallb].
  - destruct (Nat.eqb_spec (b - 1) d); [lia | reflexivity].
  - rewrite Nat.eqb_refl. apply IH. exact Hd.
Qed.

Hypothesis Hb : 1 < b.
Hypothesis Hz : Forall (fun d => d < b) z.

Lemma inc_valZ : forall x, Forall (fun d => d < b) x -> alltopZ x = false ->
  val_pos b (incZ x) = S (val_pos b x).
Proof.
  induction x as [|d t IH]; intros Hx Ht; [discriminate|].
  inversion Hx as [|? ? Hd Htl]; subst.
  cbn [incZ alltopZ forallb] in *.
  destruct (Nat.eqb_spec d (b - 1)) as [E|E].
  - subst d. rewrite Nat.eqb_refl in Ht. cbn [andb] in Ht.
    cbn [val_pos]. rewrite (IH Htl Ht). nia.
  - cbn [val_pos]. lia.
Qed.

Lemma inc_lenZ : forall x, length (incZ x) = length x.
Proof.
  induction x as [|d t IH]; [reflexivity|]. cbn [incZ].
  destruct (d =? b - 1); cbn [length]; [rewrite IH|]; reflexivity.
Qed.

Lemma inc_bndZ : forall x, Forall (fun d => d < b) x -> alltopZ x = false ->
  Forall (fun d => d < b) (incZ x).
Proof.
  induction x as [|d t IH]; intros Hx Ht; [constructor|].
  inversion Hx as [|? ? Hd Htl]; subst.
  cbn [incZ alltopZ forallb] in *.
  destruct (Nat.eqb_spec d (b - 1)) as [E|E].
  - subst d. rewrite Nat.eqb_refl in Ht. constructor; [lia | apply IH; assumption].
  - constructor; [lia | exact Htl].
Qed.

Lemma repeat0_bndZ : forall n, Forall (fun d => d < b) (repeat 0 n).
Proof.
  intros n. apply Forall_forall. intros y Hy. apply repeat_spec in Hy. lia.
Qed.

(** *** Refills recur *)

Definition RInvZ (s : RStZ) : Prop :=
  let '(x, m) := s in Forall (fun d => d < b) x.

Lemma rsucc_invZ : forall s, RInvZ s -> RInvZ (rsuccZ s).
Proof.
  intros [x m] Hx. destruct x as [|d t]; cbn [rsuccZ].
  - apply Forall_app. split; [apply repeat0_bndZ | exact Hz].
  - destruct (alltopZ (d :: t)) eqn:E.
    + apply repeat0_bndZ.
    + apply inc_bndZ; assumption.
Qed.

Lemma riter_invZ : forall n s, RInvZ s -> RInvZ (riterZ s n).
Proof.
  induction n as [|n IH]; intros s Hs; [exact Hs|]. apply IH, rsucc_invZ, Hs.
Qed.

Lemma refill_reachedZ : forall k v s, RInvZ s ->
  length (fst s) <= k ->
  Nat.pow b (length (fst s)) - val_pos b (fst s) <= v ->
  exists n, fst (riterZ s n) = [].
Proof.
  induction k as [|k IHk]; intros v [x m] Hs Hk Hv; cbn [fst] in *.
  - destruct x; [exists 0; reflexivity | cbn in Hk; lia].
  - revert x m Hs Hk Hv. induction v as [|v IHv]; intros x m Hs Hk Hv.
    + exfalso. pose proof (val_pos_lt b x Hb Hs). lia.
    + destruct x as [|d t]; [exists 0; reflexivity|]. cbn [length] in Hk, Hv.
      destruct (alltopZ (d :: t)) eqn:E.
      * (* the narrowing: one digit fewer *)
        destruct (IHk (Nat.pow b (length t)) (rsuccZ (d :: t, m)) (rsucc_invZ _ Hs))
          as (n & Hn).
        -- cbn [rsuccZ]. rewrite E. cbn [fst length]. rewrite repeat_length. lia.
        -- cbn [rsuccZ]. rewrite E. cbn [fst length]. rewrite repeat_length.
           replace (S (length t) - 1) with (length t) by lia. lia.
        -- exists (S n). exact Hn.
      * (* inside the length: the value rises by one *)
        assert (Hi : RInvZ (incZ (d :: t), m)) by (apply inc_bndZ; assumption).
        destruct (IHv (incZ (d :: t)) m Hi) as (n & Hn).
        -- rewrite inc_lenZ. cbn [length] in *. exact Hk.
        -- rewrite inc_lenZ, inc_valZ by assumption. cbn [length] in *. lia.
        -- exists (S n). cbn [riterZ rsuccZ]. rewrite E. exact Hn.
Qed.

Theorem refill_cofinalZ : forall s N, RInvZ s ->
  exists n, N <= n /\ fst (riterZ s n) = [] /\ RInvZ (riterZ s n).
Proof.
  intros s N Hs.
  pose proof (riter_invZ N s Hs) as HsN.
  destruct (refill_reachedZ (length (fst (riterZ s N)))
              (Nat.pow b (length (fst (riterZ s N))) - val_pos b (fst (riterZ s N)))
              (riterZ s N) HsN ltac:(lia) ltac:(lia)) as (n & Hn).
  exists (N + n). rewrite riter_addZ.
  split; [lia | split; [exact Hn | apply riter_invZ, HsN]].
Qed.

(** *** Narrowings recur too (LE6): from a nonempty [x] the count reaches its
    top, and with [z <> []] every refill leaves [x] nonempty *)

Lemma top_reachedZ : forall v s, RInvZ s -> fst s <> [] ->
  Nat.pow b (length (fst s)) - val_pos b (fst s) <= v ->
  exists n, fst (riterZ s n) <> [] /\ alltopZ (fst (riterZ s n)) = true /\ RInvZ (riterZ s n).
Proof.
  induction v as [|v IHv]; intros [x m] Hs Hne Hv; cbn [fst] in *.
  - exfalso. pose proof (val_pos_lt b x Hb Hs). lia.
  - destruct (alltopZ x) eqn:E.
    + exists 0. cbn [riterZ fst]. auto.
    + destruct x as [|d t]; [congruence|].
      assert (Hi : RInvZ (incZ (d :: t), m)) by (apply inc_bndZ; assumption).
      destruct (IHv (incZ (d :: t), m) Hi) as (n & Hn).
      * cbn [fst]. intros H. pose proof (inc_lenZ (d :: t)) as HL.
        rewrite H in HL. discriminate.
      * cbn [fst]. rewrite inc_lenZ, inc_valZ by assumption. cbn [length] in *. lia.
      * exists (S n). cbn [riterZ rsuccZ]. rewrite E. exact Hn.
Qed.

Theorem nar_cofinalZ : z <> [] -> forall s N, RInvZ s ->
  exists n, N <= n /\ fst (riterZ s n) <> [] /\ alltopZ (fst (riterZ s n)) = true
            /\ RInvZ (riterZ s n).
Proof.
  intros Hzne s N Hs.
  destruct (refill_cofinalZ s N Hs) as (n & HN & Hx & Hi).
  assert (Hs1 : RInvZ (riterZ s (S n))) by (apply riter_invZ; exact Hs).
  assert (Hne : fst (riterZ s (S n)) <> []).
  { replace (S n) with (n + 1) by lia. rewrite riter_addZ.
    destruct (riterZ s n) as [x m]. cbn [fst] in Hx. subst x. cbn.
    intros H. apply app_eq_nil in H as [_ H]. exact (Hzne H). }
  destruct (top_reachedZ _ (riterZ s (S n)) Hs1 Hne (le_n _)) as (j & Hj).
  exists (S n + j). split; [lia|]. rewrite riter_addZ. exact Hj.
Qed.

(** *** The cells of each class *)

(** The word after the digit an interior arm increments: the next digit
    [e < b], or the marker when [x] ends there ([e = b]).  LE4's rows read
    it (one word of lookahead): with the rest of the counter opaque their
    carry has no chain, with the next word concrete its cost is affine. *)
Definition ilookZ (e : nat) : list Sym := if e <? b then dig F e else M.

Lemma rcells_intlZ : forall t r st n d e rest m, e < b ->
  rcellsZ (repeat t (r + st * n) ++ d :: e :: rest) m
    = sden (flat_map (dig F) rest ++ M ++ rep T m ++ suf) n
        (blk (fm_pre F ++ rep (dig F t) r) (dig F t) st (dig F d ++ ilookZ e)).
Proof.
  intros t r st n d e rest m He. unfold rcellsZ, ilookZ.
  destruct (Nat.ltb_spec e b) as [_|]; [|lia].
  rewrite blk_den, flat_map_app, flat_map_repeat_nil.
  cbn [flat_map app]. rewrite rep_add, !app_assoc. reflexivity.
Qed.

Lemma rcells_intmZ : forall t r st n d m,
  rcellsZ (repeat t (r + st * n) ++ [d]) m
    = sden (rep T m ++ suf) n
        (blk (fm_pre F ++ rep (dig F t) r) (dig F t) st (dig F d ++ ilookZ b)).
Proof.
  intros t r st n d m. unfold rcellsZ, ilookZ. rewrite Nat.ltb_irrefl.
  rewrite blk_den, flat_map_app, flat_map_repeat_nil.
  cbn [flat_map app]. rewrite app_nil_r, rep_add, !app_assoc. reflexivity.
Qed.

Lemma rcells_intZ : forall t r st n d rest m,
  rcellsZ (repeat t (r + st * n) ++ d :: rest) m
    = sden (flat_map (dig F) rest ++ M ++ rep T m ++ suf) n
        (cls_side F [] t r st [d]).
Proof.
  intros t r st n d rest m. unfold rcellsZ, cls_side.
  rewrite blk_den, flat_map_app, flat_map_repeat_nil.
  cbn [flat_map app]. rewrite app_nil_r, rep_add, !app_assoc. reflexivity.
Qed.

Lemma rcells_topZ : forall t r st n m,
  rcellsZ (repeat t (r + st * n)) m
    = sden (rep T m ++ suf) n
        (blk (fm_pre F ++ rep (dig F t) r) (dig F t) st M).
Proof.
  intros t r st n m. unfold rcellsZ.
  rewrite blk_den, flat_map_repeat_nil, rep_add.
  rewrite !app_assoc. reflexivity.
Qed.

Lemma rcells_narZ : forall t r st n m,
  rcellsZ (repeat t (r + st * n)) (S m)
    = sden (rep T m ++ suf) n
        (blk (fm_pre F ++ rep (dig F t) r) (dig F t) st (M ++ T)).
Proof.
  intros t r st n m. unfold rcellsZ.
  rewrite blk_den, flat_map_repeat_nil, rep_add. cbn [rep].
  rewrite !app_assoc. reflexivity.
Qed.

Lemma rcells_refillZ : forall r st n,
  rcellsZ [] (r + st * n)
    = sden [] n (blk (fm_pre F ++ M ++ rep T r) T st suf).
Proof.
  intros r st n. unfold rcellsZ.
  rewrite blk_den, rep_add. cbn [flat_map].
  rewrite ?app_nil_r, !app_assoc, ?app_nil_r. reflexivity.
Qed.

Lemma rcells_refilledZ : forall f1 st n f2,
  rcellsZ (repeat 0 (f1 + st * n + f2) ++ z) c
    = sden [] n (blk (fm_pre F ++ rep (dig F 0) f1) (dig F 0) st
                   (rep (dig F 0) f2 ++ flat_map (dig F) z ++ M ++ rep T c ++ suf)).
Proof.
  intros f1 st n f2. unfold rcellsZ.
  rewrite flat_map_app, blk_den, flat_map_repeat_nil, !rep_add, !app_nil_r, !app_assoc.
  reflexivity.
Qed.

Lemma rsucc_consZ : forall x m, x <> [] ->
  rsuccZ (x, m) = if alltopZ x then (repeat 0 (length x - 1), S m) else (incZ x, m).
Proof. intros [|d t] m H; [congruence | reflexivity]. Qed.

End RunZ.

(** ** 2. The board *)

Section BoardRTrZ.

Variable tm0   : TM.
Variable pins  : list Instr.
Local Notation tm := (tm_wrap_trs tm0 pins).

Variable F     : Fam.
Variable M T suf : list Sym.
Variable a c   : nat.
Variable z     : list nat.
Variable AI    : nat -> nat -> nat -> LRule.   (** interior: digit, next word, index *)
Variable N0i sti : nat.
Variable AN    : nat -> LRule.          (** narrowing: index *)
Variable N0n stn : nat.
Variable AR    : nat -> LRule.          (** refill: index *)
Variable N0r str : nat.
Variable fm1 fm2 : nat -> nat.
Variable rsv   : list LRule.
Variable vsegs : nat -> Instr -> list nseg.
Variable visI  : nat -> Instr -> list lstep.
Variable vsegsN : nat -> Instr -> list nseg.
Variable visN  : nat -> Instr -> list lstep.
Variable x0    : list nat.
Variable m0    : nat.

Local Notation b := (fm_b F).

Hypothesis Hb    : 1 < b.
Hypothesis Hbnd0 : Forall (fun d => d < b) x0.
Hypothesis Hz0   : Forall (fun d => d < b) z.

Hypothesis Hsti : 0 < sti.
Hypothesis HAIS : forall d e r, d < b - 1 -> e <= b -> r < N0i + sti ->
  ReachL tm (negb (fm_left F)) (fm_left F) (lr_lhs (AI d e r)) (lr_rhs (AI d e r)).
Hypothesis HAIL : forall d e r, d < b - 1 -> e <= b -> r < N0i + sti ->
  lr_lhs (AI d e r) = cls_conf F (blk (fm_pre F ++ rep (dig F (b - 1)) r) (dig F (b - 1))
                                   (astride N0i sti r) (dig F d ++ ilookZ F M e)).
Hypothesis HAIR : forall d e r, d < b - 1 -> e <= b -> r < N0i + sti ->
  lr_rhs (AI d e r) = cls_conf F (blk (fm_pre F ++ rep (dig F 0) r) (dig F 0)
                                   (astride N0i sti r) (dig F (S d) ++ ilookZ F M e)).

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
                                (rep (dig F 0) (fm2 r) ++ flat_map (dig F) z ++ M ++ rep T c ++ suf)).
Hypothesis Hfm : forall r, r < N0r + str -> fm1 r + fm2 r = r + a.

Hypothesis Hrsv : Forall (RuleSound tm false false) rsv.
(** each instruction is witnessed from every refill arm, or (LE6, when the
    refill leaves [x] nonempty) from every narrowing arm *)
Hypothesis Hfire : forall t, ~ In t pins ->
  (forall r, r < N0r + str ->
     nfire tm true true rsv (vsegs r t) (visI r t) (lr_lhs (AR r)) = Some t)
  \/ (z <> [] /\ forall r, 0 < r -> r < N0n + stn ->
     nfire tm (negb (fm_left F)) (fm_left F) rsv (vsegsN r t) (visN r t) (lr_lhs (AN r))
       = Some t).

Local Notation Cf := (fun n => rcfgZ F M T suf (riterZ F a c z (x0, m0) n)).

Lemma rinv0Z : RInvZ F (x0, m0).
Proof. exact Hbnd0. Qed.

Lemma board_armRZ : forall s, RInvZ F s ->
  exists A el er X n,
    ReachL tm el er (lr_lhs A) (lr_rhs A)
    /\ (el = true -> tailL F X = []) /\ (er = true -> tailR F X = [])
    /\ rcfgZ F M T suf s = cden (tailL F X) (tailR F X) n (lr_lhs A)
    /\ rcfgZ F M T suf (rsuccZ F a c z s) = cden (tailL F X) (tailR F X) n (lr_rhs A).
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
    + rewrite (HARL r Hrlt). symmetry. apply rcfg_clsZ.
      rewrite <- Hk at 1. apply rcells_refillZ.
    + rewrite (HARR r Hrlt). symmetry. cbn [rsuccZ]. apply rcfg_clsZ.
      pose proof (Hfm r Hrlt).
      rewrite <- (rcells_refilledZ F M T suf c z (fm1 r) (astride N0r str r)
                    (acnt N0r str m) (fm2 r)).
      f_equal. f_equal. f_equal. lia.
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
      * rewrite (HANL r Hr0 Hrlt). symmetry. apply rcfg_clsZ.
        rewrite Htop, <- Hk at 1. apply rcells_topZ.
      * rewrite (HANR r Hr0 Hrlt). symmetry.
        rewrite (rsucc_consZ F a c z x m Hne).
        rewrite Htop at 1. rewrite (alltop_repeatZ F).
        apply rcfg_clsZ. fold j.
        replace (j - 1) with ((r - 1) + astride N0n stn r * acnt N0n stn j) by lia.
        apply rcells_narZ.
    + (* the interior *)
      rewrite Hxe in Hx.
      apply Forall_app in Hx as [_ Hrest'].
      inversion Hrest' as [|? ? Hdb Hrest].
      assert (Hdlt : d < b - 1) by lia.
      remember (aoff N0i sti n) as r eqn:Er.
      assert (Hrlt : r < N0i + sti) by (subst r; apply arm_index_lt; assumption).
      assert (Hn : r + astride N0i sti r * acnt N0i sti n = n)
        by (subst r; apply arm_index; assumption).
      destruct rest as [|e rest].
      { (* x ends after the digit: the marker follows *)
        exists (AI d b r), (negb (fm_left F)), (fm_left F),
               (rep T m ++ suf), (acnt N0i sti n).
        split; [|split; [|split; [|split]]].
        * exact (HAIS d b r Hdlt (le_n b) Hrlt).
        * intros He. unfold tailL. destruct (fm_left F); [discriminate|reflexivity].
        * intros He. unfold tailR. rewrite He. reflexivity.
        * rewrite (HAIL d b r Hdlt (le_n b) Hrlt). symmetry. apply rcfg_clsZ.
          rewrite Hxe, <- Hn at 1. apply rcells_intmZ.
        * rewrite (HAIR d b r Hdlt (le_n b) Hrlt). symmetry.
          rewrite (rsucc_consZ F a c z x m Hne), Hxe.
          rewrite (alltop_classZ F n d [] Hd), (inc_classZ F n d [] Hdlt).
          apply rcfg_clsZ. rewrite <- Hn at 1. apply rcells_intmZ. }
      inversion Hrest as [|? ? Heb _].
      exists (AI d e r), (negb (fm_left F)), (fm_left F),
             (flat_map (dig F) rest ++ M ++ rep T m ++ suf), (acnt N0i sti n).
      split; [|split; [|split; [|split]]].
      * exact (HAIS d e r Hdlt ltac:(lia) Hrlt).
      * intros He. unfold tailL. destruct (fm_left F); [discriminate|reflexivity].
      * intros He. unfold tailR. rewrite He. reflexivity.
      * rewrite (HAIL d e r Hdlt ltac:(lia) Hrlt). symmetry. apply rcfg_clsZ.
        rewrite Hxe, <- Hn at 1. apply rcells_intlZ; assumption.
      * rewrite (HAIR d e r Hdlt ltac:(lia) Hrlt). symmetry.
        rewrite (rsucc_consZ F a c z x m Hne), Hxe.
        rewrite (alltop_classZ F n d (e :: rest) Hd), (inc_classZ F n d (e :: rest) Hdlt).
        apply rcfg_clsZ. rewrite <- Hn at 1. apply rcells_intlZ; assumption.
Qed.

Lemma lapRZ : forall n, exists m c',
  0 < m /\ csteps tm m (Cf n) = Some c' /\ lift c' = lift (Cf (S n)).
Proof.
  intros n.
  pose proof (riter_invZ F a c z Hb Hz0 n (x0, m0) rinv0Z) as Hi.
  destruct (board_armRZ _ Hi) as (A & el & er & X & k & HA & HL & HR & Hl & Hr).
  destruct (HA _ _ k HL HR) as (m & c' & Hm & Hc' & Hlc).
  exists m, c'. split; [exact Hm|]. split.
  - cbn beta. rewrite Hl. exact Hc'.
  - rewrite Hlc, <- Hr. cbn beta.
    replace (S n) with (n + 1) by lia. rewrite riter_addZ. reflexivity.
Qed.

Lemma fireRZ : forall t N, ~ In t pins ->
  exists n k c', N <= n /\ csteps tm k (Cf n) = Some c' /\ cinstr c' = t.
Proof.
  intros t N Hnp.
  destruct (Hfire t Hnp) as [HfR | (Hzne & HfN)].
  - destruct (refill_cofinalZ F a c z Hb Hz0 (x0, m0) N rinv0Z) as (n & HN & Hx & Hi).
    exists n.
    destruct (riterZ F a c z (x0, m0) n) as [x m] eqn:Eit.
    cbn [fst] in Hx. subst x.
    remember (aoff N0r str m) as r eqn:Er.
    assert (Hrlt : r < N0r + str) by (subst r; apply arm_index_lt; assumption).
    assert (Hk : r + astride N0r str r * acnt N0r str m = m)
      by (subst r; apply arm_index; assumption).
    assert (Hden : rcfgZ F M T suf ([], m)
                   = cden [] [] (acnt N0r str m) (lr_lhs (AR r))).
    { rewrite (HARL r Hrlt).
      rewrite <- (rcfg_clsZ F M T suf
                    (blk (fm_pre F ++ M ++ rep T r) T (astride N0r str r) suf)
                    [] (acnt N0r str m) [] m).
      - unfold tailL, tailR; destruct (fm_left F); reflexivity.
      - rewrite <- Hk at 1. apply rcells_refillZ. }
    destruct (nfire_sound tm true true rsv (vsegs r t) (visI r t)
                (lr_lhs (AR r)) t Hrsv (HfR r Hrlt)
                [] [] (acnt N0r str m)
                (fun _ => eq_refl) (fun _ => eq_refl)) as (k & c' & Hc' & Ht).
    exists k, c'. cbn beta. rewrite ?Eit, Hden.
    split; [exact HN | split; [exact Hc' | exact Ht]].
  - destruct (nar_cofinalZ F a c z Hb Hz0 Hzne (x0, m0) N rinv0Z)
      as (n & HN & Hne & Htop & Hi).
    exists n.
    destruct (riterZ F a c z (x0, m0) n) as [x m] eqn:Eit.
    cbn [fst] in Hne, Htop.
    destruct (digs_decomp (b - 1) x) as [Hx | (n' & d & rest & Hxe & Hd)].
    2:{ exfalso. rewrite Hxe, (alltop_classZ F n' d rest Hd) in Htop. discriminate. }
    set (j := length x) in Hx.
    assert (Hj : 0 < j) by (unfold j; destruct x; [congruence | cbn; lia]).
    remember (aoff N0n stn j) as r eqn:Er.
    assert (Hr0 : 0 < r) by (subst r; apply arm_index_pos; assumption).
    assert (Hrlt : r < N0n + stn) by (subst r; apply arm_index_lt; assumption).
    assert (Hk : r + astride N0n stn r * acnt N0n stn j = j)
      by (subst r; apply arm_index; assumption).
    set (X := rep T m ++ suf).
    assert (Hden : rcfgZ F M T suf (x, m)
                   = cden (tailL F X) (tailR F X) (acnt N0n stn j) (lr_lhs (AN r))).
    { rewrite (HANL r Hr0 Hrlt). symmetry. apply rcfg_clsZ.
      rewrite Hx, <- Hk at 1. apply rcells_topZ. }
    destruct (nfire_sound tm (negb (fm_left F)) (fm_left F) rsv (vsegsN r t) (visN r t)
                (lr_lhs (AN r)) t Hrsv (HfN r Hr0 Hrlt)
                (tailL F X) (tailR F X) (acnt N0n stn j)) as (k & c' & Hc' & Ht).
    + intros He. unfold tailL. destruct (fm_left F); [discriminate|reflexivity].
    + intros He. unfold tailR. rewrite He. reflexivity.
    + exists k, c'. cbn beta. rewrite ?Eit, Hden.
      split; [exact HN | split; [exact Hc' | exact Ht]].
Qed.

Theorem boardR_neverqhtrZ : forall t0,
  stepn tm t0 InitES = Some (lift (rcfgZ F M T suf (x0, m0))) ->
  NeverQuasiHaltsTr tm0.
Proof.
  intros t0 Hboot.
  apply (glue_neverqhtrN tm0 pins Cf).
  - exists t0. exact Hboot.
  - intros n. destruct (lapRZ n) as (m & c' & Hm & Hrun & Hl).
    exists m, c'. split; [exact Hrun | split; [exact Hl | exact Hm]].
  - intros t Hnp N. exact (fireRZ t N Hnp).
Qed.

Lemma reachRZ : forall d n,
  exists Tm, stepn tm Tm (lift (Cf n)) = Some (lift (Cf (n + d))).
Proof.
  induction d; intros n.
  - exists 0. rewrite Nat.add_0_r. reflexivity.
  - destruct (IHd n) as (Tm & HT).
    destruct (lapRZ (n + d)) as (m & c' & _ & Hm & Hl).
    exists (Tm + m). rewrite stepn_add, HT.
    replace (n + S d) with (S (n + d)) by lia.
    rewrite <- Hl. apply csteps_lift. exact Hm.
Qed.

Lemma fire_everyRZ : forall t, ~ In t pins -> forall n,
  exists k c', csteps tm k (Cf n) = Some c' /\ cinstr c' = t.
Proof.
  intros t Hnp n.
  destruct (fireRZ t n Hnp) as (m & k & c' & Hm & Hk & Hc').
  destruct (reachRZ (m - n) n) as (Tm & HT).
  replace (n + (m - n)) with m in HT by lia.
  assert (Hs : stepn tm (Tm + k) (lift (Cf n)) = Some (lift c')).
  { rewrite stepn_add, HT. apply csteps_lift. exact Hk. }
  destruct (stepn_csteps_at tm (Tm + k) (Cf n) (lift c') Hs) as (c'' & Hc'' & Hl').
  exists (Tm + k), c''. split; [exact Hc''|].
  rewrite <- cinstr_lift, Hl', cinstr_lift. exact Hc'.
Qed.

Theorem boardR_qhtrZ : forall t0 B,
  stepn tm0 t0 InitES = Some (lift (rcfgZ F M T suf (x0, m0))) ->
  existsb (fun tg => cfires tm0 CTape.c0 t0 tg) pins = true ->
  (t0 <=? B) = true ->
  NonHalt tm0 /\ QHBoundTr B tm0 /\ QuasiHaltsTr tm0.
Proof.
  intros t0 B Hboot Hwit Hle.
  apply (lap_qh_stage tm0 pins (fun p => Cf (Nat.pred (Pos.to_nat p)))
           1%positive t0 B).
  - exact Hboot.
  - intros p _.
    destruct (lapRZ (Nat.pred (Pos.to_nat p))) as (m & c' & Hm & Hrun & Hl).
    exists m, c'. split; [exact Hrun | split; [|exact Hm]].
    rewrite Hl, Pos2Nat.inj_succ.
    replace (S (Nat.pred (Pos.to_nat p))) with (Pos.to_nat p)
      by (pose proof (Pos2Nat.is_pos p); lia).
    reflexivity.
  - intros t Hnp p _. exact (fire_everyRZ t Hnp (Nat.pred (Pos.to_nat p))).
  - exact Hwit.
  - exact Hle.
Qed.

End BoardRTrZ.
