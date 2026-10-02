(** * Checkers.LadderCheckTankTr: a binary counter that widens into a TANK
    (SCOPING_INSTR 7.4.LE7).

    LE6's B2 residue has rows whose tape is a counter followed by a run of a
    third word, the TANK, and the run SHRINKS as the counter widens.
    [1RB0LC_0LA1RC_1RD1LA_1RB0RD], read from its right end, is
    [(1011 | 1111)^k (0111)^m]: the counter counts (down, in the machine's
    words; up with the words swapped), every overflow widens it by one digit
    and turns one [0111] into a digit, and when the tank is empty the machine
    walks to the far end and rewrites the whole tape as a fresh tank.  With
    [LadderCheckRun2zTr] the run grows at the top (the counter narrows); here
    it is consumed:

      (x, m)          -> (x + 1, m)          x not all-top
      (top^k, m + 1)  -> (0^k 1, m)          the widening eats one tank word
      (top^k, 0)      -> (z, k + a)          the refill

    cells [pre ++ flat_map dig x ++ T^m ++ suf] on the family's counter side.
    Liveness: within a tank the value rises until the top, every top lowers
    [m], so refills recur; the fires are read from the refill arms.

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

Section Tank.

Variable F : Fam.
Variable T suf : list Sym.
Variable a : nat.
Variable z : list nat.     (** the refill's digits *)

Local Notation b := (fm_b F).

Fixpoint incK (x : list nat) : list nat :=
  match x with
  | [] => [1]
  | d :: t => if d =? b - 1 then 0 :: incK t else S d :: t
  end.

Definition alltopK (x : list nat) : bool := forallb (Nat.eqb (b - 1)) x.

Definition KSt : Type := (list nat * nat)%type.

Definition ksucc (s : KSt) : KSt :=
  let '(x, m) := s in
  if alltopK x
  then match m with
       | O => (z, length x + a)
       | S m' => (incK x, m')
       end
  else (incK x, m).

Fixpoint kiter (s : KSt) (n : nat) : KSt :=
  match n with
  | O => s
  | S n' => kiter (ksucc s) n'
  end.

Lemma kiter_add : forall n1 n2 s, kiter s (n1 + n2) = kiter (kiter s n1) n2.
Proof. induction n1 as [|n1 IH]; intros n2 s; [reflexivity | apply IH]. Qed.

Definition kcells (x : list nat) (m : nat) : list Sym :=
  fm_pre F ++ flat_map (dig F) x ++ rep T m ++ suf.

Definition kcfg (s : KSt) : cconf :=
  let '(x, m) := s in
  if fm_left F
  then (fm_st F, (kcells x m, fm_hs F, fm_other F))
  else (fm_st F, (fm_other F, fm_hs F, kcells x m)).

Lemma kcfg_cls : forall sd X n x m,
  kcells x m = sden X n sd ->
  cden (tailL F X) (tailR F X) n (cls_conf F sd) = kcfg (x, m).
Proof.
  intros sd X n x m H.
  unfold cden, cls_conf, kcfg, tailL, tailR.
  destruct (fm_left F); simpl; rewrite sden_flat, app_nil_r, <- H; reflexivity.
Qed.

(** *** The carry *)

Lemma inc_classK : forall n d rest, d < b - 1 ->
  incK (repeat (b - 1) n ++ d :: rest) = repeat 0 n ++ S d :: rest.
Proof.
  induction n as [|n IH]; intros d rest Hd; cbn [repeat app incK].
  - destruct (Nat.eqb_spec d (b - 1)); [lia | reflexivity].
  - rewrite Nat.eqb_refl, IH by exact Hd. reflexivity.
Qed.

Lemma inc_topK : forall n, incK (repeat (b - 1) n) = repeat 0 n ++ [1].
Proof.
  induction n as [|n IH]; [reflexivity|]. cbn [repeat incK app].
  rewrite Nat.eqb_refl, IH. reflexivity.
Qed.

Lemma alltop_repeatK : forall n, alltopK (repeat (b - 1) n) = true.
Proof.
  induction n as [|n IH]; [reflexivity|]. cbn [repeat alltopK forallb].
  rewrite Nat.eqb_refl. exact IH.
Qed.

Lemma alltop_classK : forall n d rest, d <> b - 1 ->
  alltopK (repeat (b - 1) n ++ d :: rest) = false.
Proof.
  induction n as [|n IH]; intros d rest Hd; cbn [repeat app alltopK forallb].
  - destruct (Nat.eqb_spec (b - 1) d); [lia | reflexivity].
  - rewrite Nat.eqb_refl. apply IH. exact Hd.
Qed.

Hypothesis Hb : 1 < b.
Hypothesis Hz : Forall (fun d => d < b) z.
Hypothesis Hzne : z <> [].

Lemma inc_valK : forall x, Forall (fun d => d < b) x -> alltopK x = false ->
  val_pos b (incK x) = S (val_pos b x).
Proof.
  induction x as [|d t IH]; intros Hx Ht; [discriminate|].
  inversion Hx as [|? ? Hd Htl]; subst.
  cbn [incK alltopK forallb] in *.
  destruct (Nat.eqb_spec d (b - 1)) as [E|E].
  - subst d. rewrite Nat.eqb_refl in Ht. cbn [andb] in Ht.
    cbn [val_pos]. rewrite (IH Htl Ht). nia.
  - cbn [val_pos]. lia.
Qed.

Lemma inc_lenK : forall x, alltopK x = false -> length (incK x) = length x.
Proof.
  induction x as [|d t IH]; intros Ht; [discriminate|]. cbn [incK alltopK forallb] in *.
  destruct (Nat.eqb_spec d (b - 1)) as [E|E].
  - subst d. rewrite Nat.eqb_refl in Ht. cbn [andb] in Ht.
    cbn [length]. rewrite (IH Ht). reflexivity.
  - reflexivity.
Qed.

Lemma inc_bndK : forall x, Forall (fun d => d < b) x -> Forall (fun d => d < b) (incK x).
Proof.
  induction x as [|d t IH]; intros Hx; [constructor; [lia | constructor]|].
  inversion Hx as [|? ? Hd Htl]; subst. cbn [incK].
  destruct (Nat.eqb_spec d (b - 1)) as [E|E].
  - constructor; [lia | apply IH; exact Htl].
  - constructor; [lia | exact Htl].
Qed.

Lemma inc_neK : forall x, incK x <> [].
Proof. intros [|d t]; cbn [incK]; [discriminate|]. destruct (d =? b - 1); discriminate. Qed.

(** *** Refills recur *)

Definition KInv (s : KSt) : Prop :=
  let '(x, m) := s in Forall (fun d => d < b) x /\ x <> [].

Lemma ksucc_inv : forall s, KInv s -> KInv (ksucc s).
Proof.
  intros [x m] [Hx Hne]. cbn [ksucc].
  destruct (alltopK x); [destruct m|];
    split; try apply inc_bndK; try apply inc_neK; auto.
Qed.

Lemma kiter_inv : forall n s, KInv s -> KInv (kiter s n).
Proof. induction n as [|n IH]; intros s Hs; [exact Hs|]. apply IH, ksucc_inv, Hs. Qed.

(** the top of the empty tank: [x] all-top, [m = 0] *)
Definition ktop (s : KSt) : Prop := alltopK (fst s) = true /\ snd s = 0.

Lemma refill_reachedK : forall m v x, KInv (x, m) ->
  Nat.pow b (length x) - val_pos b x <= v ->
  exists n, ktop (kiter (x, m) n) /\ KInv (kiter (x, m) n).
Proof.
  induction m as [|m IHm]; intros v; induction v as [|v IHv]; intros x Hs Hv.
  - exfalso. pose proof (val_pos_lt b x Hb (proj1 Hs)). lia.
  - destruct (alltopK x) eqn:E.
    + exists 0. split; [split; [exact E | reflexivity] | exact Hs].
    + assert (Hi : KInv (incK x, 0)) by (split; [apply inc_bndK, (proj1 Hs) | apply inc_neK]).
      destruct (IHv (incK x) Hi) as (n & Hn).
      * rewrite (inc_lenK x E), (inc_valK x (proj1 Hs) E). lia.
      * exists (S n). cbn [kiter ksucc]. rewrite E. exact Hn.
  - exfalso. pose proof (val_pos_lt b x Hb (proj1 Hs)). lia.
  - destruct (alltopK x) eqn:E.
    + (* the widening: one tank word fewer *)
      assert (Hi : KInv (incK x, m)) by (split; [apply inc_bndK, (proj1 Hs) | apply inc_neK]).
      destruct (IHm (Nat.pow b (length (incK x)) - val_pos b (incK x)) (incK x) Hi (le_n _))
        as (n & Hn).
      exists (S n). cbn [kiter ksucc]. rewrite E. exact Hn.
    + assert (Hi : KInv (incK x, S m)) by (split; [apply inc_bndK, (proj1 Hs) | apply inc_neK]).
      destruct (IHv (incK x) Hi) as (n & Hn).
      * rewrite (inc_lenK x E), (inc_valK x (proj1 Hs) E). lia.
      * exists (S n). cbn [kiter ksucc]. rewrite E. exact Hn.
Qed.

Theorem refill_cofinalK : forall s N, KInv s ->
  exists n, N <= n /\ ktop (kiter s n) /\ KInv (kiter s n).
Proof.
  intros s N Hs.
  pose proof (kiter_inv N s Hs) as HsN.
  destruct (kiter s N) as [x m] eqn:EN.
  destruct (refill_reachedK m (Nat.pow b (length x) - val_pos b x) x HsN (le_n _))
    as (n & Hn).
  exists (N + n). rewrite kiter_add, EN. split; [lia | exact Hn].
Qed.

(** *** The cells of each class *)

Lemma kcells_int : forall t r st n d rest m,
  kcells (repeat t (r + st * n) ++ d :: rest) m
    = sden (flat_map (dig F) rest ++ rep T m ++ suf) n
        (blk (fm_pre F ++ rep (dig F t) r) (dig F t) st (dig F d)).
Proof.
  intros t r st n d rest m. unfold kcells.
  rewrite blk_den, flat_map_app, flat_map_repeat_nil.
  cbn [flat_map]. rewrite rep_add, !app_assoc. reflexivity.
Qed.

Lemma kcells_wid : forall t r st n m,
  kcells (repeat t (r + st * n)) (S m)
    = sden (rep T m ++ suf) n (blk (fm_pre F ++ rep (dig F t) r) (dig F t) st T).
Proof.
  intros t r st n m. unfold kcells.
  rewrite blk_den, flat_map_repeat_nil, rep_add. cbn [rep].
  rewrite !app_assoc. reflexivity.
Qed.

Lemma kcells_widened : forall r st n m,
  kcells (repeat 0 (r + st * n) ++ [1]) m
    = sden (rep T m ++ suf) n
        (blk (fm_pre F ++ rep (dig F 0) r) (dig F 0) st (dig F 1)).
Proof.
  intros r st n m. unfold kcells.
  rewrite blk_den, flat_map_app, flat_map_repeat_nil, rep_add.
  cbn [flat_map]. rewrite app_nil_r, !app_assoc. reflexivity.
Qed.

Lemma kcells_top : forall t r st n,
  kcells (repeat t (r + st * n)) 0
    = sden [] n (blk (fm_pre F ++ rep (dig F t) r) (dig F t) st suf).
Proof.
  intros t r st n. unfold kcells.
  rewrite blk_den, flat_map_repeat_nil, rep_add. cbn [rep].
  rewrite !app_assoc, !app_nil_r. reflexivity.
Qed.

Lemma kcells_refilled : forall f1 st n f2,
  kcells z (f1 + st * n + f2)
    = sden [] n (blk (fm_pre F ++ flat_map (dig F) z ++ rep T f1) T st (rep T f2 ++ suf)).
Proof.
  intros f1 st n f2. unfold kcells.
  rewrite blk_den, !rep_add, !app_nil_r, !app_assoc. reflexivity.
Qed.

End Tank.

(** ** 2. The board *)

Section BoardK.

Variable tm0   : TM.
Variable pins  : list Instr.
Local Notation tm := (tm_wrap_trs tm0 pins).

Variable F     : Fam.
Variable T suf : list Sym.
Variable a     : nat.
Variable z     : list nat.
Variable AI    : nat -> nat -> LRule.   (** interior: digit, index *)
Variable N0i sti : nat.
Variable AW    : nat -> LRule.          (** widening: index (the width) *)
Variable N0w stw : nat.
Variable AR    : nat -> LRule.          (** refill: index (the width) *)
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
Hypothesis Hne0  : x0 <> [].
Hypothesis Hz0   : Forall (fun d => d < b) z.
Hypothesis Hzne  : z <> [].

Hypothesis Hsti : 0 < sti.
Hypothesis HAIS : forall d r, d < b - 1 -> r < N0i + sti ->
  ReachL tm (negb (fm_left F)) (fm_left F) (lr_lhs (AI d r)) (lr_rhs (AI d r)).
Hypothesis HAIL : forall d r, d < b - 1 -> r < N0i + sti ->
  lr_lhs (AI d r) = cls_conf F (blk (fm_pre F ++ rep (dig F (b - 1)) r) (dig F (b - 1))
                                  (astride N0i sti r) (dig F d)).
Hypothesis HAIR : forall d r, d < b - 1 -> r < N0i + sti ->
  lr_rhs (AI d r) = cls_conf F (blk (fm_pre F ++ rep (dig F 0) r) (dig F 0)
                                  (astride N0i sti r) (dig F (S d))).

Hypothesis Hstw : 0 < stw.
Hypothesis HN0w : 0 < N0w.
Hypothesis HAWS : forall r, 0 < r -> r < N0w + stw ->
  ReachL tm (negb (fm_left F)) (fm_left F) (lr_lhs (AW r)) (lr_rhs (AW r)).
Hypothesis HAWL : forall r, 0 < r -> r < N0w + stw ->
  lr_lhs (AW r) = cls_conf F (blk (fm_pre F ++ rep (dig F (b - 1)) r)
                                (dig F (b - 1)) (astride N0w stw r) T).
Hypothesis HAWR : forall r, 0 < r -> r < N0w + stw ->
  lr_rhs (AW r) = cls_conf F (blk (fm_pre F ++ rep (dig F 0) r)
                                (dig F 0) (astride N0w stw r) (dig F 1)).

Hypothesis Hstr : 0 < str.
Hypothesis HN0r : 0 < N0r.
Hypothesis HARS : forall r, 0 < r -> r < N0r + str ->
  ReachL tm true true (lr_lhs (AR r)) (lr_rhs (AR r)).
Hypothesis HARL : forall r, 0 < r -> r < N0r + str ->
  lr_lhs (AR r) = cls_conf F (blk (fm_pre F ++ rep (dig F (b - 1)) r) (dig F (b - 1))
                                (astride N0r str r) suf).
Hypothesis HARR : forall r, 0 < r -> r < N0r + str ->
  lr_rhs (AR r) = cls_conf F (blk (fm_pre F ++ flat_map (dig F) z ++ rep T (fm1 r)) T
                                (astride N0r str r) (rep T (fm2 r) ++ suf)).
Hypothesis Hfm : forall r, 0 < r -> r < N0r + str -> fm1 r + fm2 r = r + a.

Hypothesis Hrsv : Forall (RuleSound tm false false) rsv.
(** each instruction is witnessed from every refill arm *)
Hypothesis Hfire : forall t, ~ In t pins -> forall r, 0 < r -> r < N0r + str ->
  nfire tm true true rsv (vsegs r t) (visI r t) (lr_lhs (AR r)) = Some t.

Local Notation Cf := (fun n => kcfg F T suf (kiter F a z (x0, m0) n)).

Lemma kinv0 : KInv F (x0, m0).
Proof. split; assumption. Qed.

Lemma board_armK : forall s, KInv F s ->
  exists A el er X n,
    ReachL tm el er (lr_lhs A) (lr_rhs A)
    /\ (el = true -> tailL F X = []) /\ (er = true -> tailR F X = [])
    /\ kcfg F T suf s = cden (tailL F X) (tailR F X) n (lr_lhs A)
    /\ kcfg F T suf (ksucc F a z s) = cden (tailL F X) (tailR F X) n (lr_rhs A).
Proof.
  intros [x m] [Hx Hne].
  destruct (digs_decomp (b - 1) x) as [Htop | (n & d & rest & Hxe & Hd)].
  - set (j := length x) in Htop.
    assert (Hj : 0 < j) by (unfold j; destruct x; [congruence | cbn; lia]).
    assert (Ht : alltopK F x = true) by (rewrite Htop; apply alltop_repeatK).
    destruct m as [|m].
    + (* the refill *)
      remember (aoff N0r str j) as r eqn:Er.
      assert (Hr0 : 0 < r) by (subst r; apply arm_index_pos; assumption).
      assert (Hrlt : r < N0r + str) by (subst r; apply arm_index_lt; assumption).
      assert (Hk : r + astride N0r str r * acnt N0r str j = j)
        by (subst r; apply arm_index; assumption).
      exists (AR r), true, true, [], (acnt N0r str j).
      split; [|split; [|split; [|split]]].
      * exact (HARS r Hr0 Hrlt).
      * intros _; apply tailL_nil.
      * intros _; apply tailR_nil.
      * rewrite (HARL r Hr0 Hrlt). symmetry. apply kcfg_cls.
        rewrite Htop, <- Hk at 1. apply kcells_top.
      * rewrite (HARR r Hr0 Hrlt). symmetry. cbn [ksucc]. rewrite Ht.
        apply kcfg_cls. fold j. pose proof (Hfm r Hr0 Hrlt).
        rewrite <- (kcells_refilled F T suf z (fm1 r) (astride N0r str r)
                      (acnt N0r str j) (fm2 r)).
        f_equal. lia.
    + (* the widening *)
      remember (aoff N0w stw j) as r eqn:Er.
      assert (Hr0 : 0 < r) by (subst r; apply arm_index_pos; assumption).
      assert (Hrlt : r < N0w + stw) by (subst r; apply arm_index_lt; assumption).
      assert (Hk : r + astride N0w stw r * acnt N0w stw j = j)
        by (subst r; apply arm_index; assumption).
      exists (AW r), (negb (fm_left F)), (fm_left F), (rep T m ++ suf), (acnt N0w stw j).
      split; [|split; [|split; [|split]]].
      * exact (HAWS r Hr0 Hrlt).
      * intros He. unfold tailL. destruct (fm_left F); [discriminate|reflexivity].
      * intros He. unfold tailR. rewrite He. reflexivity.
      * rewrite (HAWL r Hr0 Hrlt). symmetry. apply kcfg_cls.
        rewrite Htop, <- Hk at 1. apply kcells_wid.
      * rewrite (HAWR r Hr0 Hrlt). symmetry. cbn [ksucc]. rewrite Ht.
        apply kcfg_cls. rewrite Htop, (inc_topK F). fold j.
        replace (repeat 0 j ++ [1])
          with (repeat 0 (r + astride N0w stw r * acnt N0w stw j) ++ [1]) by (rewrite Hk; reflexivity).
        apply kcells_widened.
  - (* the interior *)
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
    + exact (HAIS d r Hdlt Hrlt).
    + intros He. unfold tailL. destruct (fm_left F); [discriminate|reflexivity].
    + intros He. unfold tailR. rewrite He. reflexivity.
    + rewrite (HAIL d r Hdlt Hrlt). symmetry. apply kcfg_cls.
      rewrite Hxe, <- Hn at 1. apply kcells_int.
    + rewrite (HAIR d r Hdlt Hrlt). symmetry. cbn [ksucc].
      rewrite Hxe, (alltop_classK F n d rest Hd), (inc_classK F n d rest Hdlt).
      apply kcfg_cls. rewrite <- Hn at 1. apply kcells_int.
Qed.

Lemma lapK : forall n, exists m c',
  0 < m /\ csteps tm m (Cf n) = Some c' /\ lift c' = lift (Cf (S n)).
Proof.
  intros n.
  pose proof (kiter_inv F a z Hb Hz0 Hzne n (x0, m0) kinv0) as Hi.
  destruct (board_armK _ Hi) as (A & el & er & X & k & HA & HL & HR & Hl & Hr).
  destruct (HA _ _ k HL HR) as (m & c' & Hm & Hc' & Hlc).
  exists m, c'. split; [exact Hm|]. split.
  - cbn beta. rewrite Hl. exact Hc'.
  - rewrite Hlc, <- Hr. cbn beta.
    replace (S n) with (n + 1) by lia. rewrite kiter_add. reflexivity.
Qed.

Lemma fireK : forall t N, ~ In t pins ->
  exists n k c', N <= n /\ csteps tm k (Cf n) = Some c' /\ cinstr c' = t.
Proof.
  intros t N Hnp.
  destruct (refill_cofinalK F a z Hb Hz0 Hzne (x0, m0) N kinv0) as (n & HN & [Htop Hm] & Hi).
  exists n.
  destruct (kiter F a z (x0, m0) n) as [x m] eqn:Eit.
  cbn [fst snd] in Htop, Hm. subst m.
  destruct Hi as [_ Hne].
  destruct (digs_decomp (b - 1) x) as [Hx | (n' & d & rest & Hxe & Hd)].
  2:{ exfalso. rewrite Hxe, (alltop_classK F n' d rest Hd) in Htop. discriminate. }
  set (j := length x) in Hx.
  assert (Hj : 0 < j) by (unfold j; destruct x; [congruence | cbn; lia]).
  remember (aoff N0r str j) as r eqn:Er.
  assert (Hr0 : 0 < r) by (subst r; apply arm_index_pos; assumption).
  assert (Hrlt : r < N0r + str) by (subst r; apply arm_index_lt; assumption).
  assert (Hk : r + astride N0r str r * acnt N0r str j = j)
    by (subst r; apply arm_index; assumption).
  assert (Hden : kcfg F T suf (x, 0) = cden [] [] (acnt N0r str j) (lr_lhs (AR r))).
  { rewrite (HARL r Hr0 Hrlt).
    rewrite <- (kcfg_cls F T suf (blk (fm_pre F ++ rep (dig F (b - 1)) r) (dig F (b - 1))
                                (astride N0r str r) suf) [] (acnt N0r str j) x 0).
    - unfold tailL, tailR; destruct (fm_left F); reflexivity.
    - rewrite Hx, <- Hk at 1. apply kcells_top. }
  destruct (nfire_sound tm true true rsv (vsegs r t) (visI r t)
              (lr_lhs (AR r)) t Hrsv (Hfire t Hnp r Hr0 Hrlt)
              [] [] (acnt N0r str j)
              (fun _ => eq_refl) (fun _ => eq_refl)) as (k & c' & Hc' & Ht).
  exists k, c'. cbn beta. rewrite ?Eit, Hden.
  split; [exact HN | split; [exact Hc' | exact Ht]].
Qed.

Theorem boardK_neverqhtr : forall t0,
  stepn tm t0 InitES = Some (lift (kcfg F T suf (x0, m0))) ->
  NeverQuasiHaltsTr tm0.
Proof.
  intros t0 Hboot.
  apply (glue_neverqhtrN tm0 pins Cf).
  - exists t0. exact Hboot.
  - intros n. destruct (lapK n) as (m & c' & Hm & Hrun & Hl).
    exists m, c'. split; [exact Hrun | split; [exact Hl | exact Hm]].
  - intros t Hnp N. exact (fireK t N Hnp).
Qed.

Lemma reachK : forall d n,
  exists Tm, stepn tm Tm (lift (Cf n)) = Some (lift (Cf (n + d))).
Proof.
  induction d; intros n.
  - exists 0. rewrite Nat.add_0_r. reflexivity.
  - destruct (IHd n) as (Tm & HT).
    destruct (lapK (n + d)) as (m & c' & _ & Hm & Hl).
    exists (Tm + m). rewrite stepn_add, HT.
    replace (n + S d) with (S (n + d)) by lia.
    rewrite <- Hl. apply csteps_lift. exact Hm.
Qed.

Lemma fire_everyK : forall t, ~ In t pins -> forall n,
  exists k c', csteps tm k (Cf n) = Some c' /\ cinstr c' = t.
Proof.
  intros t Hnp n.
  destruct (fireK t n Hnp) as (m & k & c' & Hm & Hk & Hc').
  destruct (reachK (m - n) n) as (Tm & HT).
  replace (n + (m - n)) with m in HT by lia.
  assert (Hs : stepn tm (Tm + k) (lift (Cf n)) = Some (lift c')).
  { rewrite stepn_add, HT. apply csteps_lift. exact Hk. }
  destruct (stepn_csteps_at tm (Tm + k) (Cf n) (lift c') Hs) as (c'' & Hc'' & Hl').
  exists (Tm + k), c''. split; [exact Hc''|].
  rewrite <- cinstr_lift, Hl', cinstr_lift. exact Hc'.
Qed.

Theorem boardK_qhtr : forall t0 B,
  stepn tm0 t0 InitES = Some (lift (kcfg F T suf (x0, m0))) ->
  existsb (fun tg => cfires tm0 CTape.c0 t0 tg) pins = true ->
  (t0 <=? B) = true ->
  NonHalt tm0 /\ QHBoundTr B tm0 /\ QuasiHaltsTr tm0.
Proof.
  intros t0 B Hboot Hwit Hle.
  apply (lap_qh_stage tm0 pins (fun p => Cf (Nat.pred (Pos.to_nat p)))
           1%positive t0 B).
  - exact Hboot.
  - intros p _.
    destruct (lapK (Nat.pred (Pos.to_nat p))) as (m & c' & Hm & Hrun & Hl).
    exists m, c'. split; [exact Hrun | split; [|exact Hm]].
    rewrite Hl, Pos2Nat.inj_succ.
    replace (S (Nat.pred (Pos.to_nat p))) with (Pos.to_nat p)
      by (pose proof (Pos2Nat.is_pos p); lia).
    reflexivity.
  - intros t Hnp p _. exact (fire_everyK t Hnp (Nat.pred (Pos.to_nat p))).
  - exact Hwit.
  - exact Hle.
Qed.

End BoardK.
