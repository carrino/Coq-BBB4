(** * Checkers.LadderCheckRun3Tr: terminator-run counters whose TOP digit
    has its own spelling (SCOPING_INSTR 7.4.LE5).

    LE4 read 90 rows as positional counters whose FILL costs about twice as
    much at each width, and 18 as marker runs whose REFILL does; it filed
    them as counters nested two and three deep.  Most are one counter that
    no reading stated.  On [0RB1LA_1LC1RD_0RB0LD_1RB0LA] the anchor
    [A1] sees

      x ++ e ++ (01)^m,   x over 11 (= 0) / 01 (= 1),  e over 10 (= 0) / 00 (= 1)

    [x ++ [e]] is one binary counter whose top digit is spelled with the
    words [E0], [E1]; the top of the whole counter narrows [x] by a digit
    and lengthens the run:

      (x, e, m)          -> ((x, e) + 1, m)           while (x, e) is not all top;
      (top^j, E_top, m)  -> (0^(j-1), E_0, m + 1)  (j >= 1)   the top narrows x;
      ([], E_top, m)     -> (0^(m + a), E_0, c)               an empty x refills.

    LE4's positional reading takes [E0 T] for a terminator, so its "fill" is
    every narrowing and every inner count between two refills, and its cost
    doubles; its marker reading ([LadderCheckRun2Tr]) is the case of ONE
    top word ([be = 1]), where the top carry below never fires.

    The top digit is base [be] over the words [EW] (any [be >= 1]); the
    cells are [pre ++ x ++ EW_e ++ T^m ++ suf].  Four arm classes, all
    [LadderNest.ReachL] programs:
    - interior: [t^n d w X -> 0^n (d+1) w X], [X] opaque, [w] the next digit
      or the top word [EW_e] when [x] ends (one word of lookahead);
    - the top carry: [t^j EW_e X -> 0^j EW_(e+1) X], [X] opaque, [j >= 0];
    - narrowing: [t^j EW_top X -> 0^(j-1) EW_0 T X], [X] opaque, [j >= 1];
    - refill: [EW_top T^m suf -> 0^(m+a) EW_0 T^c suf], both tails known empty.

    Liveness: inside a length the mixed-radix value of [(x, e)] rises by one
    each step, and the narrowing shortens [x], so refills recur and every
    instruction fires from the refill arms.

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

Section Run3.

Variable F : Fam.
Variable EW : list (list Sym).
Variable T suf : list Sym.
Variable a c : nat.

Local Notation b := (fm_b F).
Local Notation be := (length EW).

Definition ew3 (e : nat) : list Sym := nth e EW [].

Fixpoint inc3 (x : list nat) : list nat :=
  match x with
  | [] => []
  | d :: t => if d =? b - 1 then 0 :: inc3 t else S d :: t
  end.

Definition alltop3 (x : list nat) : bool := forallb (Nat.eqb (b - 1)) x.

Definition RSt3 : Type := (list nat * nat * nat)%type.

Definition rsucc3 (s : RSt3) : RSt3 :=
  let '(x, e, m) := s in
  if alltop3 x then
    if S e <? be then (repeat 0 (length x), S e, m)
    else match x with
         | [] => (repeat 0 (m + a), 0, c)
         | _ :: _ => (repeat 0 (length x - 1), 0, S m)
         end
  else (inc3 x, e, m).

Fixpoint riter3 (s : RSt3) (n : nat) : RSt3 :=
  match n with
  | O => s
  | S n' => riter3 (rsucc3 s) n'
  end.

Lemma riter_add3 : forall n1 n2 s, riter3 s (n1 + n2) = riter3 (riter3 s n1) n2.
Proof. induction n1 as [|n1 IH]; intros n2 s; [reflexivity | apply IH]. Qed.

Definition rcells3 (x : list nat) (e m : nat) : list Sym :=
  fm_pre F ++ flat_map (dig F) x ++ ew3 e ++ rep T m ++ suf.

Definition rcfg3 (s : RSt3) : cconf :=
  let '(x, e, m) := s in
  if fm_left F
  then (fm_st F, (rcells3 x e m, fm_hs F, fm_other F))
  else (fm_st F, (fm_other F, fm_hs F, rcells3 x e m)).

Lemma rcfg_cls3 : forall sd X n x e m,
  rcells3 x e m = sden X n sd ->
  cden (tailL F X) (tailR F X) n (cls_conf F sd) = rcfg3 (x, e, m).
Proof.
  intros sd X n x e m H.
  unfold cden, cls_conf, rcfg3, tailL, tailR.
  destruct (fm_left F); simpl; rewrite sden_flat, app_nil_r, <- H; reflexivity.
Qed.

(** *** The odometer carry, and the value it adds one to *)

Lemma inc_class3 : forall n d rest, d < b - 1 ->
  inc3 (repeat (b - 1) n ++ d :: rest) = repeat 0 n ++ S d :: rest.
Proof.
  induction n as [|n IH]; intros d rest Hd; cbn [repeat app inc3].
  - destruct (Nat.eqb_spec d (b - 1)); [lia | reflexivity].
  - rewrite Nat.eqb_refl, IH by exact Hd. reflexivity.
Qed.

Lemma alltop_repeat3 : forall n, alltop3 (repeat (b - 1) n) = true.
Proof.
  induction n as [|n IH]; [reflexivity|]. cbn [repeat alltop3 forallb].
  rewrite Nat.eqb_refl. exact IH.
Qed.

Lemma alltop_class3 : forall n d rest, d <> b - 1 ->
  alltop3 (repeat (b - 1) n ++ d :: rest) = false.
Proof.
  induction n as [|n IH]; intros d rest Hd; cbn [repeat app alltop3 forallb].
  - destruct (Nat.eqb_spec (b - 1) d); [lia | reflexivity].
  - rewrite Nat.eqb_refl. apply IH. exact Hd.
Qed.

Lemma alltop_shape3 : forall x, alltop3 x = true -> x = repeat (b - 1) (length x).
Proof.
  intros x H. destruct (digs_decomp (b - 1) x) as [E | (n & d & rest & E & Hd)].
  - exact E.
  - rewrite E, alltop_class3 in H by exact Hd. discriminate.
Qed.

(** *** The cells of each class *)

(** The word after the digit an interior arm increments: the next digit
    [e < b], or the top word [EW_(e - b)] when [x] ends there. *)
Definition ilook3 (e : nat) : list Sym := if e <? b then dig F e else ew3 (e - b).

Lemma rcells_intl3 : forall t r st n d e' rest e m, e' < b ->
  rcells3 (repeat t (r + st * n) ++ d :: e' :: rest) e m
    = sden (flat_map (dig F) rest ++ ew3 e ++ rep T m ++ suf) n
        (blk (fm_pre F ++ rep (dig F t) r) (dig F t) st (dig F d ++ ilook3 e')).
Proof.
  intros t r st n d e' rest e m He. unfold rcells3, ilook3.
  destruct (Nat.ltb_spec e' b) as [_|]; [|lia].
  rewrite blk_den, flat_map_app, flat_map_repeat_nil.
  cbn [flat_map app]. rewrite rep_add, !app_assoc. reflexivity.
Qed.

Lemma rcells_intm3 : forall t r st n d e m,
  rcells3 (repeat t (r + st * n) ++ [d]) e m
    = sden (rep T m ++ suf) n
        (blk (fm_pre F ++ rep (dig F t) r) (dig F t) st (dig F d ++ ilook3 (b + e))).
Proof.
  intros t r st n d e m. unfold rcells3, ilook3.
  destruct (Nat.ltb_spec (b + e) b) as [|_]; [lia|].
  replace (b + e - b) with e by lia.
  rewrite blk_den, flat_map_app, flat_map_repeat_nil.
  cbn [flat_map app]. rewrite app_nil_r, rep_add, !app_assoc. reflexivity.
Qed.

Lemma rcells_top3 : forall t r st n e m,
  rcells3 (repeat t (r + st * n)) e m
    = sden (rep T m ++ suf) n
        (blk (fm_pre F ++ rep (dig F t) r) (dig F t) st (ew3 e)).
Proof.
  intros t r st n e m. unfold rcells3.
  rewrite blk_den, flat_map_repeat_nil, rep_add.
  rewrite !app_assoc. reflexivity.
Qed.

Lemma rcells_nar3 : forall t r st n m,
  rcells3 (repeat t (r + st * n)) 0 (S m)
    = sden (rep T m ++ suf) n
        (blk (fm_pre F ++ rep (dig F t) r) (dig F t) st (ew3 0 ++ T)).
Proof.
  intros t r st n m. unfold rcells3.
  rewrite blk_den, flat_map_repeat_nil, rep_add. cbn [rep].
  rewrite !app_assoc. reflexivity.
Qed.

Lemma rcells_refill3 : forall e r st n,
  rcells3 [] e (r + st * n)
    = sden [] n (blk (fm_pre F ++ ew3 e ++ rep T r) T st suf).
Proof.
  intros e r st n. unfold rcells3.
  rewrite blk_den, rep_add. cbn [flat_map].
  rewrite ?app_nil_r, !app_assoc, ?app_nil_r. reflexivity.
Qed.

Lemma rcells_refilled3 : forall f1 st n f2,
  rcells3 (repeat 0 (f1 + st * n + f2)) 0 c
    = sden [] n (blk (fm_pre F ++ rep (dig F 0) f1) (dig F 0) st
                   (rep (dig F 0) f2 ++ ew3 0 ++ rep T c ++ suf)).
Proof.
  intros f1 st n f2. unfold rcells3.
  rewrite blk_den, flat_map_repeat_nil, !rep_add, !app_nil_r, !app_assoc.
  reflexivity.
Qed.

Hypothesis Hb : 1 < b.

Lemma inc_val3 : forall x, Forall (fun d => d < b) x -> alltop3 x = false ->
  val_pos b (inc3 x) = S (val_pos b x).
Proof.
  induction x as [|d t IH]; intros Hx Ht; [discriminate|].
  inversion Hx as [|? ? Hd Htl]; subst.
  cbn [inc3 alltop3 forallb] in *.
  destruct (Nat.eqb_spec d (b - 1)) as [E|E].
  - subst d. rewrite Nat.eqb_refl in Ht. cbn [andb] in Ht.
    cbn [val_pos]. rewrite (IH Htl Ht). nia.
  - cbn [val_pos]. lia.
Qed.

Lemma inc_len3 : forall x, length (inc3 x) = length x.
Proof.
  induction x as [|d t IH]; [reflexivity|]. cbn [inc3].
  destruct (d =? b - 1); cbn [length]; [rewrite IH|]; reflexivity.
Qed.

Lemma inc_bnd3 : forall x, Forall (fun d => d < b) x -> alltop3 x = false ->
  Forall (fun d => d < b) (inc3 x).
Proof.
  induction x as [|d t IH]; intros Hx Ht; [constructor|].
  inversion Hx as [|? ? Hd Htl]; subst.
  cbn [inc3 alltop3 forallb] in *.
  destruct (Nat.eqb_spec d (b - 1)) as [E|E].
  - subst d. rewrite Nat.eqb_refl in Ht. constructor; [lia | apply IH; assumption].
  - constructor; [lia | exact Htl].
Qed.

Lemma repeat0_bnd3 : forall n, Forall (fun d => d < b) (repeat 0 n).
Proof.
  intros n. apply Forall_forall. intros y Hy. apply repeat_spec in Hy. lia.
Qed.

(** *** Refills recur *)

Hypothesis Hbe : 0 < be.

Definition RInv3 (s : RSt3) : Prop :=
  let '(x, e, m) := s in Forall (fun d => d < b) x /\ e < be.

(** a refill state: [x] empty and its top digit at the top *)
Definition isref3 (s : RSt3) : bool :=
  let '(x, e, m) := s in
  match x with [] => negb (S e <? be) | _ :: _ => false end.

Lemma rsucc_inv3 : forall s, RInv3 s -> RInv3 (rsucc3 s).
Proof.
  intros [[x e] m] [Hx He]. cbn [rsucc3].
  destruct (alltop3 x) eqn:Et.
  - destruct (Nat.ltb_spec (S e) be).
    + split; [apply repeat0_bnd3 | exact H].
    + destruct x; (split; [apply repeat0_bnd3 | lia]).
  - split; [apply inc_bnd3; assumption | exact He].
Qed.

Lemma riter_inv3 : forall n s, RInv3 s -> RInv3 (riter3 s n).
Proof.
  induction n as [|n IH]; intros s Hs; [exact Hs|]. apply IH, rsucc_inv3, Hs.
Qed.

Lemma refill_step3 : forall k,
  (forall s, RInv3 s -> length (fst (fst s)) < k -> exists n, isref3 (riter3 s n) = true) ->
  forall v s, RInv3 s -> length (fst (fst s)) <= k ->
  be * Nat.pow b (length (fst (fst s)))
    <= v + val_pos b (fst (fst s)) + Nat.pow b (length (fst (fst s))) * snd (fst s) ->
  exists n, isref3 (riter3 s n) = true.
Proof.
  intros k IHk v. induction v as [|v IHv]; intros [[x e] m] Hs Hk Hv;
    cbn [fst snd] in *; destruct Hs as [Hx He];
    pose proof (val_pos_lt b x Hb Hx) as Hlt;
    pose proof (pow_pos b (length x) ltac:(lia)) as Hp.
  - exfalso. nia.
  - destruct (isref3 (x, e, m)) eqn:Er; [exists 0; exact Er|].
    destruct (alltop3 x) eqn:Et.
    + destruct (Nat.ltb_spec (S e) be) as [Hse|Hse].
      * (* the top carry: the value rises by one *)
        destruct (IHv (repeat 0 (length x), S e, m)) as (n & Hn).
        -- split; [apply repeat0_bnd3 | exact Hse].
        -- cbn [fst]. rewrite repeat_length. exact Hk.
        -- cbn [fst snd]. rewrite repeat_length.
           replace (val_pos b (repeat 0 (length x)))
             with (val_pos b (repeat 0 (length x) ++ [])) by (rewrite app_nil_r; reflexivity).
           rewrite val_pos_repeat0. cbn [val_pos].
           rewrite (alltop_shape3 x Et) in Hv at 2.
           rewrite val_pos_repeat_max in Hv by exact Hb. nia.
        -- exists (S n). cbn [riter3 rsucc3]. rewrite Et.
           destruct (Nat.ltb_spec (S e) be); [exact Hn | lia].
      * destruct x as [|d t].
        -- cbn [isref3] in Er. destruct (Nat.ltb_spec (S e) be); [lia | discriminate].
        -- (* the narrowing: one digit fewer *)
           destruct (IHk (repeat 0 (length (d :: t) - 1), 0, S m)) as (n & Hn).
           ++ split; [apply repeat0_bnd3 | exact Hbe].
           ++ cbn [fst length]. rewrite repeat_length. cbn [length] in Hk. lia.
           ++ exists (S n). cbn [riter3]. cbn [rsucc3]. rewrite Et.
              destruct (Nat.ltb_spec (S e) be); [lia | exact Hn].
    + (* inside the length: the value rises by one *)
      destruct (IHv (inc3 x, e, m)) as (n & Hn).
      * split; [apply inc_bnd3; assumption | exact He].
      * cbn [fst]. rewrite inc_len3. exact Hk.
      * cbn [fst snd]. rewrite inc_len3, inc_val3 by assumption. lia.
      * exists (S n). cbn [riter3 rsucc3]. rewrite Et. exact Hn.
Qed.

Lemma refill_reached3 : forall k s, RInv3 s -> length (fst (fst s)) <= k ->
  exists n, isref3 (riter3 s n) = true.
Proof.
  induction k as [k IHk] using lt_wf_ind. intros s Hs Hk.
  apply (refill_step3 (length (fst (fst s)))) with
    (v := be * Nat.pow b (length (fst (fst s)))); [|exact Hs|lia|lia].
  intros s' Hs' Hl. apply (IHk (length (fst (fst s')))); [lia|exact Hs'|lia].
Qed.

Theorem refill_cofinal3 : forall s N, RInv3 s ->
  exists n, N <= n /\ isref3 (riter3 s n) = true /\ RInv3 (riter3 s n).
Proof.
  intros s N Hs.
  pose proof (riter_inv3 N s Hs) as HsN.
  destruct (refill_reached3 (length (fst (fst (riter3 s N)))) (riter3 s N) HsN (le_n _))
    as (n & Hn).
  exists (N + n). rewrite riter_add3.
  split; [lia | split; [exact Hn | apply riter_inv3, HsN]].
Qed.

End Run3.

(** ** 2. The board *)

Section BoardRTr3.

Variable tm0   : TM.
Variable pins  : list Instr.
Local Notation tm := (tm_wrap_trs tm0 pins).

Variable F     : Fam.
Variable EW    : list (list Sym).
Variable T suf : list Sym.
Variable a c   : nat.
Variable AI    : nat -> nat -> nat -> LRule.   (** interior: digit, next word, index *)
Variable N0i sti : nat.
Variable AT    : nat -> nat -> LRule.          (** top carry: top digit, index *)
Variable N0t stt : nat.
Variable AN    : nat -> LRule.                 (** narrowing: index *)
Variable N0n stn : nat.
Variable AR    : nat -> LRule.                 (** refill: index *)
Variable N0r str : nat.
Variable fm1 fm2 : nat -> nat.
Variable rsv   : list LRule.
Variable vsegs : nat -> Instr -> list nseg.
Variable visI  : nat -> Instr -> list lstep.
Variable x0    : list nat.
Variable e0 m0 : nat.

Local Notation b := (fm_b F).
Local Notation be := (length EW).
Local Notation ew := (ew3 EW).

Hypothesis Hb    : 1 < b.
Hypothesis Hbe   : 0 < be.
Hypothesis Hbnd0 : Forall (fun d => d < b) x0.
Hypothesis He0   : e0 < be.

Hypothesis Hsti : 0 < sti.
Hypothesis HAIS : forall d e r, d < b - 1 -> e < b + be -> r < N0i + sti ->
  ReachL tm (negb (fm_left F)) (fm_left F) (lr_lhs (AI d e r)) (lr_rhs (AI d e r)).
Hypothesis HAIL : forall d e r, d < b - 1 -> e < b + be -> r < N0i + sti ->
  lr_lhs (AI d e r) = cls_conf F (blk (fm_pre F ++ rep (dig F (b - 1)) r) (dig F (b - 1))
                                   (astride N0i sti r) (dig F d ++ ilook3 F EW e)).
Hypothesis HAIR : forall d e r, d < b - 1 -> e < b + be -> r < N0i + sti ->
  lr_rhs (AI d e r) = cls_conf F (blk (fm_pre F ++ rep (dig F 0) r) (dig F 0)
                                   (astride N0i sti r) (dig F (S d) ++ ilook3 F EW e)).

Hypothesis Hstt : 0 < stt.
Hypothesis HATS : forall e r, S e < be -> r < N0t + stt ->
  ReachL tm (negb (fm_left F)) (fm_left F) (lr_lhs (AT e r)) (lr_rhs (AT e r)).
Hypothesis HATL : forall e r, S e < be -> r < N0t + stt ->
  lr_lhs (AT e r) = cls_conf F (blk (fm_pre F ++ rep (dig F (b - 1)) r)
                                  (dig F (b - 1)) (astride N0t stt r) (ew e)).
Hypothesis HATR : forall e r, S e < be -> r < N0t + stt ->
  lr_rhs (AT e r) = cls_conf F (blk (fm_pre F ++ rep (dig F 0) r)
                                  (dig F 0) (astride N0t stt r) (ew (S e))).

Hypothesis Hstn : 0 < stn.
Hypothesis HN0n : 0 < N0n.
Hypothesis HANS : forall r, 0 < r -> r < N0n + stn ->
  ReachL tm (negb (fm_left F)) (fm_left F) (lr_lhs (AN r)) (lr_rhs (AN r)).
Hypothesis HANL : forall r, 0 < r -> r < N0n + stn ->
  lr_lhs (AN r) = cls_conf F (blk (fm_pre F ++ rep (dig F (b - 1)) r)
                                (dig F (b - 1)) (astride N0n stn r) (ew (be - 1))).
Hypothesis HANR : forall r, 0 < r -> r < N0n + stn ->
  lr_rhs (AN r) = cls_conf F (blk (fm_pre F ++ rep (dig F 0) (r - 1))
                                (dig F 0) (astride N0n stn r) (ew 0 ++ T)).

Hypothesis Hstr : 0 < str.
Hypothesis HARS : forall r, r < N0r + str ->
  ReachL tm true true (lr_lhs (AR r)) (lr_rhs (AR r)).
Hypothesis HARL : forall r, r < N0r + str ->
  lr_lhs (AR r) = cls_conf F (blk (fm_pre F ++ ew (be - 1) ++ rep T r) T
                                (astride N0r str r) suf).
Hypothesis HARR : forall r, r < N0r + str ->
  lr_rhs (AR r) = cls_conf F (blk (fm_pre F ++ rep (dig F 0) (fm1 r)) (dig F 0)
                                (astride N0r str r)
                                (rep (dig F 0) (fm2 r) ++ ew 0 ++ rep T c ++ suf)).
Hypothesis Hfm : forall r, r < N0r + str -> fm1 r + fm2 r = r + a.

Hypothesis Hrsv : Forall (RuleSound tm false false) rsv.
Hypothesis Hfire : forall r t, ~ In t pins -> r < N0r + str ->
  nfire tm true true rsv (vsegs r t) (visI r t) (lr_lhs (AR r)) = Some t.

Local Notation Cf := (fun n => rcfg3 F EW T suf (riter3 F EW a c (x0, e0, m0) n)).

Lemma rinv03 : RInv3 F EW (x0, e0, m0).
Proof. split; assumption. Qed.

Lemma board_arm3 : forall s, RInv3 F EW s ->
  exists A el er X n,
    ReachL tm el er (lr_lhs A) (lr_rhs A)
    /\ (el = true -> tailL F X = []) /\ (er = true -> tailR F X = [])
    /\ rcfg3 F EW T suf s = cden (tailL F X) (tailR F X) n (lr_lhs A)
    /\ rcfg3 F EW T suf (rsucc3 F EW a c s) = cden (tailL F X) (tailR F X) n (lr_rhs A).
Proof.
  intros [[x e] m] [Hx He].
  assert (HtL : negb (fm_left F) = true -> forall X, tailL F X = []).
  { intros H X. unfold tailL. destruct (fm_left F); [discriminate|reflexivity]. }
  assert (HtR : fm_left F = true -> forall X, tailR F X = []).
  { intros H X. unfold tailR. rewrite H. reflexivity. }
  destruct (digs_decomp (b - 1) x) as [Htop | (n & d & rest & Hxe & Hd)].
  - assert (Et : alltop3 F x = true) by (rewrite Htop; apply alltop_repeat3).
    set (j := length x) in Htop.
    destruct (Nat.ltb_spec (S e) be) as [Hse|Hse].
    + (* the top carry *)
      remember (aoff N0t stt j) as r eqn:Er.
      assert (Hrlt : r < N0t + stt) by (subst r; apply arm_index_lt; assumption).
      assert (Hk : r + astride N0t stt r * acnt N0t stt j = j)
        by (subst r; apply arm_index; assumption).
      exists (AT e r), (negb (fm_left F)), (fm_left F), (rep T m ++ suf), (acnt N0t stt j).
      split; [|split; [|split; [|split]]].
      * exact (HATS e r Hse Hrlt).
      * intros Hz; apply HtL, Hz.
      * intros Hz; apply HtR, Hz.
      * rewrite (HATL e r Hse Hrlt). symmetry. apply rcfg_cls3.
        rewrite Htop, <- Hk at 1. apply rcells_top3.
      * rewrite (HATR e r Hse Hrlt). symmetry. cbn [rsucc3]. rewrite Et.
        destruct (Nat.ltb_spec (S e) be) as [_|]; [|lia].
        apply rcfg_cls3. fold j. rewrite <- Hk at 1. apply rcells_top3.
    + assert (Hee : e = be - 1) by lia.
      destruct x as [|d0 t0] eqn:Ex.
      * (* the refill *)
        remember (aoff N0r str m) as r eqn:Er.
        assert (Hrlt : r < N0r + str) by (subst r; apply arm_index_lt; assumption).
        assert (Hk : r + astride N0r str r * acnt N0r str m = m)
          by (subst r; apply arm_index; assumption).
        exists (AR r), true, true, [], (acnt N0r str m).
        split; [|split; [|split; [|split]]].
        -- exact (HARS r Hrlt).
        -- intros _; apply tailL_nil.
        -- intros _; apply tailR_nil.
        -- rewrite (HARL r Hrlt). symmetry. apply rcfg_cls3.
           rewrite Hee, <- Hk at 1. apply rcells_refill3.
        -- rewrite (HARR r Hrlt). symmetry. cbn [rsucc3 alltop3 forallb].
           destruct (Nat.ltb_spec (S e) be) as [|_]; [lia|].
           apply rcfg_cls3. pose proof (Hfm r Hrlt).
           rewrite <- (rcells_refilled3 F EW T suf c (fm1 r) (astride N0r str r)
                         (acnt N0r str m) (fm2 r)).
           f_equal. f_equal. lia.
      * (* the narrowing *)
        rewrite <- Ex in *.
        assert (Hj : 0 < j) by (unfold j; subst x; cbn; lia).
        remember (aoff N0n stn j) as r eqn:Er.
        assert (Hr0 : 0 < r) by (subst r; apply arm_index_pos; assumption).
        assert (Hrlt : r < N0n + stn) by (subst r; apply arm_index_lt; assumption).
        assert (Hk : r + astride N0n stn r * acnt N0n stn j = j)
          by (subst r; apply arm_index; assumption).
        exists (AN r), (negb (fm_left F)), (fm_left F), (rep T m ++ suf), (acnt N0n stn j).
        split; [|split; [|split; [|split]]].
        -- exact (HANS r Hr0 Hrlt).
        -- intros Hz; apply HtL, Hz.
        -- intros Hz; apply HtR, Hz.
        -- rewrite (HANL r Hr0 Hrlt). symmetry. apply rcfg_cls3.
           rewrite Hee, Htop, <- Hk at 1. apply rcells_top3.
        -- rewrite (HANR r Hr0 Hrlt). symmetry.
           assert (Hs : rsucc3 F EW a c (x, e, m) = (repeat 0 (j - 1), 0, S m)).
           { cbn [rsucc3]. rewrite Et. destruct (Nat.ltb_spec (S e) be) as [|_]; [lia|].
             subst x. reflexivity. }
           rewrite Hs. apply rcfg_cls3.
           replace (j - 1) with ((r - 1) + astride N0n stn r * acnt N0n stn j) by lia.
           apply rcells_nar3.
  - (* the interior *)
    assert (Hne : alltop3 F x = false) by (rewrite Hxe; apply alltop_class3, Hd).
    rewrite Hxe in Hx.
    apply Forall_app in Hx as [_ Hrest'].
    inversion Hrest' as [|? ? Hdb Hrest].
    assert (Hdlt : d < b - 1) by lia.
    assert (Hs : rsucc3 F EW a c (x, e, m) = (repeat 0 n ++ S d :: rest, e, m)).
    { cbn [rsucc3]. rewrite Hne, Hxe, (inc_class3 F n d rest Hdlt). reflexivity. }
    remember (aoff N0i sti n) as r eqn:Er.
    assert (Hrlt : r < N0i + sti) by (subst r; apply arm_index_lt; assumption).
    assert (Hn : r + astride N0i sti r * acnt N0i sti n = n)
      by (subst r; apply arm_index; assumption).
    destruct rest as [|e' rest].
    { (* x ends after the digit: the top word follows *)
      exists (AI d (b + e) r), (negb (fm_left F)), (fm_left F),
             (rep T m ++ suf), (acnt N0i sti n).
      split; [|split; [|split; [|split]]].
      * exact (HAIS d (b + e) r Hdlt ltac:(lia) Hrlt).
      * intros Hz; apply HtL, Hz.
      * intros Hz; apply HtR, Hz.
      * rewrite (HAIL d (b + e) r Hdlt ltac:(lia) Hrlt). symmetry. apply rcfg_cls3.
        rewrite Hxe, <- Hn at 1. apply rcells_intm3.
      * rewrite (HAIR d (b + e) r Hdlt ltac:(lia) Hrlt). symmetry. rewrite Hs.
        apply rcfg_cls3. rewrite <- Hn at 1. apply rcells_intm3. }
    inversion Hrest as [|? ? Heb _].
    exists (AI d e' r), (negb (fm_left F)), (fm_left F),
           (flat_map (dig F) rest ++ ew e ++ rep T m ++ suf), (acnt N0i sti n).
    split; [|split; [|split; [|split]]].
    + exact (HAIS d e' r Hdlt ltac:(lia) Hrlt).
    + intros Hz; apply HtL, Hz.
    + intros Hz; apply HtR, Hz.
    + rewrite (HAIL d e' r Hdlt ltac:(lia) Hrlt). symmetry. apply rcfg_cls3.
      rewrite Hxe, <- Hn at 1. apply rcells_intl3; assumption.
    + rewrite (HAIR d e' r Hdlt ltac:(lia) Hrlt). symmetry. rewrite Hs.
      apply rcfg_cls3. rewrite <- Hn at 1. apply rcells_intl3; assumption.
Qed.

Lemma lapR3 : forall n, exists m c',
  0 < m /\ csteps tm m (Cf n) = Some c' /\ lift c' = lift (Cf (S n)).
Proof.
  intros n.
  pose proof (riter_inv3 F EW a c Hb Hbe n (x0, e0, m0) rinv03) as Hi.
  destruct (board_arm3 _ Hi) as (A & el & er & X & k & HA & HL & HR & Hl & Hr).
  destruct (HA _ _ k HL HR) as (m & c' & Hm & Hc' & Hlc).
  exists m, c'. split; [exact Hm|]. split.
  - cbn beta. rewrite Hl. exact Hc'.
  - rewrite Hlc, <- Hr. cbn beta.
    replace (S n) with (n + 1) by lia. rewrite riter_add3. reflexivity.
Qed.

Lemma fireR3 : forall t N, ~ In t pins ->
  exists n k c', N <= n /\ csteps tm k (Cf n) = Some c' /\ cinstr c' = t.
Proof.
  intros t N Hnp.
  destruct (refill_cofinal3 F EW a c Hb Hbe (x0, e0, m0) N rinv03) as (n & HN & Hx & Hi).
  exists n.
  destruct (riter3 F EW a c (x0, e0, m0) n) as [[x e] m] eqn:Eit.
  destruct Hi as [_ He]. destruct x as [|? ?]; [|discriminate].
  cbn [isref3] in Hx. destruct (Nat.ltb_spec (S e) be) as [|Hse]; [discriminate|].
  assert (Hee : e = be - 1) by lia. subst e.
  remember (aoff N0r str m) as r eqn:Er.
  assert (Hrlt : r < N0r + str) by (subst r; apply arm_index_lt; assumption).
  assert (Hk : r + astride N0r str r * acnt N0r str m = m)
    by (subst r; apply arm_index; assumption).
  assert (Hden : rcfg3 F EW T suf ([], be - 1, m)
                 = cden [] [] (acnt N0r str m) (lr_lhs (AR r))).
  { rewrite (HARL r Hrlt).
    rewrite <- (rcfg_cls3 F EW T suf
                  (blk (fm_pre F ++ ew (be - 1) ++ rep T r) T (astride N0r str r) suf)
                  [] (acnt N0r str m) [] (be - 1) m).
    - unfold tailL, tailR; destruct (fm_left F); reflexivity.
    - rewrite <- Hk at 1. apply rcells_refill3. }
  destruct (nfire_sound tm true true rsv (vsegs r t) (visI r t)
              (lr_lhs (AR r)) t Hrsv (Hfire r t Hnp Hrlt)
              [] [] (acnt N0r str m)
              (fun _ => eq_refl) (fun _ => eq_refl)) as (k & c' & Hc' & Ht).
  exists k, c'. cbn beta. rewrite ?Eit, Hden.
  split; [exact HN | split; [exact Hc' | exact Ht]].
Qed.

Theorem boardR_neverqhtr3 : forall t0,
  stepn tm t0 InitES = Some (lift (rcfg3 F EW T suf (x0, e0, m0))) ->
  NeverQuasiHaltsTr tm0.
Proof.
  intros t0 Hboot.
  apply (glue_neverqhtrN tm0 pins Cf).
  - exists t0. exact Hboot.
  - intros n. destruct (lapR3 n) as (m & c' & Hm & Hrun & Hl).
    exists m, c'. split; [exact Hrun | split; [exact Hl | exact Hm]].
  - intros t Hnp N. exact (fireR3 t N Hnp).
Qed.

Lemma reachR3 : forall d n,
  exists Tm, stepn tm Tm (lift (Cf n)) = Some (lift (Cf (n + d))).
Proof.
  induction d; intros n.
  - exists 0. rewrite Nat.add_0_r. reflexivity.
  - destruct (IHd n) as (Tm & HT).
    destruct (lapR3 (n + d)) as (m & c' & _ & Hm & Hl).
    exists (Tm + m). rewrite stepn_add, HT.
    replace (n + S d) with (S (n + d)) by lia.
    rewrite <- Hl. apply csteps_lift. exact Hm.
Qed.

Lemma fire_everyR3 : forall t, ~ In t pins -> forall n,
  exists k c', csteps tm k (Cf n) = Some c' /\ cinstr c' = t.
Proof.
  intros t Hnp n.
  destruct (fireR3 t n Hnp) as (m & k & c' & Hm & Hk & Hc').
  destruct (reachR3 (m - n) n) as (Tm & HT).
  replace (n + (m - n)) with m in HT by lia.
  assert (Hs : stepn tm (Tm + k) (lift (Cf n)) = Some (lift c')).
  { rewrite stepn_add, HT. apply csteps_lift. exact Hk. }
  destruct (stepn_csteps_at tm (Tm + k) (Cf n) (lift c') Hs) as (c'' & Hc'' & Hl').
  exists (Tm + k), c''. split; [exact Hc''|].
  rewrite <- cinstr_lift, Hl', cinstr_lift. exact Hc'.
Qed.

Theorem boardR_qhtr3 : forall t0 B,
  stepn tm0 t0 InitES = Some (lift (rcfg3 F EW T suf (x0, e0, m0))) ->
  existsb (fun tg => cfires tm0 CTape.c0 t0 tg) pins = true ->
  (t0 <=? B) = true ->
  NonHalt tm0 /\ QHBoundTr B tm0 /\ QuasiHaltsTr tm0.
Proof.
  intros t0 B Hboot Hwit Hle.
  apply (lap_qh_stage tm0 pins (fun p => Cf (Nat.pred (Pos.to_nat p)))
           1%positive t0 B).
  - exact Hboot.
  - intros p _.
    destruct (lapR3 (Nat.pred (Pos.to_nat p))) as (m & c' & Hm & Hrun & Hl).
    exists m, c'. split; [exact Hrun | split; [|exact Hm]].
    rewrite Hl, Pos2Nat.inj_succ.
    replace (S (Nat.pred (Pos.to_nat p))) with (Pos.to_nat p)
      by (pose proof (Pos2Nat.is_pos p); lia).
    reflexivity.
  - intros t Hnp p _. exact (fire_everyR3 t Hnp (Nat.pred (Pos.to_nat p))).
  - exact Hwit.
  - exact Hle.
Qed.

End BoardRTr3.
