(** * Checkers.LadderCheckPhRunTr: counters with a PHASE and a run
    (SCOPING_INSTR 7.4.LE5).

    [LadderCheckRunTr], [LadderCheckRun2Tr] and [LadderCheckRun3Tr] each
    state one shape of [x ++ (words) ++ T^m]: a binary [x] whose top narrows
    it and lengthens the run [T^m], and an empty [x] that refills from the
    run.  LE5's rows ([0RB1LA_1LC1RD_1RB0LD_1RB0LA]: [A0 x 00 (10)^m 11],
    then [x 11], [x 1], [x 00 (10)^m 1], [x 1 001], ...) go through SEVERAL
    such shapes in turn.  This file states them all at once: a finite set of
    phases [p < NP], each with a word [W p] between [x] and the run and a
    word [V p] after it,

      cells (x, p, m) = pre ++ x ++ W p ++ T^m ++ V p,

    and two moves per phase, taken when [x] is all top: one for a nonempty
    [x] ([mvT]) and one for an empty [x] ([mvE]):

    - [TCarry q dw dm]:  (top^j, p, m) -> (0^(j+dw), q, m + dm)    j >= 1;
    - [TNarrow q dm]:    (top^j, p, m) -> (0^(j-1), q, m + dm)     j >= 1;
    - [TNone]:           the phase never holds a nonempty [x] ([xe p]);
    - [ECarry q dw dm]:  ([], p, m)    -> (0^dw, q, m + dm);
    - [ERefill a q c]:   ([], p, m)    -> (0^(m+a), q, c)          (a refill).

    A phase may be RUNLESS ([nr p = true]): its run is always empty (every
    move into it sets [m = 0]), so its moves may rewrite [V] (their arms
    have both tails known empty); a phase with a run keeps [V] ([V q = V p]
    on its moves) and its arms leave the run opaque.  [Run3] is two phases
    ([e = 0]: carry, [e = 1]: narrow and refill); [Run2] one.

    Liveness: a linear rank [A |x| + B m + g p] falls at every move but a
    refill, and inside a phase [x] counts up, so refills recur; every
    instruction fires from every refill arm.

    Arms, all [LadderNest.ReachL] programs: interior
    [t^n d w X -> 0^n (d+1) w X] ([w] the next digit, or [W p] when [x]
    ends), per phase the carry or narrowing of a nonempty [x] (one index),
    the carry of an empty [x] (no index) or its refill (one index, the run).

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


Inductive TMove : Type :=
| TCarry  (q dw dm : nat)
| TNarrow (q dm : nat)
| TNone.

Inductive EMove : Type :=
| ECarry  (q dw dm : nat)
| ERefill (a q c : nat).

(** ** 1. The counter *)

Section PhRun.

Variable F : Fam.
Variable W V : nat -> list Sym.
Variable T : list Sym.
Variable mvT : nat -> TMove.
Variable mvE : nat -> EMove.

Local Notation b := (fm_b F).

Fixpoint incP (x : list nat) : list nat :=
  match x with
  | [] => []
  | d :: t => if d =? b - 1 then 0 :: incP t else S d :: t
  end.

Definition alltopP (x : list nat) : bool := forallb (Nat.eqb (b - 1)) x.

Definition PSt : Type := (list nat * nat * nat)%type.

Definition psucc (s : PSt) : PSt :=
  let '(x, p, m) := s in
  if alltopP x then
    match x with
    | [] =>
        match mvE p with
        | ECarry q dw dm => (repeat 0 dw, q, m + dm)
        | ERefill a q c => (repeat 0 (m + a), q, c)
        end
    | _ :: _ =>
        match mvT p with
        | TCarry q dw dm => (repeat 0 (length x + dw), q, m + dm)
        | TNarrow q dm => (repeat 0 (length x - 1), q, m + dm)
        | TNone => s
        end
    end
  else (incP x, p, m).

Fixpoint piter (s : PSt) (n : nat) : PSt :=
  match n with
  | O => s
  | S n' => piter (psucc s) n'
  end.

Lemma piter_add : forall n1 n2 s, piter s (n1 + n2) = piter (piter s n1) n2.
Proof. induction n1 as [|n1 IH]; intros n2 s; [reflexivity | apply IH]. Qed.

Definition pcells (x : list nat) (p m : nat) : list Sym :=
  fm_pre F ++ flat_map (dig F) x ++ W p ++ rep T m ++ V p.

Definition pcfg (s : PSt) : cconf :=
  let '(x, p, m) := s in
  if fm_left F
  then (fm_st F, (pcells x p m, fm_hs F, fm_other F))
  else (fm_st F, (fm_other F, fm_hs F, pcells x p m)).

Lemma pcfg_cls : forall sd X n x p m,
  pcells x p m = sden X n sd ->
  cden (tailL F X) (tailR F X) n (cls_conf F sd) = pcfg (x, p, m).
Proof.
  intros sd X n x p m H.
  unfold cden, cls_conf, pcfg, tailL, tailR.
  destruct (fm_left F); simpl; rewrite sden_flat, app_nil_r, <- H; reflexivity.
Qed.

(** *** The odometer carry *)

Lemma inc_classP : forall n d rest, d < b - 1 ->
  incP (repeat (b - 1) n ++ d :: rest) = repeat 0 n ++ S d :: rest.
Proof.
  induction n as [|n IH]; intros d rest Hd; cbn [repeat app incP].
  - destruct (Nat.eqb_spec d (b - 1)); [lia | reflexivity].
  - rewrite Nat.eqb_refl, IH by exact Hd. reflexivity.
Qed.

Lemma alltop_repeatP : forall n, alltopP (repeat (b - 1) n) = true.
Proof.
  induction n as [|n IH]; [reflexivity|]. cbn [repeat alltopP forallb].
  rewrite Nat.eqb_refl. exact IH.
Qed.

Lemma alltop_classP : forall n d rest, d <> b - 1 ->
  alltopP (repeat (b - 1) n ++ d :: rest) = false.
Proof.
  induction n as [|n IH]; intros d rest Hd; cbn [repeat app alltopP forallb].
  - destruct (Nat.eqb_spec (b - 1) d); [lia | reflexivity].
  - rewrite Nat.eqb_refl. apply IH. exact Hd.
Qed.

Lemma inc_lenP : forall x, length (incP x) = length x.
Proof.
  induction x as [|d t IH]; [reflexivity|]. cbn [incP].
  destruct (d =? b - 1); cbn [length]; [rewrite IH|]; reflexivity.
Qed.

(** *** The cells of each class *)

(** the word after the digit an interior arm increments: the next digit
    [e < b], or the phase word [W (e - b)] when [x] ends there *)
Definition ilookP (e : nat) : list Sym := if e <? b then dig F e else W (e - b).

Lemma pcells_intl : forall t r st n d e rest p m, e < b ->
  pcells (repeat t (r + st * n) ++ d :: e :: rest) p m
    = sden (flat_map (dig F) rest ++ W p ++ rep T m ++ V p) n
        (blk (fm_pre F ++ rep (dig F t) r) (dig F t) st (dig F d ++ ilookP e)).
Proof.
  intros t r st n d e rest p m He. unfold pcells, ilookP.
  destruct (Nat.ltb_spec e b) as [_|]; [|lia].
  rewrite blk_den, flat_map_app, flat_map_repeat_nil.
  cbn [flat_map app]. rewrite rep_add, !app_assoc. reflexivity.
Qed.

Lemma pcells_intm : forall t r st n d p m,
  pcells (repeat t (r + st * n) ++ [d]) p m
    = sden (rep T m ++ V p) n
        (blk (fm_pre F ++ rep (dig F t) r) (dig F t) st (dig F d ++ ilookP (b + p))).
Proof.
  intros t r st n d p m. unfold pcells, ilookP.
  destruct (Nat.ltb_spec (b + p) b) as [|_]; [lia|].
  replace (b + p - b) with p by lia.
  rewrite blk_den, flat_map_app, flat_map_repeat_nil.
  cbn [flat_map app]. rewrite app_nil_r, rep_add, !app_assoc. reflexivity.
Qed.

(** a phase's arms: the word after [x] and the tail beyond it, by whether
    the phase has a run *)
Variable nr : nat -> bool.

Definition lwP (p : nat) : list Sym := if nr p then W p ++ V p else W p.
Definition rwP (p q dm : nat) : list Sym :=
  if nr p then W q ++ rep T dm ++ V q else W q ++ rep T dm.
Definition txP (p m : nat) : list Sym := if nr p then [] else rep T m ++ V p.

Lemma pcells_top : forall t r st n p m, (nr p = true -> m = 0) ->
  pcells (repeat t (r + st * n)) p m
    = sden (txP p m) n (blk (fm_pre F ++ rep (dig F t) r) (dig F t) st (lwP p)).
Proof.
  intros t r st n p m Hm. unfold pcells, txP, lwP.
  rewrite blk_den, flat_map_repeat_nil, rep_add.
  destruct (nr p); [rewrite (Hm eq_refl)|]; cbn [rep];
    rewrite ?app_nil_l, !app_assoc, ?app_nil_r; reflexivity.
Qed.

Lemma pcells_moved : forall r st n p q m dm, (nr p = true -> m = 0) ->
  (nr p = false -> V q = V p) ->
  pcells (repeat 0 (r + st * n)) q (m + dm)
    = sden (txP p m) n (blk (fm_pre F ++ rep (dig F 0) r) (dig F 0) st (rwP p q dm)).
Proof.
  intros r st n p q m dm Hm HV. unfold pcells, txP, rwP.
  rewrite blk_den, flat_map_repeat_nil, rep_add.
  destruct (nr p).
  - rewrite (Hm eq_refl). cbn [Nat.add rep].
    rewrite ?app_nil_l, !app_assoc, ?app_nil_r. reflexivity.
  - rewrite (HV eq_refl), Nat.add_comm, rep_add, !app_assoc. reflexivity.
Qed.

Lemma pcells_empty : forall p m n, (nr p = true -> m = 0) ->
  pcells [] p m = sden (txP p m) n (sflat (fm_pre F ++ lwP p)).
Proof.
  intros p m n Hm. rewrite sden_flat. unfold pcells, txP, lwP. cbn [flat_map].
  destruct (nr p); [rewrite (Hm eq_refl)|]; cbn [rep];
    rewrite ?app_nil_l, !app_assoc, ?app_nil_r; reflexivity.
Qed.

Lemma pcells_emoved : forall p q m dw dm n, (nr p = true -> m = 0) ->
  (nr p = false -> V q = V p) ->
  pcells (repeat 0 dw) q (m + dm)
    = sden (txP p m) n (sflat (fm_pre F ++ rep (dig F 0) dw ++ rwP p q dm)).
Proof.
  intros p q m dw dm n Hm HV. rewrite sden_flat. unfold pcells, txP, rwP.
  rewrite flat_map_repeat_nil.
  destruct (nr p).
  - rewrite (Hm eq_refl). cbn [Nat.add rep].
    rewrite ?app_nil_l, !app_assoc, ?app_nil_r. reflexivity.
  - rewrite (HV eq_refl), Nat.add_comm, rep_add, !app_assoc. reflexivity.
Qed.

Lemma pcells_refill : forall p r st n,
  pcells [] p (r + st * n)
    = sden [] n (blk (fm_pre F ++ W p ++ rep T r) T st (V p)).
Proof.
  intros p r st n. unfold pcells.
  rewrite blk_den, rep_add. cbn [flat_map].
  rewrite ?app_nil_r, !app_assoc, ?app_nil_r. reflexivity.
Qed.

Lemma pcells_refilled : forall f1 st n f2 q c,
  pcells (repeat 0 (f1 + st * n + f2)) q c
    = sden [] n (blk (fm_pre F ++ rep (dig F 0) f1) (dig F 0) st
                   (rep (dig F 0) f2 ++ W q ++ rep T c ++ V q)).
Proof.
  intros f1 st n f2 q c. unfold pcells.
  rewrite blk_den, flat_map_repeat_nil, !rep_add, !app_nil_r, !app_assoc.
  reflexivity.
Qed.

(** *** Refills recur *)

Hypothesis Hb : 1 < b.

Lemma inc_valP : forall x, Forall (fun d => d < b) x -> alltopP x = false ->
  val_pos b (incP x) = S (val_pos b x).
Proof.
  induction x as [|d t IH]; intros Hx Ht; [discriminate|].
  inversion Hx as [|? ? Hd Htl]; subst.
  cbn [incP alltopP forallb] in *.
  destruct (Nat.eqb_spec d (b - 1)) as [E|E].
  - subst d. rewrite Nat.eqb_refl in Ht. cbn [andb] in Ht.
    cbn [val_pos]. rewrite (IH Htl Ht). nia.
  - cbn [val_pos]. lia.
Qed.

Lemma inc_bndP : forall x, Forall (fun d => d < b) x -> alltopP x = false ->
  Forall (fun d => d < b) (incP x).
Proof.
  induction x as [|d t IH]; intros Hx Ht; [constructor|].
  inversion Hx as [|? ? Hd Htl]; subst.
  cbn [incP alltopP forallb] in *.
  destruct (Nat.eqb_spec d (b - 1)) as [E|E].
  - subst d. rewrite Nat.eqb_refl in Ht. constructor; [lia | apply IH; assumption].
  - constructor; [lia | exact Htl].
Qed.

Lemma repeat0_bndP : forall n, Forall (fun d => d < b) (repeat 0 n).
Proof.
  intros n. apply Forall_forall. intros y Hy. apply repeat_spec in Hy. lia.
Qed.

Variable xe : nat -> bool.
Variable NP : nat.
Variable A B : nat.
Variable g : nat -> nat.

(** the table: moves stay inside the phases, a runless phase is entered
    with an empty run, an empty-only phase with an empty [x], and the rank
    falls at every move but a refill *)
Hypothesis HtC : forall p q dw dm, p < NP -> mvT p = TCarry q dw dm ->
  q < NP /\ (nr q = true -> nr p = true /\ dm = 0) /\ xe q = false
  /\ A * dw + B * dm + g q < g p.
Hypothesis HtN : forall p q dm, p < NP -> mvT p = TNarrow q dm ->
  q < NP /\ (nr q = true -> nr p = true /\ dm = 0) /\ xe q = false
  /\ B * dm + g q < A + g p.
Hypothesis HtX : forall p, p < NP -> mvT p = TNone -> xe p = true.
Hypothesis HeC : forall p q dw dm, p < NP -> mvE p = ECarry q dw dm ->
  q < NP /\ (nr q = true -> nr p = true /\ dm = 0) /\ (xe q = true -> dw = 0)
  /\ A * dw + B * dm + g q < g p.
Hypothesis HeR : forall p a q c, p < NP -> mvE p = ERefill a q c ->
  q < NP /\ (nr q = true -> c = 0) /\ xe q = false.

Definition PInv (s : PSt) : Prop :=
  let '(x, p, m) := s in
  Forall (fun d => d < b) x /\ p < NP /\ (nr p = true -> m = 0) /\ (xe p = true -> x = []).

Definition isrefP (s : PSt) : bool :=
  let '(x, p, m) := s in
  match x, mvE p with [], ERefill _ _ _ => true | _, _ => false end.

Lemma psucc_inv : forall s, PInv s -> PInv (psucc s).
Proof.
  intros [[x p] m] (Hx & Hp & Hm & Hxe). cbn [psucc].
  destruct (alltopP x) eqn:Et.
  - destruct x as [|d t].
    + destruct (mvE p) as [q dw dm | a q c] eqn:Emv.
      * destruct (HeC p q dw dm Hp Emv) as (Hq & Hnr & Hxq & _).
        split; [apply repeat0_bndP | split; [exact Hq | split]].
        -- intros Hq'. destruct (Hnr Hq') as (Hp' & ->). rewrite (Hm Hp'). reflexivity.
        -- intros Hq'. rewrite (Hxq Hq'). reflexivity.
      * destruct (HeR p a q c Hp Emv) as (Hq & Hnr & Hxq).
        split; [apply repeat0_bndP | split; [exact Hq | split; [exact Hnr|]]].
        intros Hq'. congruence.
    + destruct (mvT p) as [q dw dm | q dm |] eqn:Emv.
      * destruct (HtC p q dw dm Hp Emv) as (Hq & Hnr & Hxq & _).
        split; [apply repeat0_bndP | split; [exact Hq | split]].
        -- intros Hq'. destruct (Hnr Hq') as (Hp' & ->). rewrite (Hm Hp'). reflexivity.
        -- intros Hq'. congruence.
      * destruct (HtN p q dm Hp Emv) as (Hq & Hnr & Hxq & _).
        split; [apply repeat0_bndP | split; [exact Hq | split]].
        -- intros Hq'. destruct (Hnr Hq') as (Hp' & ->). rewrite (Hm Hp'). reflexivity.
        -- intros Hq'. congruence.
      * split; [exact Hx | split; [exact Hp | split; assumption]].
  - split; [apply inc_bndP; assumption | split; [exact Hp | split; [exact Hm|]]].
    intros Hp'. rewrite (Hxe Hp') in Et. discriminate.
Qed.

Lemma piter_inv : forall n s, PInv s -> PInv (piter s n).
Proof.
  induction n as [|n IH]; intros s Hs; [exact Hs|]. apply IH, psucc_inv, Hs.
Qed.

Definition rankP (s : PSt) : nat :=
  let '(x, p, m) := s in A * length x + B * m + g p.

Lemma refill_stepP : forall k,
  (forall s, PInv s -> rankP s < k -> exists n, isrefP (piter s n) = true) ->
  forall v s, PInv s -> rankP s <= k ->
  Nat.pow b (length (fst (fst s))) <= v + val_pos b (fst (fst s)) ->
  exists n, isrefP (piter s n) = true.
Proof.
  intros k IHk v. induction v as [|v IHv]; intros [[x p] m] Hs Hk Hv;
    cbn [fst snd] in *; pose proof Hs as (Hx & Hp & Hm & Hxe);
    pose proof (val_pos_lt b x Hb Hx) as Hlt.
  - exfalso. lia.
  - destruct (isrefP (x, p, m)) eqn:Er; [exists 0; exact Er|].
    destruct (alltopP x) eqn:Et.
    + destruct x as [|d t].
      * destruct (mvE p) as [q dw dm | a q c] eqn:Emv.
        -- (* the carry of an empty x: the rank falls *)
           destruct (HeC p q dw dm Hp Emv) as (_ & _ & _ & Hr).
           destruct (IHk (repeat 0 dw, q, m + dm)) as (n & Hn).
           ++ apply (psucc_inv ([], p, m)) in Hs. cbn [psucc alltopP forallb] in Hs.
              rewrite Emv in Hs. exact Hs.
           ++ cbn [rankP length] in *. rewrite repeat_length. nia.
           ++ exists (S n). cbn [piter psucc alltopP forallb]. rewrite Emv. exact Hn.
        -- cbn [isrefP] in Er. rewrite Emv in Er. discriminate.
      * destruct (mvT p) as [q dw dm | q dm |] eqn:Emv.
        -- (* the carry: the rank falls *)
           destruct (HtC p q dw dm Hp Emv) as (_ & _ & _ & Hr).
           destruct (IHk (repeat 0 (length (d :: t) + dw), q, m + dm)) as (n & Hn).
           ++ apply (psucc_inv (d :: t, p, m)) in Hs. cbn [psucc] in Hs.
              rewrite Et, Emv in Hs. exact Hs.
           ++ cbn [rankP length] in *. rewrite repeat_length. nia.
           ++ exists (S n). cbn [piter]. cbn [psucc]. rewrite Et, Emv. exact Hn.
        -- (* the narrowing: the rank falls *)
           destruct (HtN p q dm Hp Emv) as (_ & _ & _ & Hr).
           destruct (IHk (repeat 0 (length (d :: t) - 1), q, m + dm)) as (n & Hn).
           ++ apply (psucc_inv (d :: t, p, m)) in Hs. cbn [psucc] in Hs.
              rewrite Et, Emv in Hs. exact Hs.
           ++ cbn [rankP length] in *. rewrite repeat_length. nia.
           ++ exists (S n). cbn [piter]. cbn [psucc]. rewrite Et, Emv. exact Hn.
        -- exfalso. pose proof (Hxe (HtX p Hp Emv)). discriminate.
    + (* inside the phase: the value rises by one *)
      destruct (IHv (incP x, p, m)) as (n & Hn).
      * split; [apply inc_bndP; assumption | split; [exact Hp | split; [exact Hm|]]].
        intros Hp'. rewrite (Hxe Hp') in Et. discriminate.
      * cbn [rankP] in *. rewrite inc_lenP. exact Hk.
      * cbn [fst]. rewrite inc_lenP, inc_valP by assumption. lia.
      * exists (S n). cbn [piter psucc]. rewrite Et. exact Hn.
Qed.

Lemma refill_reachedP : forall k s, PInv s -> rankP s <= k ->
  exists n, isrefP (piter s n) = true.
Proof.
  induction k as [k IHk] using lt_wf_ind. intros s Hs Hk.
  apply (refill_stepP k) with (v := Nat.pow b (length (fst (fst s)))); [|exact Hs|exact Hk|lia].
  intros s' Hs' Hl. apply (IHk (rankP s')); [lia|exact Hs'|lia].
Qed.

Theorem refill_cofinalP : forall s N, PInv s ->
  exists n, N <= n /\ isrefP (piter s n) = true /\ PInv (piter s n).
Proof.
  intros s N Hs.
  pose proof (piter_inv N s Hs) as HsN.
  destruct (refill_reachedP (rankP (piter s N)) (piter s N) HsN (le_n _)) as (n & Hn).
  exists (N + n). rewrite piter_add.
  split; [lia | split; [exact Hn | apply piter_inv, HsN]].
Qed.

End PhRun.

(** ** 2. The board *)

Section BoardPTr.

Variable tm0   : TM.
Variable pins  : list Instr.
Local Notation tm := (tm_wrap_trs tm0 pins).

Variable F     : Fam.
Variable NP    : nat.
Variable W V   : nat -> list Sym.
Variable T     : list Sym.
Variable mvT   : nat -> TMove.
Variable mvE   : nat -> EMove.
Variable nr xe : nat -> bool.
Variable A B   : nat.
Variable g     : nat -> nat.
Variable AI    : nat -> nat -> nat -> LRule.   (** interior: digit, next word, index *)
Variable N0i sti : nat.
Variable AC    : nat -> nat -> LRule.          (** carry of a nonempty x: phase, index *)
Variable N0c stc : nat.
Variable AN    : nat -> nat -> LRule.          (** narrowing: phase, index *)
Variable N0n stn : nat.
Variable AE    : nat -> LRule.                 (** carry of an empty x: phase *)
Variable AR    : nat -> nat -> LRule.          (** refill: phase, index *)
Variable N0r str : nat.
Variable fm1 fm2 : nat -> nat -> nat.
Variable rsv   : list LRule.
Variable vsegs : nat -> nat -> Instr -> list nseg.
Variable visI  : nat -> nat -> Instr -> list lstep.
Variable x0    : list nat.
Variable p0 m0 : nat.

Local Notation b := (fm_b F).
Local Notation elP p := (if nr p then true else negb (fm_left F)).
Local Notation erP p := (if nr p then true else fm_left F).

Hypothesis Hb  : 1 < b.
Hypothesis HtC : forall p q dw dm, p < NP -> mvT p = TCarry q dw dm ->
  q < NP /\ (nr q = true -> nr p = true /\ dm = 0) /\ xe q = false
  /\ A * dw + B * dm + g q < g p.
Hypothesis HtN : forall p q dm, p < NP -> mvT p = TNarrow q dm ->
  q < NP /\ (nr q = true -> nr p = true /\ dm = 0) /\ xe q = false
  /\ B * dm + g q < A + g p.
Hypothesis HtX : forall p, p < NP -> mvT p = TNone -> xe p = true.
Hypothesis HeC : forall p q dw dm, p < NP -> mvE p = ECarry q dw dm ->
  q < NP /\ (nr q = true -> nr p = true /\ dm = 0) /\ (xe q = true -> dw = 0)
  /\ A * dw + B * dm + g q < g p.
Hypothesis HeR : forall p a q c, p < NP -> mvE p = ERefill a q c ->
  q < NP /\ (nr q = true -> c = 0) /\ xe q = false.
(** a phase with a run keeps the word after it *)
Hypothesis HVtc : forall p q dw dm, p < NP -> mvT p = TCarry q dw dm ->
  nr p = false -> V q = V p.
Hypothesis HVtn : forall p q dm, p < NP -> mvT p = TNarrow q dm -> nr p = false -> V q = V p.
Hypothesis HVec : forall p q dw dm, p < NP -> mvE p = ECarry q dw dm ->
  nr p = false -> V q = V p.
Hypothesis Hbnd0 : Forall (fun d => d < b) x0.
Hypothesis Hp0   : p0 < NP.
Hypothesis Hm0   : nr p0 = true -> m0 = 0.
Hypothesis Hx0   : xe p0 = true -> x0 = [].

Hypothesis Hsti : 0 < sti.
Hypothesis HAIS : forall d e r, d < b - 1 -> e < b + NP ->
  (b <= e -> xe (e - b) = false) -> r < N0i + sti ->
  ReachL tm (negb (fm_left F)) (fm_left F) (lr_lhs (AI d e r)) (lr_rhs (AI d e r)).
Hypothesis HAIL : forall d e r, d < b - 1 -> e < b + NP ->
  (b <= e -> xe (e - b) = false) -> r < N0i + sti ->
  lr_lhs (AI d e r) = cls_conf F (blk (fm_pre F ++ rep (dig F (b - 1)) r) (dig F (b - 1))
                                   (astride N0i sti r) (dig F d ++ ilookP F W e)).
Hypothesis HAIR : forall d e r, d < b - 1 -> e < b + NP ->
  (b <= e -> xe (e - b) = false) -> r < N0i + sti ->
  lr_rhs (AI d e r) = cls_conf F (blk (fm_pre F ++ rep (dig F 0) r) (dig F 0)
                                   (astride N0i sti r) (dig F (S d) ++ ilookP F W e)).

Hypothesis Hstc : 0 < stc.
Hypothesis HACS : forall p q dw dm r, p < NP -> mvT p = TCarry q dw dm -> r < N0c + stc ->
  ReachL tm (elP p) (erP p) (lr_lhs (AC p r)) (lr_rhs (AC p r)).
Hypothesis HACL : forall p q dw dm r, p < NP -> mvT p = TCarry q dw dm -> r < N0c + stc ->
  lr_lhs (AC p r) = cls_conf F (blk (fm_pre F ++ rep (dig F (b - 1)) r)
                                  (dig F (b - 1)) (astride N0c stc r) (lwP W V nr p)).
Hypothesis HACR : forall p q dw dm r, p < NP -> mvT p = TCarry q dw dm -> r < N0c + stc ->
  lr_rhs (AC p r) = cls_conf F (blk (fm_pre F ++ rep (dig F 0) (r + dw))
                                  (dig F 0) (astride N0c stc r) (rwP W V T nr p q dm)).

Hypothesis Hstn : 0 < stn.
Hypothesis HN0n : 0 < N0n.
Hypothesis HANS : forall p q dm r, p < NP -> mvT p = TNarrow q dm ->
  0 < r -> r < N0n + stn ->
  ReachL tm (elP p) (erP p) (lr_lhs (AN p r)) (lr_rhs (AN p r)).
Hypothesis HANL : forall p q dm r, p < NP -> mvT p = TNarrow q dm ->
  0 < r -> r < N0n + stn ->
  lr_lhs (AN p r) = cls_conf F (blk (fm_pre F ++ rep (dig F (b - 1)) r)
                                  (dig F (b - 1)) (astride N0n stn r) (lwP W V nr p)).
Hypothesis HANR : forall p q dm r, p < NP -> mvT p = TNarrow q dm ->
  0 < r -> r < N0n + stn ->
  lr_rhs (AN p r) = cls_conf F (blk (fm_pre F ++ rep (dig F 0) (r - 1))
                                  (dig F 0) (astride N0n stn r) (rwP W V T nr p q dm)).

Hypothesis HAES : forall p q dw dm, p < NP -> mvE p = ECarry q dw dm ->
  ReachL tm (elP p) (erP p) (lr_lhs (AE p)) (lr_rhs (AE p)).
Hypothesis HAEL : forall p q dw dm, p < NP -> mvE p = ECarry q dw dm ->
  lr_lhs (AE p) = cls_conf F (sflat (fm_pre F ++ lwP W V nr p)).
Hypothesis HAER : forall p q dw dm, p < NP -> mvE p = ECarry q dw dm ->
  lr_rhs (AE p) = cls_conf F (sflat (fm_pre F ++ rep (dig F 0) dw ++ rwP W V T nr p q dm)).

Hypothesis Hstr : 0 < str.
Hypothesis HARS : forall p a q c r, p < NP -> mvE p = ERefill a q c -> r < N0r + str ->
  ReachL tm true true (lr_lhs (AR p r)) (lr_rhs (AR p r)).
Hypothesis HARL : forall p a q c r, p < NP -> mvE p = ERefill a q c -> r < N0r + str ->
  lr_lhs (AR p r) = cls_conf F (blk (fm_pre F ++ W p ++ rep T r) T
                                  (astride N0r str r) (V p)).
Hypothesis HARR : forall p a q c r, p < NP -> mvE p = ERefill a q c -> r < N0r + str ->
  lr_rhs (AR p r) = cls_conf F (blk (fm_pre F ++ rep (dig F 0) (fm1 p r)) (dig F 0)
                                  (astride N0r str r)
                                  (rep (dig F 0) (fm2 p r) ++ W q ++ rep T c ++ V q)).
Hypothesis Hfm : forall p a q c r, p < NP -> mvE p = ERefill a q c -> r < N0r + str ->
  fm1 p r + fm2 p r = r + a.

Hypothesis Hrsv : Forall (RuleSound tm false false) rsv.
Hypothesis Hfire : forall p a q c r t, p < NP -> mvE p = ERefill a q c ->
  ~ In t pins -> r < N0r + str ->
  nfire tm true true rsv (vsegs p r t) (visI p r t) (lr_lhs (AR p r)) = Some t.

Local Notation Cf := (fun n => pcfg F W V T (piter F mvT mvE (x0, p0, m0) n)).

Lemma pinv0 : PInv F nr xe NP (x0, p0, m0).
Proof. split; [exact Hbnd0 | split; [exact Hp0 | split; [exact Hm0 | exact Hx0]]]. Qed.

Lemma board_armP : forall s, PInv F nr xe NP s ->
  exists Ar el er X n,
    ReachL tm el er (lr_lhs Ar) (lr_rhs Ar)
    /\ (el = true -> tailL F X = []) /\ (er = true -> tailR F X = [])
    /\ pcfg F W V T s = cden (tailL F X) (tailR F X) n (lr_lhs Ar)
    /\ pcfg F W V T (psucc F mvT mvE s) = cden (tailL F X) (tailR F X) n (lr_rhs Ar).
Proof.
  intros [[x p] m] (Hx & Hp & Hm & Hxe).
  assert (HtL : negb (fm_left F) = true -> forall X, tailL F X = []).
  { intros Hz X. unfold tailL. destruct (fm_left F); [discriminate|reflexivity]. }
  assert (HtR : fm_left F = true -> forall X, tailR F X = []).
  { intros Hz X. unfold tailR. rewrite Hz. reflexivity. }
  assert (HtLp : elP p = true -> tailL F (txP V T nr p m) = []).
  { unfold txP. destruct (nr p); [intros _; apply tailL_nil | exact (fun Hz => HtL Hz _)]. }
  assert (HtRp : erP p = true -> tailR F (txP V T nr p m) = []).
  { unfold txP. destruct (nr p); [intros _; apply tailR_nil | exact (fun Hz => HtR Hz _)]. }
  destruct (digs_decomp (b - 1) x) as [Htop | (n & d & rest & Hxe' & Hd)].
  - assert (Et : alltopP F x = true) by (rewrite Htop; apply alltop_repeatP).
    set (j := length x) in Htop.
    destruct x as [|x1 xs] eqn:Ex.
    + destruct (mvE p) as [q dw dm | a q c] eqn:Emv.
      * (* the carry of an empty x *)
        exists (AE p), (elP p), (erP p), (txP V T nr p m), 0.
        split; [|split; [|split; [|split]]].
        -- exact (HAES p q dw dm Hp Emv).
        -- exact HtLp.
        -- exact HtRp.
        -- rewrite (HAEL p q dw dm Hp Emv). symmetry. apply pcfg_cls.
           apply pcells_empty. exact Hm.
        -- rewrite (HAER p q dw dm Hp Emv). symmetry.
           cbn [psucc alltopP forallb]. rewrite Emv. apply pcfg_cls.
           apply pcells_emoved; [exact Hm|]. exact (HVec p q dw dm Hp Emv).
      * (* the refill *)
        remember (aoff N0r str m) as r eqn:Er.
        assert (Hrlt : r < N0r + str) by (subst r; apply arm_index_lt; assumption).
        assert (Hk : r + astride N0r str r * acnt N0r str m = m)
          by (subst r; apply arm_index; assumption).
        exists (AR p r), true, true, [], (acnt N0r str m).
        split; [|split; [|split; [|split]]].
        -- exact (HARS p a q c r Hp Emv Hrlt).
        -- intros _; apply tailL_nil.
        -- intros _; apply tailR_nil.
        -- rewrite (HARL p a q c r Hp Emv Hrlt). symmetry. apply pcfg_cls.
           rewrite <- Hk at 1. apply pcells_refill.
        -- rewrite (HARR p a q c r Hp Emv Hrlt). symmetry.
           cbn [psucc alltopP forallb]. rewrite Emv.
           apply pcfg_cls. pose proof (Hfm p a q c r Hp Emv Hrlt).
           rewrite <- (pcells_refilled F W V T (fm1 p r) (astride N0r str r)
                         (acnt N0r str m) (fm2 p r) q c).
           f_equal. f_equal. lia.
    + rewrite <- Ex in *.
      assert (Hj : 0 < j) by (unfold j; subst x; cbn; lia).
      destruct (mvT p) as [q dw dm | q dm |] eqn:Emv.
      * (* the carry of a nonempty x *)
        remember (aoff N0c stc j) as r eqn:Er.
        assert (Hrlt : r < N0c + stc) by (subst r; apply arm_index_lt; assumption).
        assert (Hk : r + astride N0c stc r * acnt N0c stc j = j)
          by (subst r; apply arm_index; assumption).
        exists (AC p r), (elP p), (erP p), (txP V T nr p m), (acnt N0c stc j).
        split; [|split; [|split; [|split]]].
        -- exact (HACS p q dw dm r Hp Emv Hrlt).
        -- exact HtLp.
        -- exact HtRp.
        -- rewrite (HACL p q dw dm r Hp Emv Hrlt). symmetry. apply pcfg_cls.
           rewrite Htop, <- Hk at 1. apply pcells_top. exact Hm.
        -- rewrite (HACR p q dw dm r Hp Emv Hrlt). symmetry.
           assert (Hs : psucc F mvT mvE (x, p, m) = (repeat 0 (j + dw), q, m + dm)).
           { cbn [psucc]. rewrite Et, Emv. subst x. reflexivity. }
           rewrite Hs. apply pcfg_cls.
           replace (j + dw) with ((r + dw) + astride N0c stc r * acnt N0c stc j) by lia.
           apply pcells_moved; [exact Hm|]. exact (HVtc p q dw dm Hp Emv).
      * (* the narrowing *)
        remember (aoff N0n stn j) as r eqn:Er.
        assert (Hr0 : 0 < r) by (subst r; apply arm_index_pos; assumption).
        assert (Hrlt : r < N0n + stn) by (subst r; apply arm_index_lt; assumption).
        assert (Hk : r + astride N0n stn r * acnt N0n stn j = j)
          by (subst r; apply arm_index; assumption).
        exists (AN p r), (elP p), (erP p), (txP V T nr p m), (acnt N0n stn j).
        split; [|split; [|split; [|split]]].
        -- exact (HANS p q dm r Hp Emv Hr0 Hrlt).
        -- exact HtLp.
        -- exact HtRp.
        -- rewrite (HANL p q dm r Hp Emv Hr0 Hrlt). symmetry. apply pcfg_cls.
           rewrite Htop, <- Hk at 1. apply pcells_top. exact Hm.
        -- rewrite (HANR p q dm r Hp Emv Hr0 Hrlt). symmetry.
           assert (Hs : psucc F mvT mvE (x, p, m) = (repeat 0 (j - 1), q, m + dm)).
           { cbn [psucc]. rewrite Et, Emv. subst x. reflexivity. }
           rewrite Hs. apply pcfg_cls.
           replace (j - 1) with ((r - 1) + astride N0n stn r * acnt N0n stn j) by lia.
           apply pcells_moved; [exact Hm|]. exact (HVtn p q dm Hp Emv).
      * exfalso. pose proof (Hxe (HtX p Hp Emv)). subst x. discriminate.
  - (* the interior *)
    assert (Hne : alltopP F x = false) by (rewrite Hxe'; apply alltop_classP, Hd).
    rewrite Hxe' in Hx.
    apply Forall_app in Hx as [_ Hrest'].
    inversion Hrest' as [|? ? Hdb Hrest].
    assert (Hdlt : d < b - 1) by lia.
    assert (Hs : psucc F mvT mvE (x, p, m) = (repeat 0 n ++ S d :: rest, p, m)).
    { cbn [psucc]. rewrite Hne, Hxe', (inc_classP F n d rest Hdlt). reflexivity. }
    remember (aoff N0i sti n) as r eqn:Er.
    assert (Hrlt : r < N0i + sti) by (subst r; apply arm_index_lt; assumption).
    assert (Hn : r + astride N0i sti r * acnt N0i sti n = n)
      by (subst r; apply arm_index; assumption).
    assert (Hxp : b <= b + p -> xe (b + p - b) = false).
    { intros _. replace (b + p - b) with p by lia.
      destruct (xe p) eqn:Ex; [|reflexivity].
      pose proof (Hxe eq_refl) as Hx0'. rewrite Hxe' in Hx0'. destruct n; discriminate. }
    destruct rest as [|e' rest].
    { (* x ends after the digit: the phase word follows *)
      exists (AI d (b + p) r), (negb (fm_left F)), (fm_left F),
             (rep T m ++ V p), (acnt N0i sti n).
      split; [|split; [|split; [|split]]].
      * exact (HAIS d (b + p) r Hdlt ltac:(lia) Hxp Hrlt).
      * intros Hz; apply HtL, Hz.
      * intros Hz; apply HtR, Hz.
      * rewrite (HAIL d (b + p) r Hdlt ltac:(lia) Hxp Hrlt). symmetry. apply pcfg_cls.
        rewrite Hxe', <- Hn at 1. apply pcells_intm.
      * rewrite (HAIR d (b + p) r Hdlt ltac:(lia) Hxp Hrlt). symmetry. rewrite Hs.
        apply pcfg_cls. rewrite <- Hn at 1. apply pcells_intm. }
    inversion Hrest as [|? ? Heb _].
    exists (AI d e' r), (negb (fm_left F)), (fm_left F),
           (flat_map (dig F) rest ++ W p ++ rep T m ++ V p), (acnt N0i sti n).
    split; [|split; [|split; [|split]]].
    + exact (HAIS d e' r Hdlt ltac:(lia) (fun Hz => ltac:(lia)) Hrlt).
    + intros Hz; apply HtL, Hz.
    + intros Hz; apply HtR, Hz.
    + rewrite (HAIL d e' r Hdlt ltac:(lia) (fun Hz => ltac:(lia)) Hrlt). symmetry. apply pcfg_cls.
      rewrite Hxe', <- Hn at 1. apply pcells_intl; assumption.
    + rewrite (HAIR d e' r Hdlt ltac:(lia) (fun Hz => ltac:(lia)) Hrlt). symmetry. rewrite Hs.
      apply pcfg_cls. rewrite <- Hn at 1. apply pcells_intl; assumption.
Qed.

Lemma lapP : forall n, exists m c',
  0 < m /\ csteps tm m (Cf n) = Some c' /\ lift c' = lift (Cf (S n)).
Proof.
  intros n.
  assert (Hi : PInv F nr xe NP (piter F mvT mvE (x0, p0, m0) n))
    by (apply piter_inv with (A := A) (B := B) (g := g); first [exact pinv0 | assumption]).
  destruct (board_armP _ Hi) as (Ar & el & er & X & k & HA & HL & HR & Hl & Hr).
  destruct (HA _ _ k HL HR) as (m & c' & Hm & Hc' & Hlc).
  exists m, c'. split; [exact Hm|]. split.
  - cbn beta. rewrite Hl. exact Hc'.
  - rewrite Hlc, <- Hr. cbn beta.
    replace (S n) with (n + 1) by lia. rewrite piter_add. reflexivity.
Qed.

Lemma fireP : forall t N, ~ In t pins ->
  exists n k c', N <= n /\ csteps tm k (Cf n) = Some c' /\ cinstr c' = t.
Proof.
  intros t N Hnp.
  assert (Hcof : exists n, N <= n /\ isrefP mvE (piter F mvT mvE (x0, p0, m0) n) = true
                          /\ PInv F nr xe NP (piter F mvT mvE (x0, p0, m0) n))
    by (apply refill_cofinalP with (A := A) (B := B) (g := g); first [exact pinv0 | assumption]).
  destruct Hcof as (n & HN & Hx & Hi).
  exists n.
  destruct (piter F mvT mvE (x0, p0, m0) n) as [[x p] m] eqn:Eit.
  destruct Hi as (_ & Hp & _). destruct x as [|? ?]; [|discriminate].
  cbn [isrefP] in Hx. destruct (mvE p) as [q dw dm | a q c] eqn:Emv; [discriminate|].
  remember (aoff N0r str m) as r eqn:Er.
  assert (Hrlt : r < N0r + str) by (subst r; apply arm_index_lt; assumption).
  assert (Hk : r + astride N0r str r * acnt N0r str m = m)
    by (subst r; apply arm_index; assumption).
  assert (Hden : pcfg F W V T ([], p, m)
                 = cden [] [] (acnt N0r str m) (lr_lhs (AR p r))).
  { rewrite (HARL p a q c r Hp Emv Hrlt).
    rewrite <- (pcfg_cls F W V T
                  (blk (fm_pre F ++ W p ++ rep T r) T (astride N0r str r) (V p))
                  [] (acnt N0r str m) [] p m).
    - unfold tailL, tailR; destruct (fm_left F); reflexivity.
    - rewrite <- Hk at 1. apply pcells_refill. }
  destruct (nfire_sound tm true true rsv (vsegs p r t) (visI p r t)
              (lr_lhs (AR p r)) t Hrsv (Hfire p a q c r t Hp Emv Hnp Hrlt)
              [] [] (acnt N0r str m)
              (fun _ => eq_refl) (fun _ => eq_refl)) as (k & c' & Hc' & Ht).
  exists k, c'. cbn beta. rewrite ?Eit, Hden.
  split; [exact HN | split; [exact Hc' | exact Ht]].
Qed.

Theorem boardP_neverqhtr : forall t0,
  stepn tm t0 InitES = Some (lift (pcfg F W V T (x0, p0, m0))) ->
  NeverQuasiHaltsTr tm0.
Proof.
  intros t0 Hboot.
  apply (glue_neverqhtrN tm0 pins Cf).
  - exists t0. exact Hboot.
  - intros n. destruct (lapP n) as (m & c' & Hm & Hrun & Hl).
    exists m, c'. split; [exact Hrun | split; [exact Hl | exact Hm]].
  - intros t Hnp N. exact (fireP t N Hnp).
Qed.

Lemma reachP : forall d n,
  exists Tm, stepn tm Tm (lift (Cf n)) = Some (lift (Cf (n + d))).
Proof.
  induction d; intros n.
  - exists 0. rewrite Nat.add_0_r. reflexivity.
  - destruct (IHd n) as (Tm & HT).
    destruct (lapP (n + d)) as (m & c' & _ & Hm & Hl).
    exists (Tm + m). rewrite stepn_add, HT.
    replace (n + S d) with (S (n + d)) by lia.
    rewrite <- Hl. apply csteps_lift. exact Hm.
Qed.

Lemma fire_everyP : forall t, ~ In t pins -> forall n,
  exists k c', csteps tm k (Cf n) = Some c' /\ cinstr c' = t.
Proof.
  intros t Hnp n.
  destruct (fireP t n Hnp) as (m & k & c' & Hm & Hk & Hc').
  destruct (reachP (m - n) n) as (Tm & HT).
  replace (n + (m - n)) with m in HT by lia.
  assert (Hs : stepn tm (Tm + k) (lift (Cf n)) = Some (lift c')).
  { rewrite stepn_add, HT. apply csteps_lift. exact Hk. }
  destruct (stepn_csteps_at tm (Tm + k) (Cf n) (lift c') Hs) as (c'' & Hc'' & Hl').
  exists (Tm + k), c''. split; [exact Hc''|].
  rewrite <- cinstr_lift, Hl', cinstr_lift. exact Hc'.
Qed.

Theorem boardP_qhtr : forall t0 Bd,
  stepn tm0 t0 InitES = Some (lift (pcfg F W V T (x0, p0, m0))) ->
  existsb (fun tg => cfires tm0 CTape.c0 t0 tg) pins = true ->
  (t0 <=? Bd) = true ->
  NonHalt tm0 /\ QHBoundTr Bd tm0 /\ QuasiHaltsTr tm0.
Proof.
  intros t0 Bd Hboot Hwit Hle.
  apply (lap_qh_stage tm0 pins (fun p => Cf (Nat.pred (Pos.to_nat p)))
           1%positive t0 Bd).
  - exact Hboot.
  - intros p _.
    destruct (lapP (Nat.pred (Pos.to_nat p))) as (m & c' & Hm & Hrun & Hl).
    exists m, c'. split; [exact Hrun | split; [|exact Hm]].
    rewrite Hl, Pos2Nat.inj_succ.
    replace (S (Nat.pred (Pos.to_nat p))) with (Pos.to_nat p)
      by (pose proof (Pos2Nat.is_pos p); lia).
    reflexivity.
  - intros t Hnp p _. exact (fire_everyP t Hnp (Nat.pred (Pos.to_nat p))).
  - exact Hwit.
  - exact Hle.
Qed.

End BoardPTr.
