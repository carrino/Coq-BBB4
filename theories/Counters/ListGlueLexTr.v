(** * ListGlueLexTr: [ListGlue2Tr] with a lexicographic liveness read from
    the list's far end.

    The block lists of SCOPING_INSTR.md §7.4.BLC4 whose exploration closes
    but whose rare instruction fires only at the list's OVERFLOW are
    counters: the list [b_0 .. b_k] is a numeral (on a halving list,
    [b_i = 2 b_(i+1) + d_i]), every round adds one to it, and the rare
    instruction fires when the list grows by an item.  The distance to the
    overflow is about [a^k], so no ranking that ADDS a weight per tail item
    ([ListGlue2Tr]'s [lrk]) can bound the rounds.

    Here the liveness of an instruction may instead be a LEXICOGRAPHIC rank
    over the whole list, read from its most significant (far) end.  Per
    node (TriGlue's (leaf, residue) pairs) the certificate gives a list of
    window forms [W] (affine in the family's variables) and, per side and
    tail transition, a list of weights [(alpha, beta)], each one sequence
    entry [alpha * e + beta] (an end word that pins the last block may stand
    for no entry, so the far end's spellings agree on the length).  The
    SEQUENCE of an anchor is

      rev (hi tail's item weights) ++ W(vars) ++ (lo tail's item weights)

    ([hi] the side of the far end, [lo] the other one), followed by the old
    item-additive ranking value [V] as a last entry.  On every step between
    two nodes whose leaves do not fire the instruction:

    - the MIDDLE (the hi items the leaf unfolds, reversed, the window
      entries, the lo items it unfolds) and its image at the target (the
      folded items, the target's window entries) have the same LENGTH, so
      the untouched tails line up;
    - the hi side's weights do not grow (target <= source, per transition,
      the entry counts equal), so the untouched far part of the sequence is
      lexicographically <=; the lo side's entry counts do not change;
    - the middle drops lexicographically, checked symbolically: the first
      entry that is not [<=] coefficient-wise must not exist, and some entry
      before which every entry is [<=] must be strictly smaller ([lexchk]);
    - if the middle may stay equal, the lo side's weights do not grow and
      [V] drops, as in [ListGlue2Tr].

    The weights are per NODE: the meaning of a passed element may change
    when the carry resolves (a digit 2 the sweep has passed is a pending
    carry before the turn and a digit 1 after it), and the step where it
    changes is the one where the middle drops, so the lo tail behind it is
    free to be revalued.  The sequence length is constant along a run that
    does not fire the instruction, and the lexicographic order on [N^n] is
    well founded ([lex_wf]), so the instruction fires from every anchor.
    An instruction with no lexicographic entry keeps [ListGlue2Tr]'s
    check verbatim.

    Families, leaves, tails, bounds and the boot are [ListGlue2Tr]'s and
    are checked by its own [fams_ok], [mins_ok], [maxs_ok] and [lboot_ok].
    Only axiom: [functional_extensionality_dep] (through [CTape]). *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape ClosureTr Mirror.
From BBB4.Checkers Require Import WrapTr LapDecider.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
From BBB4.Checkers Require Import TCyclerQHTr.
From BBB4.Counters Require Import WTape LapCertGlueLift LapGlueTr SweepGlueTr TriGlueTr ListGlue2Tr.
From BBB4.CensusTr Require Import TNF_QHTr QHConveyorTr.

Import ListNotations.

(** ** The lexicographic order on lists of the same length *)

Fixpoint lexlt (l1 l2 : list nat) : Prop :=
  match l1, l2 with
  | x1 :: r1, x2 :: r2 => x1 < x2 \/ (x1 = x2 /\ lexlt r1 r2)
  | _, _ => False
  end.

Definition lexle (l1 l2 : list nat) : Prop := l1 = l2 \/ lexlt l1 l2.

Definition lexR (n : nat) (a b : list nat) : Prop := length a = n /\ length b = n /\ lexlt a b.

Lemma lex_wf : forall n, well_founded (lexR n).
Proof.
  induction n as [|n IHn].
  - intros l. constructor. intros [|y ys] (Hy & Hb & Hlt); cbn in Hy; [| discriminate].
    destruct l; contradiction.
  - assert (Hx : forall x r, length r = n -> Acc (lexR (S n)) (x :: r)).
    { intros x. induction x as [x IHx] using (well_founded_induction lt_wf).
      intros r Hr. revert Hr. induction (IHn r) as [r _ IHr]. intros Hr.
      constructor. intros [|y ys] (Hy & Hb & Hlt); [contradiction|].
      cbn in Hy, Hlt. destruct Hlt as [Hlt | [<- Hlt]].
      + apply IHx; [exact Hlt | lia].
      + apply IHr; [| lia]. split; [lia|]. split; [exact Hr | exact Hlt]. }
    intros [|x r].
    + constructor. intros y (_ & Hb & _). discriminate.
    + destruct (Nat.eq_dec (length r) n) as [Hr|Hr]; [exact (Hx x r Hr)|].
      constructor. intros y (_ & Hb & _). cbn in Hb. lia.
Qed.

Lemma lexlt_app_r : forall A' A B' B, length A' = length A -> lexlt A' A -> lexlt (A' ++ B') (A ++ B).
Proof.
  induction A' as [|x' A' IH]; intros [|x A] B' B Hl H; cbn in *; try contradiction; try discriminate.
  destruct H as [H | [-> H]]; [left; exact H|]. right. split; [reflexivity|]. apply IH; [lia | exact H].
Qed.

Lemma lexlt_app_l : forall A B' B, lexlt B' B -> lexlt (A ++ B') (A ++ B).
Proof. induction A as [|x A IH]; intros B' B H; cbn; [exact H|]. right. split; [reflexivity | apply IH, H]. Qed.

Lemma lexle_app : forall A' A B' B, length A' = length A -> lexle A' A -> lexlt B' B ->
  lexlt (A' ++ B') (A ++ B).
Proof.
  intros A' A B' B Hl [-> | H] HB; [apply lexlt_app_l, HB | apply lexlt_app_r; assumption].
Qed.

Fixpoint pwle (l1 l2 : list nat) : Prop :=
  match l1, l2 with
  | [], [] => True
  | x1 :: r1, x2 :: r2 => x1 <= x2 /\ pwle r1 r2
  | _, _ => False
  end.

Lemma pwle_len : forall l1 l2, pwle l1 l2 -> length l1 = length l2.
Proof. induction l1 as [|x l IH]; intros [|y m] H; cbn in *; try contradiction; auto. f_equal. apply IH, H. Qed.

Lemma pwle_lexle : forall l1 l2, pwle l1 l2 -> lexle l1 l2.
Proof.
  induction l1 as [|x l IH]; intros [|y m] H; cbn in H; try contradiction.
  - left. reflexivity.
  - destruct H as [Hxy H]. destruct (IH m H) as [-> | Hl].
    + destruct (Nat.eq_dec x y) as [-> | Hne]; [left; reflexivity|]. right. cbn. left. lia.
    + right. cbn. destruct (Nat.eq_dec x y) as [-> | Hne]; [right; split; [reflexivity | exact Hl]|].
      left. lia.
Qed.

Lemma pwle_app : forall a b c d, pwle a b -> pwle c d -> pwle (a ++ c) (b ++ d).
Proof. induction a as [|x a IH]; intros [|y b] c d H1 H2; cbn in *; try contradiction; auto. split; [apply H1 | apply IH; [apply H1 | exact H2]]. Qed.

Lemma pwle_rev : forall a b, pwle a b -> pwle (rev a) (rev b).
Proof.
  induction a as [|x a IH]; intros [|y b] H; cbn in *; try contradiction; auto.
  apply pwle_app; [apply IH, H | cbn; split; [apply H | exact I]].
Qed.

(** ** Item weights, concrete and symbolic *)

(** a weight table: per transition a LIST of entries [(alpha, beta)], one
    sequence entry [alpha * e + beta] each (so a transition may stand for no
    entry, e.g. an end word that pins the last block); a transition past the
    table: one entry [(0, b)] *)
Definition xget (w : list (list (nat * nat))) (b k : nat) : list (nat * nat) := nth k w [(0, b)].

Definition went (w : list (list (nat * nat))) (b : nat) (te : nat * nat) : list nat :=
  map (fun ab => fst ab * snd te + snd ab) (xget w b (fst te)).

Definition wents (w : list (list (nat * nat))) (b : nat) (T : list (nat * nat)) : list nat :=
  flat_map (went w b) T.

Definition wenta (w : list (list (nat * nat))) (b : nat) (te : nat * aexp) : list aexp :=
  map (fun ab => aaddc (ascale (fst ab) (snd te)) (snd ab)) (xget w b (fst te)).

Lemma wenta_ok : forall z w b I, map (aeval z) (flat_map (wenta w b) I) = wents w b (conc z I).
Proof.
  intros z w b I. induction I as [|[t e] I IH]; [reflexivity|].
  unfold wents, conc in *. cbn [flat_map map fst snd]. rewrite map_app, IH. f_equal.
  unfold wenta, went. cbn [fst snd]. rewrite map_map. apply map_ext. intros ab.
  rewrite aeval_aaddc, aeval_ascale. reflexivity.
Qed.

Lemma wents_app : forall w b T1 T2, wents w b (T1 ++ T2) = wents w b T1 ++ wents w b T2.
Proof. intros. apply flat_map_app. Qed.

Fixpoint ple (l1 l2 : list (nat * nat)) : bool :=
  match l1, l2 with
  | [], [] => true
  | x1 :: r1, x2 :: r2 => (fst x1 <=? fst x2) && (snd x1 <=? snd x2) && ple r1 r2
  | _, _ => false
  end.

(** entrywise [<=], the entry counts equal *)
Definition xwle (w1 : list (list (nat * nat))) (b1 : nat) (w2 : list (list (nat * nat))) (b2 : nat) : bool :=
  (b1 <=? b2)
  && forallb (fun k => ple (xget w1 b1 k) (xget w2 b2 k)) (seq 0 (Nat.max (length w1) (length w2))).

(** the entry counts equal *)
Definition xwshape (w1 : list (list (nat * nat))) (b1 : nat) (w2 : list (list (nat * nat))) (b2 : nat) : bool :=
  forallb (fun k => length (xget w1 b1 k) =? length (xget w2 b2 k)) (seq 0 (Nat.max (length w1) (length w2))).

Lemma ple_pwle : forall e l1 l2, ple l1 l2 = true ->
  pwle (map (fun ab => fst ab * e + snd ab) l1) (map (fun ab => fst ab * e + snd ab) l2).
Proof.
  intros e. induction l1 as [|x l IH]; intros [|y m] H; cbn in H |- *; try discriminate; [exact I|].
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply Nat.leb_le in H1, H2.
  split; [|exact (IH m H3)]. pose proof (Nat.mul_le_mono_r _ _ e H1). lia.
Qed.

Lemma wents_wle : forall w1 b1 w2 b2 T, xwle w1 b1 w2 b2 = true -> pwle (wents w1 b1 T) (wents w2 b2 T).
Proof.
  intros w1 b1 w2 b2 T H. unfold xwle in H. apply andb_prop in H as [Hb H].
  apply Nat.leb_le in Hb. rewrite forallb_forall in H.
  assert (Hk : forall k, ple (xget w1 b1 k) (xget w2 b2 k) = true).
  { intros k. destruct (lt_dec k (Nat.max (length w1) (length w2))) as [Hl|Hl].
    - exact (H k (proj2 (in_seq _ _ _) (conj (Nat.le_0_l k) Hl))).
    - unfold xget. rewrite !nth_overflow by lia. cbn. apply Nat.leb_le in Hb. rewrite Hb. reflexivity. }
  induction T as [|[t e] T IH]; cbn; [exact I|]. apply pwle_app; [|exact IH].
  unfold went. cbn [fst snd]. apply ple_pwle, Hk.
Qed.

Lemma wents_shape : forall w1 b1 w2 b2 T, xwshape w1 b1 w2 b2 = true ->
  length (wents w1 b1 T) = length (wents w2 b2 T).
Proof.
  intros w1 b1 w2 b2 T H. unfold xwshape in H. rewrite forallb_forall in H.
  assert (Hk : forall k, length (xget w1 b1 k) = length (xget w2 b2 k)).
  { intros k. destruct (lt_dec k (Nat.max (length w1) (length w2))) as [Hl|Hl].
    - apply Nat.eqb_eq. exact (H k (proj2 (in_seq _ _ _) (conj (Nat.le_0_l k) Hl))).
    - unfold xget. rewrite !nth_overflow by lia. reflexivity. }
  induction T as [|[t e] T IH]; [reflexivity|]. unfold wents in *. cbn [flat_map].
  rewrite !app_length, IH.
  unfold went. rewrite !map_length. cbn [fst]. rewrite Hk. reflexivity.
Qed.

(** ** The symbolic lexicographic comparison *)

(** [Some true]: strictly smaller for every valuation; [Some false]: smaller
    or equal *)
Fixpoint lexchk (l1 l2 : list aexp) : option bool :=
  match l1, l2 with
  | [], [] => Some false
  | x1 :: r1, x2 :: r2 =>
      if ale (aaddc x1 1) x2 then Some true
      else if ale x1 x2 then lexchk r1 r2 else None
  | _, _ => None
  end.

Lemma lexchk_sound : forall l1 l2 b z, lexchk l1 l2 = Some b ->
  if b then lexlt (map (aeval z) l1) (map (aeval z) l2) else lexle (map (aeval z) l1) (map (aeval z) l2).
Proof.
  induction l1 as [|x1 r1 IH]; intros [|x2 r2] b z H; cbn in H; try discriminate.
  - injection H as <-. left. reflexivity.
  - destruct (ale (aaddc x1 1) x2) eqn:E1.
    + injection H as <-. cbn. left. apply (ale_sound z) in E1. rewrite aeval_aaddc in E1. lia.
    + destruct (ale x1 x2) eqn:E2; [|discriminate]. apply (ale_sound z) in E2.
      specialize (IH r2 b z H). destruct b; cbn [map].
      * destruct (Nat.eq_dec (aeval z x1) (aeval z x2)) as [Ee|Ee].
        -- cbn. right. split; [exact Ee | exact IH].
        -- cbn. left. lia.
      * destruct (Nat.eq_dec (aeval z x1) (aeval z x2)) as [Ee|Ee].
        -- destruct IH as [IH | IH]; [left; rewrite Ee, IH; reflexivity|].
           right. cbn. right. split; [exact Ee | exact IH].
        -- right. cbn. left. lia.
Qed.

(** the combination of one step: far part [<=], middle [<] or ([<=], near
    part [<=] and the last entry [<]) *)
Lemma lex_step : forall hiT loT whi bhi whi' bhi' wlo blo wlo' blo' (Ms Mt : list nat) V V',
  xwle whi' bhi' whi bhi = true -> length Mt = length Ms ->
  (lexlt Mt Ms \/ (lexle Mt Ms /\ xwle wlo' blo' wlo blo = true /\ V' < V)) ->
  lexlt (rev (wents whi' bhi' hiT) ++ Mt ++ wents wlo' blo' loT ++ [V'])
        (rev (wents whi bhi hiT) ++ Ms ++ wents wlo blo loT ++ [V]).
Proof.
  intros hiT loT whi bhi whi' bhi' wlo blo wlo' blo' Ms Mt V V' Hhi Hl Hm.
  pose proof (pwle_rev _ _ (wents_wle whi' bhi' whi bhi hiT Hhi)) as Hp.
  apply lexle_app; [exact (pwle_len _ _ Hp) | exact (pwle_lexle _ _ Hp)|].
  destruct Hm as [Hm | (Hm & Hlo & HV)]; [apply lexlt_app_r; assumption|].
  apply lexle_app; [exact Hl | exact Hm|].
  pose proof (wents_wle wlo' blo' wlo blo loT Hlo) as Hq.
  apply lexle_app; [exact (pwle_len _ _ Hq) | exact (pwle_lexle _ _ Hq)|].
  cbn. left. exact HV.
Qed.

(** ** The certificate's lexicographic part *)

Record lxrk := mkLx {
  lx_W  : list (nat * list nat);     (** the window entries, far end first *)
  lx_wL : list (list (nat * nat));
  lx_bL : nat;
  lx_wR : list (list (nat * nat));
  lx_bR : nat
}.

Definition lx0 : lxrk := mkLx [] [] 0 [] 0.

(** the side of the far end first: [hi] *)
Definition lx_hiw (msd : bool) (r : lxrk) : list (list (nat * nat)) := if msd then lx_wR r else lx_wL r.
Definition lx_hib (msd : bool) (r : lxrk) : nat := if msd then lx_bR r else lx_bL r.
Definition lx_low (msd : bool) (r : lxrk) : list (list (nat * nat)) := if msd then lx_wL r else lx_wR r.
Definition lx_lob (msd : bool) (r : lxrk) : nat := if msd then lx_bL r else lx_bR r.

(** the middle of a step, symbolic: the hi items unfolded, the window, the lo
    items unfolded *)
Definition mida (msd : bool) (r : lxrk) (xs : list aexp) (IL IR : list (nat * aexp)) : list aexp :=
  rev (flat_map (wenta (lx_hiw msd r) (lx_hib msd r)) (if msd then IR else IL))
  ++ map (fun v => veval v xs) (lx_W r)
  ++ flat_map (wenta (lx_low msd r) (lx_lob msd r)) (if msd then IL else IR).

(** the sequence of an anchor *)
Definition seqv (msd : bool) (r : lxrk) (vals : list nat) (TL TR : list (nat * nat)) : list nat :=
  rev (wents (lx_hiw msd r) (lx_hib msd r) (if msd then TR else TL))
  ++ map (fun v => vval v vals) (lx_W r)
  ++ wents (lx_low msd r) (lx_lob msd r) (if msd then TL else TR).

Section LiveX.

Variable tmw : TM.
Variable kinds : list (list Sym * list Sym).
Variable trans : list ltrans.
Variable acc : list (bool * nat).
Variable mins : list (bool * nat * nat).
Variable maxs : list (bool * nat * nat).
Variable fams : list lfam.
Variable leaves : list lleaf.

Hypothesis Hmins : mins_ok trans acc mins = true.
Hypothesis Hmaxs : maxs_ok trans acc maxs = true.
Hypothesis Hfams : fams_ok tmw kinds trans acc mins maxs fams leaves = true.

Variable pins : list Instr.
Variable P : nat.
Variable S : list (nat * list nat).
Variable rk : list (Instr * list lrk).
Variable lex : list (Instr * (bool * list lxrk)).

Definition lexrank_of (t : Instr) : option (bool * list lxrk) :=
  match find (fun p => instr_eqb (fst p) t) lex with Some p => Some (snd p) | None => None end.

(** [ListGlue2Tr]'s step condition on the additive ranking [V] *)
Definition vchk (r r' : lrk) (src tgt : list aexp) (uL uR fL fR : list (nat * aexp)) : bool :=
  ale (aaddc (aadd (veval (rk_V r') tgt)
                   (aadd (twa (rk_wL r') (rk_bL r') fL) (twa (rk_wR r') (rk_bR r') fR))) 1)
      (aadd (veval (rk_V r) src) (aadd (twa (rk_wL r) (rk_bL r) uL) (twa (rk_wR r) (rk_bR r) uR)))
  && wle (rk_wL r') (rk_bL r') (rk_wL r) (rk_bL r)
  && wle (rk_wR r') (rk_bR r') (rk_wR r) (rk_bR r).

Definition xedge (t : Instr) (i i' : nat) (src tgt : list aexp) (uL uR fL fR : list (nat * aexp)) : bool :=
  let r := nth i (lrank_of rk t) rk0 in
  let r' := nth i' (lrank_of rk t) rk0 in
  let vok := vchk r r' src tgt uL uR fL fR in
  match lexrank_of t with
  | None => vok
  | Some (msd, xs) =>
      let x := nth i xs lx0 in
      let x' := nth i' xs lx0 in
      let Ms := mida msd x src uL uR in
      let Mt := mida msd x' tgt fL fR in
      (length Mt =? length Ms)
      && xwle (lx_hiw msd x') (lx_hib msd x') (lx_hiw msd x) (lx_hib msd x)
      && xwshape (lx_low msd x') (lx_lob msd x') (lx_low msd x) (lx_lob msd x)
      && match lexchk Mt Ms with
         | Some true => true
         | Some false => xwle (lx_low msd x') (lx_lob msd x') (lx_low msd x) (lx_lob msd x) && vok
         | None => false
         end
  end.

Definition xnode_ok (fired : list (list Instr)) (i : nat) (lr : nat * list nat) : bool :=
  match nth_error leaves (fst lr) with
  | None => false
  | Some lf =>
      let fl := nth (fst lr) fired [] in
      forallb (fun s =>
        let sub := zsub P s in
        let src := map (asubst sub) (rsub (ll_reg lf)) in
        let tgt := map (asubst sub) (ll_tgt lf) in
        let uL := isub sub (ll_uL lf) in
        let uR := isub sub (ll_uR lf) in
        let fL := isub sub (ll_fL lf) in
        let fR := isub sub (ll_fR lf) in
        let rho' := map (fun e => a_c e mod P) tgt in
        forallb (pdiv P) tgt
        && forallb (fun l' =>
             match nth_error leaves l' with
             | None => true
             | Some lf' =>
                 if (ll_f lf' =? ll_g lf) && compat P (ll_reg lf') tgt then
                   match nidx S l' rho' with
                   | None => false
                   | Some i' =>
                       let fl' := nth l' fired [] in
                       forallb (fun t =>
                         tr_inb t pins || tr_inb t fl || tr_inb t fl'
                         || xedge t i i' src tgt uL uR fL fR)
                         all_Instr
                   end
                 else true
             end) (seq 0 (length leaves)))
        (sassign P (ll_reg lf) (snd lr))
  end.

Definition xlive_ok : bool :=
  let fired := map (lleaf_fired tmw) leaves in
  (0 <? P)
  && forallb (fun ilr => xnode_ok fired (fst ilr) (snd ilr)) (combine (seq 0 (length S)) S).

Hypothesis Hlive : xlive_ok = true.

Lemma xHP : 0 < P.
Proof. unfold xlive_ok in Hlive. apply andb_prop in Hlive as [H _]. apply Nat.ltb_lt, H. Qed.

Lemma xnode : forall i lr, nth_error S i = Some lr -> xnode_ok (map (lleaf_fired tmw) leaves) i lr = true.
Proof.
  intros i lr H. unfold xlive_ok in Hlive. apply andb_prop in Hlive as [_ Hl].
  rewrite forallb_forall in Hl. apply (Hl (i, lr)).
  assert (Hc : forall s0 l i, nth_error l i = Some lr ->
            In (s0 + i, lr) (combine (seq s0 (length l)) l)).
  { clear. intros s0 l. revert s0. induction l as [|x l IH]; intros s0 [|i] H; cbn in H |- *;
      try discriminate.
    - injection H as ->. left. f_equal. lia.
    - right. rewrite <- Nat.add_succ_comm. apply IH. exact H. }
  exact (Hc 0 S i H).
Qed.

Notation GoodS := (GoodS trans acc fams P S).
Notation lnodeidx := (lnodeidx fams P S).
Notation lnxt := (lnxt fams leaves).
Notation lfires_at := (lfires_at tmw fams leaves).
Notation tanc := (tanc kinds trans fams).

(** the measure of an anchor for an instruction *)
Definition xmeas (t : Instr) (a : lanc) : list nat :=
  match lnodeidx a with
  | Some i =>
      let r := nth i (lrank_of rk t) rk0 in
      let V := vval (rk_V r) (an_v a) + twv (rk_wL r) (rk_bL r) (an_L a) + twv (rk_wR r) (rk_bR r) (an_R a) in
      match lexrank_of t with
      | Some (msd, xs) => seqv msd (nth i xs lx0) (an_v a) (an_L a) (an_R a)
      | None => []
      end ++ [V]
  | None => []
  end.

Lemma seqv_split : forall msd r vals IL TL IR TR,
  seqv msd r vals (IL ++ TL) (IR ++ TR)
  = rev (wents (lx_hiw msd r) (lx_hib msd r) (if msd then TR else TL))
    ++ (rev (wents (lx_hiw msd r) (lx_hib msd r) (if msd then IR else IL))
        ++ map (fun v => vval v vals) (lx_W r)
        ++ wents (lx_low msd r) (lx_lob msd r) (if msd then IL else IR))
    ++ wents (lx_low msd r) (lx_lob msd r) (if msd then TL else TR).
Proof.
  intros msd r vals IL TL IR TR. unfold seqv.
  destruct msd; rewrite !wents_app, rev_app_distr, <- !app_assoc; reflexivity.
Qed.

Lemma mida_ok : forall z msd r xs IL IR,
  map (aeval z) (mida msd r xs IL IR)
  = rev (wents (lx_hiw msd r) (lx_hib msd r) (conc z (if msd then IR else IL)))
    ++ map (fun v => vval v (map (aeval z) xs)) (lx_W r)
    ++ wents (lx_low msd r) (lx_lob msd r) (conc z (if msd then IL else IR)).
Proof.
  intros z msd r xs IL IR. unfold mida. rewrite !map_app, map_rev, !wenta_ok, map_map.
  replace (map (fun x => aeval z (veval x xs)) (lx_W r))
    with (map (fun v => vval v (map (aeval z) xs)) (lx_W r))
    by (apply map_ext; intros v; symmetry; apply veval_ok).
  reflexivity.
Qed.

Lemma xnext_ok : forall a, GoodS a ->
  GoodS (lnxt a)
  /\ forall t, ~ In t pins -> lfires_at a t = false -> lfires_at (lnxt a) t = false ->
       length (xmeas t (lnxt a)) = length (xmeas t a) /\ lexlt (xmeas t (lnxt a)) (xmeas t a).
Proof.
  intros a [Ha Hn].
  destruct (lwalk_leaf tmw kinds trans acc mins maxs fams leaves Hmins Hmaxs Hfams a Ha)
    as (F & lf & l & R & z & TL & TR & pL & pR & iL & iR & HF & Hw
    & Hlf & Hf & HR & HuL & HuR & Hok & Hv & HzR & HsL & HsR & HaL & HaR).
  unfold ListGlue2Tr.lnodeidx in Hn. rewrite Hw in Hn.
  destruct (nidx S l (modl P (an_v a))) as [i|] eqn:Ei; [|contradiction].
  pose proof (nidx_ok _ _ _ _ Ei) as HSi.
  pose proof (xnode _ _ HSi) as Hln.
  unfold xnode_ok in Hln. cbn [fst snd] in Hln. rewrite Hlf in Hln.
  rewrite forallb_forall in Hln.
  set (s := modl P z).
  assert (Hs : In s (sassign P (ll_reg lf) (modl P (an_v a)))).
  { rewrite HR, Hv, (lmodl_rsub P) by exact HzR. apply sassign_in; [exact xHP | exact HzR]. }
  specialize (Hln s Hs). cbv zeta in Hln. apply andb_prop in Hln as [Hdiv Hln].
  rewrite forallb_forall in Hln.
  destruct (lstep_ok tmw kinds trans acc mins maxs fams leaves Hmins Hmaxs Hfams a Ha) as (_ & Ha').
  assert (Hnx : lnxt a = mkAn (ll_g lf) (map (aeval z) (ll_tgt lf))
                             (conc z (ll_fL lf) ++ TL) (conc z (ll_fR lf) ++ TR)).
  { unfold ListGlue2Tr.lnxt. rewrite Hw, Hlf. reflexivity. }
  destruct (lwalk_leaf tmw kinds trans acc mins maxs fams leaves Hmins Hmaxs Hfams _ Ha')
    as (G & lf' & l' & R' & z2 & TL2 & TR2 & pL2 & pR2 & iL2 & iR2
    & HG & Hw' & Hlf' & Hf' & HR' & _ & _ & _ & Hv' & HzR' & _ & _ & _ & _).
  rewrite Hnx in HG, Hw', Hf', Hv'. cbn [an_f an_v an_L an_R] in HG, Hw', Hf', Hv'.
  set (z' := map (fun x => x / P) z).
  assert (Hzs : forall e, aeval z' (asubst (zsub P s) e) = aeval z e).
  { intros e. subst z' s. apply aeval_zsub. exact xHP. }
  set (tgt := map (asubst (zsub P s)) (ll_tgt lf)) in *.
  set (src := map (asubst (zsub P s)) (rsub (ll_reg lf))) in *.
  assert (Htgt : map (aeval z') tgt = map (aeval z) (ll_tgt lf)).
  { subst tgt. rewrite map_map. apply map_ext. exact Hzs. }
  assert (Hsrc : map (aeval z') src = an_v a).
  { subst src. rewrite map_map, Hv, <- HR. apply map_ext. exact Hzs. }
  assert (Hl' : In l' (seq 0 (length leaves))).
  { apply in_seq. split; [lia|]. apply nth_error_Some. rewrite Hlf'. discriminate. }
  specialize (Hln l' Hl'). rewrite Hlf' in Hln.
  assert (HlenR' : length R' = length (ll_tgt lf)).
  { pose proof (f_equal (@length nat) Hv') as E. rewrite !map_length, rsub_length in E. lia. }
  assert (Hcomp : compat P (ll_reg lf') tgt = true).
  { apply (compat_ok P z' (ll_reg lf') tgt z2 Hdiv).
    - subst tgt. rewrite map_length, HR'. lia.
    - intros k Hk. rewrite HR' in Hk |- *.
      assert (Hk2 : k < length tgt) by (subst tgt; rewrite map_length; lia).
      rewrite <- (nth_map_lt (aeval z') tgt k (aconst 0) 0 Hk2), Htgt, Hv'.
      apply rsub_nth. exact Hk. }
  rewrite Hf', Nat.eqb_refl, Hcomp in Hln. cbn [andb] in Hln.
  assert (Hrho : map (fun e => a_c e mod P) tgt = modl P (map (aeval z) (ll_tgt lf))).
  { rewrite <- Htgt. unfold modl. rewrite map_map. apply map_ext_in. intros e He.
    rewrite forallb_forall in Hdiv. symmetry. apply pdiv_mod. exact (Hdiv e He). }
  rewrite Hrho in Hln.
  destruct (nidx S l' (modl P (map (aeval z) (ll_tgt lf)))) as [i'|] eqn:Ei'; [|discriminate].
  assert (Hn' : lnodeidx (lnxt a) = Some i').
  { unfold ListGlue2Tr.lnodeidx. rewrite Hnx. cbn [an_v]. rewrite Hw'. exact Ei'. }
  assert (Hn0 : lnodeidx a = Some i).
  { unfold ListGlue2Tr.lnodeidx. rewrite Hw. exact Ei. }
  split.
  - split; [exact Ha' | rewrite Hn'; discriminate].
  - intros t Hpin Hfa Hfa'.
    unfold ListGlue2Tr.lfires_at in Hfa, Hfa'. rewrite Hw, Hlf in Hfa. rewrite Hnx in Hfa'.
    rewrite Hw', Hlf' in Hfa'.
    rewrite forallb_forall in Hln. specialize (Hln t (all_Instr_complete t)).
    assert (Hpin' : tr_inb t pins = false).
    { destruct (tr_inb t pins) eqn:E; [|reflexivity].
      exfalso. apply Hpin. apply tr_inb_spec. exact E. }
    assert (Hfl : nth l (map (lleaf_fired tmw) leaves) [] = lleaf_fired tmw lf).
    { apply nth_error_nth. apply map_nth_error. exact Hlf. }
    assert (Hfl2 : nth l' (map (lleaf_fired tmw) leaves) [] = lleaf_fired tmw lf').
    { apply nth_error_nth. apply map_nth_error. exact Hlf'. }
    rewrite Hpin', Hfl, Hfl2, Hfa, Hfa' in Hln. cbn [orb] in Hln.
    (* the additive part: [V' < V] when [vchk] holds *)
    set (r := nth i (lrank_of rk t) rk0) in *.
    set (r' := nth i' (lrank_of rk t) rk0) in *.
    set (V := vval (rk_V r) (an_v a) + twv (rk_wL r) (rk_bL r) (an_L a) + twv (rk_wR r) (rk_bR r) (an_R a)).
    set (V' := vval (rk_V r') (map (aeval z) (ll_tgt lf)) + twv (rk_wL r') (rk_bL r') (conc z (ll_fL lf) ++ TL)
               + twv (rk_wR r') (rk_bR r') (conc z (ll_fR lf) ++ TR)).
    assert (HV : vchk r r' src tgt (isub (zsub P s) (ll_uL lf)) (isub (zsub P s) (ll_uR lf))
                      (isub (zsub P s) (ll_fL lf)) (isub (zsub P s) (ll_fR lf)) = true -> V' < V).
    { intros Hc. unfold vchk in Hc.
      apply andb_prop in Hc as [Hc HwR]. apply andb_prop in Hc as [Hc HwL].
      pose proof (ale_sound z' _ _ Hc) as Hle.
      rewrite aeval_aaddc, !aeval_aadd, !veval_ok, !twa_ok, Htgt, Hsrc in Hle.
      rewrite !(isub_conc z' (zsub P s) z) in Hle by exact Hzs.
      unfold V, V'. rewrite HaL, HaR, !twv_app. rewrite HuL, HuR in Hle.
      pose proof (wle_ok _ _ _ _ TL HwL). pose proof (wle_ok _ _ _ _ TR HwR). lia. }
    unfold xmeas. rewrite Hn', Hn0. fold r r'. rewrite Hnx. cbn [an_v an_L an_R]. fold V'. fold V.
    unfold xedge in Hln. fold r r' in Hln.
    destruct (lexrank_of t) as [[msd xs]|].
    + set (x := nth i xs lx0) in *. set (x' := nth i' xs lx0) in *.
      apply andb_prop in Hln as [Hln Hm]. apply andb_prop in Hln as [Hln Hsh].
      apply andb_prop in Hln as [Hlen Hhi].
      apply Nat.eqb_eq in Hlen.
      set (Ms := mida msd x src (isub (zsub P s) (ll_uL lf)) (isub (zsub P s) (ll_uR lf))) in *.
      set (Mt := mida msd x' tgt (isub (zsub P s) (ll_fL lf)) (isub (zsub P s) (ll_fR lf))) in *.
      assert (EMs : map (aeval z') Ms
                    = rev (wents (lx_hiw msd x) (lx_hib msd x) (if msd then conc z iR else conc z iL))
                      ++ map (fun v => vval v (an_v a)) (lx_W x)
                      ++ wents (lx_low msd x) (lx_lob msd x) (if msd then conc z iL else conc z iR)).
      { unfold Ms. rewrite mida_ok, Hsrc.
        destruct msd; rewrite !(isub_conc z' (zsub P s) z) by exact Hzs; rewrite <- HuL, <- HuR; reflexivity. }
      assert (EMt : map (aeval z') Mt
                    = rev (wents (lx_hiw msd x') (lx_hib msd x')
                                 (if msd then conc z (ll_fR lf) else conc z (ll_fL lf)))
                      ++ map (fun v => vval v (map (aeval z) (ll_tgt lf))) (lx_W x')
                      ++ wents (lx_low msd x') (lx_lob msd x')
                               (if msd then conc z (ll_fL lf) else conc z (ll_fR lf))).
      { unfold Mt. rewrite mida_ok, Htgt.
        destruct msd; rewrite !(isub_conc z' (zsub P s) z) by exact Hzs; reflexivity. }
      assert (Hseq : seqv msd x (an_v a) (an_L a) (an_R a)
                     = rev (wents (lx_hiw msd x) (lx_hib msd x) (if msd then TR else TL))
                       ++ map (aeval z') Ms
                       ++ wents (lx_low msd x) (lx_lob msd x) (if msd then TL else TR)).
      { rewrite EMs, HaL, HaR, seqv_split. destruct msd; reflexivity. }
      assert (Hseq' : seqv msd x' (map (aeval z) (ll_tgt lf)) (conc z (ll_fL lf) ++ TL) (conc z (ll_fR lf) ++ TR)
                     = rev (wents (lx_hiw msd x') (lx_hib msd x') (if msd then TR else TL))
                       ++ map (aeval z') Mt
                       ++ wents (lx_low msd x') (lx_lob msd x') (if msd then TL else TR)).
      { rewrite EMt, seqv_split. destruct msd; reflexivity. }
      rewrite Hseq, Hseq'. rewrite <- !app_assoc.
      split.
      * rewrite !app_length, !rev_length, !map_length, Hlen.
        rewrite (pwle_len _ _ (wents_wle _ _ _ _ (if msd then TR else TL) Hhi)).
        rewrite (wents_shape _ _ _ _ (if msd then TL else TR) Hsh). reflexivity.
      * apply lex_step; [exact Hhi | rewrite !map_length; exact Hlen|].
        destruct (lexchk Mt Ms) as [[|]|] eqn:Ec; [| |discriminate].
        -- left. exact (lexchk_sound _ _ true z' Ec).
        -- right. apply andb_prop in Hm as [Hlo Hc].
           split; [exact (lexchk_sound _ _ false z' Ec)|]. split; [exact Hlo | exact (HV Hc)].
    + cbn [app]. split; [reflexivity|]. cbn. left. exact (HV Hln).
Qed.

Lemma xfires : forall t, ~ In t pins -> forall n l, Acc (lexR n) l ->
  forall a, GoodS a -> xmeas t a = l -> length l = n ->
  exists k e, stepn tmw k (lift (tanc a)) = Some e /\ instr_of e = t.
Proof.
  intros t Hpin n l Hacc. induction Hacc as [l _ IH]. intros a Ha Hl Hn.
  assert (Hfire : forall a, GoodS a -> lfires_at a t = true ->
                 exists k e, stepn tmw k (lift (tanc a)) = Some e /\ instr_of e = t).
  { intros b [Hb _] Hf. unfold ListGlue2Tr.lfires_at in Hf.
    destruct (ListGlue2Tr.lwalk fams b) as [[[[[l0 R] z] TL] TR]|] eqn:Ew; [|discriminate].
    destruct (nth_error leaves l0) as [lf|] eqn:El; [|discriminate].
    apply tr_inb_spec in Hf.
    destruct (lleaf_fires tmw kinds trans acc mins maxs fams leaves Hmins Hmaxs Hfams
                b l0 R z TL TR lf t Hb Ew El Hf) as (k & c & Hk & Hc).
    exists k, (lift c). split; [apply csteps_lift; exact Hk | rewrite cinstr_lift; exact Hc]. }
  destruct (lfires_at a t) eqn:Ef; [exact (Hfire a Ha Ef)|].
  destruct (lstep_ok tmw kinds trans acc mins maxs fams leaves Hmins Hmaxs Hfams a (proj1 Ha))
    as ((m & c' & Hm & Hlft & _) & _).
  destruct (xnext_ok a Ha) as (Ha' & Hrk).
  assert (Hback : forall t', (exists k e, stepn tmw k (lift (tanc (lnxt a))) = Some e /\ instr_of e = t') ->
                             exists k e, stepn tmw k (lift (tanc a)) = Some e /\ instr_of e = t').
  { intros t' (k & e & Hk & He). exists (m + k), e.
    split; [rewrite stepn_add, (csteps_lift _ _ _ _ Hm), Hlft; exact Hk | exact He]. }
  apply Hback.
  destruct (lfires_at (lnxt a) t) eqn:Ef'; [exact (Hfire _ Ha' Ef')|].
  destruct (Hrk t Hpin Ef Ef') as (Hlen & Hlt).
  subst l n.
  apply (IH (xmeas t (lnxt a))); [| exact Ha' | reflexivity | exact Hlen].
  split; [exact Hlen|]. split; [reflexivity | exact Hlt].
Qed.

Lemma xreach : forall a0 t0, GoodS a0 -> stepn tmw t0 InitES = Some (lift (tanc a0)) ->
  forall N, exists T a, N <= T /\ GoodS a /\ stepn tmw T InitES = Some (lift (tanc a)).
Proof.
  intros a0 t0 H0 Hb N. induction N as [|N (T & a & HT & Ha & Hs)].
  - exists t0, a0. split; [lia|]. split; assumption.
  - destruct (lstep_ok tmw kinds trans acc mins maxs fams leaves Hmins Hmaxs Hfams a (proj1 Ha))
      as ((m & c' & Hm & Hl & Hpos) & _).
    destruct (xnext_ok a Ha) as (Ha' & _).
    exists (T + m), (lnxt a). split; [lia|]. split; [exact Ha'|].
    rewrite stepn_add, Hs, (csteps_lift _ _ _ _ Hm), Hl. reflexivity.
Qed.

End LiveX.

(** ** The certificate and the checker *)

Record lcertx := mkLCX {
  lx_base : lcert2;                                (** [ListGlue2Tr]'s certificate *)
  lx_lex  : list (Instr * (bool * list lxrk))      (** per instruction: far end on the right?, per node *)
}.

Definition lgx_check (tm : TM) (wx : lcertx) : bool :=
  let w := lx_base wx in
  let tmw := tm_wrap_trs tm (lc_pins w) in
  mins_ok (lc_trans w) (lc_acc w) (lc_mins w)
  && maxs_ok (lc_trans w) (lc_acc w) (lc_maxs w)
  && fams_ok tmw (lc_kinds w) (lc_trans w) (lc_acc w) (lc_mins w) (lc_maxs w) (lc_fams w) (lc_leaves w)
  && xlive_ok tmw (lc_leaves w) (lc_pins w) (lc_P w) (lc_S w) (lc_rank w) (lx_lex wx)
  && lboot_ok tmw w.

Theorem lgx_sound : forall tm wx, lgx_check tm wx = true -> NeverQuasiHaltsTr tm.
Proof.
  intros tm wx H. unfold lgx_check in H.
  set (w := lx_base wx) in *.
  set (tmw := tm_wrap_trs tm (lc_pins w)) in *.
  apply andb_prop in H as [H Hb]. apply andb_prop in H as [H Hl].
  apply andb_prop in H as [H Hf]. apply andb_prop in H as [Hm Hx].
  set (a0 := lc_a0 w) in *.
  unfold lboot_ok in Hb. fold a0 in Hb.
  destruct (nth_error (lc_fams w) (an_f a0)) as [F|] eqn:EF; [|discriminate].
  destruct (csteps tmw (lc_t0 w) c0) as [c|] eqn:Ec; [|discriminate].
  apply andb_prop in Hb as [Hb Hn]. apply andb_prop in Hb as [Hb HtR].
  apply andb_prop in Hb as [Hb HtL]. apply andb_prop in Hb as [Hc Hlen].
  apply Nat.eqb_eq in Hlen.
  assert (H0 : GoodS (lc_trans w) (lc_acc w) (lc_fams w) (lc_P w) (lc_S w) a0).
  { split.
    - exists F. split; [exact EF|]. split; [exact Hlen|].
      split; apply tail_bvalid_ok; assumption.
    - destruct (lnodeidx (lc_fams w) (lc_P w) (lc_S w) a0); discriminate. }
  assert (Hboot : stepn tmw (lc_t0 w) InitES
                  = Some (lift (tanc (lc_kinds w) (lc_trans w) (lc_fams w) a0))).
  { rewrite <- lift_c0, (csteps_lift _ _ _ _ Ec). f_equal. exact (ceqb_lift _ _ Hc). }
  pose proof (xreach tmw _ _ _ _ _ _ _ Hm Hx Hf _ _ _ _ _ Hl a0 (lc_t0 w) H0 Hboot) as Hreach.
  assert (Hnh : forall n, stepn tmw n InitES <> None).
  { intros n. destruct (Hreach n) as (T & a & HT & _ & Hs).
    destruct (stepn_prefix tmw n T InitES _ HT Hs) as (cm & Hcm & _).
    rewrite Hcm. discriminate. }
  pose proof (wrap_trs_agree tm (lc_pins w) InitES Hnh) as Hagree.
  intros t (n & c1 & Hc1 & Ht) N.
  assert (Hnp : ~ In t (lc_pins w)).
  { destruct (Hagree n) as [_ Hnot]. rewrite <- Ht. exact (Hnot c1 Hc1). }
  destruct (Hreach N) as (T & a & HT & Ha & Hs).
  set (l := xmeas (lc_fams w) (lc_P w) (lc_S w) (lc_rank w) (lx_lex wx) t a).
  destruct (xfires tmw _ _ _ _ _ _ _ Hm Hx Hf _ _ _ _ _ Hl t Hnp (length l) l
              (lex_wf (length l) l) a Ha eq_refl eq_refl) as (k & e & Hk & He).
  exists (T + k). split; [lia|].
  exists e. split; [| exact He].
  destruct (Hagree (T + k)) as [Heq _]. rewrite <- Heq. fold tmw.
  rewrite stepn_add, Hs. exact Hk.
Qed.

(** the anchors are mirrored: certify the mirror *)
Theorem lgx_sound_mirror : forall tm wx, lgx_check (mirror_tm tm) wx = true -> NeverQuasiHaltsTr tm.
Proof.
  intros tm wx H. apply neverqhtr_mirror. exact (lgx_sound _ wx H).
Qed.
