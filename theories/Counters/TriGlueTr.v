(** * TriGlueTr: multi-index block glue -- anchor FAMILIES of symbolic
    block tapes, one LapDecider chain per leaf, and per-instruction
    ranking functions for the fires.

    [SweepGlueTr] enumerates the two-index anchors [(i, k)] of one sweep
    family; [SweepGlueNeverTr] a cycle of such families; [HybridGlueTr] a
    counter with a block beside it.  The sweep counters §7.4.SW and §7.4.HY
    leave (SCOPING_INSTR.md §7.4.TI) keep THREE or more blocks, and the
    lap that ends a round depends on a remainder (a block shrinks by 3 per
    lap, and what happens when it runs out depends on what is left).  The
    anchor here is therefore a whole symbolic tape:

      [tinst f vals = (q, (sided vals L, h, sided vals R))]

    where the sides [L]/[R] of family [f] are lists of literal words and
    blocks [rep u e], each exponent [e] an affine expression in the
    family's variables [vals].  Three indices (§7.4.QS's sketch
    [L ++ uL^i ++ M ++ uR^k ++ N ++ uL'^i ++ R]) is the common case; the
    glue does not care how many.

    - A family carries a DISPATCH TREE on its variables: a split on
      variable [k] takes the values [0 .. n-1] one by one and the rest by
      residue mod [p].  Every leaf of the tree fixes a REGION
      [x_k = M_k z_k + c_k] with leaf parameters [z], and carries ONE
      [LapDecider] chain whose index is one [z_j]; every other block is
      inside the opaque tails or concrete in the region.  The leaf's
      chain lands on (the [lift] of) a family [g] at values that are
      affine in [z] ([tl_tgt]).  The comparisons between the chain's
      ends and the families are done by a verified normalizer on
      segment lists ([norm], [nstrip]).
    - The anchors are the iterates of [nxt] from the boot (walk the tree,
      jump to the target), which is the single [Hlap] of
      [LapGlueTr.glue_neverqhtr].
    - FIRES.  Every chain prefix of a leaf fires its end instruction from
      every anchor that takes that leaf ([leaf_fired]).  That an
      instruction fires from EVERY anchor needs a liveness argument: a
      set [S] of nodes (leaf, values mod [P]) closed under the steps and
      containing the boot, and per instruction an affine ranking on the
      nodes that drops by one at every step out of a non-firing leaf into
      a non-firing leaf.  Everything is checked coefficient-wise, so the
      whole certificate is data and [tri_check] is one boolean.

    Only axiom: [functional_extensionality_dep] (through [CTape]). *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape ClosureTr Mirror.
From BBB4.Checkers Require Import WrapTr LapDecider.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
From BBB4.Checkers Require Import TCyclerQHTr.
From BBB4.Counters Require Import WTape LapCertGlueLift LapGlueTr SweepGlueTr.
From BBB4.CensusTr Require Import TNF_QHTr QHConveyorTr.
Import ListNotations.

(** ** Affine expressions over nat variables *)

(** [c + sum a_i * v_(k_i)]; the terms are kept sorted by variable with
    positive coefficients by the operations below, but nothing in the
    soundness proofs depends on it. *)
Record aexp := mkA { a_c : nat; a_t : list (nat * nat) }.

Fixpoint teval (v : list nat) (t : list (nat * nat)) : nat :=
  match t with
  | [] => 0
  | (k, a) :: t' => a * nth k v 0 + teval v t'
  end.

Definition aeval (v : list nat) (e : aexp) : nat := a_c e + teval v (a_t e).

(** insert one term into a sorted term list *)
Fixpoint tins (k a : nat) (t : list (nat * nat)) : list (nat * nat) :=
  match t with
  | [] => [(k, a)]
  | (k2, a2) :: r =>
      if k <? k2 then (k, a) :: t
      else if k2 <? k then (k2, a2) :: tins k a r
      else (k, a + a2) :: r
  end.

Lemma teval_tins : forall v k a t, teval v (tins k a t) = a * nth k v 0 + teval v t.
Proof.
  intros v k a t. induction t as [|[k2 a2] r IH]; cbn [tins]; [reflexivity|].
  destruct (k <? k2) eqn:E1; [reflexivity|].
  destruct (k2 <? k) eqn:E2.
  - cbn [teval]. rewrite IH. lia.
  - apply Nat.ltb_ge in E1, E2. assert (k = k2) by lia. subst k2. cbn. lia.
Qed.

Definition tadd (t1 t2 : list (nat * nat)) : list (nat * nat) :=
  fold_right (fun ka acc => if snd ka =? 0 then acc else tins (fst ka) (snd ka) acc) t2 t1.

Lemma teval_tadd : forall v t1 t2, teval v (tadd t1 t2) = teval v t1 + teval v t2.
Proof.
  intros v t1 t2. induction t1 as [|[k a] r IH]; [reflexivity|].
  cbn [tadd fold_right fst snd teval]. fold (tadd r t2).
  destruct (a =? 0) eqn:E.
  - apply Nat.eqb_eq in E. subst. rewrite IH. lia.
  - rewrite teval_tins, IH. lia.
Qed.

Definition tscale (m : nat) (t : list (nat * nat)) : list (nat * nat) :=
  if m =? 0 then [] else map (fun ka => (fst ka, m * snd ka)) t.

Lemma teval_tscale : forall v m t, teval v (tscale m t) = m * teval v t.
Proof.
  intros v m t. unfold tscale. destruct (m =? 0) eqn:E.
  - apply Nat.eqb_eq in E. subst. reflexivity.
  - induction t as [|[k a] t IH]; cbn; [lia|]. rewrite IH. cbn. lia.
Qed.

Definition aadd (e1 e2 : aexp) : aexp := mkA (a_c e1 + a_c e2) (tadd (a_t e1) (a_t e2)).
Definition aaddc (e : aexp) (n : nat) : aexp := mkA (a_c e + n) (a_t e).
Definition ascale (m : nat) (e : aexp) : aexp := mkA (m * a_c e) (tscale m (a_t e)).
Definition aconst (n : nat) : aexp := mkA n [].

Lemma aeval_aadd : forall v e1 e2, aeval v (aadd e1 e2) = aeval v e1 + aeval v e2.
Proof. intros. unfold aeval, aadd; cbn. rewrite teval_tadd. lia. Qed.

Lemma aeval_aaddc : forall v e n, aeval v (aaddc e n) = aeval v e + n.
Proof. intros. unfold aeval, aaddc; cbn. lia. Qed.

Lemma aeval_ascale : forall v m e, aeval v (ascale m e) = m * aeval v e.
Proof. intros. unfold aeval, ascale; cbn. rewrite teval_tscale. lia. Qed.

(** substitute every variable [k] by [nth k s (aconst 0)] *)
Fixpoint tsubst (s : list aexp) (t : list (nat * nat)) : aexp :=
  match t with
  | [] => aconst 0
  | (k, a) :: t' => aadd (ascale a (nth k s (aconst 0))) (tsubst s t')
  end.

Definition asubst (s : list aexp) (e : aexp) : aexp := aaddc (tsubst s (a_t e)) (a_c e).

Lemma nth_map_aeval : forall v s k,
  nth k (map (aeval v) s) 0 = aeval v (nth k s (aconst 0)).
Proof.
  intros v s k. revert s. induction k as [|k IH]; intros [|x s]; cbn; try reflexivity.
  apply IH.
Qed.

Lemma aeval_tsubst : forall v s t, aeval v (tsubst s t) = teval (map (aeval v) s) t.
Proof.
  intros v s t. induction t as [|[k a] t IH]; [reflexivity|].
  cbn [tsubst teval]. rewrite aeval_aadd, aeval_ascale, IH, nth_map_aeval. reflexivity.
Qed.

Lemma aeval_asubst : forall v s e, aeval v (asubst s e) = aeval (map (aeval v) s) e.
Proof.
  intros v s [c t]. unfold asubst, aeval at 2; cbn [a_c a_t].
  rewrite aeval_aaddc, aeval_tsubst. lia.
Qed.

Fixpoint teqb (t1 t2 : list (nat * nat)) : bool :=
  match t1, t2 with
  | [], [] => true
  | (k1, a1) :: r1, (k2, a2) :: r2 => (k1 =? k2) && (a1 =? a2) && teqb r1 r2
  | _, _ => false
  end.

Lemma teqb_eq : forall t1 t2, teqb t1 t2 = true -> t1 = t2.
Proof.
  induction t1 as [|[k1 a1] r1 IH]; intros [|[k2 a2] r2] H; cbn in H; try discriminate.
  - reflexivity.
  - apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
    apply Nat.eqb_eq in H1, H2. subst. rewrite (IH r2 H3). reflexivity.
Qed.

Definition aeqb (e1 e2 : aexp) : bool := (a_c e1 =? a_c e2) && teqb (a_t e1) (a_t e2).

Lemma aeqb_eq : forall e1 e2, aeqb e1 e2 = true -> e1 = e2.
Proof.
  intros [c1 t1] [c2 t2] H. unfold aeqb in H; cbn in H.
  apply andb_prop in H as [H1 H2]. apply Nat.eqb_eq in H1. apply teqb_eq in H2.
  subst. reflexivity.
Qed.

(** coefficient-wise [e1 <= e2], over the variables [0 .. N-1] *)
Fixpoint tcoef (k : nat) (t : list (nat * nat)) : nat :=
  match t with
  | [] => 0
  | (k', a) :: t' => (if k =? k' then a else 0) + tcoef k t'
  end.

Fixpoint tbound (t : list (nat * nat)) : nat :=
  match t with [] => 0 | (k, _) :: t' => Nat.max (S k) (tbound t') end.

Fixpoint vsum (v : list nat) (t : list (nat * nat)) (ks : list nat) : nat :=
  match ks with [] => 0 | k :: ks' => tcoef k t * nth k v 0 + vsum v t ks' end.

Lemma vsum_app : forall v t l1 l2, vsum v t (l1 ++ l2) = vsum v t l1 + vsum v t l2.
Proof. intros v t l1 l2. induction l1 as [|k l1 IH]; cbn; [reflexivity | rewrite IH; lia]. Qed.

Lemma vsum_single : forall v k a N, k < N ->
  vsum v [(k, a)] (seq 0 N) = a * nth k v 0.
Proof.
  intros v k a N Hk. induction N as [|N IH]; [lia|].
  rewrite seq_S, vsum_app. cbn [vsum tcoef Nat.add].
  destruct (Nat.eq_dec k N) as [-> | Hne].
  - rewrite Nat.eqb_refl.
    assert (Hz : forall l, ~ In N l -> vsum v [(N, a)] l = 0).
    { induction l as [|x l IHl]; intros Hn; [reflexivity|].
      cbn [vsum tcoef]. destruct (x =? N) eqn:E.
      - apply Nat.eqb_eq in E. subst. exfalso. apply Hn. left. reflexivity.
      - rewrite IHl; [lia | intro; apply Hn; right; assumption]. }
    rewrite Hz; [lia|]. intro H. apply in_seq in H. lia.
  - rewrite IH by lia. apply Nat.eqb_neq in Hne. rewrite Nat.eqb_sym, Hne. lia.
Qed.

Lemma vsum_cons : forall v k a t ks,
  vsum v ((k, a) :: t) ks = vsum v [(k, a)] ks + vsum v t ks.
Proof.
  intros v k a t ks. induction ks as [|j ks IH]; [reflexivity|].
  cbn [vsum tcoef]. rewrite IH. cbn [tcoef]. lia.
Qed.

Lemma teval_vsum : forall v t N, tbound t <= N -> teval v t = vsum v t (seq 0 N).
Proof.
  intros v t N. induction t as [|[k a] t IH]; intros H.
  - cbn. clear H. induction (seq 0 N); cbn; [reflexivity | lia].
  - cbn [tbound] in H. cbn [teval]. rewrite vsum_cons, IH by lia.
    rewrite vsum_single by lia. reflexivity.
Qed.

Lemma vsum_le : forall v t1 t2 ks,
  forallb (fun k => tcoef k t1 <=? tcoef k t2) ks = true ->
  vsum v t1 ks <= vsum v t2 ks.
Proof.
  intros v t1 t2 ks. induction ks as [|k ks IH]; intros H; cbn [vsum]; [lia|].
  cbn in H. apply andb_prop in H as [H1 H2]. apply Nat.leb_le in H1.
  specialize (IH H2). pose proof (Nat.mul_le_mono_r _ _ (nth k v 0) H1). lia.
Qed.

Definition ale (e1 e2 : aexp) : bool :=
  let N := Nat.max (tbound (a_t e1)) (tbound (a_t e2)) in
  (a_c e1 <=? a_c e2)
  && forallb (fun k => tcoef k (a_t e1) <=? tcoef k (a_t e2)) (seq 0 N).

Lemma ale_sound : forall v e1 e2, ale e1 e2 = true -> aeval v e1 <= aeval v e2.
Proof.
  intros v [c1 t1] [c2 t2] H. unfold ale in H; cbn [a_c a_t] in H.
  apply andb_prop in H as [Hc Ht]. apply Nat.leb_le in Hc.
  unfold aeval; cbn [a_c a_t].
  set (N := Nat.max (tbound t1) (tbound t2)) in *.
  rewrite (teval_vsum v t1 N), (teval_vsum v t2 N) by lia.
  pose proof (vsum_le v t1 t2 _ Ht). lia.
Qed.

(** ** Segments: literal words and blocks with affine exponents *)

Inductive seg := SL (w : list Sym) | SB (u : list Sym) (e : aexp).

Definition segd (v : list nat) (s : seg) : list Sym :=
  match s with SL w => w | SB u e => rep u (aeval v e) end.

Fixpoint sided (v : list nat) (l : list seg) : list Sym :=
  match l with [] => [] | s :: l' => segd v s ++ sided v l' end.

Lemma sided_app : forall v l1 l2, sided v (l1 ++ l2) = sided v l1 ++ sided v l2.
Proof.
  intros v l1 l2. induction l1 as [|s l1 IH]; cbn; [reflexivity|].
  rewrite IH, app_assoc. reflexivity.
Qed.

Definition seg_subst (s : list aexp) (x : seg) : seg :=
  match x with SL w => SL w | SB u e => SB u (asubst s e) end.

Lemma sided_subst : forall v s l,
  sided v (map (seg_subst s) l) = sided (map (aeval v) s) l.
Proof.
  intros v s l. induction l as [|[w|u e] l IH]; cbn [map sided segd seg_subst];
    [reflexivity | rewrite IH; reflexivity |].
  rewrite IH, aeval_asubst. reflexivity.
Qed.

Lemma rep_mul : forall (v : list Sym) p n, rep (rep v p) n = rep v (p * n).
Proof.
  intros v p n. induction n as [|n IH]; cbn [rep].
  - rewrite Nat.mul_0_r. reflexivity.
  - rewrite IH, <- rep_add. f_equal. lia.
Qed.

Lemma rep_comm : forall (u : list Sym) a b, rep u a ++ rep u b = rep u b ++ rep u a.
Proof. intros. rewrite <- !rep_add. f_equal. lia. Qed.

(** the primitive root of a unit: [u = rep v p] *)
Fixpoint prim_from (u : list Sym) (d fuel : nat) : list Sym * nat :=
  match fuel with
  | 0 => (u, 1)
  | S f =>
      if (length u mod d =? 0) && syms_eqb (rep (firstn d u) (length u / d)) u
      then (firstn d u, length u / d)
      else prim_from u (S d) f
  end.

Definition primroot (u : list Sym) : list Sym * nat := prim_from u 1 (length u).

Lemma prim_from_ok : forall u fuel d v p, prim_from u d fuel = (v, p) -> rep v p = u.
Proof.
  intros u fuel. induction fuel as [|f IH]; intros d v p H; cbn [prim_from] in H.
  - injection H as <- <-. cbn. apply app_nil_r.
  - destruct ((length u mod d =? 0) && syms_eqb (rep (firstn d u) (length u / d)) u) eqn:E.
    + injection H as <- <-. apply andb_prop in E as [_ E]. apply syms_eqb_eq, E.
    + exact (IH _ _ _ H).
Qed.

Lemma primroot_ok : forall u v p, primroot u = (v, p) -> rep v p = u.
Proof. intros u v p. apply prim_from_ok. Qed.

(** counting whole copies of [u] at the front / the back of a word *)
Fixpoint cpre (u w : list Sym) (fuel : nat) : nat * list Sym :=
  match fuel with
  | 0 => (0, w)
  | S f =>
      match u with
      | [] => (0, w)
      | _ :: _ =>
          match strip u w with
          | Some w' => let (n, w'') := cpre u w' f in (S n, w'')
          | None => (0, w)
          end
      end
  end.

Lemma cpre_ok : forall fuel u w n w', cpre u w fuel = (n, w') -> w = rep u n ++ w'.
Proof.
  intros fuel. induction fuel as [|f IH]; intros u w n w' H; cbn [cpre] in H.
  - injection H as <- <-. reflexivity.
  - destruct u as [|x u0]; [injection H as <- <-; reflexivity|].
    destruct (strip (x :: u0) w) as [w1|] eqn:E; [|injection H as <- <-; reflexivity].
    destruct (cpre (x :: u0) w1 f) as [n1 w2] eqn:E1. injection H as <- <-.
    apply strip_sound in E. rewrite E, (IH _ _ _ _ E1). cbn [rep].
    rewrite app_assoc. reflexivity.
Qed.

Fixpoint csuf (u w : list Sym) (fuel : nat) : nat * list Sym :=
  match fuel with
  | 0 => (0, w)
  | S f =>
      match u with
      | [] => (0, w)
      | _ :: _ =>
          match strip_suf u w with
          | Some w' => let (n, w'') := csuf u w' f in (S n, w'')
          | None => (0, w)
          end
      end
  end.

Lemma csuf_ok : forall fuel u w n w', csuf u w fuel = (n, w') -> w = w' ++ rep u n.
Proof.
  intros fuel. induction fuel as [|f IH]; intros u w n w' H; cbn [csuf] in H.
  - injection H as <- <-. rewrite app_nil_r. reflexivity.
  - destruct u as [|x u0]; [injection H as <- <-; rewrite app_nil_r; reflexivity|].
    destruct (strip_suf (x :: u0) w) as [w1|] eqn:E;
      [|injection H as <- <-; rewrite app_nil_r; reflexivity].
    destruct (csuf (x :: u0) w1 f) as [n1 w2] eqn:E1. injection H as <- <-.
    apply strip_suf_sound in E. rewrite E, (IH _ _ _ _ E1).
    rewrite <- app_assoc, rep_shift. reflexivity.
Qed.

(** ** The normalizer: a one-pass builder, the output kept reversed *)

Definition push_blk2 (acc : list seg) (u : list Sym) (e : aexp) : list seg :=
  match acc with
  | SB u' e' :: acc' => if syms_eqb u' u then SB u (aadd e' e) :: acc' else SB u e :: acc
  | _ => SB u e :: acc
  end.

Definition push_blk (acc : list seg) (u : list Sym) (e : aexp) : list seg :=
  match acc with
  | SB u' e' :: acc' => if syms_eqb u' u then SB u (aadd e' e) :: acc' else SB u e :: acc
  | SL w0 :: acc' =>
      let (n, w0') := csuf u w0 (length w0) in
      match n with
      | 0 => SB u e :: acc
      | S _ =>
          match w0' with
          | [] => push_blk2 acc' u (aaddc e n)
          | _ :: _ => SB u (aaddc e n) :: SL w0' :: acc'
          end
      end
  | [] => [SB u e]
  end.

Definition push_lit2 (acc : list seg) (w : list Sym) : list seg :=
  match acc with
  | SB u e :: acc' =>
      let (n, w') := cpre u w (length w) in
      match w' with
      | [] => SB u (aaddc e n) :: acc'
      | _ :: _ => SL w' :: SB u (aaddc e n) :: acc'
      end
  | _ => SL w :: acc
  end.

Definition push_lit (acc : list seg) (w : list Sym) : list seg :=
  match w with
  | [] => acc
  | _ :: _ =>
      match acc with
      | SL w0 :: acc' => push_lit2 acc' (w0 ++ w)
      | _ => push_lit2 acc w
      end
  end.

Definition push (acc : list seg) (x : seg) : list seg :=
  match x with
  | SL w => push_lit acc w
  | SB u e =>
      let (v, p) := primroot u in
      let e' := ascale p e in
      match v with
      | [] => acc
      | _ :: _ =>
          match a_t e' with
          | [] => push_lit acc (rep v (a_c e'))
          | _ :: _ => push_blk acc v e'
          end
      end
  end.

Definition norm (l : list seg) : list seg := rev (fold_left push l []).

Definition rden (v : list nat) (acc : list seg) : list Sym := sided v (rev acc).

Lemma rden_cons : forall v x acc, rden v (x :: acc) = rden v acc ++ segd v x.
Proof.
  intros. unfold rden. cbn [rev]. rewrite sided_app. cbn. rewrite app_nil_r. reflexivity.
Qed.

Lemma push_blk2_ok : forall v acc u e,
  rden v (push_blk2 acc u e) = rden v acc ++ rep u (aeval v e).
Proof.
  intros v acc u e. unfold push_blk2.
  destruct acc as [|[w|u' e'] acc']; try (rewrite rden_cons; reflexivity).
  destruct (syms_eqb u' u) eqn:E; [|rewrite rden_cons; reflexivity].
  apply syms_eqb_eq in E. subst u'.
  rewrite !rden_cons. cbn [segd]. rewrite aeval_aadd, rep_add, app_assoc. reflexivity.
Qed.

Lemma push_blk_ok : forall v acc u e,
  rden v (push_blk acc u e) = rden v acc ++ rep u (aeval v e).
Proof.
  intros v acc u e. unfold push_blk.
  destruct acc as [|[w0|u' e'] acc'].
  - apply (rden_cons v (SB u e) []).
  - destruct (csuf u w0 (length w0)) as [n w0'] eqn:E.
    apply csuf_ok in E.
    destruct n as [|n1]; [rewrite rden_cons; reflexivity|].
    destruct w0' as [|x w1].
    + rewrite push_blk2_ok, rden_cons. cbn [segd]. rewrite E, aeval_aaddc.
      cbn [app]. rewrite <- app_assoc, rep_comm, <- rep_add. reflexivity.
    + rewrite !rden_cons. cbn [segd]. rewrite E, aeval_aaddc.
      rewrite <- !app_assoc. f_equal. f_equal. f_equal.
      rewrite rep_comm, <- rep_add. reflexivity.
  - destruct (syms_eqb u' u) eqn:E; [|rewrite rden_cons; reflexivity].
    apply syms_eqb_eq in E. subst u'.
    rewrite !rden_cons. cbn [segd]. rewrite aeval_aadd, rep_add, app_assoc. reflexivity.
Qed.

Lemma push_lit2_ok : forall v acc w, rden v (push_lit2 acc w) = rden v acc ++ w.
Proof.
  intros v acc w. unfold push_lit2.
  destruct acc as [|[w0|u e] acc']; try (rewrite rden_cons; reflexivity).
  destruct (cpre u w (length w)) as [n w'] eqn:E. apply cpre_ok in E.
  destruct w' as [|x w1].
  - rewrite !rden_cons. cbn [segd]. rewrite E, aeval_aaddc, rep_add, app_nil_r, app_assoc.
    reflexivity.
  - rewrite !rden_cons. cbn [segd]. rewrite E, aeval_aaddc, rep_add, <- !app_assoc.
    reflexivity.
Qed.

Lemma push_lit_ok : forall v acc w, rden v (push_lit acc w) = rden v acc ++ w.
Proof.
  intros v acc w. unfold push_lit.
  destruct w as [|x w]; [rewrite app_nil_r; reflexivity|].
  destruct acc as [|[w0|u e] acc']; try apply push_lit2_ok.
  rewrite push_lit2_ok, rden_cons. cbn [segd]. rewrite app_assoc. reflexivity.
Qed.

Lemma push_ok : forall v acc x, rden v (push acc x) = rden v acc ++ segd v x.
Proof.
  intros v acc [w|u e]; cbn [push segd]; [apply push_lit_ok|].
  destruct (primroot u) as [w0 p] eqn:Ep. apply primroot_ok in Ep.
  rewrite <- Ep, rep_mul.
  destruct w0 as [|y w0].
  - rewrite rep_nil, app_nil_r. reflexivity.
  - destruct (a_t (ascale p e)) as [|t ts] eqn:Et.
    + rewrite push_lit_ok. f_equal. f_equal.
      rewrite <- aeval_ascale. unfold aeval. rewrite Et. cbn. lia.
    + rewrite push_blk_ok, aeval_ascale. reflexivity.
Qed.

Lemma fold_push_ok : forall v l acc,
  rden v (fold_left push l acc) = rden v acc ++ sided v l.
Proof.
  intros v l. induction l as [|x l IH]; intros acc; cbn [fold_left sided].
  - rewrite app_nil_r. reflexivity.
  - rewrite IH, push_ok, app_assoc. reflexivity.
Qed.

Lemma norm_ok : forall v l, sided v (norm l) = sided v l.
Proof.
  intros v l. unfold norm. change (sided v (rev (fold_left push l [])))
    with (rden v (fold_left push l [])).
  rewrite fold_push_ok. reflexivity.
Qed.

(** ** Trailing blanks *)

Fixpoint drop_blanks (w : list Sym) : list Sym :=
  match w with
  | S0 :: w' => drop_blanks w'
  | _ => w
  end.

Definition rstrip0 (w : list Sym) : list Sym := rev (drop_blanks (rev w)).

Lemma drop_blanks_ok : forall w, exists z, w = z ++ drop_blanks w /\ all_blank z = true.
Proof.
  induction w as [|x w IH]; [exists []; split; reflexivity|].
  destruct x; cbn [drop_blanks].
  - destruct IH as (z & Hz & Hb). exists (S0 :: z). cbn. rewrite <- Hz. split; [reflexivity|].
    exact Hb.
  - exists []. split; reflexivity.
Qed.

Lemma all_blank_app : forall a b, all_blank (a ++ b) = all_blank a && all_blank b.
Proof. induction a as [|x a IH]; intros b; cbn; [reflexivity | rewrite IH, andb_assoc; reflexivity]. Qed.

Lemma all_blank_rev : forall a, all_blank (rev a) = all_blank a.
Proof.
  induction a as [|x a IH]; [reflexivity|]. cbn [rev].
  rewrite all_blank_app, IH. cbn. rewrite andb_true_r, andb_comm. reflexivity.
Qed.

Lemma rstrip0_ok : forall w, exists z, w = rstrip0 w ++ z /\ all_blank z = true.
Proof.
  intros w. unfold rstrip0. destruct (drop_blanks_ok (rev w)) as (z & Hz & Hb).
  exists (rev z). split.
  - rewrite <- rev_app_distr, <- Hz, rev_involutive. reflexivity.
  - rewrite all_blank_rev. exact Hb.
Qed.

Lemma all_blank_rep : forall u n, all_blank u = true -> all_blank (rep u n) = true.
Proof.
  intros u n Hu. induction n as [|n IH]; [reflexivity|]. cbn [rep].
  rewrite all_blank_app, Hu, IH. reflexivity.
Qed.

Fixpoint nstrip_r (l : list seg) : list seg :=
  match l with
  | SL w :: l' => match rstrip0 w with [] => nstrip_r l' | w' => SL w' :: l' end
  | SB u e :: l' => if all_blank u then nstrip_r l' else l
  | [] => []
  end.

Definition nstrip (l : list seg) : list seg := rev (nstrip_r (rev l)).

Lemma nstrip_r_ok : forall v r, exists z,
  rden v r = rden v (nstrip_r r) ++ z /\ all_blank z = true.
Proof.
  intros v r. induction r as [|[w|u e] r IH].
  - exists []. split; reflexivity.
  - cbn [nstrip_r]. destruct (rstrip0_ok w) as (z & Hz & Hb).
    destruct (rstrip0 w) as [|y w'] eqn:E.
    + destruct IH as (z' & Hz' & Hb'). exists (z' ++ z). rewrite rden_cons, Hz', Hz.
      cbn [segd app]. rewrite <- app_assoc. split; [reflexivity|].
      rewrite all_blank_app, Hb, Hb'. reflexivity.
    + exists z. rewrite !rden_cons. cbn [segd]. rewrite Hz at 1.
      rewrite app_assoc. split; [reflexivity | exact Hb].
  - cbn [nstrip_r]. destruct (all_blank u) eqn:Eu.
    + destruct IH as (z' & Hz' & Hb'). exists (z' ++ rep u (aeval v e)).
      rewrite rden_cons, Hz'. cbn [segd]. rewrite <- app_assoc. split; [reflexivity|].
      rewrite all_blank_app, Hb', all_blank_rep; auto.
    + exists []. rewrite app_nil_r. split; reflexivity.
Qed.

Lemma lpad_eqb_app_blank : forall x z, all_blank z = true -> lpad_eqb (x ++ z) x = true.
Proof.
  intros x z Hz. induction x as [|y x IH]; cbn [app].
  - induction z as [|a z IHz]; [reflexivity|].
    cbn in Hz |- *. apply andb_prop in Hz as [H1 H2]. rewrite H1, IHz by exact H2.
    reflexivity.
  - cbn [lpad_eqb]. rewrite IH, andb_true_r. apply sym_eqb_spec. reflexivity.
Qed.

Lemma nstrip_ok : forall v l, lift_side (sided v l) = lift_side (sided v (nstrip l)).
Proof.
  intros v l. destruct (nstrip_r_ok v (rev l)) as (z & Hz & Hb).
  unfold rden in Hz. rewrite rev_involutive in Hz. unfold nstrip.
  rewrite Hz. apply lpad_eqb_lift. apply lpad_eqb_app_blank. exact Hb.
Qed.

(** ** Structural equality of segment lists *)

Definition seg_eqb (x y : seg) : bool :=
  match x, y with
  | SL w1, SL w2 => syms_eqb w1 w2
  | SB u1 e1, SB u2 e2 => syms_eqb u1 u2 && aeqb e1 e2
  | _, _ => false
  end.

Fixpoint segs_eqb (l1 l2 : list seg) : bool :=
  match l1, l2 with
  | [], [] => true
  | x :: l1', y :: l2' => seg_eqb x y && segs_eqb l1' l2'
  | _, _ => false
  end.

Lemma segs_eqb_eq : forall l1 l2, segs_eqb l1 l2 = true -> l1 = l2.
Proof.
  induction l1 as [|x l1 IH]; intros [|y l2] H; cbn in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H1 H2]. rewrite (IH _ H2). f_equal.
  destruct x as [w1|u1 e1], y as [w2|u2 e2]; cbn in H1; try discriminate.
  - apply syms_eqb_eq in H1. subst. reflexivity.
  - apply andb_prop in H1 as [Hu He]. apply syms_eqb_eq in Hu. apply aeqb_eq in He.
    subst. reflexivity.
Qed.

(** exact: the two lists denote the same word for every assignment *)
Definition same_segs (l1 l2 : list seg) : bool := segs_eqb (norm l1) (norm l2).

Lemma same_segs_ok : forall v l1 l2, same_segs l1 l2 = true -> sided v l1 = sided v l2.
Proof.
  intros v l1 l2 H. apply segs_eqb_eq in H.
  rewrite <- (norm_ok v l1), <- (norm_ok v l2), H. reflexivity.
Qed.

(** up to trailing blanks *)
Definition lsame_segs (l1 l2 : list seg) : bool := segs_eqb (nstrip (norm l1)) (nstrip (norm l2)).

Lemma lsame_segs_ok : forall v l1 l2, lsame_segs l1 l2 = true ->
  lift_side (sided v l1) = lift_side (sided v l2).
Proof.
  intros v l1 l2 H. apply segs_eqb_eq in H.
  rewrite <- (norm_ok v l1), <- (norm_ok v l2), (nstrip_ok v (norm l1)),
    (nstrip_ok v (norm l2)), H.
  reflexivity.
Qed.

(** ** Families, dispatch trees, leaves *)

(** a dispatch tree is an array of nodes, node 0 the root.  [TSplit k n p
    kids]: on variable [k], the values [0 .. n-1] go to [kids[0 .. n-1]]
    and the value [n + p*q + s] to [kids[n + s]] with [q] the new
    parameter. *)
Inductive tnode := TLeaf (l : nat) | TSplit (k n p : nat) (kids : list nat).

Record tfam := mkTF {
  tf_q    : St;
  tf_h    : Sym;
  tf_L    : list seg;        (** nearest-first, exponents over the variables *)
  tf_R    : list seg;
  tf_n    : nat;             (** number of variables *)
  tf_tree : list tnode
}.

Record tleaf := mkTL {
  tl_f     : nat;               (** its family *)
  tl_reg   : list (nat * nat);  (** region: [x_k = M_k * z_k + c_k] *)
  tl_g     : nat;               (** target family *)
  tl_tgt   : list aexp;         (** target values, affine in [z] *)
  tl_c0    : sconf;
  tl_j     : nat;               (** the chain index is [z_j] *)
  tl_el    : bool;
  tl_er    : bool;
  tl_nL    : nat;               (** pattern segments the chain start replaces *)
  tl_nR    : nat;
  tl_chain : list lstep
}.

Definition tinst (f : tfam) (vals : list nat) : cconf :=
  (tf_q f, (sided vals (tf_L f), tf_h f, sided vals (tf_R f))).

Definition reg1 (k : nat) (Mc : nat * nat) : aexp :=
  mkA (snd Mc) (if fst Mc =? 0 then [] else [(k, fst Mc)]).

Definition rsub (R : list (nat * nat)) : list aexp :=
  map (fun kMc => reg1 (fst kMc) (snd kMc)) (combine (seq 0 (length R)) R).

Definition rv (R : list (nat * nat)) (z : list nat) (k : nat) : nat :=
  fst (nth k R (0, 0)) * nth k z 0 + snd (nth k R (0, 0)).

Lemma aeval_reg1 : forall z k Mc, aeval z (reg1 k Mc) = fst Mc * nth k z 0 + snd Mc.
Proof.
  intros z k [M c]. unfold reg1, aeval; cbn [a_c a_t fst snd].
  destruct (M =? 0) eqn:E; cbn.
  - apply Nat.eqb_eq in E. subst. lia.
  - lia.
Qed.

Lemma rsub_nth : forall z R k, k < length R ->
  nth k (map (aeval z) (rsub R)) 0 = rv R z k.
Proof.
  intros z R k Hk. unfold rsub, rv. rewrite map_map.
  assert (H : forall s, nth k (map (fun x => aeval z (reg1 (fst x) (snd x)))
                                  (combine (seq s (length R)) R)) 0
                   = fst (nth k R (0, 0)) * nth (s + k) z 0 + snd (nth k R (0, 0))).
  { revert k Hk. induction R as [|Mc R IH]; intros k Hk s; [cbn in Hk; lia|].
    destruct k as [|k]; cbn [length seq combine map nth].
    - rewrite aeval_reg1, Nat.add_0_r. reflexivity.
    - cbn [length] in Hk. rewrite IH by lia. rewrite Nat.add_succ_r. reflexivity. }
  rewrite H. reflexivity.
Qed.

Lemma rsub_length : forall R, length (rsub R) = length R.
Proof.
  intros R. unfold rsub. rewrite map_length, combine_length, seq_length. lia.
Qed.

(** the chain start/end sides as segments, the index being [z_j] *)
Definition ss_segs (s : sside) (j : nat) : list seg :=
  [SL (s_pre s); SB (s_u s) (mkA (s_b s) (if s_a s =? 0 then [] else [(j, s_a s)]));
   SL (s_post s)].

Lemma ss_segs_ok : forall z j s X,
  sden X (nth j z 0) s = sided z (ss_segs s j) ++ X.
Proof.
  intros z j [pre u a b post] X. unfold sden, ss_segs, aeval; cbn.
  rewrite app_nil_r, <- !app_assoc. f_equal. f_equal.
  - f_equal. destruct (a =? 0) eqn:E; cbn.
    + apply Nat.eqb_eq in E. subst. lia.
    + lia.
Qed.

Definition leaf_ok (tmw : TM) (fams : list tfam) (f : tfam) (l : tleaf) : bool :=
  let sub := rsub (tl_reg l) in
  let Lz := map (seg_subst sub) (tf_L f) in
  let Rz := map (seg_subst sub) (tf_R f) in
  let c0 := tl_c0 l in
  match nth_error fams (tl_g l), srun tmw (tl_el l) (tl_er l) (tl_chain l) c0 with
  | Some g, Some (c1, _, cb) =>
      st_eqb (c_st c0) (tf_q f) && sym_eqb (c_h c0) (tf_h f)
      && same_segs (ss_segs (c_l c0) (tl_j l) ++ skipn (tl_nL l) Lz) Lz
      && same_segs (ss_segs (c_r c0) (tl_j l) ++ skipn (tl_nR l) Rz) Rz
      && (negb (tl_el l) || (length Lz <=? tl_nL l))
      && (negb (tl_er l) || (length Rz <=? tl_nR l))
      && st_eqb (c_st c1) (tf_q g) && sym_eqb (c_h c1) (tf_h g)
      && lsame_segs (ss_segs (c_l c1) (tl_j l) ++ skipn (tl_nL l) Lz)
                    (map (seg_subst (tl_tgt l)) (tf_L g))
      && lsame_segs (ss_segs (c_r c1) (tl_j l) ++ skipn (tl_nR l) Rz)
                    (map (seg_subst (tl_tgt l)) (tf_R g))
      && (0 <? cb) && (length (tl_tgt l) =? tf_n g) && (length (tl_reg l) =? tf_n f)
  | _, _ => false
  end.

Lemma skipn_all_le : forall {A} n (l : list A), length l <= n -> skipn n l = [].
Proof.
  intros A n. induction n as [|n IH]; intros [|x l] H; cbn in *; try reflexivity; [lia|].
  apply IH. lia.
Qed.

Lemma leaf_ok_inv : forall tmw fams f l, leaf_ok tmw fams f l = true ->
  exists g c1 ca cb,
    nth_error fams (tl_g l) = Some g
    /\ srun tmw (tl_el l) (tl_er l) (tl_chain l) (tl_c0 l) = Some (c1, ca, cb)
    /\ c_st (tl_c0 l) = tf_q f /\ c_h (tl_c0 l) = tf_h f
    /\ same_segs (ss_segs (c_l (tl_c0 l)) (tl_j l)
                   ++ skipn (tl_nL l) (map (seg_subst (rsub (tl_reg l))) (tf_L f)))
                  (map (seg_subst (rsub (tl_reg l))) (tf_L f)) = true
    /\ same_segs (ss_segs (c_r (tl_c0 l)) (tl_j l)
                   ++ skipn (tl_nR l) (map (seg_subst (rsub (tl_reg l))) (tf_R f)))
                  (map (seg_subst (rsub (tl_reg l))) (tf_R f)) = true
    /\ (tl_el l = true -> length (tf_L f) <= tl_nL l)
    /\ (tl_er l = true -> length (tf_R f) <= tl_nR l)
    /\ c_st c1 = tf_q g /\ c_h c1 = tf_h g
    /\ lsame_segs (ss_segs (c_l c1) (tl_j l)
                   ++ skipn (tl_nL l) (map (seg_subst (rsub (tl_reg l))) (tf_L f)))
                  (map (seg_subst (tl_tgt l)) (tf_L g)) = true
    /\ lsame_segs (ss_segs (c_r c1) (tl_j l)
                   ++ skipn (tl_nR l) (map (seg_subst (rsub (tl_reg l))) (tf_R f)))
                  (map (seg_subst (tl_tgt l)) (tf_R g)) = true
    /\ 0 < cb /\ length (tl_tgt l) = tf_n g /\ length (tl_reg l) = tf_n f.
Proof.
  intros tmw fams f l H. unfold leaf_ok in H.
  destruct (nth_error fams (tl_g l)) as [g|]; [|discriminate].
  destruct (srun tmw (tl_el l) (tl_er l) (tl_chain l) (tl_c0 l)) as [[[c1 ca] cb]|];
    [|discriminate].
  apply andb_prop in H as [H H13]. apply andb_prop in H as [H H12].
  apply andb_prop in H as [H H11]. apply andb_prop in H as [H H10].
  apply andb_prop in H as [H H9]. apply andb_prop in H as [H H8].
  apply andb_prop in H as [H H7]. apply andb_prop in H as [H H6].
  apply andb_prop in H as [H H5]. apply andb_prop in H as [H H4].
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  exists g, c1, ca, cb.
  apply st_eqb_spec in H1, H7. apply sym_eqb_spec in H2, H8.
  apply Nat.ltb_lt in H11. apply Nat.eqb_eq in H12, H13.
  rewrite map_length in H5, H6.
  repeat split; auto.
  - intros He. rewrite He in H5. apply Nat.leb_le. exact H5.
  - intros He. rewrite He in H6. apply Nat.leb_le. exact H6.
Qed.

(** the chain start IS the anchor, for every [z] *)
Lemma leaf_start : forall tmw fams f l, leaf_ok tmw fams f l = true -> forall z,
  let sub := rsub (tl_reg l) in
  let XL := sided z (skipn (tl_nL l) (map (seg_subst sub) (tf_L f))) in
  let XR := sided z (skipn (tl_nR l) (map (seg_subst sub) (tf_R f))) in
  tinst f (map (aeval z) sub) = cden XL XR (nth (tl_j l) z 0) (tl_c0 l)
  /\ (tl_el l = true -> XL = []) /\ (tl_er l = true -> XR = []).
Proof.
  intros tmw fams f l H z sub XL XR.
  destruct (leaf_ok_inv _ _ _ _ H) as (g & c1 & ca & cb & _ & _ & Hq & Hh & HL & HR
    & Hel & Her & _).
  pose proof (same_segs_ok z _ _ HL) as EL. pose proof (same_segs_ok z _ _ HR) as ER.
  split; [| split].
  - unfold tinst, cden. rewrite <- Hq, <- Hh. subst sub XL XR.
    rewrite <- !sided_subst, !ss_segs_ok, <- !sided_app, EL, ER.
    destruct (tl_c0 l). reflexivity.
  - intros He. subst XL. rewrite skipn_all_le; [reflexivity|].
    rewrite map_length. exact (Hel He).
  - intros He. subst XR. rewrite skipn_all_le; [reflexivity|].
    rewrite map_length. exact (Her He).
Qed.

Lemma leaf_lap : forall tmw fams f l g, leaf_ok tmw fams f l = true ->
  nth_error fams (tl_g l) = Some g -> forall z,
  exists n c', csteps tmw n (tinst f (map (aeval z) (rsub (tl_reg l)))) = Some c'
          /\ lift c' = lift (tinst g (map (aeval z) (tl_tgt l))) /\ 0 < n.
Proof.
  intros tmw fams f l g H Hg z.
  destruct (leaf_start tmw fams f l H z) as (Hst & HL & HR).
  destruct (leaf_ok_inv _ _ _ _ H) as (g' & c1 & ca & cb & Hg' & Er & _ & _ & _ & _
    & _ & _ & Hq1 & Hh1 & HL1 & HR1 & Hcb & _).
  rewrite Hg in Hg'. injection Hg' as <-.
  pose proof (lsame_segs_ok z _ _ HL1) as EL. pose proof (lsame_segs_ok z _ _ HR1) as ER.
  exists (ca * nth (tl_j l) z 0 + cb), (cden (sided z (skipn (tl_nL l)
      (map (seg_subst (rsub (tl_reg l))) (tf_L f))))
    (sided z (skipn (tl_nR l) (map (seg_subst (rsub (tl_reg l))) (tf_R f))))
    (nth (tl_j l) z 0) c1).
  split; [| split; [| lia]].
  - rewrite Hst. exact (srun_sound _ _ _ _ _ _ _ _ Er _ _ _ HL HR).
  - unfold cden, tinst, lift, lift_tape; cbn [fst snd]. rewrite <- Hq1, <- Hh1.
    rewrite !ss_segs_ok, <- !sided_app, EL, ER, !sided_subst. reflexivity.
Qed.

(** ** The walk *)

Fixpoint replace {A} (k : nat) (x : A) (l : list A) : list A :=
  match l, k with
  | [], _ => []
  | _ :: l', 0 => x :: l'
  | y :: l', S k' => y :: replace k' x l'
  end.

Lemma nth_replace_eq : forall {A} k (x : A) l d, k < length l -> nth k (replace k x l) d = x.
Proof.
  intros A k x l d. revert k. induction l as [|y l IH]; intros [|k] H; cbn in *;
    [lia | lia | reflexivity | apply IH; lia].
Qed.

Lemma nth_replace_ge : forall {A} k (x : A) l d, length l <= k -> nth k (replace k x l) d = d.
Proof.
  intros A k x l d. revert k. induction l as [|y l IH]; intros [|k] H; cbn in *;
    [reflexivity | reflexivity | lia | apply IH; lia].
Qed.

Lemma nth_replace_ne : forall {A} k k' (x : A) l d, k' <> k ->
  nth k' (replace k x l) d = nth k' l d.
Proof.
  intros A k k' x l d. revert k k'. induction l as [|y l IH]; intros [|k] [|k'] H; cbn;
    try reflexivity; try lia. apply IH. lia.
Qed.

Fixpoint twalk (nodes : list tnode) (fuel i : nat) (R : list (nat * nat)) (z : list nat)
  : option (nat * list (nat * nat) * list nat) :=
  match fuel with
  | 0 => None
  | S fu =>
      match nth_error nodes i with
      | Some (TLeaf l) => Some (l, R, z)
      | Some (TSplit k n p kids) =>
          let zk := nth k z 0 in
          let M := fst (nth k R (0, 0)) in
          let c := snd (nth k R (0, 0)) in
          if zk <? n then
            match nth_error kids zk with
            | Some i' => twalk nodes fu i' (replace k (0, c + M * zk) R) (replace k 0 z)
            | None => None
            end
          else
            match nth_error kids (n + (zk - n) mod p) with
            | Some i' => twalk nodes fu i' (replace k (M * p, c + M * (n + (zk - n) mod p)) R)
                               (replace k ((zk - n) / p) z)
            | None => None
            end
      | None => None
      end
  end.

Fixpoint ocat {A} (l : list (option (list A))) : option (list A) :=
  match l with
  | [] => Some []
  | Some x :: l' => match ocat l' with Some y => Some (x ++ y) | None => None end
  | None :: _ => None
  end.

Fixpoint tleaves (nodes : list tnode) (fuel i : nat) (R : list (nat * nat))
  : option (list (nat * list (nat * nat))) :=
  match fuel with
  | 0 => None
  | S fu =>
      match nth_error nodes i with
      | Some (TLeaf l) => Some [(l, R)]
      | Some (TSplit k n p kids) =>
          if (p =? 0) || negb (length kids =? n + p) || negb (k <? length R) then None else
          let M := fst (nth k R (0, 0)) in
          let c := snd (nth k R (0, 0)) in
          ocat (map (fun jc => tleaves nodes fu (snd jc)
                                 (replace k (if fst jc <? n then (0, c + M * fst jc)
                                             else (M * p, c + M * fst jc)) R))
                    (combine (seq 0 (n + p)) kids))
      | None => None
      end
  end.

Lemma ocat_in : forall {A} (l : list (option (list A))) L x ys,
  ocat l = Some L -> In (Some ys) l -> In x ys -> In x L.
Proof.
  intros A l. induction l as [|[o|] l IH]; intros L x ys H Hin Hx; cbn in H.
  - destruct Hin.
  - destruct (ocat l) as [y|] eqn:E in H; [|discriminate]. injection H as <-.
    destruct Hin as [Hin | Hin].
    + injection Hin as ->. apply in_or_app. left. exact Hx.
    + apply in_or_app. right. exact (IH _ _ _ E Hin Hx).
  - discriminate.
Qed.

Lemma ocat_some : forall {A} (l : list (option (list A))) L o,
  ocat l = Some L -> In o l -> exists ys, o = Some ys.
Proof.
  intros A l. induction l as [|[x|] l IH]; intros L o H Hin; cbn in H.
  - destruct Hin.
  - destruct (ocat l) as [y|] eqn:E in H; [|discriminate].
    destruct Hin as [<- | Hin]; [exists x; reflexivity | exact (IH _ _ E Hin)].
  - discriminate.
Qed.

Lemma in_combine_seq : forall {A} (kids : list A) j i', nth_error kids j = Some i' ->
  forall s, In (s + j, i') (combine (seq s (length kids)) kids).
Proof.
  intros A kids. induction kids as [|x kids IH]; intros [|j] i' H s; cbn in H |- *;
    try discriminate.
  - injection H as ->. left. rewrite Nat.add_0_r. reflexivity.
  - right. rewrite <- Nat.add_succ_comm. apply IH. exact H.
Qed.

Lemma replace_length : forall {A} k (x : A) l, length (replace k x l) = length l.
Proof.
  intros A k x l. revert k. induction l as [|y l IH]; intros [|k]; cbn; auto.
Qed.

Lemma twalk_total : forall nodes fuel i R L, tleaves nodes fuel i R = Some L ->
  forall z, length z = length R -> exists l R' z', twalk nodes fuel i R z = Some (l, R', z')
    /\ In (l, R') L /\ (forall k, rv R z k = rv R' z' k) /\ length z' = length R'.
Proof.
  intros nodes fuel. induction fuel as [|fu IH]; intros i R L H z Hzl; cbn [tleaves] in H;
    [discriminate|].
  cbn [twalk].
  destruct (nth_error nodes i) as [[l|k n p kids]|]; [| |discriminate].
  - injection H as <-. exists l, R, z. split; [reflexivity|]. split; [left; reflexivity|].
    split; [intros; reflexivity | exact Hzl].
  - destruct ((p =? 0) || negb (length kids =? n + p) || negb (k <? length R)) eqn:Ebad;
      [discriminate|].
    apply orb_false_iff in Ebad as [Ebad HkR]. apply orb_false_iff in Ebad as [Hp Hlen].
    apply Nat.eqb_neq in Hp. apply negb_false_iff, Nat.eqb_eq in Hlen.
    apply negb_false_iff, Nat.ltb_lt in HkR.
    remember (fst (nth k R (0, 0))) as M eqn:EM.
    remember (snd (nth k R (0, 0))) as c eqn:Ec.
    remember (nth k z 0) as zk eqn:Ezk.
    (* the kid taken, its region and its parameter *)
    assert (Hbr : exists j zk2,
      j < n + p /\ M * zk + c = fst (if j <? n then (0, c + M * j) else (M * p, c + M * j)) * zk2
                                + snd (if j <? n then (0, c + M * j) else (M * p, c + M * j))
      /\ (if zk <? n then (zk, replace k 0 z)
          else (n + (zk - n) mod p, replace k ((zk - n) / p) z)) = (j, replace k zk2 z)).
    { destruct (zk <? n) eqn:E.
      - exists zk, 0. rewrite E. apply Nat.ltb_lt in E.
        split; [lia|]. split; [cbn; lia | reflexivity].
      - apply Nat.ltb_ge in E.
        pose proof (Nat.mod_upper_bound (zk - n) p Hp) as Hub.
        exists (n + (zk - n) mod p), ((zk - n) / p).
        split; [lia|]. split; [|reflexivity].
        destruct (n + (zk - n) mod p <? n) eqn:E2; [apply Nat.ltb_lt in E2; lia|].
        cbn [fst snd]. pose proof (Nat.div_mod (zk - n) p Hp). nia. }
    destruct Hbr as (j & zk2 & Hj & Hval & Hjz).
    set (Mc2 := if j <? n then (0, c + M * j) else (M * p, c + M * j)) in Hval.
    assert (Hjk : j < length kids) by lia.
    destruct (nth_error kids j) as [i'|] eqn:Ei.
    2: { apply nth_error_None in Ei. lia. }
    assert (Hin : In (j, i') (combine (seq 0 (n + p)) kids)).
    { rewrite <- Hlen. exact (in_combine_seq kids j i' Ei 0). }
    pose proof (in_map (fun jc => tleaves nodes fu (snd jc)
                          (replace k (if fst jc <? n then (0, c + M * fst jc)
                                      else (M * p, c + M * fst jc)) R)) _ _ Hin) as Hin2.
    cbn [fst snd] in Hin2. fold Mc2 in Hin2.
    destruct (ocat_some _ _ _ H Hin2) as (ys & Hys).
    rewrite Hys in Hin2.
    assert (Hzl2 : length (replace k zk2 z) = length (replace k Mc2 R))
      by (rewrite !replace_length; exact Hzl).
    destruct (IH i' (replace k Mc2 R) ys Hys (replace k zk2 z) Hzl2)
      as (l & R' & z' & Hw & HinL & Hrv & HzR).
    exists l, R', z'. split; [| split; [| split; [| exact HzR]]].
    + subst Mc2. destruct (zk <? n) eqn:E; injection Hjz as Ej Ez; subst j.
      * rewrite Ei, Ez. rewrite E in Hw. exact Hw.
      * rewrite Ei, Ez.
        destruct (n + (zk - n) mod p <? n) eqn:E2; [apply Nat.ltb_lt in E2; lia|].
        exact Hw.
    + exact (ocat_in _ _ _ _ H Hin2 HinL).
    + intros k'. rewrite <- Hrv. unfold rv.
      destruct (Nat.eq_dec k' k) as [-> | Hne].
      2: { rewrite !nth_replace_ne by exact Hne. reflexivity. }
      rewrite <- EM, <- Ec, <- Ezk.
      rewrite nth_replace_eq by exact HkR. rewrite nth_replace_eq by lia. exact Hval.
Qed.

(** ** Families checked, and the enumeration *)

Definition R0 (n : nat) : list (nat * nat) := repeat (1, 0) n.

Definition fwalk (F : tfam) (vals : list nat) :=
  twalk (tf_tree F) (length (tf_tree F)) 0 (R0 (tf_n F)) vals.

Definition fleaves (F : tfam) := tleaves (tf_tree F) (length (tf_tree F)) 0 (R0 (tf_n F)).

Fixpoint regeqb (R1 R2 : list (nat * nat)) : bool :=
  match R1, R2 with
  | [], [] => true
  | (a, b) :: R1', (c, d) :: R2' => (a =? c) && (b =? d) && regeqb R1' R2'
  | _, _ => false
  end.

Lemma regeqb_eq : forall R1 R2, regeqb R1 R2 = true -> R1 = R2.
Proof.
  induction R1 as [|[a b] R1 IH]; intros [|[c d] R2] H; cbn in H; try discriminate;
    [reflexivity|].
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Nat.eqb_eq in H1, H2. subst. rewrite (IH _ H3). reflexivity.
Qed.

Definition fam_ok (tmw : TM) (fams : list tfam) (leaves : list tleaf) (fi : nat) (F : tfam)
  : bool :=
  match fleaves F with
  | Some L =>
      forallb (fun lR => match nth_error leaves (fst lR) with
                         | Some lf => (tl_f lf =? fi) && regeqb (tl_reg lf) (snd lR)
                                      && leaf_ok tmw fams F lf
                         | None => false
                         end) L
  | None => false
  end.

Definition fams_ok (tmw : TM) (fams : list tfam) (leaves : list tleaf) : bool :=
  forallb (fun fF => fam_ok tmw fams leaves (fst fF) (snd fF))
          (combine (seq 0 (length fams)) fams).

Section Enum.

Variable tmw : TM.
Variable fams : list tfam.
Variable leaves : list tleaf.
Hypothesis Hfams : fams_ok tmw fams leaves = true.

Definition tanc (a : nat * list nat) : cconf :=
  match nth_error fams (fst a) with Some F => tinst F (snd a) | None => c0 end.

Definition tnxt (a : nat * list nat) : nat * list nat :=
  match nth_error fams (fst a) with
  | Some F =>
      match fwalk F (snd a) with
      | Some (l, _, z) =>
          match nth_error leaves l with
          | Some lf => (tl_g lf, map (aeval z) (tl_tgt lf))
          | None => a
          end
      | None => a
      end
  | None => a
  end.

Definition Good (a : nat * list nat) : Prop :=
  exists F, nth_error fams (fst a) = Some F /\ length (snd a) = tf_n F.

Lemma fam_ok_of : forall fi F, nth_error fams fi = Some F -> fam_ok tmw fams leaves fi F = true.
Proof.
  intros fi F H. unfold fams_ok in Hfams. rewrite forallb_forall in Hfams.
  apply (Hfams (fi, F)).
  assert (Hlt : fi < length fams) by (apply nth_error_Some; rewrite H; discriminate).
  assert (Hc : forall s, nth_error (combine (seq s (length fams)) fams) fi = Some (s + fi, F)).
  { clear Hfams. revert fi H Hlt.
    induction fams as [|x fs IH]; intros [|fi] H Hlt s; cbn in *; try discriminate; try lia.
    - injection H as ->. rewrite Nat.add_0_r. reflexivity.
    - rewrite <- Nat.add_succ_comm. apply IH; [exact H | lia]. }
  specialize (Hc 0).
  apply nth_error_In in Hc. exact Hc.
Qed.

Lemma nth_repeat_lt' : forall {A} (x d : A) n k, k < n -> nth k (repeat x n) d = x.
Proof.
  intros A x d n. induction n as [|n IH]; intros [|k] Hk; cbn; try lia; [reflexivity|].
  apply IH. lia.
Qed.

Lemma rv_R0 : forall n vals k, length vals = n -> rv (R0 n) vals k = nth k vals 0.
Proof.
  intros n vals k Hl. unfold rv, R0.
  destruct (lt_dec k n) as [Hk | Hk].
  - rewrite nth_repeat_lt' by exact Hk. cbn. lia.
  - rewrite nth_overflow by (rewrite repeat_length; lia).
    rewrite nth_overflow by lia. reflexivity.
Qed.

(** what a walk yields: the leaf, checked, and the values as its region *)
Lemma walk_leaf : forall a, Good a -> exists F lf l R z,
  nth_error fams (fst a) = Some F /\ fwalk F (snd a) = Some (l, R, z)
  /\ nth_error leaves l = Some lf /\ tl_f lf = fst a /\ tl_reg lf = R
  /\ leaf_ok tmw fams F lf = true /\ snd a = map (aeval z) (rsub R)
  /\ length z = length R.
Proof.
  intros [fi vals] (F & HF & Hl). cbn [fst snd] in *.
  pose proof (fam_ok_of fi F HF) as Hok. unfold fam_ok in Hok.
  destruct (fleaves F) as [L|] eqn:EL; [|discriminate].
  assert (Hzl : length vals = length (R0 (tf_n F))) by (unfold R0; rewrite repeat_length; exact Hl).
  destruct (twalk_total _ _ _ _ _ EL vals Hzl) as (l & R & z & Hw & Hin & Hrv & HzR).
  rewrite forallb_forall in Hok. specialize (Hok _ Hin). cbn [fst snd] in Hok.
  destruct (nth_error leaves l) as [lf|] eqn:Elf; [|discriminate].
  apply andb_prop in Hok as [Hok Hlo]. apply andb_prop in Hok as [Hf Hreg].
  apply Nat.eqb_eq in Hf. apply regeqb_eq in Hreg.
  exists F, lf, l, R, z. repeat split; auto.
  destruct (leaf_ok_inv _ _ _ _ Hlo) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
    & _ & _ & _ & _ & _ & HlenR).
  rewrite Hreg in HlenR.
  apply nth_ext with (d := 0) (d' := 0).
  - rewrite map_length, rsub_length. lia.
  - intros k Hk. rewrite rsub_nth by lia. rewrite <- Hrv. symmetry. apply rv_R0. exact Hl.
Qed.

Lemma step_ok : forall a, Good a ->
  (exists n c', csteps tmw n (tanc a) = Some c' /\ lift c' = lift (tanc (tnxt a)) /\ 0 < n)
  /\ Good (tnxt a).
Proof.
  intros a Ha.
  destruct (walk_leaf a Ha) as (F & lf & l & R & z & HF & Hw & Hlf & _ & HR & Hok & Hv & _).
  destruct (leaf_ok_inv _ _ _ _ Hok) as (g & _ & _ & _ & Hg & _ & _ & _ & _ & _ & _ & _ & _
    & _ & _ & _ & _ & Htl & _).
  unfold tanc, tnxt. rewrite HF, Hw, Hlf. cbn [fst snd]. rewrite Hg.
  split.
  - rewrite Hv, <- HR. exact (leaf_lap _ _ _ _ _ Hok Hg z).
  - exists g. split; [exact Hg|]. cbn [snd]. rewrite map_length. exact Htl.
Qed.

End Enum.

(** ** Fires: every chain prefix of a leaf, from every anchor taking it *)

Definition cuts (st : lstep) : list lstep :=
  match st with
  | SWin n => map SWin (seq 1 n)
  | SWinL n => map SWinL (seq 1 n)
  | SWinR n => map SWinR (seq 1 n)
  | _ => [st]
  end.

Fixpoint prefs (l : list lstep) : list (list lstep) :=
  match l with
  | [] => [[]]
  | st :: l' => [] :: map (fun x => [x]) (cuts st) ++ map (cons st) (prefs l')
  end.

Definition leaf_fired (tmw : TM) (l : tleaf) : list Instr :=
  flat_map (fun pr => match srun_instr tmw (tl_el l) (tl_er l) pr (tl_c0 l) with
                      | Some t => [t]
                      | None => []
                      end) (prefs (tl_chain l)).

Lemma leaf_fires : forall tmw fams f l t, leaf_ok tmw fams f l = true ->
  In t (leaf_fired tmw l) -> forall z,
  exists k c, csteps tmw k (tinst f (map (aeval z) (rsub (tl_reg l)))) = Some c
              /\ cinstr c = t.
Proof.
  intros tmw fams f l t Hok Hin z.
  unfold leaf_fired in Hin. apply in_flat_map in Hin as (pr & _ & Hpr).
  destruct (srun_instr tmw (tl_el l) (tl_er l) pr (tl_c0 l)) as [t'|] eqn:E;
    [|destruct Hpr].
  destruct Hpr as [<- | []].
  destruct (leaf_start _ _ _ _ Hok z) as (Hst & HL & HR).
  exact (fire_of_run_instr tmw (fun _ => tinst f (map (aeval z) (rsub (tl_reg l))))
           (tl_el l) (tl_er l) pr (tl_c0 l) xH (nth (tl_j l) z 0) _ _ t' E HL HR Hst).
Qed.

(** ** Liveness: a closed set of nodes (leaf, values mod P), and rankings *)

Definition modl (P : nat) (v : list nat) : list nat := map (fun x => x mod P) v.

Fixpoint nat_list_eqb (a b : list nat) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => (x =? y) && nat_list_eqb a' b'
  | _, _ => false
  end.

Lemma nat_list_eqb_eq : forall a b, nat_list_eqb a b = true -> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b] H; cbn in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H1 H2]. apply Nat.eqb_eq in H1. subst. rewrite (IH _ H2).
  reflexivity.
Qed.

Lemma nat_list_eqb_refl : forall a, nat_list_eqb a a = true.
Proof. induction a as [|x a IH]; cbn; [reflexivity | rewrite Nat.eqb_refl, IH; reflexivity]. Qed.

Fixpoint nidx (NS : list (nat * list nat)) (l : nat) (rho : list nat) : option nat :=
  match NS with
  | [] => None
  | (l', r') :: NS' =>
      if (l' =? l) && nat_list_eqb r' rho then Some 0
      else match nidx NS' l rho with Some i => Some (S i) | None => None end
  end.

Lemma nidx_ok : forall NS l rho i, nidx NS l rho = Some i -> nth_error NS i = Some (l, rho).
Proof.
  induction NS as [|[l' r'] NS IH]; intros l rho i H; cbn in H; [discriminate|].
  destruct ((l' =? l) && nat_list_eqb r' rho) eqn:E.
  - injection H as <-. apply andb_prop in E as [E1 E2].
    apply Nat.eqb_eq in E1. apply nat_list_eqb_eq in E2. subst. reflexivity.
  - destruct (nidx NS l rho) as [j|] eqn:Ej; [|discriminate].
    injection H as <-. cbn. exact (IH _ _ _ Ej).
Qed.

(** the residue classes of the leaf parameters that fit a node *)
Fixpoint sassign (P : nat) (R : list (nat * nat)) (rho : list nat) : list (list nat) :=
  match R, rho with
  | [], _ => [[]]
  | (M, c) :: R', r :: rho' =>
      flat_map (fun s => map (cons s) (sassign P R' rho'))
               (filter (fun s => (M * s + c) mod P =? r) (seq 0 P))
  | _ :: _, [] => []
  end.

Lemma sassign_in : forall P R z, 0 < P -> length z = length R ->
  In (modl P z) (sassign P R (map (fun Mz => (fst (fst Mz) * snd Mz + snd (fst Mz)) mod P)
                                   (combine R z))).
Proof.
  intros P R. induction R as [|[M c] R IH]; intros z HP Hl.
  - destruct z; [left; reflexivity | discriminate].
  - destruct z as [|x z]; [discriminate|]. cbn in Hl |- *.
    apply in_flat_map. exists (x mod P). split.
    + apply filter_In. split.
      * apply in_seq. split; [lia|]. cbn. apply Nat.mod_upper_bound. lia.
      * apply Nat.eqb_eq.
        rewrite (Nat.Div0.add_mod (M * (x mod P))), (Nat.Div0.add_mod (M * x)).
        rewrite (Nat.Div0.mul_mod M (x mod P)), Nat.Div0.mod_mod, <- Nat.Div0.mul_mod.
        reflexivity.
    + apply in_map. apply IH; [exact HP | lia].
Qed.

(** [z := P * z' + s] as a substitution *)
Fixpoint zsub_from (P k : nat) (s : list nat) : list aexp :=
  match s with
  | [] => []
  | x :: s' => mkA x [(k, P)] :: zsub_from P (S k) s'
  end.

Definition zsub (P : nat) (s : list nat) : list aexp := zsub_from P 0 s.

Lemma zsub_from_nth : forall P v s k i, i < length s ->
  nth i (map (aeval v) (zsub_from P k s)) 0 = nth i s 0 + P * nth (k + i) v 0.
Proof.
  intros P v s. induction s as [|x s IH]; intros k i Hi; cbn in Hi; [lia|].
  destruct i as [|i]; cbn [zsub_from map nth].
  - unfold aeval; cbn. rewrite !Nat.add_0_r. reflexivity.
  - rewrite IH by lia. rewrite Nat.add_succ_r. reflexivity.
Qed.

Lemma zsub_from_length : forall P k s, length (zsub_from P k s) = length s.
Proof. intros P k s. revert k. induction s; intros k; cbn; auto. Qed.

Lemma nth_map_lt : forall {A B} (f : A -> B) l i d d', i < length l ->
  nth i (map f l) d' = f (nth i l d).
Proof.
  intros A B f l. induction l as [|x l IH]; intros [|i] d d' H; cbn in *; try lia;
    [reflexivity | apply IH; lia].
Qed.

Lemma zsub_ok : forall P z, 0 < P ->
  map (aeval (map (fun x => x / P) z)) (zsub P (modl P z)) = z.
Proof.
  intros P z HP. unfold zsub.
  apply nth_ext with (d := 0) (d' := 0).
  - rewrite map_length, zsub_from_length. unfold modl. apply map_length.
  - intros i Hi. rewrite map_length, zsub_from_length in Hi. unfold modl in Hi |- *.
    rewrite map_length in Hi.
    rewrite zsub_from_nth by (rewrite map_length; exact Hi). cbn [Nat.add].
    rewrite (nth_map_lt _ _ _ 0 0 Hi), (nth_map_lt _ _ _ 0 0 Hi).
    pose proof (Nat.div_mod (nth i z 0) P ltac:(lia)). lia.
Qed.

Lemma aeval_zsub : forall P z e, 0 < P ->
  aeval (map (fun x => x / P) z) (asubst (zsub P (modl P z)) e) = aeval z e.
Proof. intros P z e HP. rewrite aeval_asubst, zsub_ok by exact HP. reflexivity. Qed.

(** coefficients divisible by [P]: the value is its constant mod [P] *)
Definition pdiv (P : nat) (e : aexp) : bool := forallb (fun ka => snd ka mod P =? 0) (a_t e).

Lemma pdiv_teval : forall P v t, forallb (fun ka => snd ka mod P =? 0) t = true ->
  teval v t mod P = 0.
Proof.
  intros P v t. induction t as [|[k a] t IH]; intros H; cbn [teval]; [apply Nat.Div0.mod_0_l|].
  cbn in H. apply andb_prop in H as [H1 H2]. apply Nat.eqb_eq in H1.
  apply Nat.Div0.mod_divides in H1 as (b & ->).
  rewrite Nat.Div0.add_mod, IH by exact H2.
  replace (P * b * nth k v 0) with (b * nth k v 0 * P) by lia.
  rewrite Nat.Div0.mod_mul. apply Nat.Div0.mod_0_l.
Qed.

Lemma pdiv_mod : forall P v e, pdiv P e = true -> aeval v e mod P = a_c e mod P.
Proof.
  intros P v e H. unfold aeval. rewrite Nat.Div0.add_mod, (pdiv_teval P v _ H), Nat.add_0_r.
  apply Nat.Div0.mod_mod.
Qed.

Lemma pdiv_divides : forall P v e, pdiv P e = true -> exists T, aeval v e = a_c e + P * T.
Proof.
  intros P v e H. unfold aeval. pose proof (pdiv_teval P v _ H) as Ht.
  apply Nat.Div0.mod_divides in Ht as (T & HT). exists T. rewrite HT. reflexivity.
Qed.

(** could a target value land in a leaf's region?  (sound over-approximation) *)
Definition compat1 (P : nat) (Mc : nat * nat) (e : aexp) : bool :=
  let M := fst Mc in let c := snd Mc in
  match a_t e with
  | [] => if M =? 0 then a_c e =? c else (c <=? a_c e) && ((a_c e - c) mod M =? 0)
  | _ :: _ =>
      if M =? 0 then (a_c e <=? c) && ((c - a_c e) mod P =? 0)
      else if P mod M =? 0 then a_c e mod M =? c mod M else true
  end.

Lemma compat1_ok : forall P Mc e v y, pdiv P e = true ->
  aeval v e = fst Mc * y + snd Mc -> compat1 P Mc e = true.
Proof.
  intros P [M c] e v y Hd He. unfold compat1; cbn [fst snd] in *.
  destruct (pdiv_divides P v e Hd) as (T & HT).
  destruct (a_t e) as [|x t] eqn:Et.
  - assert (Hv : aeval v e = a_c e) by (unfold aeval; rewrite Et; cbn; lia).
    destruct (M =? 0) eqn:EM.
    + apply Nat.eqb_eq in EM. subst M. apply Nat.eqb_eq. lia.
    + apply Nat.eqb_neq in EM. apply andb_true_intro. split; [apply Nat.leb_le; lia|].
      apply Nat.eqb_eq. replace (a_c e - c) with (y * M) by lia. apply Nat.Div0.mod_mul.
  - destruct (M =? 0) eqn:EM.
    + apply Nat.eqb_eq in EM. subst M. apply andb_true_intro.
      split; [apply Nat.leb_le; lia|]. apply Nat.eqb_eq.
      replace (c - a_c e) with (T * P) by lia. apply Nat.Div0.mod_mul.
    + destruct (P mod M =? 0) eqn:EP; [|reflexivity].
      apply Nat.eqb_eq in EP. apply Nat.Div0.mod_divides in EP as (Q & HQ).
      apply Nat.eqb_eq.
      assert (Hx : a_c e + M * (Q * T) = M * y + c) by (rewrite HQ in HT; nia).
      rewrite <- (Nat.Div0.mod_add (a_c e) (Q * T) M), <- (Nat.Div0.mod_add c y M).
      f_equal. lia.
Qed.

Fixpoint compat (P : nat) (R : list (nat * nat)) (tgt : list aexp) : bool :=
  match R, tgt with
  | [], [] => true
  | Mc :: R', e :: tgt' => compat1 P Mc e && compat P R' tgt'
  | _, _ => false
  end.

Lemma compat_ok : forall P v R tgt z,
  forallb (pdiv P) tgt = true -> length tgt = length R ->
  (forall k, k < length R -> aeval v (nth k tgt (aconst 0)) = rv R z k) ->
  compat P R tgt = true.
Proof.
  intros P v R. induction R as [|Mc R IH]; intros tgt z Hd Hl Hv.
  - destruct tgt; [reflexivity | discriminate].
  - destruct tgt as [|e tgt]; [discriminate|]. cbn in Hd, Hl |- *.
    apply andb_prop in Hd as [Hd1 Hd2]. apply andb_true_intro. split.
    + apply (compat1_ok P Mc e v (nth 0 z 0) Hd1).
      pose proof (Hv 0 ltac:(cbn; lia)) as H0. cbn in H0. rewrite H0. unfold rv. cbn.
      reflexivity.
    + apply (IH tgt (tl z) Hd2 ltac:(lia)). intros k Hk.
      pose proof (Hv (S k) ltac:(cbn; lia)) as H1. cbn [nth] in H1. rewrite H1.
      unfold rv. cbn [nth]. destruct z as [|x z]; cbn [tl nth]; [destruct k|]; reflexivity.
Qed.

(** rankings *)
Definition vval (V : nat * list nat) (vals : list nat) : nat :=
  fst V + fold_right (fun ax acc => fst ax * snd ax + acc) 0 (combine (snd V) vals).

Definition veval (V : nat * list nat) (xs : list aexp) : aexp :=
  fold_right (fun ax acc => aadd (ascale (fst ax) (snd ax)) acc) (aconst (fst V))
             (combine (snd V) xs).

Lemma veval_ok : forall z V xs, aeval z (veval V xs) = vval V (map (aeval z) xs).
Proof.
  intros z [c vs] xs. unfold veval, vval; cbn [fst snd].
  revert xs. induction vs as [|a vs IH]; intros [|x xs]; cbn [combine fold_right map];
    try (unfold aeval; cbn; lia).
  rewrite aeval_aadd, aeval_ascale, IH. cbn [fst snd]. lia.
Qed.

Definition rank_of (rk : list (Instr * list (nat * list nat))) (t : Instr)
  : list (nat * list nat) :=
  match find (fun p => instr_eqb (fst p) t) rk with Some p => snd p | None => [] end.

(** ** The certificate and the checker *)

Record tcert := mkTC {
  tc_pins   : list Instr;             (** claimed never to fire *)
  tc_fams   : list tfam;
  tc_leaves : list tleaf;
  tc_P      : nat;                    (** the residue modulus, >= 1 *)
  tc_S      : list (nat * list nat);  (** the closed node set *)
  tc_rank   : list (Instr * list (nat * list nat));  (** per instruction, per node *)
  tc_t0     : nat;                    (** boot, on the wrapped machine *)
  tc_f0     : nat;
  tc_v0     : list nat
}.

Definition live_node_ok (tmw : TM) (w : tcert) (fired : list (list Instr))
    (i : nat) (lr : nat * list nat) : bool :=
  let P := tc_P w in
  let lvs := tc_leaves w in
  match nth_error lvs (fst lr) with
  | None => false
  | Some lf =>
      let fl := nth (fst lr) fired [] in
      forallb (fun s =>
        let sub := zsub P s in
        let src := map (asubst sub) (rsub (tl_reg lf)) in
        let tgt := map (asubst sub) (tl_tgt lf) in
        let rho' := map (fun e => a_c e mod P) tgt in
        forallb (pdiv P) tgt
        && forallb (fun l' =>
             match nth_error lvs l' with
             | None => true
             | Some lf' =>
                 if (tl_f lf' =? tl_g lf) && compat P (tl_reg lf') tgt then
                   match nidx (tc_S w) l' rho' with
                   | None => false
                   | Some i' =>
                       let fl' := nth l' fired [] in
                       forallb (fun t =>
                         tr_inb t (tc_pins w) || tr_inb t fl || tr_inb t fl'
                         || ale (aaddc (veval (nth i' (rank_of (tc_rank w) t) (0, [])) tgt) 1)
                                (veval (nth i (rank_of (tc_rank w) t) (0, [])) src)) all_Instr
                   end
                 else true
             end) (seq 0 (length lvs)))
        (sassign P (tl_reg lf) (snd lr))
  end.

Definition live_ok (tmw : TM) (w : tcert) : bool :=
  let fired := map (leaf_fired tmw) (tc_leaves w) in
  (0 <? tc_P w)
  && forallb (fun ilr => live_node_ok tmw w fired (fst ilr) (snd ilr))
             (combine (seq 0 (length (tc_S w))) (tc_S w)).

Definition nodeidx (w : tcert) (a : nat * list nat) : option nat :=
  match nth_error (tc_fams w) (fst a) with
  | Some F =>
      match fwalk F (snd a) with
      | Some (l, _, _) => nidx (tc_S w) l (modl (tc_P w) (snd a))
      | None => None
      end
  | None => None
  end.

Definition boot_ok (tmw : TM) (w : tcert) : bool :=
  match nth_error (tc_fams w) (tc_f0 w), csteps tmw (tc_t0 w) c0 with
  | Some F, Some c =>
      ceqb c (tinst F (tc_v0 w)) && (length (tc_v0 w) =? tf_n F)
      && match nodeidx w (tc_f0 w, tc_v0 w) with Some _ => true | None => false end
  | _, _ => false
  end.

Definition tri_check (tm : TM) (w : tcert) : bool :=
  let tmw := tm_wrap_trs tm (tc_pins w) in
  fams_ok tmw (tc_fams w) (tc_leaves w) && boot_ok tmw w && live_ok tmw w.

(** ** Soundness *)

Section Live.

Variable tm : TM.
Variable w : tcert.

Let tmw := tm_wrap_trs tm (tc_pins w).
Let fams := tc_fams w.
Let lvs := tc_leaves w.
Let P := tc_P w.

Hypothesis Hfams : fams_ok tmw fams lvs = true.
Hypothesis Hlive : live_ok tmw w = true.

Lemma HP : 0 < P.
Proof.
  unfold live_ok in Hlive. apply andb_prop in Hlive as [H _]. apply Nat.ltb_lt, H.
Qed.

Lemma live_node : forall i lr, nth_error (tc_S w) i = Some lr ->
  live_node_ok tmw w (map (leaf_fired tmw) lvs) i lr = true.
Proof.
  intros i lr H. unfold live_ok in Hlive. apply andb_prop in Hlive as [_ Hl].
  rewrite forallb_forall in Hl. apply (Hl (i, lr)).
  assert (Hlt : i < length (tc_S w)) by (apply nth_error_Some; rewrite H; discriminate).
  assert (Hc : forall s, nth_error (combine (seq s (length (tc_S w))) (tc_S w)) i
                         = Some (s + i, lr)).
  { clear Hl. revert i H Hlt. induction (tc_S w) as [|x xs IH]; intros [|i] H Hlt s;
      cbn in *; try discriminate; try lia.
    - injection H as ->. rewrite Nat.add_0_r. reflexivity.
    - rewrite <- Nat.add_succ_comm. apply IH; [exact H | lia]. }
  specialize (Hc 0). apply nth_error_In in Hc. exact Hc.
Qed.

Definition GoodS (a : nat * list nat) : Prop := Good fams a /\ nodeidx w a <> None.

Definition leafof (a : nat * list nat) : option tleaf :=
  match nth_error fams (fst a) with
  | Some F => match fwalk F (snd a) with
              | Some (l, _, _) => nth_error lvs l
              | None => None
              end
  | None => None
  end.

Definition fires_at (a : nat * list nat) (t : Instr) : bool :=
  match leafof a with Some lf => tr_inb t (leaf_fired tmw lf) | None => false end.

Definition rval (t : Instr) (a : nat * list nat) : nat :=
  match nodeidx w a with
  | Some i => vval (nth i (rank_of (tc_rank w) t) (0, [])) (snd a)
  | None => 0
  end.

Lemma modl_rsub : forall R z, length z = length R ->
  modl P (map (aeval z) (rsub R))
  = map (fun Mz => (fst (fst Mz) * snd Mz + snd (fst Mz)) mod P) (combine R z).
Proof.
  intros R z Hl. apply nth_ext with (d := 0) (d' := 0).
  - unfold modl. rewrite !map_length, rsub_length, combine_length. lia.
  - intros k Hk. unfold modl in Hk |- *. rewrite !map_length, rsub_length in Hk.
    rewrite (nth_map_lt _ _ _ 0 0) by (rewrite map_length, rsub_length; exact Hk).
    rewrite rsub_nth by exact Hk.
    rewrite (nth_map_lt _ _ _ ((0, 0), 0) 0) by (rewrite combine_length; lia).
    rewrite combine_nth by lia. reflexivity.
Qed.

Lemma next_ok : forall a, GoodS a ->
  GoodS (tnxt fams lvs a)
  /\ forall t, ~ In t (tc_pins w) -> fires_at a t = false -> fires_at (tnxt fams lvs a) t = false ->
       rval t (tnxt fams lvs a) + 1 <= rval t a.
Proof.
  intros a [Ha Hn].
  destruct (walk_leaf tmw fams lvs Hfams a Ha)
    as (F & lf & l & R & z & HF & Hw & Hlf & _ & HR & Hok & Hv & HzR).
  unfold nodeidx in Hn. fold fams in Hn. rewrite HF, Hw in Hn.
  destruct (nidx (tc_S w) l (modl (tc_P w) (snd a))) as [i|] eqn:Ei; [|contradiction].
  pose proof (nidx_ok _ _ _ _ Ei) as HSi.
  pose proof (live_node _ _ HSi) as Hln.
  unfold live_node_ok in Hln. cbn [fst snd] in Hln. fold lvs in Hln. rewrite Hlf in Hln.
  rewrite forallb_forall in Hln.
  set (s := modl P z).
  assert (Hs : In s (sassign (tc_P w) (tl_reg lf) (modl (tc_P w) (snd a)))).
  { fold P. rewrite HR, Hv, modl_rsub by exact HzR. apply sassign_in; [exact HP | exact HzR]. }
  specialize (Hln s Hs). cbv zeta in Hln. apply andb_prop in Hln as [Hdiv Hln].
  rewrite forallb_forall in Hln.
  (* the next anchor *)
  destruct (step_ok tmw fams lvs Hfams a Ha) as (_ & Ha').
  assert (Hnx : tnxt fams lvs a = (tl_g lf, map (aeval z) (tl_tgt lf))).
  { unfold tnxt. rewrite HF, Hw, Hlf. reflexivity. }
  destruct (walk_leaf tmw fams lvs Hfams _ Ha')
    as (G & lf' & l' & R' & z2 & HG & Hw' & Hlf' & Hfl' & HR' & Hok' & Hv' & HzR').
  rewrite Hnx in HG, Hw', Hfl', Hv'. cbn [fst snd] in HG, Hw', Hfl', Hv'.
  set (z' := map (fun x => x / P) z).
  set (tgt := map (asubst (zsub (tc_P w) s)) (tl_tgt lf)) in *.
  set (src := map (asubst (zsub (tc_P w) s)) (rsub (tl_reg lf))) in *.
  assert (Hzs : forall e, aeval z' (asubst (zsub (tc_P w) s) e) = aeval z e).
  { intros e. subst z' s. apply aeval_zsub. exact HP. }
  assert (Htgt : map (aeval z') tgt = map (aeval z) (tl_tgt lf)).
  { subst tgt. rewrite map_map. apply map_ext. exact Hzs. }
  assert (Hsrc : map (aeval z') src = snd a).
  { subst src. rewrite map_map, Hv, <- HR. apply map_ext. exact Hzs. }
  assert (Hl' : In l' (seq 0 (length (tc_leaves w)))).
  { apply in_seq. split; [lia|]. apply nth_error_Some. fold lvs. rewrite Hlf'. discriminate. }
  specialize (Hln l' Hl'). fold lvs in Hln. rewrite Hlf' in Hln.
  destruct (leaf_ok_inv _ _ _ _ Hok) as (g & _ & _ & _ & Hg & _ & _ & _ & _ & _ & _ & _ & _
    & _ & _ & _ & _ & Htl & _).
  destruct (leaf_ok_inv _ _ _ _ Hok') as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
    & _ & _ & _ & _ & _ & HrG).
  fold fams in Hg. rewrite HG in Hg. injection Hg as <-.
  assert (Hcomp : compat (tc_P w) (tl_reg lf') tgt = true).
  { apply (compat_ok (tc_P w) z' (tl_reg lf') tgt z2 Hdiv).
    - subst tgt. rewrite map_length, Htl, HrG. reflexivity.
    - intros k Hk. rewrite HR' in Hk |- *.
      assert (Hk2 : k < length tgt) by (subst tgt; rewrite map_length, Htl, <- HrG, HR'; exact Hk).
      rewrite <- (nth_map_lt (aeval z') tgt k (aconst 0) 0 Hk2), Htgt, Hv'.
      apply rsub_nth. exact Hk. }
  rewrite Hfl', Nat.eqb_refl, Hcomp in Hln. cbn [andb] in Hln.
  assert (Hrho : map (fun e => a_c e mod tc_P w) tgt = modl (tc_P w) (map (aeval z) (tl_tgt lf))).
  { rewrite <- Htgt. unfold modl. rewrite map_map. apply map_ext_in. intros e He.
    rewrite forallb_forall in Hdiv. symmetry. apply pdiv_mod. exact (Hdiv e He). }
  rewrite Hrho in Hln.
  destruct (nidx (tc_S w) l' (modl (tc_P w) (map (aeval z) (tl_tgt lf)))) as [i'|] eqn:Ei';
    [|discriminate].
  assert (Hn' : nodeidx w (tnxt fams lvs a) = Some i').
  { unfold nodeidx. rewrite Hnx. cbn [fst snd]. fold fams. rewrite HG, Hw'. exact Ei'. }
  split.
  - split; [exact Ha' | rewrite Hn'; discriminate].
  - intros t Hpin Hf Hf'.
    unfold fires_at, leafof in Hf, Hf'. fold fams lvs in Hf, Hf'.
    rewrite HF, Hw, Hlf in Hf. rewrite Hnx in Hf'. cbn [fst snd] in Hf'.
    rewrite HG, Hw', Hlf' in Hf'.
    rewrite forallb_forall in Hln. specialize (Hln t (all_Instr_complete t)).
    assert (Hpin' : tr_inb t (tc_pins w) = false).
    { destruct (tr_inb t (tc_pins w)) eqn:E; [|reflexivity].
      exfalso. apply Hpin. apply tr_inb_spec. exact E. }
    assert (Hfl : nth l (map (leaf_fired tmw) lvs) [] = leaf_fired tmw lf).
    { apply nth_error_nth. apply map_nth_error. exact Hlf. }
    assert (Hfl2 : nth l' (map (leaf_fired tmw) lvs) [] = leaf_fired tmw lf').
    { apply nth_error_nth. apply map_nth_error. exact Hlf'. }
    rewrite Hpin', Hfl, Hfl2, Hf, Hf' in Hln. cbn [orb] in Hln.
    pose proof (ale_sound z' _ _ Hln) as Hle.
    rewrite aeval_aaddc, !veval_ok, Htgt, Hsrc in Hle.
    unfold rval. rewrite Hn'. unfold nodeidx. fold fams. rewrite HF, Hw, Ei.
    rewrite Hnx. cbn [snd]. exact Hle.
Qed.

Definition FiresFrom (c : cconf) (t : Instr) : Prop :=
  exists k e, stepn tmw k (lift c) = Some e /\ instr_of e = t.

Lemma fires_rank : forall t, ~ In t (tc_pins w) ->
  forall n a, GoodS a -> rval t a <= n -> FiresFrom (tanc fams a) t.
Proof.
  intros t Hpin n. induction n as [|n IH]; intros a Ha Hr.
  all: destruct (fires_at a t) eqn:Ef.
  1, 3:
    destruct Ha as [Ha _];
    destruct (walk_leaf tmw fams lvs Hfams a Ha)
      as (F & lf & l & R & z & HF & Hw & Hlf & _ & HR & Hok & Hv & _);
    unfold fires_at, leafof in Ef; fold fams lvs in Ef; rewrite HF, Hw, Hlf in Ef;
    apply tr_inb_spec in Ef;
    destruct (leaf_fires _ _ _ _ _ Hok Ef z) as (k & c & Hk & Hc);
    exists k, (lift c); split;
    [ unfold tanc; rewrite HF, Hv, <- HR; apply csteps_lift; exact Hk
    | rewrite cinstr_lift; exact Hc ].
  all: destruct (step_ok tmw fams lvs Hfams a (proj1 Ha)) as ((m & c' & Hm & Hl & _) & _).
  all: destruct (next_ok a Ha) as (Ha' & Hrk).
  all: assert (Hback : forall t', FiresFrom (tanc fams (tnxt fams lvs a)) t' ->
                                  FiresFrom (tanc fams a) t')
         by (intros t' (k & e & Hk & He); exists (m + k), e;
             split; [rewrite stepn_add, (csteps_lift _ _ _ _ Hm), Hl; exact Hk | exact He]).
  all: apply Hback.
  all: destruct (fires_at (tnxt fams lvs a) t) eqn:Ef'.
  1, 3:
    destruct Ha' as [Ha' _];
    destruct (walk_leaf tmw fams lvs Hfams _ Ha')
      as (F & lf & l & R & z & HF & Hw & Hlf & _ & HR & Hok & Hv & _);
    unfold fires_at, leafof in Ef'; fold fams lvs in Ef'; rewrite HF, Hw, Hlf in Ef';
    apply tr_inb_spec in Ef';
    destruct (leaf_fires _ _ _ _ _ Hok Ef' z) as (k & c & Hk & Hc);
    exists k, (lift c); split;
    [ unfold tanc; rewrite HF, Hv, <- HR; apply csteps_lift; exact Hk
    | rewrite cinstr_lift; exact Hc ].
  - pose proof (Hrk t Hpin Ef Ef'). lia.
  - apply (IH _ Ha'). pose proof (Hrk t Hpin Ef Ef'). lia.
Qed.

Definition triCf (a0 : nat * list nat) (p : positive) : cconf :=
  tanc fams (Nat.iter (Nat.pred (Pos.to_nat p)) (tnxt fams lvs) a0).

Lemma triCf_succ : forall a0 p, triCf a0 (Pos.succ p) =
  tanc fams (tnxt fams lvs (Nat.iter (Nat.pred (Pos.to_nat p)) (tnxt fams lvs) a0)).
Proof.
  intros a0 p. unfold triCf. rewrite Pos2Nat.inj_succ.
  destruct (Pos2Nat.is_succ p) as (m & Hm). rewrite Hm. reflexivity.
Qed.

Lemma iter_good : forall a0, GoodS a0 -> forall m, GoodS (Nat.iter m (tnxt fams lvs) a0).
Proof.
  intros a0 H0 m. induction m as [|m IH]; [exact H0|].
  cbn [Nat.iter nat_rect]. exact (proj1 (next_ok _ IH)).
Qed.

Theorem tri_glue : forall a0, GoodS a0 ->
  (exists t0, stepn tmw t0 InitES = Some (lift (tanc fams a0))) ->
  NeverQuasiHaltsTr tm.
Proof.
  intros a0 H0 Hboot.
  apply (glue_neverqhtr tm (tc_pins w) (triCf a0) xH).
  - exact Hboot.
  - intros p _. rewrite triCf_succ. unfold triCf.
    exact (proj1 (step_ok tmw fams lvs Hfams _ (proj1 (iter_good a0 H0 _)))).
  - intros t Hnin p _. apply fire_csteps_of_lift. unfold triCf.
    exact (fires_rank t Hnin _ _ (iter_good a0 H0 _) (le_n _)).
Qed.

(** the quasihalting rows: the boot on the original machine, a pinned
    instruction fired before it *)
Theorem tri_glue_qh : forall a0 t0, GoodS a0 ->
  stepn tm t0 InitES = Some (lift (tanc fams a0)) ->
  existsb (fun tg => cfires tm c0 t0 tg) (tc_pins w) = true ->
  (t0 <=? 32779478) = true ->
  NonHalt tm /\ QHBoundTr 32779478 tm /\ QuasiHaltsTr tm.
Proof.
  intros a0 t0 H0 Hboot Hwit Hcap.
  apply (lap_qh_stage tm (tc_pins w) (triCf a0) xH t0 32779478).
  - exact Hboot.
  - intros p _. rewrite triCf_succ. unfold triCf.
    exact (proj1 (step_ok tmw fams lvs Hfams _ (proj1 (iter_good a0 H0 _)))).
  - intros t Hnin p _. apply fire_csteps_of_lift. unfold triCf.
    exact (fires_rank t Hnin _ _ (iter_good a0 H0 _) (le_n _)).
  - exact Hwit.
  - exact Hcap.
Qed.

End Live.

Theorem tri_sound : forall tm w, tri_check tm w = true -> NeverQuasiHaltsTr tm.
Proof.
  intros tm w H. unfold tri_check in H.
  apply andb_prop in H as [H Hl]. apply andb_prop in H as [Hf Hb].
  apply (tri_glue tm w Hf Hl (tc_f0 w, tc_v0 w)).
  - unfold boot_ok in Hb.
    destruct (nth_error (tc_fams w) (tc_f0 w)) as [F|] eqn:EF; [|discriminate].
    destruct (csteps (tm_wrap_trs tm (tc_pins w)) (tc_t0 w) c0) as [c|]; [|discriminate].
    apply andb_prop in Hb as [Hb Hn]. apply andb_prop in Hb as [_ Hlen].
    apply Nat.eqb_eq in Hlen.
    split; [exists F; split; assumption|].
    destruct (nodeidx w (tc_f0 w, tc_v0 w)); [discriminate | discriminate].
  - unfold boot_ok in Hb.
    destruct (nth_error (tc_fams w) (tc_f0 w)) as [F|] eqn:EF; [|discriminate].
    destruct (csteps (tm_wrap_trs tm (tc_pins w)) (tc_t0 w) c0) as [c|] eqn:E; [|discriminate].
    apply andb_prop in Hb as [Hb _]. apply andb_prop in Hb as [Hc _].
    exists (tc_t0 w). rewrite <- lift_c0, (csteps_lift _ _ _ _ E).
    unfold tanc. cbn [fst snd]. rewrite EF. f_equal. exact (ceqb_lift _ _ Hc).
Qed.

(** the anchors are mirrored: certify the mirror *)
Theorem tri_sound_mirror : forall tm w, tri_check (mirror_tm tm) w = true ->
  NeverQuasiHaltsTr tm.
Proof.
  intros tm w H. apply neverqhtr_mirror. exact (tri_sound _ w H).
Qed.

(** ** Quasihalting rows *)

Definition boot_qh_ok (tm : TM) (w : tcert) : bool :=
  match nth_error (tc_fams w) (tc_f0 w), csteps tm (tc_t0 w) c0 with
  | Some F, Some c =>
      ceqb c (tinst F (tc_v0 w)) && (length (tc_v0 w) =? tf_n F)
      && match nodeidx w (tc_f0 w, tc_v0 w) with Some _ => true | None => false end
  | _, _ => false
  end.

Definition tri_check_qh (tm : TM) (w : tcert) : bool :=
  let tmw := tm_wrap_trs tm (tc_pins w) in
  fams_ok tmw (tc_fams w) (tc_leaves w) && boot_qh_ok tm w && live_ok tmw w
  && existsb (fun tg => cfires tm c0 (tc_t0 w) tg) (tc_pins w)
  && (tc_t0 w <=? sw_boot_cap).

Theorem tri_sound_qh : forall tm w, tri_check_qh tm w = true ->
  NonHalt tm /\ QHBoundTr 32779478 tm /\ QuasiHaltsTr tm.
Proof.
  intros tm w H. unfold tri_check_qh in H.
  apply andb_prop in H as [H Hcap]. apply andb_prop in H as [H Hwit].
  apply andb_prop in H as [H Hl]. apply andb_prop in H as [Hf Hb].
  unfold boot_qh_ok in Hb.
  destruct (nth_error (tc_fams w) (tc_f0 w)) as [F|] eqn:EF; [|discriminate].
  destruct (csteps tm (tc_t0 w) c0) as [c|] eqn:E; [|discriminate].
  apply andb_prop in Hb as [Hb Hn]. apply andb_prop in Hb as [Hc Hlen].
  apply Nat.eqb_eq in Hlen.
  apply (tri_glue_qh tm w Hf Hl (tc_f0 w, tc_v0 w) (tc_t0 w)).
  - split; [exists F; split; assumption|].
    destruct (nodeidx w (tc_f0 w, tc_v0 w)); [discriminate | discriminate].
  - rewrite <- lift_c0, (csteps_lift _ _ _ _ E).
    unfold tanc. cbn [fst snd]. rewrite EF. f_equal. exact (ceqb_lift _ _ Hc).
  - exact Hwit.
  - exact (sw_cap_le _ Hcap).
Qed.

Theorem tri_sound_qh_mirror : forall tm w, tri_check_qh (mirror_tm tm) w = true ->
  NonHalt tm /\ QHBoundTr 32779478 tm /\ QuasiHaltsTr tm.
Proof.
  intros tm w H.
  destruct (tri_sound_qh (mirror_tm tm) w H) as (Hnh & Hb & (t & (n & Hn) & N & HN)).
  split; [exact (mirror_nonhalt tm Hnh) |].
  split; [exact (qhboundtr_mirror 32779478 tm Hb) |].
  exists t. split.
  - exists n. apply mirror_fires. exact Hn.
  - exists N. intros m Hm Hf. apply (HN m Hm). apply mirror_fires. exact Hf.
Qed.
