(** * IRules.EngineK: the block-run symbolic replay engine.

    A fork of [Engine] whose run symbols range over [nat] (0 = [S0],
    1 = [S1], and every id >= 2 a BLOCK defined by the certificate's
    (untrusted) block table [tbl : nat -> list Sym]).  A run [(b, e)]
    now denotes [cnt nu e] copies of [tbl b]'s cell sequence, not
    [cnt nu e] copies of a single symbol -- the CRUX of the block
    machinery (BBB docs/irules2.md "Block-level chain hops").

    The denotation [bdside tbl] is parametric in [tbl]; soundness holds
    for ANY table, so the table is never trusted.  A raw symbol [s < 2]
    is the degenerate block [tbl s = [nat_sym s]], so a raw-only side
    reduces exactly to [RLE.dside].

    This file layers, on top of a re-proof of the [Engine] concrete
    step + chain hops against [bdside]:

    - block hop: a bounded one-copy concrete replay ([hop_sim]) that,
      when the head exits the far side in the entry state, crosses ALL
      [e] copies in one op (induction on the copies);
    - block peel: expanding one copy of a block run into cells (a pure
      denotation-preserving re-representation, no concrete step);

    with the canonical re-blocking and cell-stream equality in the
    companion sections.  The Reach/csteps plumbing (concrete tape
    machinery, chain-crossing lemmas) is reused verbatim from
    [Engine]; only the denotation-facing parts are re-derived. *)

From Coq Require Import Arith ZArith Lia Bool List Setoid FunctionalExtensionality.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Checkers.IRules Require Import Expr RLE Engine.
Import ListNotations.
Open Scope Z_scope.

(** ** Block symbols, the block table, and the block denotation *)

Definition BSym := nat.
Definition BRun : Set := (BSym * Expr)%type.
Definition BTbl := BSym -> list Sym.

Record BCfg : Set := mkBCfg {
  b_st : St;
  b_hs : Sym;
  b_L : list BRun;
  b_R : list BRun
}.

(** [nat] -> [Sym] for the two raw symbols (anything else is [S0]). *)
Definition nsym (n : nat) : Sym := match n with O => S0 | _ => S1 end.

(** [n] concatenated copies of a cell word. *)
Definition nreps (l : list Sym) (n : nat) : list Sym := concat (repeat l n).

Lemma nreps_0 : forall l, nreps l 0 = [].
Proof. reflexivity. Qed.

Lemma nreps_S : forall l n, nreps l (S n) = l ++ nreps l n.
Proof. reflexivity. Qed.

Lemma nreps_add : forall l a b, nreps l (a + b) = nreps l a ++ nreps l b.
Proof.
  intros l a b. induction a as [|a IH]; simpl.
  - reflexivity.
  - rewrite !nreps_S, IH, app_assoc. reflexivity.
Qed.

Lemma nreps_1 : forall l, nreps l 1 = l.
Proof. intro l. rewrite nreps_S, nreps_0, app_nil_r. reflexivity. Qed.

Lemma nreps_single : forall x n, nreps [x] n = repeat x n.
Proof.
  intros x n. induction n as [|n IH]; simpl; [reflexivity|].
  rewrite nreps_S, IH. reflexivity.
Qed.

(** The block denotation of a half-tape. *)
Definition bdside (tbl : BTbl) (nu : nat -> Z) (rs : list BRun) : list Sym :=
  flat_map (fun r => nreps (tbl (fst r)) (cnt nu (snd r))) rs.

Definition bdcfg (tbl : BTbl) (nu : nat -> Z) (c : BCfg) : cconf :=
  (b_st c, (bdside tbl nu (b_L c), b_hs c, bdside tbl nu (b_R c))).

Definition bsem (tbl : BTbl) (nu : nat -> Z) (c : BCfg) : ExecState :=
  lift (bdcfg tbl nu c).

Lemma bdside_cons : forall tbl nu s e t,
  bdside tbl nu ((s, e) :: t) =
  nreps (tbl s) (cnt nu e) ++ bdside tbl nu t.
Proof. reflexivity. Qed.

(** A canonical table: raw ids map to the singleton cell. *)
Definition raw_ok (tbl : BTbl) : Prop :=
  tbl O = [S0] /\ tbl (S O) = [S1].

(** ** Push / merge / trim on block runs (mirror of [RLE]) *)

Definition bpush (lo : list Z) (s : BSym) (e : Expr) (rs : list BRun)
  : option (list BRun) :=
  if negb (expr_ge lo e 0) then None else
  match rs with
  | [] => if Nat.eqb s 0 then Some [] else Some [(s, e)]
  | (s', e') :: t =>
      if Nat.eqb s s'
      then if expr_ge lo e' 0 then Some ((s', eadd e e') :: t) else None
      else Some ((s, e) :: rs)
  end.

Lemma bpush_den : forall tbl lo s e rs rs' nu,
  raw_ok tbl ->
  bpush lo s e rs = Some rs' -> bge lo nu ->
  lift_side (bdside tbl nu rs') =
  lift_side (nreps (tbl s) (cnt nu e) ++ bdside tbl nu rs).
Proof.
  intros tbl lo s e rs rs' nu [Hr0 Hr1] H Hb.
  unfold bpush in H.
  destruct (expr_ge lo e 0) eqn:Hge; simpl in H; [|discriminate].
  destruct rs as [|[s' e'] t].
  - destruct (Nat.eqb s 0) eqn:Hs; injection H as <-.
    + apply Nat.eqb_eq in Hs; subst s.
      rewrite Hr0. simpl bdside.
      rewrite app_nil_r, nreps_single, lift_side_blanks.
      apply lift_side_nil.
    + reflexivity.
  - destruct (Nat.eqb s s') eqn:Hs.
    + destruct (expr_ge lo e' 0) eqn:Hge'; [|discriminate].
      injection H as <-.
      apply Nat.eqb_eq in Hs; subst s'.
      rewrite !bdside_cons.
      rewrite cnt_add;
        [| eapply expr_ge_sound; eauto | eapply expr_ge_sound; eauto].
      rewrite nreps_add, app_assoc. reflexivity.
    + injection H as <-. rewrite bdside_cons. reflexivity.
Qed.

Fixpoint bmerge_adj (lo : list Z) (rs : list BRun) : option (list BRun) :=
  match rs with
  | [] => Some []
  | (s, e) :: t =>
      match bmerge_adj lo t with
      | None => None
      | Some [] => Some [(s, e)]
      | Some ((s', e') :: t') =>
          if Nat.eqb s s'
          then if expr_ge lo e 0 && expr_ge lo e' 0
               then Some ((s, eadd e e') :: t') else None
          else Some ((s, e) :: (s', e') :: t')
      end
  end.

Lemma bmerge_adj_den : forall tbl lo rs rs' nu,
  bmerge_adj lo rs = Some rs' -> bge lo nu ->
  bdside tbl nu rs' = bdside tbl nu rs.
Proof.
  induction rs as [|[s e] t IH]; intros rs' nu H Hb; simpl in H.
  - injection H as <-. reflexivity.
  - destruct (bmerge_adj lo t) as [mt|] eqn:Em; [|discriminate].
    specialize (IH mt nu eq_refl Hb).
    destruct mt as [|[s' e'] t'].
    + injection H as <-.
      rewrite !bdside_cons, <- IH. simpl. reflexivity.
    + destruct (Nat.eqb s s') eqn:Hs.
      * destruct (expr_ge lo e 0 && expr_ge lo e' 0) eqn:Hge;
          [|discriminate].
        apply andb_prop in Hge as [Hge1 Hge2].
        injection H as <-.
        apply Nat.eqb_eq in Hs; subst s'.
        rewrite !bdside_cons, <- IH, bdside_cons.
        rewrite cnt_add;
          [| eapply expr_ge_sound; eauto | eapply expr_ge_sound; eauto].
        rewrite nreps_add, app_assoc. reflexivity.
      * injection H as <-.
        rewrite !bdside_cons, <- IH. reflexivity.
Qed.

Lemma bdside_lift_cons_cong : forall tbl nu s e A B,
  lift_side (bdside tbl nu A) = lift_side (bdside tbl nu B) ->
  lift_side (bdside tbl nu ((s, e) :: A)) =
  lift_side (bdside tbl nu ((s, e) :: B)).
Proof.
  intros tbl nu s e A B H.
  rewrite !bdside_cons. apply lift_side_app. exact H.
Qed.

Fixpoint btrim_blanks (rs : list BRun) : list BRun :=
  match rs with
  | [] => []
  | (s, e) :: t =>
      match btrim_blanks t with
      | [] => if Nat.eqb s 0 then [] else [(s, e)]
      | t' => (s, e) :: t'
      end
  end.

Lemma btrim_blanks_den : forall tbl rs nu,
  raw_ok tbl ->
  lift_side (bdside tbl nu (btrim_blanks rs)) = lift_side (bdside tbl nu rs).
Proof.
  induction rs as [|[s e] t IH]; intros nu Hraw; [reflexivity|].
  destruct Hraw as [Hr0 Hr1].
  specialize (IH nu (conj Hr0 Hr1)).
  cbn [btrim_blanks].
  destruct (btrim_blanks t) as [|r' t'] eqn:Et.
  - assert (Hbl : lift_side (bdside tbl nu t) = blank_side).
    { rewrite <- IH. apply lift_side_nil. }
    destruct (Nat.eqb s 0) eqn:Hs.
    + apply Nat.eqb_eq in Hs; subst s.
      rewrite bdside_cons, Hr0, nreps_single.
      change (bdside tbl nu []) with (@nil Sym).
      rewrite lift_side_nil.
      symmetry. apply lift_side_blank_app. exact Hbl.
    + apply (bdside_lift_cons_cong tbl nu s e [] t).
      change (bdside tbl nu []) with (@nil Sym).
      rewrite lift_side_nil, Hbl. reflexivity.
  - apply (bdside_lift_cons_cong tbl nu s e (r' :: t') t). exact IH.
Qed.
