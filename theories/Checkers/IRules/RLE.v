(** * IRules.RLE: run-length symbolic configurations.

    A symbolic configuration (BBB docs/irules.md "Configurations")
    is a state, a head symbol, and two half-tapes of runs
    [(symbol, count expression)], nearest-first, with the trailing
    blank infinity implicit.  Under a valuation [nu] a configuration
    denotes the computable configuration [dcfg nu c : cconf] (counts
    through [Expr.cnt]) and hence the abstract execution state
    [asem nu c] by [CTape.lift].

    This file is the representation layer: denotations, the
    (checked) push/merge/trim operations the engine and the rule
    applicator perform, and their denotation-preservation lemmas.
    Push and trim preserve the *lifted* half-tape (blank padding may
    differ); merge preserves the denoted cell list exactly.  Like
    [CTape], functional half-tape equalities use the
    [functional_extensionality] axiom. *)

From Coq Require Import Arith ZArith Lia Bool List FunctionalExtensionality.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Checkers.IRules Require Import Expr.
Import ListNotations.
Open Scope Z_scope.

(** ** Configurations and denotation *)

Definition SRun : Set := (Sym * Expr)%type.

Record SCfg : Set := mkSCfg {
  s_st : St;
  s_hs : Sym;
  s_L : list SRun;   (* left half-tape, nearest run first *)
  s_R : list SRun
}.

Definition dside (nu : nat -> Z) (rs : list SRun) : list Sym :=
  flat_map (fun r => repeat (fst r) (cnt nu (snd r))) rs.

Definition dcfg (nu : nat -> Z) (c : SCfg) : cconf :=
  (s_st c, (dside nu (s_L c), s_hs c, dside nu (s_R c))).

Definition asem (nu : nat -> Z) (c : SCfg) : ExecState := lift (dcfg nu c).

Lemma dside_cons : forall nu s e t,
  dside nu ((s, e) :: t) = repeat s (cnt nu e) ++ dside nu t.
Proof. reflexivity. Qed.

(** Pointwise equal counts and symbols give equal denotations. *)
Lemma dside_eq_pointwise : forall nu1 nu2 rs1 rs2,
  length rs1 = length rs2 ->
  (forall i, (i < length rs1)%nat ->
     fst (nth i rs1 (S0, econst 0)) = fst (nth i rs2 (S0, econst 0)) /\
     cnt nu1 (snd (nth i rs1 (S0, econst 0))) =
     cnt nu2 (snd (nth i rs2 (S0, econst 0)))) ->
  dside nu1 rs1 = dside nu2 rs2.
Proof.
  induction rs1 as [|[s e] t IH]; intros rs2 Hlen Hp.
  - destruct rs2; [reflexivity | discriminate].
  - destruct rs2 as [|[s' e'] t']; [discriminate|].
    simpl in Hlen. injection Hlen as Hlen.
    destruct (Hp O ltac:(simpl; lia)) as [Hs Hc]; simpl in Hs, Hc.
    rewrite !dside_cons, Hs, Hc.
    f_equal. apply IH; [exact Hlen|].
    intros i Hi. exact (Hp (S i) ltac:(simpl; lia)).
Qed.

(** ** Half-tape function facts *)

Lemma nthb_app_left : forall a b n,
  (n < length a)%nat -> nthb (a ++ b) n = nthb a n.
Proof. intros; unfold nthb; apply app_nth1; assumption. Qed.

Lemma nthb_app_right : forall a b n,
  (length a <= n)%nat -> nthb (a ++ b) n = nthb b (n - length a).
Proof. intros; unfold nthb; apply app_nth2; assumption. Qed.

Lemma nthb_repeat : forall s n i, (i < n)%nat -> nthb (repeat s n) i = s.
Proof.
  intros s n i H. unfold nthb.
  rewrite nth_indep with (d' := s)
    by (rewrite repeat_length; assumption).
  apply nth_repeat.
Qed.

Lemma lift_side_app_blanks : forall a n,
  lift_side (a ++ repeat S0 n) = lift_side a.
Proof.
  intros a n. apply functional_extensionality; intro i.
  unfold lift_side.
  destruct (Nat.lt_ge_cases i (length a)) as [Hlt | Hge].
  - apply nthb_app_left; assumption.
  - rewrite nthb_app_right by assumption.
    destruct (Nat.lt_ge_cases (i - length a) n) as [H2 | H2].
    + rewrite nthb_repeat by assumption.
      unfold nthb. rewrite nth_overflow by assumption. reflexivity.
    + unfold nthb.
      rewrite (nth_overflow (repeat S0 n))
        by (rewrite repeat_length; assumption).
      rewrite nth_overflow by assumption. reflexivity.
Qed.

Lemma lift_side_blanks : forall n, lift_side (repeat S0 n) = blank_side.
Proof.
  intro n.
  replace (repeat S0 n) with ([] ++ repeat S0 n) by reflexivity.
  rewrite lift_side_app_blanks. apply lift_side_nil.
Qed.

Lemma lift_side_app : forall a b c,
  lift_side b = lift_side c ->
  lift_side (a ++ b) = lift_side (a ++ c).
Proof.
  intros a b c H. apply functional_extensionality; intro i.
  destruct (Nat.lt_ge_cases i (length a)) as [Hlt | Hge].
  - rewrite !nthb_app_left by assumption. reflexivity.
  - rewrite !nthb_app_right by assumption.
    change (lift_side b (i - length a) = lift_side c (i - length a)).
    rewrite H. reflexivity.
Qed.

(** ** Push (the engine's [iv_push]): prepend [cnt e] copies of [s],
    merging with an equal-symbol nearest run and absorbing a blank
    push onto an empty side.  The merge requires provable
    nonnegativity of both counts, so the lemma needs no invariant. *)

Definition push (lo : list Z) (s : Sym) (e : Expr) (rs : list SRun)
  : option (list SRun) :=
  if negb (expr_ge lo e 0) then None else
  match rs with
  | [] => if sym_eqb s S0 then Some [] else Some [(s, e)]
  | (s', e') :: t =>
      if sym_eqb s s'
      then if expr_ge lo e' 0 then Some ((s', eadd e e') :: t) else None
      else Some ((s, e) :: rs)
  end.

Lemma push_den : forall lo s e rs rs' nu,
  push lo s e rs = Some rs' -> bge lo nu ->
  lift_side (dside nu rs') =
  lift_side (repeat s (cnt nu e) ++ dside nu rs).
Proof.
  intros lo s e rs rs' nu H Hb.
  unfold push in H.
  destruct (expr_ge lo e 0) eqn:Hge; simpl in H; [|discriminate].
  destruct rs as [|[s' e'] t].
  - destruct (sym_eqb s S0) eqn:Hs; injection H as <-.
    + apply sym_eqb_spec in Hs; subst s.
      unfold dside at 1; simpl.
      rewrite app_nil_r. rewrite lift_side_blanks.
      apply lift_side_nil.
    + reflexivity.
  - destruct (sym_eqb s s') eqn:Hs.
    + destruct (expr_ge lo e' 0) eqn:Hge'; [|discriminate].
      injection H as <-.
      apply sym_eqb_spec in Hs; subst s'.
      rewrite !dside_cons.
      rewrite cnt_add;
        [| eapply expr_ge_sound; eauto | eapply expr_ge_sound; eauto].
      rewrite repeat_app, app_assoc. reflexivity.
    + injection H as <-. rewrite dside_cons. reflexivity.
Qed.

(** ** Merge adjacent equal-symbol runs (rule-application rebuild) *)

Fixpoint merge_adj (lo : list Z) (rs : list SRun) : option (list SRun) :=
  match rs with
  | [] => Some []
  | (s, e) :: t =>
      match merge_adj lo t with
      | None => None
      | Some [] => Some [(s, e)]
      | Some ((s', e') :: t') =>
          if sym_eqb s s'
          then if expr_ge lo e 0 && expr_ge lo e' 0
               then Some ((s, eadd e e') :: t') else None
          else Some ((s, e) :: (s', e') :: t')
      end
  end.

Lemma merge_adj_den : forall lo rs rs' nu,
  merge_adj lo rs = Some rs' -> bge lo nu ->
  dside nu rs' = dside nu rs.
Proof.
  induction rs as [|[s e] t IH]; intros rs' nu H Hb; simpl in H.
  - injection H as <-. reflexivity.
  - destruct (merge_adj lo t) as [mt|] eqn:Em; [|discriminate].
    specialize (IH mt nu eq_refl Hb).
    destruct mt as [|[s' e'] t'].
    + injection H as <-.
      rewrite !dside_cons, <- IH. simpl. reflexivity.
    + destruct (sym_eqb s s') eqn:Hs.
      * destruct (expr_ge lo e 0 && expr_ge lo e' 0) eqn:Hge;
          [|discriminate].
        apply andb_prop in Hge as [Hge1 Hge2].
        injection H as <-.
        apply sym_eqb_spec in Hs; subst s'.
        rewrite !dside_cons, <- IH, dside_cons.
        rewrite cnt_add;
          [| eapply expr_ge_sound; eauto | eapply expr_ge_sound; eauto].
        rewrite repeat_app, app_assoc. reflexivity.
      * injection H as <-.
        rewrite !dside_cons, <- IH. reflexivity.
Qed.

(** ** Trim trailing (outermost) blank runs *)

Fixpoint trim_blanks (rs : list SRun) : list SRun :=
  match rs with
  | [] => []
  | (s, e) :: t =>
      match trim_blanks t with
      | [] => if sym_eqb s S0 then [] else [(s, e)]
      | t' => (s, e) :: t'
      end
  end.

Lemma lift_side_blank_app : forall n b,
  lift_side b = blank_side ->
  lift_side (repeat S0 n ++ b) = blank_side.
Proof.
  intros n b Hb. apply functional_extensionality; intro i.
  destruct (Nat.lt_ge_cases i (length (repeat S0 n))) as [Hlt | Hge].
  - unfold lift_side.
    rewrite nthb_app_left by assumption.
    rewrite repeat_length in Hlt.
    apply nthb_repeat; assumption.
  - unfold lift_side.
    rewrite nthb_app_right by assumption.
    change (lift_side b (i - length (repeat S0 n)) = blank_side i).
    rewrite Hb. reflexivity.
Qed.

Lemma trim_blanks_den : forall rs nu,
  lift_side (dside nu (trim_blanks rs)) = lift_side (dside nu rs).
Proof.
  induction rs as [|[s e] t IH]; intro nu; simpl; [reflexivity|].
  specialize (IH nu).
  destruct (trim_blanks t) as [|r' t'] eqn:Et.
  - assert (Hbl : lift_side (dside nu t) = blank_side).
    { rewrite <- IH. apply lift_side_nil. }
    destruct (sym_eqb s S0) eqn:Hs.
    + apply sym_eqb_spec in Hs; subst s.
      change (dside nu []) with (@nil Sym).
      rewrite lift_side_nil.
      symmetry. apply lift_side_blank_app. exact Hbl.
    + rewrite dside_cons.
      apply lift_side_app.
      change (dside nu []) with (@nil Sym).
      rewrite lift_side_nil, Hbl. reflexivity.
  - rewrite dside_cons.
    apply lift_side_app. exact IH.
Qed.

Lemma cnt_ext : forall e f g,
  (forall j, f j = g j) -> cnt f e = cnt g e.
Proof. intros. unfold cnt. rewrite (eval_ext e f g); auto. Qed.

Lemma dside_ext : forall rs f g,
  (forall j, f j = g j) -> dside f rs = dside g rs.
Proof.
  induction rs as [|[s e] t IH]; intros f g H; [reflexivity|].
  rewrite !dside_cons, (cnt_ext e f g H), (IH f g H). reflexivity.
Qed.
