(** * IRules.StreamEq2: multi-run cell-stream equality for the v5c end-match.

    [StreamEq.cseq] recognises a symbolic cell-stream equality only when
    each side has AT MOST ONE variable-count run ([exp1] fails on two).
    The 8 remaining v5-gap scalar machines close the meta cycle on a
    configuration that is CELL-equal to the shifted template but whose
    two sides each carry TWO variable-count runs -- e.g.
    [b1^3 . b10^(k+1) . b1^7 . b0 . b1^(1+3k) . b0 . b1^3] denotes the
    same tape as [b1^7 . b6^(k+1) . b1^3 . b0 . b1^(1+3k) . b0 . b1^3]
    (the trailing [b1^(1+3k) . b0 . b1^3] is common; the leading
    one-pump prefixes are conjugate).  The C verifier's [iv_streams_eq]
    walks the cells symbolically and accepts.

    [cseq2] recognises exactly this shape SOUNDLY by reduction to the
    landed [cseq]: strip the maximal common (syntactically-equal) run
    prefix and suffix from the two sides, then apply the one-pump
    [cseq] to the residues.  Stripping common runs is denotation-
    preserving by construction (identical runs denote identical cells),
    so [cseq2_sound] reduces to [cseq_sound] with two [bdside_app]
    rewrites.  [Print Assumptions cseq2_sound] / [bend_eqb3_bsem] is
    [functional_extensionality_dep] only. *)

From Coq Require Import Arith ZArith Lia Bool List.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Checkers.IRules Require Import Expr RLE Engine EngineK RulesBlk
     StreamEq.
Import ListNotations.
Open Scope Z_scope.

(** ** Syntactic run equality *)

Fixpoint lzeqb (a b : list Z) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => Z.eqb x y && lzeqb a' b'
  | _, _ => false
  end.

Lemma lzeqb_eq : forall a b, lzeqb a b = true -> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b] H; simpl in H; try discriminate;
    [reflexivity|].
  apply andb_prop in H as [Hx Ht]. apply Z.eqb_eq in Hx.
  rewrite Hx, (IH b Ht). reflexivity.
Qed.

Definition xexpr_eqb (a b : Expr) : bool :=
  (e_c0 a =? e_c0 b) && lzeqb (e_cf a) (e_cf b).

Lemma xexpr_eqb_eq : forall a b, xexpr_eqb a b = true -> a = b.
Proof.
  intros [c0a cfa] [c0b cfb] H. unfold xexpr_eqb in H. simpl in H.
  apply andb_prop in H as [Hc Hf]. apply Z.eqb_eq in Hc.
  apply lzeqb_eq in Hf. subst. reflexivity.
Qed.

Definition brun_eqb (a b : BRun) : bool :=
  Nat.eqb (fst a) (fst b) && xexpr_eqb (snd a) (snd b).

Lemma brun_eqb_eq : forall a b, brun_eqb a b = true -> a = b.
Proof.
  intros [sa ea] [sb eb] H. unfold brun_eqb in H. simpl in H.
  apply andb_prop in H as [Hs He]. apply Nat.eqb_eq in Hs.
  apply xexpr_eqb_eq in He. subst. reflexivity.
Qed.

(** ** Stripping the common run prefix / suffix *)

Fixpoint strip_pre (xa xb : list BRun) : (list BRun * list BRun) :=
  match xa, xb with
  | ra :: ta, rb :: tb =>
      if brun_eqb ra rb then strip_pre ta tb else (xa, xb)
  | _, _ => (xa, xb)
  end.

Lemma strip_pre_correct : forall xa xb a b,
  strip_pre xa xb = (a, b) -> exists p, xa = p ++ a /\ xb = p ++ b.
Proof.
  induction xa as [|ra ta IH]; intros xb a b H; simpl in H.
  - injection H as <- <-. exists []. split; reflexivity.
  - destruct xb as [|rb tb].
    + injection H as <- <-. exists []. split; reflexivity.
    + destruct (brun_eqb ra rb) eqn:E.
      * apply brun_eqb_eq in E; subst rb.
        destruct (IH tb a b H) as [p [Hp1 Hp2]].
        exists (ra :: p). simpl. rewrite Hp1, Hp2. split; reflexivity.
      * injection H as <- <-. exists []. split; reflexivity.
Qed.

Definition strip_common (xa xb : list BRun) : (list BRun * list BRun) :=
  let '(a1, b1) := strip_pre xa xb in
  let '(a2, b2) := strip_pre (rev a1) (rev b1) in
  (rev a2, rev b2).

Lemma strip_common_correct : forall xa xb a b,
  strip_common xa xb = (a, b) ->
  exists p s, xa = p ++ a ++ s /\ xb = p ++ b ++ s.
Proof.
  intros xa xb a b H. unfold strip_common in H.
  destruct (strip_pre xa xb) as [a1 b1] eqn:E1.
  destruct (strip_pre (rev a1) (rev b1)) as [a2 b2] eqn:E2.
  injection H as <- <-.
  destruct (strip_pre_correct xa xb a1 b1 E1) as [p [Hxa Hxb]].
  destruct (strip_pre_correct (rev a1) (rev b1) a2 b2 E2) as [q [Ha1 Hb1]].
  (* rev a1 = q ++ a2  ->  a1 = rev a2 ++ rev q *)
  assert (Ha1' : a1 = rev a2 ++ rev q).
  { rewrite <- (rev_involutive a1), Ha1, rev_app_distr. reflexivity. }
  assert (Hb1' : b1 = rev b2 ++ rev q).
  { rewrite <- (rev_involutive b1), Hb1, rev_app_distr. reflexivity. }
  exists p, (rev q). split.
  - rewrite Hxa, Ha1', app_assoc. reflexivity.
  - rewrite Hxb, Hb1', app_assoc. reflexivity.
Qed.

(** ** The recognizer *)

Definition cseq2 (tbl : BTbl) (lo : list Z) (xa xb : list BRun) : bool :=
  let '(a, b) := strip_common xa xb in cseq tbl lo a b.

Theorem cseq2_sound : forall tbl lo xa xb nu,
  bge lo nu ->
  cseq2 tbl lo xa xb = true ->
  bdside tbl nu xa = bdside tbl nu xb.
Proof.
  intros tbl lo xa xb nu Hb H. unfold cseq2 in H.
  destruct (strip_common xa xb) as [a b] eqn:Hsc.
  destruct (strip_common_correct xa xb a b Hsc) as [p [s [Hxa Hxb]]].
  subst xa xb.
  rewrite !bdside_app.
  rewrite (cseq_sound tbl lo a b nu Hb H). reflexivity.
Qed.

(** ** The v5c end-match and its denotation soundness *)

Definition bend_eqb3 (tbl : BTbl) (lo : list Z) (c want : BCfg) : bool :=
  bend_eqb2 tbl lo c want
  || (st_eqb (b_st c) (b_st want) && sym_eqb (b_hs c) (b_hs want)
      && cseq2 tbl lo (b_L c) (b_L want)
      && cseq2 tbl lo (b_R c) (b_R want)).

Theorem bend_eqb3_bsem : forall tbl lo c want nu,
  raw_ok tbl -> bge lo nu ->
  bend_eqb3 tbl lo c want = true -> bsem tbl nu c = bsem tbl nu want.
Proof.
  intros tbl lo c want nu Hraw Hb H. unfold bend_eqb3 in H.
  apply orb_prop in H as [H | H].
  - exact (bend_eqb2_bsem tbl lo c want nu Hraw Hb H).
  - apply andb_prop in H as [H HR].
    apply andb_prop in H as [H HL].
    apply andb_prop in H as [Hst Hhs].
    apply st_eqb_spec in Hst. apply sym_eqb_spec in Hhs.
    unfold bsem, bdcfg. rewrite Hst, Hhs.
    rewrite (cseq2_sound tbl lo _ _ nu Hb HL).
    rewrite (cseq2_sound tbl lo _ _ nu Hb HR). reflexivity.
Qed.
