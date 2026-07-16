(** * IRules.Expr: affine expressions over bounded variables.

    The count language of the inductive-rules certificates (BBB
    docs/irules.md "Configurations"): an expression is
    [c0 + sum_i cf_i * x_i] with integer constant [c0] and
    coefficients [cf_i], evaluated at a valuation [nu : nat -> Z].
    The engine only ever needs *provable lower bounds* under a
    vector [lo] of per-variable lower bounds: when every coefficient
    is nonnegative, the evaluation at [lo] itself ([elo]) is the
    minimum over all valuations [nu >= lo] ([elo_le_eval]).

    In the main meta-cycle replay the only variable is [k] (index
    0, bound [kmin]); in a rule-validation replay the variables are
    the rule's fresh generalization variables (bounds = the rule's
    [lb_i]).  Everything here is variable-count agnostic.

    Run counts denote tape cell multiplicities through [cnt]
    ([Z.to_nat] of the evaluation); the checker guards every place
    that needs positivity with [expr_ge], so no global invariant on
    expressions is required. *)

From Coq Require Import Arith ZArith Lia Bool List.
Import ListNotations.
Open Scope Z_scope.

Record Expr : Set := mkExpr { e_c0 : Z; e_cf : list Z }.

(** Evaluation at a valuation. *)
Fixpoint dot (cf : list Z) (nu : nat -> Z) (i : nat) : Z :=
  match cf with
  | [] => 0
  | c :: t => c * nu i + dot t nu (S i)
  end.

Definition eval (nu : nat -> Z) (e : Expr) : Z :=
  e_c0 e + dot (e_cf e) nu 0.

(** A bounds vector: variable [i] is known to satisfy
    [nth i lo 0 <= nu i].  Out-of-range variables get bound 0; the
    valuations the soundness proofs instantiate are nonnegative
    everywhere, so this costs nothing. *)
Definition bge (lo : list Z) (nu : nat -> Z) : Prop :=
  forall i, nth i lo 0 <= nu i.

Definition lo_nu (lo : list Z) : nat -> Z := fun i => nth i lo 0.

Definition elo (lo : list Z) (e : Expr) : Z := eval (lo_nu lo) e.

Fixpoint cf_nonneg (cf : list Z) : bool :=
  match cf with
  | [] => true
  | c :: t => (0 <=? c) && cf_nonneg t
  end.

Lemma dot_le : forall cf nu1 nu2 i,
  cf_nonneg cf = true ->
  (forall j, nu1 j <= nu2 j) ->
  dot cf nu1 i <= dot cf nu2 i.
Proof.
  induction cf as [|c t IH]; intros nu1 nu2 i Hnn Hle; simpl.
  - lia.
  - simpl in Hnn. apply andb_prop in Hnn as [Hc Ht].
    apply Z.leb_le in Hc.
    specialize (IH nu1 nu2 (S i) Ht Hle).
    specialize (Hle i). nia.
Qed.

Lemma elo_le_eval : forall lo e nu,
  cf_nonneg (e_cf e) = true -> bge lo nu -> elo lo e <= eval nu e.
Proof.
  intros lo e nu Hnn Hb.
  unfold elo, eval.
  pose proof (dot_le (e_cf e) (lo_nu lo) nu 0 Hnn Hb). lia.
Qed.

(** The one bound-checking primitive: [need <= eval nu e] provably,
    for every [nu >= lo]. *)
Definition expr_ge (lo : list Z) (e : Expr) (need : Z) : bool :=
  cf_nonneg (e_cf e) && (need <=? elo lo e).

Lemma expr_ge_sound : forall lo e need nu,
  expr_ge lo e need = true -> bge lo nu -> need <= eval nu e.
Proof.
  intros lo e need nu H Hb.
  apply andb_prop in H as [Hnn Hle].
  apply Z.leb_le in Hle.
  pose proof (elo_le_eval lo e nu Hnn Hb). lia.
Qed.

(** ** Constructors and arithmetic *)

Definition econst (v : Z) : Expr := mkExpr v [].

Fixpoint unit_cf (i : nat) : list Z :=
  match i with
  | O => [1]
  | S j => 0 :: unit_cf j
  end.

(** The variable [x_i], as an expression. *)
Definition evar (i : nat) : Expr := mkExpr 0 (unit_cf i).

Lemma dot_unit : forall i nu j, dot (unit_cf i) nu j = nu (i + j)%nat.
Proof.
  induction i as [|i IH]; intros nu j; simpl.
  - destruct (nu j); reflexivity.
  - rewrite IH.
    replace ((i + S j)%nat) with ((S (i + j))%nat) by lia. lia.
Qed.

Lemma eval_evar : forall nu i, eval nu (evar i) = nu i.
Proof.
  intros. unfold eval, evar. simpl.
  rewrite dot_unit. rewrite Nat.add_0_r. lia.
Qed.

Lemma eval_econst : forall nu v, eval nu (econst v) = v.
Proof. intros. unfold eval, econst. simpl. lia. Qed.

(** Pointwise coefficient combination: [a + d * b]. *)
Fixpoint cf_scale (d : Z) (b : list Z) : list Z :=
  match b with
  | [] => []
  | cb :: tb => d * cb :: cf_scale d tb
  end.

Fixpoint cf_addmul (a : list Z) (d : Z) (b : list Z) : list Z :=
  match a, b with
  | [], _ => cf_scale d b
  | _, [] => a
  | ca :: ta, cb :: tb => ca + d * cb :: cf_addmul ta d tb
  end.

Definition eaddmul (a : Expr) (d : Z) (b : Expr) : Expr :=
  mkExpr (e_c0 a + d * e_c0 b) (cf_addmul (e_cf a) d (e_cf b)).

Lemma dot_scale : forall b d nu i,
  dot (cf_scale d b) nu i = d * dot b nu i.
Proof.
  induction b as [|cb tb IH]; intros d nu i; simpl; [lia|].
  rewrite IH. lia.
Qed.

Lemma dot_addmul : forall a d b nu i,
  dot (cf_addmul a d b) nu i = dot a nu i + d * dot b nu i.
Proof.
  induction a as [|ca ta IH]; intros d b nu i.
  - simpl. rewrite dot_scale. lia.
  - destruct b as [|cb tb]; simpl; [lia | rewrite IH; lia].
Qed.

Lemma eval_eaddmul : forall nu a d b,
  eval nu (eaddmul a d b) = eval nu a + d * eval nu b.
Proof.
  intros. unfold eval, eaddmul. simpl. rewrite dot_addmul. lia.
Qed.

Definition eadd (a b : Expr) : Expr := eaddmul a 1 b.

Lemma eval_eadd : forall nu a b, eval nu (eadd a b) = eval nu a + eval nu b.
Proof. intros. unfold eadd. rewrite eval_eaddmul. lia. Qed.

Definition eaddc (a : Expr) (v : Z) : Expr :=
  mkExpr (e_c0 a + v) (e_cf a).

Lemma eval_eaddc : forall nu a v, eval nu (eaddc a v) = eval nu a + v.
Proof. intros. unfold eval, eaddc. simpl. lia. Qed.

(** ** Decidable equality (up to trailing zero coefficients) *)

Fixpoint cf_zeros (a : list Z) : bool :=
  match a with
  | [] => true
  | c :: t => (c =? 0) && cf_zeros t
  end.

Fixpoint cf_eqb (a b : list Z) : bool :=
  match a, b with
  | [], _ => cf_zeros b
  | _, [] => cf_zeros a
  | ca :: ta, cb :: tb => (ca =? cb) && cf_eqb ta tb
  end.

Definition eeqb (a b : Expr) : bool :=
  (e_c0 a =? e_c0 b) && cf_eqb (e_cf a) (e_cf b).

Lemma cf_zeros_dot : forall a nu i, cf_zeros a = true -> dot a nu i = 0.
Proof.
  induction a as [|c t IH]; intros nu i H; simpl in *; [reflexivity|].
  apply andb_prop in H as [Hc Ht].
  apply Z.eqb_eq in Hc. rewrite (IH nu (S i) Ht). lia.
Qed.

Lemma cf_eqb_dot : forall a b nu i,
  cf_eqb a b = true -> dot a nu i = dot b nu i.
Proof.
  induction a as [|ca ta IH]; intros b nu i H.
  - simpl in H. rewrite (cf_zeros_dot b nu i H). reflexivity.
  - destruct b as [|cb tb]; simpl in H.
    + rewrite (cf_zeros_dot (ca :: ta) nu i H). reflexivity.
    + apply andb_prop in H as [Hc Ht].
      apply Z.eqb_eq in Hc. simpl.
      rewrite (IH tb nu (S i) Ht). lia.
Qed.

Lemma eeqb_eval : forall a b nu, eeqb a b = true -> eval nu a = eval nu b.
Proof.
  intros a b nu H. apply andb_prop in H as [Hc Hcf].
  apply Z.eqb_eq in Hc. unfold eval.
  rewrite (cf_eqb_dot _ _ nu 0 Hcf). lia.
Qed.

(** ** Denoted cell counts *)

Definition cnt (nu : nat -> Z) (e : Expr) : nat := Z.to_nat (eval nu e).

Lemma cnt_eeqb : forall a b nu, eeqb a b = true -> cnt nu a = cnt nu b.
Proof. intros. unfold cnt. rewrite (eeqb_eval a b nu); auto. Qed.

Lemma cnt_add : forall nu a b,
  0 <= eval nu a -> 0 <= eval nu b ->
  cnt nu (eadd a b) = (cnt nu a + cnt nu b)%nat.
Proof.
  intros. unfold cnt. rewrite eval_eadd. lia.
Qed.

(** Evaluation only depends on the valuation pointwise. *)
Lemma dot_ext : forall cf f g i,
  (forall j, f j = g j) -> dot cf f i = dot cf g i.
Proof.
  induction cf as [|c t IH]; intros f g i H; simpl; [reflexivity|].
  rewrite (H i), (IH f g (S i) H). reflexivity.
Qed.

Lemma eval_ext : forall e f g,
  (forall j, f j = g j) -> eval f e = eval g e.
Proof.
  intros. unfold eval. rewrite (dot_ext _ f g 0); auto.
Qed.
