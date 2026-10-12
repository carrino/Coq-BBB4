(** Avoid allocating the unary census bound for every small comparison.

    The numeral conversion is checked once. Every caller still proves its
    original [Nat.leb] goal through [bound_tr_leb]; only the computation used
    to discharge that goal works on binary naturals. *)
From Coq Require Import Arith NArith.

Lemma bound_tr_as_N : N.of_nat 32779478 = 32779478%N.
Proof. native_cast_no_check (eq_refl 32779478%N). Qed.

Lemma bound_tr_leb : forall n,
  (N.of_nat n <=? 32779478)%N = true -> (n <=? 32779478) = true.
Proof.
  intros n H. apply Nat.leb_le. apply Nat.compare_le_iff.
  rewrite Nat2N.inj_compare, bound_tr_as_N.
  apply N.compare_le_iff. now apply N.leb_le.
Qed.
