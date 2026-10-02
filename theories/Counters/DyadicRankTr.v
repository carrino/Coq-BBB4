(** * A decreasing binary-complement rank for a fixed tape window.

    [u] is the reversed prefix to the left of the current zero; [v] is
    the suffix to its right.  The complement value strictly decreases
    when a macro changes the first differing bit from zero to one.
    Multiplication by [N+1] dominates any movement within the window;
    a move with unchanged bits decreases the head-index component. *)
From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement CTape.
Import ListNotations.

Fixpoint dw_z (w:list Sym) : nat :=
 match w with []=>0|S0::v=>2^length v+dw_z v|S1::v=>dw_z v end.
Lemma dw_z_bound : forall w, dw_z w < 2^length w.
Proof.
 induction w as [|[] w IH];simpl in *;lia.
Qed.
Lemma dw_z_app : forall u v,
 dw_z (u++v) = dw_z u * 2^length v + dw_z v.
Proof.
 induction u as [|[] u IH];intro v;cbn [dw_z length app];try lia.
 - rewrite app_length,Nat.pow_add_r,IH. nia.
 - rewrite IH. lia.
Qed.
Lemma dw_z_flip : forall p a b, length a=length b ->
 dw_z (p++S1::b) < dw_z (p++S0::a).
Proof.
 intros p a b H. rewrite !dw_z_app. cbn [dw_z length]. rewrite H.
 pose proof (dw_z_bound b). lia.
Qed.
Definition dw_full u v := rev u ++ S0::v.
Definition dw_rank N u v := (N+1)*dw_z (dw_full u v)+length u.
Lemma dw_rank_right : forall N u m v,
 length u+1+(m+1+length v)=N ->
 dw_rank N (repeat S0 m++S1::u) v < dw_rank N u (repeat S1 m++S0::v).
Proof.
 intros N u m v Hn. unfold dw_rank,dw_full.
 rewrite rev_app_distr. cbn [rev app]. rewrite rev_repeat.
 rewrite <- !app_assoc. cbn [app].
 assert (Hz : dw_z (rev u ++ S1::repeat S0 m++S0::v) <
              dw_z (rev u ++ S0::repeat S1 m++S0::v)).
 { apply dw_z_flip. rewrite !app_length,!repeat_length. reflexivity. }
 rewrite app_length,repeat_length. cbn [length]. nia.
Qed.
Lemma dw_rank_left : forall N u m v,
 dw_rank N u (S0::repeat S1 (S m)++v) <
 dw_rank N (S0::u) (repeat S1 m++S0::v).
Proof.
 intros N u m v. unfold dw_rank,dw_full. cbn [rev length].
 rewrite <- !app_assoc. cbn [app].
 replace (repeat S1 (S m)++v) with (repeat S1 m++S1::v).
 2:{ replace (S m) with (m+1) by lia. rewrite repeat_app, <- app_assoc. reflexivity. }
 pose proof (dw_z_flip ((rev u++[S0;S0])++repeat S1 m) v v eq_refl) as Hz.
 rewrite <- !app_assoc in Hz. cbn [app] in Hz. nia.
Qed.
Lemma dw_rank_tail : forall N u v,
 dw_rank N u (S0::v) < dw_rank N (S0::u) v.
Proof.
 intros N u v. unfold dw_rank,dw_full. cbn [rev length].
 rewrite <- !app_assoc. cbn [app]. lia.
Qed.

Lemma dw_full_length : forall u v,
 length (dw_full u v)=length u+1+length v.
Proof. intros. unfold dw_full. rewrite app_length,rev_length. cbn [length];lia. Qed.

Lemma dw_right_length : forall u m v,
 length (repeat S0 m++S1::u)+1+length v =
 length u+1+length (repeat S1 m++S0::v).
Proof. intros. rewrite !app_length,!repeat_length. cbn [length];lia. Qed.

Lemma dw_left_length : forall u m v,
 length u+1+length (S0::repeat S1 (S m)++v) =
 length (S0::u)+1+length (repeat S1 m++S0::v).
Proof. intros. cbn [length]. rewrite !app_length,!repeat_length. cbn [length];lia. Qed.

Lemma dw_tail_length : forall u v,
 length u+1+length (S0::v) = length(S0::u)+1+length v.
Proof. intros. cbn [length];lia. Qed.
