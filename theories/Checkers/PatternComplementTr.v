(** Every nonblank pattern occurrence has a distinct chosen one cell.
    Its count is therefore bounded by the count of ones in that region. *)
From Coq Require Import Arith Lia Bool List ZArith.
From BBB4 Require Import BBB4_Statement CTape PattCount.
From BBB4.Checkers Require Import NGram.
Import ListNotations.
Lemma pc_nth_firstn_one:forall n xs k,
 nth k(firstn n xs)S0=S1 -> nth k xs S0=S1.
Proof.
 induction n as[|n IH];intros[|x xs][|k]H;cbn in H|-*;try discriminate;auto.
Qed.
Lemma pc_count_skip_cons:forall k x xs,
 count1(skipn k(x::xs))=nc1(nth k(x::xs)S0)+count1(skipn k xs).
Proof.
 induction k as[|k IH];intros x xs.
 - destruct x;reflexivity.
 - destruct xs as[|y xs];[destruct k;reflexivity|].
   cbn[skipn nth]. apply IH.
Qed.
Lemma pc_count_skip_le:forall k xs,count1(skipn k xs)<=count1 xs.
Proof.
 induction k as[|k IH];intros[|[]xs];cbn[skipn count1];try lia;specialize(IH xs);lia.
Qed.
Theorem occ_le_count1:forall p xs,In S1 p -> occ p xs<=count1 xs.
Proof.
 intros p xs H. destruct(In_nth_error p S1 H)as(k&Hk).
 assert(Hnth:nth k p S0=S1)by(exact(nth_error_nth p k S0 Hk)).
 assert(B:forall xs,occ p xs<=count1(skipn k xs)).
 { intro ys;induction ys as[|x ys IH];[apply Nat.le_0_l|].
   rewrite occ_cons,pc_count_skip_cons. destruct(prefix_eqb p(x::ys))eqn:E.
   - unfold prefix_eqb in E. apply syms_eqb_eq in E.
     rewrite E in Hnth. apply pc_nth_firstn_one in Hnth. rewrite Hnth. cbn[nc1];lia.
   - lia. }
 specialize(B xs). pose proof(pc_count_skip_le k xs);lia.
Qed.
Lemma pc_count1_app:forall xs ys,count1(xs++ys)=count1 xs+count1 ys.
Proof. induction xs as[|[]xs IH];intro ys;cbn[count1 app];rewrite ?IH;lia. Qed.
Lemma pc_count1_zeros:forall n,count1(repeat S0 n)=0.
Proof. induction n;cbn;auto. Qed.
Lemma pc_occ_one:forall xs,occ[S1]xs=count1 xs.
Proof. induction xs as[|[]xs IH];cbn[occ prefix_eqb syms_eqb firstn length sym_eqb count1];rewrite ?IH;reflexivity. Qed.
Lemma pc_count1_pad:forall p xs,
 count1(pm_pad p++xs++pm_pad p)=count1 xs.
Proof. intros. rewrite !pc_count1_app. unfold pm_pad. rewrite pc_count1_zeros. lia. Qed.
Lemma pc_pm_one_A:forall q L h R,
 pm_val[S1] RgA(q,(L,h,R))=count1(rev L++h::R).
Proof. intros. unfold pm_val,pm_pad;cbn[length Nat.sub repeat app]. rewrite app_nil_r,pc_occ_one;reflexivity. Qed.
Lemma pc_pm_one_L:forall q L h R,
 pm_val[S1] RgL(q,(L,h,R))=count1 L.
Proof. intros. unfold pm_val,pm_pad;cbn[length Nat.sub repeat rev app]. rewrite app_nil_r,pc_occ_one;reflexivity. Qed.
Lemma pc_pm_one_R:forall q L h R,
 pm_val[S1] RgR(q,(L,h,R))=count1 R.
Proof. intros. unfold pm_val,pm_pad;cbn[length Nat.sub repeat app]. rewrite app_nil_r,pc_occ_one;reflexivity. Qed.
Theorem pm_val_pattern_bound:forall p rg cc,
 In S1 p -> pm_val p rg cc<=pm_val[S1]rg cc.
Proof.
 intros p rg[q[[L h]R]]H. destruct rg.
 - rewrite pc_pm_one_A. unfold pm_val.
   eapply Nat.le_trans;[apply occ_le_count1;exact H|].
   replace(pm_pad p++rev L++h::R++pm_pad p)
    with(pm_pad p++(rev L++h::R)++pm_pad p)by(rewrite <-app_assoc;reflexivity).
   rewrite pc_count1_pad. reflexivity.
 - rewrite pc_pm_one_L. unfold pm_val.
   eapply Nat.le_trans;[apply occ_le_count1;rewrite <-in_rev;exact H|].
   rewrite pc_count1_app. unfold pm_pad. rewrite pc_count1_zeros. lia.
 - rewrite pc_pm_one_R. unfold pm_val.
   eapply Nat.le_trans;[apply occ_le_count1;exact H|].
   rewrite pc_count1_app. unfold pm_pad. rewrite pc_count1_zeros. lia.
Qed.

(** Distance to the farthest nonblank cell, measured from the near end. *)
Fixpoint pc_extent(xs:list Sym):nat :=
 match xs with
 | []=>0
 | S1::xs=>S(pc_extent xs)
 | S0::xs=>match pc_extent xs with 0=>0|S n=>S(S n)end
 end.
Lemma pc_extent_zero:forall xs,pc_extent xs=0 <-> count1 xs=0.
Proof.
 induction xs as[|[]xs IH];cbn;[tauto| |lia].
 destruct(pc_extent xs);simpl in IH|-*;lia.
Qed.
Lemma pc_count1_extent:forall xs,count1 xs<=pc_extent xs.
Proof.
 induction xs as[|[]xs IH];cbn;try lia.
 destruct(pc_extent xs);lia.
Qed.
Lemma pc_extent_push:forall x xs,
 pc_extent(x::xs)=pc_extent xs+(if (0<?count1 xs)||sym_eqb x S1 then 1 else 0).
Proof.
 intros[]xs;cbn[pc_extent sym_eqb orb].
 - destruct(pc_extent xs)eqn:E.
   + apply pc_extent_zero in E. rewrite E. reflexivity.
   + assert(P:0<count1 xs).
     { assert(count1 xs<>0).
       { intro Z. apply (proj2(pc_extent_zero xs))in Z. congruence. } lia. }
     apply Nat.ltb_lt in P. rewrite P. cbn;lia.
 - rewrite orb_true_r;lia.
Qed.
Lemma pc_extent_pop:forall x xs,
 Z.of_nat(pc_extent xs)=
 (Z.of_nat(pc_extent(x::xs))-(if Nat.ltb 0 (count1(x::xs))then 1 else 0))%Z.
Proof.
 intros x xs. rewrite pc_extent_push.
 destruct x;cbn[count1 sym_eqb]in *.
 - destruct(0<?count1 xs);cbn;lia.
 - destruct(0<?count1 xs);cbn;lia.
Qed.
