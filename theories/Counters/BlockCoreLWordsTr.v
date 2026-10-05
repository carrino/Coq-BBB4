(** * Counters.BlockCoreLWordsTr: a productive run-list grammar

    Runs are positive lengths of consecutive ones, separated by zeros.
    [bl_tr] is the run form of the partial left-word transformation T.
    [bl_ur] increments the first output run.  The relation avoids a
    default value for the undefined all-even-run case.

    The run [2] commutes with U.  Four finite prefixes satisfy
      U(P0 w)=P1 U(w), U(P1 w)=P2 w,
      U(P2 w)=P3 w, U(P3 w)=2 2 P0 w,
    where P0=[8].  The two seed families beginning [1;2;1] and [1;3;1]
    each have nine phases and then become four [2] runs followed by
    P0 and the other seed.  Structural induction on this grammar
    proves that U always has another output in the grammar.

    Finally, two T passes on [4]++w produce [4]++U(w).  All lemmas in
    this file are closed under the global context. *)
From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement.
Import ListNotations.
Fixpoint bl_runs(w:list nat):list Sym:=match w with
|[]=>[]|a::xs=>repeat S1 a++match xs with[]=>[]|_::_=>S0::bl_runs xs end end.
Definition bl_inc(w:list nat):list nat:=match w with[]=>[]|a::xs=>S a::xs end.
Inductive bl_tr:list nat->list nat->Prop:=
| bl_tr_last:bl_tr[1][2;1]
| bl_tr_stop:forall b xs,1<=b->bl_tr(1::b::xs)((b+3)::xs)
| bl_tr_carry:forall a xs ys,1<=a->bl_tr(a::xs)ys->bl_tr(S(S a)::xs)(1::ys)
| bl_tr_even:forall xs ys,bl_tr xs ys->bl_tr(2::xs)(1::bl_inc ys).
Definition bl_ur(xs ys:list nat):Prop:=exists z,bl_tr xs z/\ys=bl_inc z.
Definition bl_P0:list nat:=[8].
Definition bl_P1:list nat:=[2;1;1;1].
Definition bl_P2:list nat:=[2;5;1].
Definition bl_P3:list nat:=[2;2;1;4].
Definition bl_seeds:list(list nat):=[
 [1;2;1];[6;1];[1;1;3;1];[5;3;1];[1;6;1];[10;1];[1;1;1;1;3;1];[5;1;1;3;1];[1;4;1;3;1];
 [1;3;1];[7;1];[1;1;4];[5;4];[1;7];[11];[1;1;1;1;2;1];[5;1;1;2;1];[1;4;1;2;1]].
Inductive bl_good:list nat->Prop:=
| bl_good_seed:forall x,In x bl_seeds->bl_good x
| bl_good_two:forall x,bl_good x->bl_good(2::x)
| bl_good_P0:forall x,bl_good x->bl_good(bl_P0++x)
| bl_good_P1:forall x,bl_good x->bl_good(bl_P1++x)
| bl_good_P2:forall x,bl_good x->bl_good(bl_P2++x)
| bl_good_P3:forall x,bl_good x->bl_good(bl_P3++x).
Local Ltac solve_tr:=first
 [apply bl_tr_last
 |apply bl_tr_stop;lia
 |apply bl_tr_even;solve_tr
 |eapply bl_tr_carry;[lia|solve_tr]].
Lemma bl_ur_two:forall x y,bl_ur x y->bl_ur(2::x)(2::y).
Proof. intros x y(z&HT&->);exists(1::bl_inc z);split;[constructor;exact HT|reflexivity]. Qed.
Lemma bl_ur_P0:forall x y,bl_ur x y->bl_ur(bl_P0++x)(bl_P1++y).
Proof.
 intros x y(z&HT&->). exists([1;1;1;1]++bl_inc z).
 split;[unfold bl_P0;cbn[app];repeat(eapply bl_tr_carry;[lia|]);apply bl_tr_even;exact HT|reflexivity].
Qed.
Lemma bl_ur_P1:forall x,bl_ur(bl_P1++x)(bl_P2++x).
Proof. intro x;unfold bl_ur,bl_P1,bl_P2;cbn[app];eexists;split;[solve_tr|reflexivity]. Qed.
Lemma bl_ur_P2:forall x,bl_ur(bl_P2++x)(bl_P3++x).
Proof. intro x;unfold bl_ur,bl_P2,bl_P3;cbn[app];eexists;split;[solve_tr|reflexivity]. Qed.
Lemma bl_ur_P3:forall x,bl_ur(bl_P3++x)(2::2::bl_P0++x).
Proof. intro x;unfold bl_ur,bl_P3,bl_P0;cbn[app];eexists;split;[solve_tr|reflexivity]. Qed.
Lemma bl_seed_step:forall x,In x bl_seeds->exists y,bl_ur x y/\bl_good y.
Proof.
 intros x H;unfold bl_seeds in H;cbn in H.
 repeat destruct H as[<-|H];try contradiction.
 all:(eexists;split;[unfold bl_ur;eexists;split;[solve_tr|reflexivity]|cbn[bl_inc Nat.add];
 repeat apply bl_good_two;
 first[apply bl_good_seed;unfold bl_seeds;cbn;tauto
 |match goal with |- bl_good(8::?x)=>change(bl_good(bl_P0++x)) end;apply bl_good_P0,bl_good_seed;unfold bl_seeds;cbn;tauto]]).
Qed.
Theorem bl_good_step:forall x,bl_good x->exists y,bl_ur x y/\bl_good y.
Proof.
 intros x H;induction H.
 - apply bl_seed_step;assumption.
 - destruct IHbl_good as(y&HY&HG);exists(2::y);split;[apply bl_ur_two;exact HY|constructor;exact HG].
 - destruct IHbl_good as(y&HY&HG);exists(bl_P1++y);split;[apply bl_ur_P0;exact HY|constructor;exact HG].
 - exists(bl_P2++x);split;[apply bl_ur_P1|constructor;exact H].
 - exists(bl_P3++x);split;[apply bl_ur_P2|constructor;exact H].
 - exists(2::2::bl_P0++x);split;[apply bl_ur_P3|apply bl_good_two,bl_good_two,bl_good_P0;exact H].
Qed.
Lemma bl_inc_positive:forall x,Forall(fun a=>1<=a)x->Forall(fun a=>1<=a)(bl_inc x).
Proof. intros x H;destruct x;cbn[bl_inc];[constructor|inversion H;constructor;auto;lia]. Qed.
Lemma bl_tr_positive:forall x y,bl_tr x y->Forall(fun a=>1<=a)x->Forall(fun a=>1<=a)y.
Proof.
 intros x y H;induction H;intro HP.
 - repeat constructor;lia.
 - apply Forall_inv_tail in HP. apply Forall_inv_tail in HP. constructor;[lia|exact HP].
 - apply Forall_inv_tail in HP. constructor;[lia|apply IHbl_tr;constructor;assumption].
 - apply Forall_inv_tail in HP. constructor;[lia|apply bl_inc_positive,IHbl_tr;assumption].
Qed.
Lemma bl_good_positive:forall x,bl_good x->Forall(fun a=>1<=a)x.
Proof.
 intros x H;induction H.
 - unfold bl_seeds in H;cbn in H;repeat destruct H as[<-|H];try contradiction;repeat constructor;lia.
 - constructor;[lia|assumption].
 - unfold bl_P0;cbn[app];repeat constructor;auto;lia.
 - unfold bl_P1;cbn[app];repeat constructor;auto;lia.
 - unfold bl_P2;cbn[app];repeat constructor;auto;lia.
 - unfold bl_P3;cbn[app];repeat constructor;auto;lia.
Qed.
Lemma bl_good_initial:bl_good[7;1].
Proof. apply bl_good_seed;unfold bl_seeds;cbn;tauto. Qed.
Lemma bl_pair_step:forall x y,bl_ur x y->exists z,bl_tr(4::x)z/\bl_tr z(4::y).
Proof.
 intros x y(v&HT&->). exists(1::1::bl_inc v);split.
 - eapply bl_tr_carry;[lia|apply bl_tr_even;exact HT].
 - replace 4 with(1+3)by lia;apply bl_tr_stop;lia.
Qed.
Lemma bl_good_nonempty:forall x,bl_good x->x<>[].
Proof.
 intros x H;induction H;try discriminate.
 - unfold bl_seeds in H;cbn in H;repeat destruct H as[<-|H];try contradiction;discriminate.
Qed.
Lemma bl_tr_nonempty:forall x y,bl_tr x y->x<>[]/\y<>[].
Proof. intros x y H;inversion H;subst;split;discriminate. Qed.
Lemma bl_runs_inc:forall x,x<>[]->bl_runs(bl_inc x)=S1::bl_runs x.
Proof. intros[|a x]H;[contradiction|destruct x;reflexivity]. Qed.
