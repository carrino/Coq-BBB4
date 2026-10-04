(** * Signed binary words for a two-sweep counter

    Tokens encode a digit as [digit;0;0] and terminate with [1].
    The signed value is V([])=-1, V(0w)=2V(w), V(1w)=-2V(w)-1.
    The successor increases V by one on nonempty words. Positive words
    therefore remain nonempty, excluding the terminal escape case.
    A marked B0 anchor has left (10)^(2n)1, n>=1, and a positive word. *)
From Coq Require Import Arith Lia List ZArith.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Counters Require Import WTape NestCountTr LoopRunTr.
Import ListNotations.
Fixpoint bk_encode(w:list Sym):list Sym:=match w with
|[]=>[S1]|d::w=>d::S0::S0::bk_encode w end.
Definition bk_H(w:list Sym):list Sym:=match w with
|[]=>[]|S0::w=>S1::S1::w|S1::w=>S1::S0::w end.
Fixpoint bk_F(w:list Sym):list Sym:=match w with
|[]=>[S1]|S0::w=>S0::bk_F w|S1::w=>bk_H w end.
Definition bk_S(w:list Sym):list Sym:=match w with
|[]=>[]|S0::w=>bk_H w|S1::w=>S0::bk_F w end.
Fixpoint bk_value(w:list Sym):Z:=match w with
|[] => (-1)%Z|S0::w=>(2*bk_value w)%Z|S1::w=>(-2*bk_value w-1)%Z end.
Lemma bk_H_value:forall w,bk_value(bk_H w)=(2*bk_value w+1)%Z.
Proof. intros[|[]w];cbn[bk_H bk_value];ring. Qed.
Lemma bk_F_value:forall w,bk_value(bk_F w)=(-bk_value w)%Z.
Proof. induction w as[|[]w IH];cbn[bk_F bk_value];try rewrite bk_H_value;try rewrite IH;ring. Qed.
Lemma bk_S_value:forall w,w<>[]->bk_value(bk_S w)=(bk_value w+1)%Z.
Proof. intros[|[]w]H;[contradiction| |];cbn[bk_S bk_value];rewrite ?bk_H_value,?bk_F_value;ring. Qed.
Lemma bk_positive_nonempty:forall w,(0<bk_value w)%Z->w<>[].
Proof. intros w H E;subst;cbn[bk_value]in H;lia. Qed.
Lemma bk_S_positive:forall w,(0<bk_value w)%Z->(0<bk_value(bk_S w))%Z.
Proof. intros;rewrite bk_S_value;[lia|apply bk_positive_nonempty;assumption]. Qed.
Definition bk_anchor(n:nat)(w:list Sym):cconf:=
 (StB,(rep[S1;S0](2*n)++[S1],S0,bk_encode w)).
Inductive bk_mark:cconf->Prop:=
|bk_marked:forall n w,1<=n->(0<bk_value w)%Z->bk_mark(bk_anchor n w).
