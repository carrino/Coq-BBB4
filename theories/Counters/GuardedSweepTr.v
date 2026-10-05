(** Repeated finite sweeps with an unchanged guard beside the head. *)
From Coq Require Import List.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Counters Require Import WTape NestCountTr LoopRunTr.
Import ListNotations.
Section Sweeps.
Variable tm:TM.
Lemma guarded_sweepR:forall q guard input output,
 (forall L R,Reach0 tm(cR q(guard++L)(input++R))
                      (cR q(guard++output++L)R))->
 forall n L R,Reach0 tm(cR q(guard++L)(rep input n++R))
                       (cR q(guard++rep output n++L)R).
Proof.
 intros q guard input output H n;induction n as[|n IH];intros L R.
 - cbn[rep];apply reach0_refl.
 - cbn[rep];rewrite <-app_assoc.
   eapply reach0_trans;[apply H|].
   eapply reach0_trans;[apply IH|].
   rewrite (app_assoc (rep output n) output L),rep_comm.
   repeat rewrite <-app_assoc;apply reach0_refl.
Qed.
Lemma guarded_sweepL:forall q guard input output,
 (forall L R,Reach0 tm(cL q(input++L)(guard++R))
                      (cL q L(guard++output++R)))->
 forall n L R,Reach0 tm(cL q(rep input n++L)(guard++R))
                       (cL q L(guard++rep output n++R)).
Proof.
 intros q guard input output H n;induction n as[|n IH];intros L R.
 - cbn[rep];apply reach0_refl.
 - cbn[rep];rewrite <-app_assoc.
   eapply reach0_trans;[apply H|].
   eapply reach0_trans;[apply IH|].
   rewrite (app_assoc (rep output n) output R),rep_comm.
   repeat rewrite <-app_assoc;apply reach0_refl.
Qed.
End Sweeps.
Lemma rep_rotate_prefix:forall(X Y:list Sym)n,
 X++rep(Y++X)n=rep(X++Y)n++X.
Proof.
 intros X Y n;induction n as[|n IH].
 - cbn[rep];rewrite app_nil_r;reflexivity.
 - cbn[rep];repeat rewrite <-app_assoc;rewrite IH;repeat rewrite <-app_assoc;reflexivity.
Qed.
Lemma rep_rotate_block:forall(X Y:list Sym)n,
 X++rep(Y++X)n++Y=rep(X++Y)(S n).
Proof.
 intros. rewrite app_assoc,rep_rotate_prefix,<-app_assoc.
 change(rep(X++Y)n++(X++Y)=rep(X++Y)(S n)).
 rewrite rep_comm;reflexivity.
Qed.
