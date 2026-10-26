(** Binary place-value rankings over finite three-symbol tapes. *)
From Coq Require Import Arith Lia List ZArith.
From SmallBB Require Import Statement StatementTr CTape ClosureTr.
Import ListNotations.
Local Open Scope Z_scope.
Fixpoint fw_pow(n:nat):Z:=match n with O=>1|S n=>2*fw_pow n end.
Lemma fw_pow_pos:forall n,0<fw_pow n.
Proof. induction n;cbn [fw_pow];lia. Qed.
Definition fw_width(c:cconf):nat:=let '(_,(L,_,R)):=c in (length L+length R)%nat.
Fixpoint bsr_left(f:list Sym->Z)(L:list Sym):Z:=match L with
|[]=>0|_::U=>fw_pow(length U)*f L+bsr_left f U end.
Fixpoint bsr_right(f:list Sym->Z)(R:list Sym):Z:=match R with
|[]=>0|_::U=>f R+2*bsr_right f U end.
Definition bsr_potential(fl fr:list Sym->Z)(b:cconf->Z)(c:cconf):Z:=
 let '(_,(L,_,R)):=c in bsr_left fl L+fw_pow(length L)*(bsr_right fr R+b c).
Definition bsr_integer(fl fr:list Sym->Z)(b:cconf->Z)(K:Z)(c:cconf):Z:=
 K*fw_pow(fw_width c)+bsr_potential fl fr b c.
Definition bsr_measure(fl fr:list Sym->Z)(b:cconf->Z)(K:Z)(c:cconf):nat:=
 Z.to_nat(bsr_integer fl fr b K c).
Definition bsr_delta(fl fr:list Sym->Z)(b:cconf->Z)(c:cconf)(tr:Trans):Z:=
 let '(q,(L,h,R)):=c in let d:=(t_next tr,ctape_move(t_dir tr)(t_write tr)(L,h,R))in
 match t_dir tr with
 |DL=> -fl L+fr(t_write tr::R)+b d-2*b c
 |DR=> fl(t_write tr::L)-fr R+2*b d-b c end.
Lemma bsr_left_prefix_bound:forall f v,
 v []<=0->(forall x L,f(x::L)+v L>=2*v(x::L))->
 forall L,fw_pow(length L)*v L<=bsr_left f L.
Proof.
 intros f v HV HD;induction L as[|x L IH].
 - cbn[bsr_left length fw_pow];lia.
 - cbn[bsr_left length fw_pow]. specialize(HD x L).
   pose proof(fw_pow_pos(length L));nia.
Qed.
Lemma bsr_right_prefix_bound:forall f v,
 v []<=0->(forall x R,f(x::R)+2*v R>=v(x::R))->
 forall R,v R<=bsr_right f R.
Proof.
 intros f v HV HD;induction R as[|x R IH].
 - cbn[bsr_right];lia.
 - cbn[bsr_right]. specialize(HD x R);lia.
Qed.
Lemma bsr_prefix_positive:forall fl fr b vl vr,
 vl []<=0->vr []<=0->
 (forall x L,fl(x::L)+vl L>=2*vl(x::L))->
 (forall x R,fr(x::R)+2*vr R>=vr(x::R))->
 forall q L h R,0<=vl L+vr R+b(q,(L,h,R))->
 0<=bsr_potential fl fr b(q,(L,h,R)).
Proof.
 intros fl fr b vl vr Hvl Hvr HL HR q L h R HB.
 pose proof(bsr_left_prefix_bound fl vl Hvl HL L).
 pose proof(bsr_right_prefix_bound fr vr Hvr HR R).
 pose proof(fw_pow_pos(length L)). unfold bsr_potential.
 unfold ctape,cconf in *. nia.
Qed.
Lemma bsr_potential_step:forall fl fr b,
 fr []=0->forall q L h R tr,
 bsr_delta fl fr b(q,(L,h,R))tr<0->
 (t_dir tr=DL->L<>[])->
 bsr_potential fl fr b(t_next tr,ctape_move(t_dir tr)(t_write tr)(L,h,R))
 <bsr_potential fl fr b(q,(L,h,R)).
Proof.
 intros fl fr b HR q L h R tr HD Hleft.
 unfold bsr_potential,bsr_delta in *.
 destruct tr as[s dir q'];cbn[t_dir t_next t_write]in *;destruct dir.
 - destruct L as[|x L];[exfalso;apply(Hleft eq_refl);reflexivity|].
   cbn[ctape_move chd ctl length bsr_left bsr_right fw_pow]in HD|-*.
   pose proof(fw_pow_pos(length L));nia.
 - destruct R as[|x R].
   + cbn[ctape_move chd ctl length bsr_left bsr_right fw_pow]in HD|-*.
     rewrite HR in HD. pose proof(fw_pow_pos(length L));nia.
   + cbn[ctape_move chd ctl length bsr_left bsr_right fw_pow]in HD|-*.
     pose proof(fw_pow_pos(length L));nia.
Qed.
Lemma bsr_potential_step_le:forall fl fr b,
 fr []=0->forall q L h R tr,
 bsr_delta fl fr b(q,(L,h,R))tr<=0->
 (t_dir tr=DL->L<>[])->
 bsr_potential fl fr b(t_next tr,ctape_move(t_dir tr)(t_write tr)(L,h,R))
 <=bsr_potential fl fr b(q,(L,h,R)).
Proof.
 intros fl fr b HR q L h R tr HD Hleft.
 unfold bsr_potential,bsr_delta in *.
 destruct tr as[s dir q'];cbn[t_dir t_next t_write]in *;destruct dir.
 - destruct L as[|x L];[exfalso;apply(Hleft eq_refl);reflexivity|].
   cbn[ctape_move chd ctl length bsr_left bsr_right fw_pow]in HD|-*.
   pose proof(fw_pow_pos(length L));nia.
 - destruct R as[|x R].
   + cbn[ctape_move chd ctl length bsr_left bsr_right fw_pow]in HD|-*.
     rewrite HR in HD. pose proof(fw_pow_pos(length L));nia.
   + cbn[ctape_move chd ctl length bsr_left bsr_right fw_pow]in HD|-*.
     pose proof(fw_pow_pos(length L));nia.
Qed.
