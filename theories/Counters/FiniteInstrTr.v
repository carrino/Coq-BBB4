(** * Instruction recurrence from finite-tape reachability.

    A total machine keeps every finite prefix of its blank run finite.
    If every finite configuration can reach an instruction, it therefore
    reaches that instruction at or after every requested time.  The final
    theorem transports this property through a surjective state renaming
    and optional reflection. *)
From Coq Require Import Arith Lia List Bool.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Counters Require Import CConjugateTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.

(** The witness may use zero steps when the starting configuration already
    reads the requested instruction.  The recurrence theorem needs only
    a witness at or after its supplied lower bound. *)
Definition finite_instr_hit (tm:TM) (t:Instr) : Prop :=
 forall c:cconf, exists k e,
 stepn tm k (lift c)=Some e /\ instr_of e=t.

Lemma finite_stepn_reverse : forall tm k c e,
 stepn tm k (lift c)=Some e ->
 exists d,csteps tm k c=Some d /\ lift d=e.
Proof.
 intros tm k;induction k as[|k IH];intros c e H.
 - cbn[stepn]in H;injection H as <-. exists c;auto.
 - cbn[stepn]in H. destruct(step tm(lift c))as[f|]eqn:E;[|discriminate].
   destruct(cstep_lift_rev _ _ _ E)as(d&Ed&Hd).
   rewrite <-Hd in H. destruct(IH d e H)as(g&Eg&Hg).
   exists g;split;[cbn[csteps];now rewrite Ed|exact Hg].
Qed.

Theorem finite_instr_recurrent : forall tm t,
 (forall q s,exists tr,tm q s=Some tr) -> finite_instr_hit tm t ->
 forall N,exists j,N<=j /\ FiresAt tm t j.
Proof.
 intros tm t Htotal Hhit N.
 assert(Hrun:forall n c,exists d,csteps tm n c=Some d).
 { induction n as[|n IH];intros[q[[L h]R]].
   - eexists;reflexivity.
   - cbn[csteps cstep]. destruct(Htotal q h)as(tr&E). rewrite E. apply IH. }
 destruct(Hrun N c0)as(c&Ec).
 destruct(Hhit c)as(k&e&Hk&Hi).
 exists(N+k);split;[lia|]. exists e;split;[|exact Hi].
 rewrite stepn_add,<-lift_c0,(csteps_lift _ _ _ _ Ec). exact Hk.
Qed.

Theorem finite_instr_conjugate : forall src dst p flip t,
 (forall q s,dst(p q)s=option_map(tconj p flip)(src q s)) ->
 (forall q,exists q0,p q0=q) -> finite_instr_hit src t ->
 finite_instr_hit dst (p(fst t),snd t).
Proof.
 intros src dst p flip t Htable Honto Hhit [q[[L h]R]].
 destruct(Honto q)as(q0&<-).
 set(c:=(q0,if flip then(R,h,L)else(L,h,R)):cconf).
 assert(E:cconj p flip c=(p q0,(L,h,R)))by(unfold c,cconj;destruct flip;reflexivity).
 destruct(Hhit c)as(k&e&Hk&Hi).
 destruct(finite_stepn_reverse _ _ _ _ Hk)as(d&Ed&Hd).
 exists k,(lift(cconj p flip d));split.
 - pose proof(cconj_steps src dst p flip Htable k c d Ed)as H.
   rewrite E in H. exact(csteps_lift _ _ _ _ H).
 - rewrite <-Hd in Hi. rewrite cinstr_lift in Hi|-*.
   now rewrite (cconj_instr src dst p flip),Hi.
Qed.
