From Coq Require Import Arith Lia Bool List ZArith.
From BBB24 Require Import Statement StatementTr CTape PosEnc Closure ClosureTr.
From BBB24.Checkers Require Import NGram WeightedStack WeightedLex.
Import ListNotations.

Lemma wn_start:forall n ls rs a c,ng_covers n ls rs a(lift c)->a=ng_start n c.
Proof.
 intros n ls rs [q[[L h]R]] [p[[l x]r]] (Hp&Hx&HL&HR&_).
 cbn in Hp,Hx;subst p x. cbn [lift lift_tape t_left t_right snd] in HL,HR.
 subst L R;reflexivity.
Qed.
Lemma wn_heads:forall n ls rs q L h R p l x r,
 1<=n->ng_covers n ls rs(q,(L,h,R))(lift(p,(l,x,r)))->
 q=p /\ h=x /\ chd L=chd l /\ chd R=chd r.
Proof.
 intros n ls rs q L h R p l x r Hn H.
 apply wn_start in H. destruct n as[|n];[lia|].
 injection H as -> -> -> ->. rewrite !win_chd,!lift_side_hd;auto.
Qed.
Fixpoint wn_sum (cs:list(nat*ngmeas)) c := match cs with
 |[]=>0 |(k,m)::cs=>k*ngm_val m c+wn_sum cs c end.
Fixpoint wn_diff tm (cs:list(nat*ngmeas)) a b:Z := match cs with
 |[]=>0%Z |(k,m)::cs=>(Z.of_nat k*ngm_delta tm m a b+wn_diff tm cs a b)%Z end.
Lemma wn_sum_exact:forall cs tm n ls rs a c b d,
 1<=n->ng_covers n ls rs a(lift c)->cstep tm c=Some d->
 Z.of_nat(wn_sum cs d)=(Z.of_nat(wn_sum cs c)+wn_diff tm cs a b)%Z.
Proof.
 induction cs as[|[k m]cs IH];intros tm n ls rs a c b d Hn HC HS;
 cbn [wn_sum wn_diff];[lia|]. rewrite !Nat2Z.inj_add,!Nat2Z.inj_mul.
 rewrite(ngm_exact tm n ls rs m a c b d Hn HC HS),
   (IH tm n ls rs a c b d Hn HC HS);ring.
Qed.
Inductive wncomp:=
 | WRank (rank:cconf->nat)
 | WLinear (cs:list(nat*ngmeas)) (bias:cconf->nat) (gate:cconf->bool)
 | WBinary (fl fr vl vr:Sym->Z) (bias:cconf->Z) (gate:cconf->bool).

Definition wn_bdelta (tm:TM) (fl fr:Sym->Z) (bias:cconf->Z) (a b:cconf) : Z :=
 let '(q,(l,h,r)):=a in match tm q h with
 |None=>0%Z|Some tr=>match t_dir tr with
 |DL=>(-fl(chd l)+fr(t_write tr)+bias b-2*bias a)%Z
 |DR=>(fl(t_write tr)-fr(chd r)+2*bias b-bias a)%Z end end.
Definition wn_delta tm c a b:Z:=match c with
 |WRank f=>(Z.of_nat(f b)-Z.of_nat(f a))%Z
 |WLinear cs f _=>(wn_diff tm cs a b+Z.of_nat(f b)-Z.of_nat(f a))%Z
 |WBinary fl fr _ _ f _=>wn_bdelta tm fl fr f a b end.
Definition wn_gate c a:=match c with WRank _=>true|WLinear _ _ g|WBinary _ _ _ _ _ g=>g a end.
Definition wn_value n c cc:nat:=let a:=ng_start n cc in
 match c with
 |WRank f=>f a
 |WLinear cs f g=>if g a then wn_sum cs cc+f a else 0
 |WBinary fl fr _ _ f g=>if g a then
   Z.to_nat(bsr_potential(fun l=>fl(chd l))(fun r=>fr(chd r))(fun c=>f(ng_start n c))cc)else 0 end.
Definition wn_strict tm c a b := wn_gate c a && wn_gate c b && (wn_delta tm c a b <? 0)%Z.
Definition wn_noninc tm c a b := negb(wn_gate c b) ||
 (wn_gate c a && wn_gate c b && (wn_delta tm c a b <=? 0)%Z).
Definition wn_denote tm n c := mkWL(wn_value n c)(wn_strict tm c)(wn_noninc tm c).

Definition wn_good Sl c:=match c with
 |WBinary fl fr vl vr bias gate=>
   (fr S0 =? 0)%Z && (vl S0<=?0)%Z && (vr S0<=?0)%Z &&
   forallb(fun x=>forallb(fun y=>
     (2*vl x<=?fl x+vl y)%Z && (vr x<=?fr x+2*vr y)%Z)[S0;S1;S2;S3])[S0;S1;S2;S3] &&
   forallb(fun a=>if gate a then let '(_,(l,_,r)):=a in
     (0<=?vl(chd l)+vr(chd r)+bias a)%Z else true)Sl
 | _=>true end.

Lemma wn_positive:forall n ls rs Sl fl fr vl vr bias gate a c,
 1<=n->wn_good Sl(WBinary fl fr vl vr bias gate)=true->
 In a Sl->ng_covers n ls rs a(lift c)->gate a=true->
 (0<=bsr_potential(fun l=>fl(chd l))(fun r=>fr(chd r))(fun c=>bias(ng_start n c))c)%Z.
Proof.
 intros n ls rs Sl fl fr vl vr bias gate a c Hn HG HA HC Hg.
 unfold wn_good in HG;repeat rewrite andb_true_iff in HG.
 destruct HG as[[[[Hfr Hvl]Hvr]Hpair]Hnode].
 apply Z.leb_le in Hvl,Hvr.
 assert(HP:forall x y,(2*vl x<=fl x+vl y /\ vr x<=fr x+2*vr y)%Z).
 { intros x y. rewrite forallb_forall in Hpair.
   specialize(Hpair x ltac:(destruct x;cbn;auto)).
   rewrite forallb_forall in Hpair;specialize(Hpair y ltac:(destruct y;cbn;auto)).
   rewrite andb_true_iff,!Z.leb_le in Hpair;exact Hpair. }
 destruct a as[q[[L h]R]],c as[p[[l x]r]].
 destruct(wn_heads n ls rs q L h R p l x r Hn HC)as(->&->&HL&HR).
 apply (bsr_prefix_positive (fun l=>fl(chd l))(fun r=>fr(chd r))
   (fun c=>bias(ng_start n c))(fun l=>vl(chd l))(fun r=>vr(chd r))).
 - exact Hvl.
 - exact Hvr.
 - intros y u;cbn[chd];pose proof(proj1(HP y(chd u)));lia.
 - intros y u;cbn[chd];pose proof(proj2(HP y(chd u)));lia.
 - rewrite forallb_forall in Hnode;specialize(Hnode _ HA);rewrite Hg in Hnode.
   apply Z.leb_le in Hnode. cbn beta. pose proof(wn_start _ _ _ _ _ HC)as EE. change ((p,(L,x,R))=ng_start n(p,(l,x,r))) in EE. rewrite <-EE,<-HL,<-HR;exact Hnode.
Qed.

Lemma wn_bdelta_exact:forall tm n ls rs fl fr bias a c b d tr,
 1<=n->ng_covers n ls rs a(lift c)->ng_covers n ls rs b(lift d)->
 tm(fst c)(snd(cinstr c))=Some tr->cstep tm c=Some d->
 wn_bdelta tm fl fr bias a b=
 bsr_delta(fun l=>fl(chd l))(fun r=>fr(chd r))(fun c=>bias(ng_start n c))c tr.
Proof.
 intros tm n ls rs fl fr bias [q[[L h]R]] [p[[l x]r]] b d tr Hn HC HD HT HS.
 destruct(wn_heads n ls rs q L h R p l x r Hn HC)as(->&->&HL&HR).
 cbn[fst cinstr snd]in HT. cbn[cstep]in HS;rewrite HT in HS;injection HS as <-.
 unfold wn_bdelta;rewrite HT. unfold bsr_delta;cbn beta iota zeta;cbn[ctape_move].
 rewrite <-(wn_start _ _ _ _ _ HC),<-(wn_start _ _ _ _ _ HD).
 destruct(t_dir tr);cbn[chd];now rewrite ?HL,?HR.
Qed.

Lemma wn_component:forall tm n ls rs Sl Inv target,
 1<=n->
 (forall q l h r tr,Inv(q,(l,h,r))->(q,h)<>target->tm q h=Some tr->t_dir tr=DL->l<>[])->
 forall k,wn_good Sl k=true->
 wl_sound tm(ng_succs tm ls rs)(fun a c=>ng_covers n ls rs a(lift c))Inv target Sl(wn_denote tm n k).
Proof.
 intros tm n ls rs Sl Inv target Hn Hwall k HG a c b d l HA HB HC HD HI HJ HN HM HS HE HL.
 assert(Ea:a=ng_start n c)by(eapply wn_start;eauto).
 assert(Eb:b=ng_start n d)by(eapply wn_start;eauto).
 unfold wn_denote;cbn [wl_strict wl_noninc wl_value].
 assert(Hgen: (wn_gate k a=true->wn_gate k b=true->
   ((wn_delta tm k a b<0)%Z->wn_value n k d<wn_value n k c) /\
   ((wn_delta tm k a b<=0)%Z->wn_value n k d<=wn_value n k c))).
 { intros Ga Gb. destruct k as[f|cs f g|fl fr vl vr f g];
   cbn[wn_value wn_delta]in *;rewrite <-Ea,<-Eb.
   - split;lia.
   - cbn[wn_gate]in Ga,Gb;rewrite Ga,Gb.
     pose proof(wn_sum_exact cs tm n ls rs a c b d Hn HC HS);split;lia.
   - cbn[wn_gate]in Ga,Gb;rewrite Ga,Gb.
     assert(Pc:(0<=bsr_potential(fun l=>fl(chd l))(fun r=>fr(chd r))(fun c=>f(ng_start n c))c)%Z)
       by(exact(wn_positive n ls rs Sl fl fr vl vr f g a c Hn HG HA HC Ga)).
     assert(Pd:(0<=bsr_potential(fun l=>fl(chd l))(fun r=>fr(chd r))(fun c=>f(ng_start n c))d)%Z)
       by(exact(wn_positive n ls rs Sl fl fr vl vr f g b d Hn HG HB HD Gb)).
     assert(F0:fr S0=0%Z).
     { cbn[wn_good]in HG;repeat apply andb_prop in HG as[HG _];now apply Z.eqb_eq in HG. }
     destruct c as[q[[L h]R]]. cbn[cstep]in HS.
     destruct(tm q h)as[tr|]eqn:HT;[|discriminate].
     assert(Hstep:cstep tm(q,(L,h,R))=Some d)by(cbn[cstep];rewrite HT;exact HS).
     pose proof(wn_bdelta_exact tm n ls rs fl fr f a(q,(L,h,R))b d tr Hn HC HD HT Hstep)as ED.
     injection HS as <-. split;intro E;rewrite ED in E.
     + apply Z2Nat.inj_lt;try assumption.
       apply bsr_potential_step;[exact F0|exact E|]. eapply Hwall;eauto.
     + apply Z2Nat.inj_le;try assumption.
       apply bsr_potential_step_le;[exact F0|exact E|]. eapply Hwall;eauto. }
 split.
 - unfold wn_strict;rewrite !andb_true_iff,Z.ltb_lt.
   intros[[Ga Gb]E];exact(proj1(Hgen Ga Gb)E).
 - unfold wn_noninc;rewrite orb_true_iff;intros[E|E].
   + apply negb_true_iff in E. destruct k;cbn[wn_gate]in E;try discriminate;
     cbn[wn_value];rewrite <-Eb,E;lia.
   + repeat rewrite andb_true_iff in E;destruct E as[[Ga Gb]E].
     apply Z.leb_le in E;exact(proj2(Hgen Ga Gb)E).
Qed.

(** Additive rankings need no fixed tape boundary.  The binary component
    remains behind the independently checked finite-wall invariant. *)
Definition wn_linear c := match c with WBinary _ _ _ _ _ _ => false | _ => true end.

Lemma wn_linear_component:forall tm n ls rs Sl Inv target k,
 1<=n -> wn_linear k=true ->
 wl_sound tm(ng_succs tm ls rs)(fun a c=>ng_covers n ls rs a(lift c))Inv target Sl(wn_denote tm n k).
Proof.
 intros tm n ls rs Sl Inv target k Hn Hlinear a c b d l HA HB HC HD HI HJ HN HM HS HE HL.
 assert(Ea:a=ng_start n c)by(eapply wn_start;eauto).
 assert(Eb:b=ng_start n d)by(eapply wn_start;eauto).
 unfold wn_denote;cbn [wl_strict wl_noninc wl_value].
 assert(Hgen: (wn_gate k a=true->wn_gate k b=true->
   ((wn_delta tm k a b<0)%Z->wn_value n k d<wn_value n k c) /\
   ((wn_delta tm k a b<=0)%Z->wn_value n k d<=wn_value n k c))).
 { intros Ga Gb. destruct k as[f|cs f g|fl fr vl vr f g];
   cbn [wn_linear] in Hlinear; try discriminate;
   cbn[wn_value wn_delta];rewrite <-Ea,<-Eb.
   - split;lia.
   - cbn[wn_gate]in Ga,Gb;rewrite Ga,Gb.
     pose proof(wn_sum_exact cs tm n ls rs a c b d Hn HC HS);split;lia. }
 split.
 - unfold wn_strict;rewrite !andb_true_iff,Z.ltb_lt.
   intros[[Ga Gb]E];exact(proj1(Hgen Ga Gb)E).
 - unfold wn_noninc;rewrite orb_true_iff;intros[E|E].
   + apply negb_true_iff in E. destruct k;cbn[wn_gate]in E;try discriminate;
     cbn[wn_value];rewrite <-Eb,E;lia.
   + repeat rewrite andb_true_iff in E;destruct E as[[Ga Gb]E].
     apply Z.leb_le in E;exact(proj2(Hgen Ga Gb)E).
Qed.
