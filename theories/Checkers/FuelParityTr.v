(** Exact sided nonblank counts with a parity refinement above one.
    The four classes are zero, one, positive even, and odd at least three.
    Increment toggles the last two classes; decrement from positive even
    branches because two and larger even counts have different classes.
    Projection to exact capped counts reuses the extent measure semantics. *)
From Coq Require Import Arith Lia Bool List ZArith.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape PosEnc Records Closure ClosureTr.
From BBB4.Checkers Require Import NGram NGramTr FuelClass FuelWide FuelWideTr FuelExactTr.
Import ListNotations.
Inductive fpclass:Set:=FP0|FP1|FPE|FPO.
Definition fp_inc(b:bool)(f:fpclass):fpclass:=
 if b then match f with FP0=>FP1|FP1=>FPE|FPE=>FPO|FPO=>FPE end else f.
Fixpoint fp_count(n:nat):fpclass:=match n with
 |0=>FP0|S k=>fp_inc true(fp_count k)end.
Definition fp_list(l:list Sym):fpclass:=fp_count(count1 l).
Definition fp_proj(f:fpclass):fclass:=match f with FP0=>F0|FP1=>F1|_=>F2 end.
Lemma fp_proj_inc:forall b f,fp_proj(fp_inc b f)=finc b(fp_proj f).
Proof. intros[][];reflexivity. Qed.
Lemma fp_proj_count:forall n,fp_proj(fp_count n)=class_of_count n.
Proof.
 induction n;[reflexivity|]. cbn[fp_count];rewrite fp_proj_inc,IHn.
 destruct n as[|[|n]];reflexivity.
Qed.
Lemma fp_proj_list:forall l,fp_proj(fp_list l)=class_of_list l.
Proof. intros;apply fp_proj_count. Qed.
Definition fpconf:Type:=(cconf*(fpclass*fpclass))%type.
Definition fp_project(a:fpconf):fcconf:=
 (fst a,(fp_proj(fst(snd a)),fp_proj(snd(snd a)))).
Definition fp_app(f:fpclass)(p:positive):positive:=match f with
 |FP0=>p~0~0|FP1=>p~0~1|FPE=>p~1~0|FPO=>p~1~1 end%positive.
Lemma fp_app_inj:forall x y p q,fp_app x p=fp_app y q->x=y/\p=q.
Proof.
 destruct x,y;simpl;intros p q H;
 solve[split;congruence|discriminate|injection H as H;discriminate].
Qed.
Definition fpconf_enc(a:fpconf):positive:=
 fp_app(fst(snd a))(fp_app(snd(snd a))(cconf_enc(fst a))).
Lemma fpconf_enc_inj:forall a b,fpconf_enc a=fpconf_enc b->a=b.
Proof.
 intros[b1[l1 r1]][b2[l2 r2]]H;unfold fpconf_enc in H;cbn in H.
 apply fp_app_inj in H as[Hl H];apply fp_app_inj in H as[Hr H].
 apply cconf_enc_inj in H;congruence.
Qed.
Definition fp_ok(a:fpconf):bool:=xf_ok(fp_project a).
Definition fp_dec(s:Sym)(f:fpclass):list fpclass:=
 match s,f with S0,_=>[f]|S1,FP0=>[]|S1,FP1=>[FP0]
 |S1,FPE=>[FP1;FPO]|S1,FPO=>[FPE]end.
Definition fp_upd(tm:TM)(b:cconf)(fl fr:fpclass):list(fpclass*fpclass):=
 let '(q,(l,h,r)):=b in match tm q h with
 |None=>[]
 |Some tr=>match t_dir tr with
 |DL=>map(fun fl'=>(fl',fp_inc(nb(t_write tr))fr))(fp_dec(chd l)fl)
 |DR=>map(fun fr'=>(fp_inc(nb(t_write tr))fl,fr'))(fp_dec(chd r)fr)
 end end.
Definition fp_succs(tm:TM)(ls rs:gset)(a:fpconf):option(list fpconf):=
 match ng_succs tm ls rs(fst a)with
 |None=>None
 |Some bs=>Some(filter fp_ok(flat_map(fun b=>map(fun fs=>(b,fs))
  (fp_upd tm(fst a)(fst(snd a))(snd(snd a))))bs))end.
Definition fp_covers(n:nat)(ls rs:gset)(a:fpconf)(c:ExecState):Prop:=
 exists cc,lift cc=c /\ ng_covers n ls rs(fst a)c /\
 let '(_,(l,_,r)):=cc in snd a=(fp_list l,fp_list r).
Lemma fp_as_xf:forall n ls rs a c,fp_covers n ls rs a c->xf_covers n ls rs(fp_project a)c.
Proof.
 intros n ls rs[b[fl fr]]c([q[[l h]r]]&E&Hg&Hcls).
 cbn in Hcls;injection Hcls as -> ->.
 exists(q,(l,h,r));split;[exact E|]. split;[exact Hg|].
 cbn[fp_project fst snd];rewrite !fp_proj_list;reflexivity.
Qed.
Definition fp_start(n:nat)(cc:cconf):fpconf:=
 let '(_,(l,_,r)):=cc in(ng_start n cc,(fp_list l,fp_list r)).
Lemma fp_start_sound:forall n ls rs cc,ng_seed_ok n ls rs cc=true->
 fp_covers n ls rs(fp_start n cc)(lift cc).
Proof.
 intros n ls rs[q[[l h]r]]H;exists(q,(l,h,r));split;[reflexivity|].
 split;[apply ng_start_covers;exact H|reflexivity].
Qed.
Lemma fp_ok_sound:forall n ls rs a c,fp_covers n ls rs a c->fp_ok a=true.
Proof. intros;eapply xf_ok_sound;apply fp_as_xf;exact H. Qed.
Lemma fp_push:forall s l,fp_list(s::l)=fp_inc(nb s)(fp_list l).
Proof. intros[]l;reflexivity. Qed.
Lemma fp_pop:forall l,In(fp_list(ctl l))(fp_dec(chd l)(fp_list l)).
Proof.
 intros[|[]l];cbn[chd ctl fp_list count1 fp_count fp_dec fp_inc In];auto.
 unfold fp_list;cbn[count1 fp_count]. destruct(fp_count(count1 l));cbn;auto.
Qed.
Lemma fp_update:forall tm b cc cc' n ls rs,
 ng_covers n ls rs b(lift cc)->1<=n->cstep tm cc=Some cc'->
 let '(_,(l,_,r)):=cc in let '(_,(l',_,r')):=cc' in
 In(fp_list l',fp_list r')(fp_upd tm b(fp_list l)(fp_list r)).
Proof.
 intros tm[q[[lw h]rw]][qc[[l hc]r]]cc' n ls rs Hg Hn Hstep.
 destruct Hg as(Hq&Hh&Hl&Hr&Hg);cbn in Hq,Hh,Hl,Hr;subst qc hc.
 unfold cstep in Hstep;cbn[fst snd]in Hstep.
 destruct(tm q h)as[tr|]eqn:Et;[|discriminate]. injection Hstep as <-.
 unfold fp_upd;rewrite Et. destruct n as[|n];[lia|].
 assert(EL:chd lw=chd l)by(rewrite Hl,win_chd;symmetry;apply lift_side_hd).
 assert(ER:chd rw=chd r)by(rewrite Hr,win_chd;symmetry;apply lift_side_hd).
 destruct(t_dir tr);cbn[ctape_move];rewrite ?fp_push,?EL,?ER;
 apply in_map_iff;eexists;split;try reflexivity;apply fp_pop.
Qed.
Lemma fp_succs_sound:forall tm n ls rs a c,1<=n->fp_covers n ls rs a c->
 match fp_succs tm ls rs a,step tm c with
 |Some l,Some c'=>exists a',In a' l /\ fp_covers n ls rs a' c'
 |Some _,None=>False|None,_=>True end.
Proof.
 intros tm n ls rs[b[fl fr]]c Hn([q[[l h]r]]&<-&Hg&E).
 cbn in E;injection E as -> ->. unfold fp_succs;cbn[fst snd].
 destruct(ng_succs tm ls rs b)as[bs|]eqn:Es;[|exact I].
 destruct(cstep tm(q,(l,h,r)))as[cc'|]eqn:Est.
 - pose proof(CTape.cstep_lift tm(q,(l,h,r))cc' Est)as Hlift.
   unfold ctape in *. rewrite Hlift.
   destruct(ng_succs_sound_some tm n ls rs b _ bs _ Hn Hg Es Hlift)as(b'&Hin&Hg').
   destruct cc' as[q'[[l' h']r']].
   set(a':=(b',(fp_list l',fp_list r'))).
   assert(Hcov:fp_covers n ls rs a'(lift(q',(l',h',r')))).
   {exists(q',(l',h',r'));repeat split;auto. }
   exists a';split;[|exact Hcov]. apply filter_In;split;[|eapply fp_ok_sound;eauto].
   apply in_flat_map;exists b';split;[exact Hin|]. apply in_map.
   exact(fp_update tm b(q,(l,h,r))(q',(l',h',r'))n ls rs Hg Hn Est).
 - assert(Hnone:step tm(lift(q,(l,h,r)))=None).
   {unfold cstep in Est;cbn[fst snd]in Est. unfold step;cbn[fst snd lift lift_tape t_head].
    destruct(tm q h);congruence. }
   unfold ctape in *. rewrite Hnone.
   exact(ng_succs_nohalt tm ls rs n b _ bs Hg Es Hnone).
Qed.
