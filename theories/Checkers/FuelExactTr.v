(** Exact capped nonblank counts for the finite n-gram abstraction.

    Unlike the lower bounds in FuelWide, F0 and F1 here mean exactly
    zero and one nonblank cell. F2 means at least two. Crossing a 1
    from F2 therefore branches to F1 or F2. The window filter removes
    count classes smaller than the known window count.

    Covers includes a finite tape witness. This permits constructive
    case analysis on the remaining count after a step; no decision
    principle for arbitrary infinite tapes is needed. Blank padding
    preserves the count, so the exact classes apply to every finite
    representative of the covered execution state. *)
From Coq Require Import Arith Lia Bool List ZArith.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape PosEnc Records Closure ClosureTr.
From BBB4.Checkers Require Import NGram NGramTr FuelClass FuelWide FuelSCCTr FuelMixTr FuelMixPartialTr.
Import ListNotations.
Lemma xf_count_win : forall n l,
 count1(win(lift_side l)0 n)=count1(firstn n l).
Proof.
 induction n;intros l;[reflexivity|].
 destruct l as[|x l].
 - rewrite win_blank by(cbn;lia). cbn[firstn].
   clear IHn. induction n;cbn[repeat count1];auto.
 - rewrite lift_side_cons,win_cons,win_push_S.
   cbn[firstn push_side]. rewrite !count1_cons,IHn;reflexivity.
Qed.
Lemma xf_count_firstn : forall n l,count1(firstn n l)<=count1 l.
Proof. induction n;intros[|[]l];cbn[firstn count1];try lia;specialize(IHn l);lia. Qed.
Lemma xf_count_ext : forall l r,lift_side l=lift_side r->count1 l=count1 r.
Proof.
 intros l r E.
 pose proof(f_equal(fun f=>count1(win f 0 (length l+length r)))E)as H.
 cbn beta in H. rewrite !xf_count_win,!firstn_all2 in H by lia;exact H.
Qed.
Definition xf_ok (a:fcconf):bool:=
 let '(b,(fl,fr)):=a in let '(_,(l,_,r)):=b in
 (match fl with F0=>count1 l=?0|F1=>count1 l<=?1|F2=>true end)&&
 (match fr with F0=>count1 r=?0|F1=>count1 r<=?1|F2=>true end).
Definition xf_dec (s:Sym)(f:fclass):list fclass:=
 match s,f with S0,_=>[f]|S1,F0=>[]|S1,F1=>[F0]|S1,F2=>[F1;F2] end.
Definition xf_upd(tm:TM)(b:cconf)(fl fr:fclass):list(fclass*fclass):=
 let '(q,(l,h,r)):=b in match tm q h with
 |None=>[]
 |Some tr=>match t_dir tr with
 |DL=>map(fun fl'=>(fl',finc(nb(t_write tr))fr))(xf_dec(chd l)fl)
 |DR=>map(fun fr'=>(finc(nb(t_write tr))fl,fr'))(xf_dec(chd r)fr)
 end end.
Definition xf_succs(tm:TM)(ls rs:gset)(a:fcconf):option(list fcconf):=
 match ng_succs tm ls rs(fst a)with
 |None=>None
 |Some bs=>Some(filter xf_ok(flat_map(fun b=>map(fun fs=>(b,fs))
  (xf_upd tm(fst a)(fst(snd a))(snd(snd a))))bs))
 end.
Definition xf_covers(n:nat)(ls rs:gset)(a:fcconf)(c:ExecState):Prop:=
 exists cc,lift cc=c /\ ng_covers n ls rs(fst a)c /\
 let '(_,(l,_,r)):=cc in snd a=(class_of_list l,class_of_list r).
Lemma xf_as_fw : forall n ls rs a c,xf_covers n ls rs a c->fw_covers n ls rs a c.
Proof.
 intros n ls rs [b [fl fr]] c ([q [[l h]r]]&<-&Hg&E).
 cbn in E;injection E as -> ->. split;[exact Hg|].
 split;apply class_of_list_holds.
Qed.
Lemma xf_start : forall n ls rs cc,ng_seed_ok n ls rs cc=true->
 xf_covers n ls rs(fw_start n cc)(lift cc).
Proof.
 intros n ls rs [q[[l h]r]] H;exists(q,(l,h,r));split;[reflexivity|].
 split;[apply ng_start_covers;exact H|reflexivity].
Qed.
Lemma xf_covers_counts : forall n ls rs a cc,xf_covers n ls rs a(lift cc)->
 let '(_,(l,_,r)):=cc in snd a=(class_of_list l,class_of_list r).
Proof.
 intros n ls rs a [q[[l h]r]]([q'[[l' h']r']]&E&Hg&Hc).
 assert(EL:lift_side l'=lift_side l)by(exact(f_equal(fun c=>t_left(snd c))E)).
 assert(ER:lift_side r'=lift_side r)by(exact(f_equal(fun c=>t_right(snd c))E)).
 cbn in Hc. unfold class_of_list in *.
 rewrite(xf_count_ext _ _ EL),(xf_count_ext _ _ ER)in Hc;exact Hc.
Qed.

Lemma xf_ok_sound : forall n ls rs a c,xf_covers n ls rs a c->xf_ok a=true.
Proof.
 intros n ls rs [[q[[lw h]rw]][fl fr]] c ([qc[[l hc]r]]&<-&Hg&E).
 cbn in E;injection E as -> ->.
 destruct Hg as(Hq&Hh&Hl&Hr&Hg);cbn in Hl,Hr.
 unfold xf_ok;cbn[fst snd]. rewrite Hl,Hr,!xf_count_win.
 pose proof(xf_count_firstn n l)as Hcl;pose proof(xf_count_firstn n r)as Hcr.
 unfold class_of_list,class_of_count.
 apply andb_true_intro;split;destruct(count1 l)as[|[|kl]]eqn:El;
 destruct(count1 r)as[|[|kr]]eqn:Er;try reflexivity;
 try(apply Nat.eqb_eq;lia);apply Nat.leb_le;lia.
Qed.
Lemma xf_push : forall s l,class_of_list(s::l)=finc(nb s)(class_of_list l).
Proof. intros[]l;unfold class_of_list,class_of_count;cbn[count1 nb finc];destruct(count1 l)as[|[|n]];reflexivity. Qed.
Lemma xf_pop : forall l,In(class_of_list(ctl l))(xf_dec(chd l)(class_of_list l)).
Proof.
 intros[|[]l];unfold class_of_list,class_of_count;cbn[chd ctl count1 xf_dec In];auto.
 destruct(count1 l)as[|[|n]];cbn;auto.
Qed.
Lemma xf_update : forall tm b cc cc' n ls rs,
 ng_covers n ls rs b(lift cc)->1<=n->cstep tm cc=Some cc'->
 let '(_,(l,_,r)):=cc in let '(_,(l',_,r')):=cc' in
 In(class_of_list l',class_of_list r')(xf_upd tm b(class_of_list l)(class_of_list r)).
Proof.
 intros tm [q[[lw h]rw]][qc[[l hc]r]]cc' n ls rs Hg Hn Hstep.
 destruct Hg as(Hq&Hh&Hl&Hr&Hg);cbn in Hq,Hh,Hl,Hr;subst qc hc.
 unfold cstep in Hstep;cbn[fst snd]in Hstep.
 destruct(tm q h)as[tr|]eqn:Et;[|discriminate]. injection Hstep as <-.
 unfold xf_upd;rewrite Et.
 destruct n as[|n];[lia|].
 assert(EL:chd lw=chd l)by(rewrite Hl,win_chd;symmetry;apply lift_side_hd).
 assert(ER:chd rw=chd r)by(rewrite Hr,win_chd;symmetry;apply lift_side_hd).
 destruct(t_dir tr);cbn[ctape_move];rewrite ?xf_push,?EL,?ER;
 apply in_map_iff;eexists;split;try reflexivity;apply xf_pop.
Qed.
Lemma xf_succs_sound : forall tm n ls rs a c,1<=n->xf_covers n ls rs a c->
 match xf_succs tm ls rs a,step tm c with
 |Some l,Some c'=>exists a',In a' l /\ xf_covers n ls rs a' c'
 |Some _,None=>False|None,_=>True end.
Proof.
 intros tm n ls rs [b[fl fr]] c Hn([q[[l h]r]]&<-&Hg&E).
 cbn in E;injection E as -> ->. unfold xf_succs;cbn[fst snd].
 destruct(ng_succs tm ls rs b)as[bs|]eqn:Es;[|exact I].
 destruct(cstep tm(q,(l,h,r)))as[cc'|]eqn:Est.
 - pose proof(CTape.cstep_lift tm (q,(l,h,r)) cc' Est)as Hlift.
   unfold ctape in *. rewrite Hlift.
   destruct(ng_succs_sound_some tm n ls rs b _ bs _ Hn Hg Es Hlift)as(b'&Hin&Hg').
   destruct cc' as[q'[[l' h']r']].
   set(a':=(b',(class_of_list l',class_of_list r'))).
   assert(Hcov:xf_covers n ls rs a'(lift(q',(l',h',r')))).
   { exists(q',(l',h',r'));repeat split;auto. }
   exists a';split;[|exact Hcov]. apply filter_In;split;[|eapply xf_ok_sound;eauto].
   apply in_flat_map;exists b';split;[exact Hin|]. apply in_map.
   exact(xf_update tm b (q,(l,h,r)) (q',(l',h',r')) n ls rs Hg Hn Est).
 - assert(Hnone:step tm(lift(q,(l,h,r)))=None).
   { unfold cstep in Est;cbn[fst snd]in Est. unfold step;cbn[fst snd lift lift_tape t_head].
     destruct(tm q h);congruence. }
   unfold ctape in *. rewrite Hnone.
   exact(ng_succs_nohalt tm ls rs n b _ bs Hg Es Hnone).
Qed.
