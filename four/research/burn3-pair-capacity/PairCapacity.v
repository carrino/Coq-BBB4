(** Adjacent-pair counts reserve a left boundary for existing binary ranks.
    All scores are nonnegative, and the blank pair has score zero, so arbitrary
    blank padding supplies an initial reserve without changing the value. *)
From Coq Require Import NArith Arith Lia Bool List ZArith.
From BBB24 Require Import Statement StatementTr CTape PosEnc Closure ClosureTr
 Bounds NGramCensus RankSearch WeightedNGram WeightedCensus WeightedCapacity InstructionPortfolio.
From BBB24.Checkers Require Import NGram WeightedLex.
Import ListNotations.

Fixpoint pc_count (score:Sym->Sym->nat)(l:list Sym) : nat :=
 match l with []=>0 |x::xs=>score x(chd xs)+pc_count score xs end.
Lemma pc_chd_pad : forall l k,chd(l++repeat S0 k)=chd l.
Proof. intros [|x l] [|k];reflexivity. Qed.
Lemma pc_count_pad : forall score,score S0 S0=0 -> forall l k,
 pc_count score(l++repeat S0 k)=pc_count score l.
Proof.
 intros score Hzero l;induction l as[|x l IH];intro k.
 - cbn[app];induction k;[reflexivity|].
   cbn[repeat pc_count];rewrite IHk.
   destruct k;cbn[repeat chd];rewrite Hzero;reflexivity.
 - cbn[app pc_count];rewrite pc_chd_pad,IH;reflexivity.
Qed.
Lemma pc_drop : forall score,score S0 S0=0 -> forall l,
 Z.of_nat(pc_count score(ctl l))=
 (Z.of_nat(pc_count score l)-Z.of_nat(score(chd l)(chd(ctl l))))%Z.
Proof.
 intros score Hzero[|x l];cbn[pc_count ctl chd].
 - rewrite Hzero;lia.
 - rewrite Nat2Z.inj_add;lia.
Qed.
Lemma pc_second : forall n l,2<=n ->
 chd(ctl(win(lift_side l)0 n))=chd(ctl l).
Proof.
 intros [|[|n]] l Hn;try lia.
 destruct l as[|x[|y l]];reflexivity.
Qed.

Record PCapacity := mkPCapacity {
 pc_scale:nat;
 pc_terms:list(nat*ngmeas);
 pc_score:Sym->Sym->nat;
 pc_bias:cconf->nat
}.
Definition pc_left(c:cconf):list Sym:=let '(_,(l,_,_)):=c in l.
Definition pc_value n C c :=
 wn_sum(pc_terms C)c+pc_count(pc_score C)(pc_left c)+pc_bias C(ng_start n c).
Definition pc_margin n C c := pc_value n C c<pc_scale C*length(pc_left c).
Definition pc_pair_delta (tm:TM) C (a:cconf) :=
 let '(q,(l,h,r)):=a in match tm q h with None=>0%Z |Some tr=>
 match t_dir tr with
 |DL=> (-Z.of_nat(pc_score C(chd l)(chd(ctl l))))%Z
 |DR=> Z.of_nat(pc_score C(t_write tr)(chd l)) end end.
Definition pc_delta tm C a b :=
 (wn_diff tm(pc_terms C)a b+pc_pair_delta tm C a+
  Z.of_nat(pc_bias C b)-Z.of_nat(pc_bias C a))%Z.
Definition pc_edge tm C a b :=
 let '(q,(_,h,_)):=a in match tm q h with None=>false|Some tr=>
 (pc_delta tm C a b<=?match t_dir tr with
 |DL=> -Z.of_nat(pc_scale C)|DR=>Z.of_nat(pc_scale C)end)%Z end.
Definition pc_ok tm ls rs Sl target C :=
 (0<?pc_scale C) && (pc_score C S0 S0=?0) &&
 forallb(fun a=>if instr_eqb(cinstr a)target then true else
 match ng_succs tm ls rs a with None=>false|Some next=>
 forallb(fun b=>if instr_eqb(cinstr b)target then true else pc_edge tm C a b)next end)Sl.

Lemma pc_pair_exact : forall tm n ls rs C a c d,
 2<=n -> pc_score C S0 S0=0 -> ng_covers n ls rs a(lift c) ->
 cstep tm c=Some d ->
 Z.of_nat(pc_count(pc_score C)(pc_left d))=
 (Z.of_nat(pc_count(pc_score C)(pc_left c))+pc_pair_delta tm C a)%Z.
Proof.
 intros tm n ls rs C [q[[L h]R]] [p[[l x]r]] d Hn Hz HC HS.
 destruct(wn_heads n ls rs q L h R p l x r ltac:(lia) HC)as(->&->&HL&HR).
 assert(HL2:chd(ctl L)=chd(ctl l)).
 {apply wn_start in HC;injection HC as EL ER.
  subst L;apply pc_second;exact Hn. }
 cbn[cstep]in HS;destruct(tm p x)as[tr|]eqn:HT;[|discriminate].
 injection HS as <-;unfold pc_pair_delta;rewrite HT.
 destruct tr as[w dir next];destruct dir;cbn[t_dir t_write ctape_move pc_left].
 - rewrite pc_drop by exact Hz;rewrite HL,HL2;lia.
 - cbn[pc_count];rewrite Nat2Z.inj_add,HL;lia.
Qed.

Lemma pc_value_pad : forall n C c k,pc_score C S0 S0=0 ->
 pc_value n C(wc_pad k c)=pc_value n C c.
Proof.
 intros n C[q[[l h]r]]k Hz;unfold pc_value.
 rewrite wca_sum_pad,wca_start_pad.
 cbn[wc_pad pc_left];rewrite pc_count_pad by exact Hz;reflexivity.
Qed.
Lemma pc_pad_margin : forall n C c,
 0<pc_scale C -> pc_score C S0 S0=0 ->
 pc_margin n C(wc_pad(S(pc_value n C c))c).
Proof.
 intros n C[q[[l h]r]]HK Hz;unfold pc_margin.
 rewrite pc_value_pad by exact Hz;cbn[wc_pad pc_left].
 rewrite app_length,repeat_length;nia.
Qed.
Lemma pc_nonempty : forall n C q l h r,
 pc_margin n C(q,(l,h,r))->l<>[].
Proof. intros n C q l h r H ->;unfold pc_margin,pc_left in H;cbn in H;nia. Qed.

Lemma pc_margin_step : forall tm n ls rs C a c b d,
 2<=n -> pc_score C S0 S0=0 ->
 ng_covers n ls rs a(lift c)->ng_covers n ls rs b(lift d)->
 cstep tm c=Some d->pc_margin n C c->pc_edge tm C a b=true->pc_margin n C d.
Proof.
 intros tm n ls rs C a c b d Hn Hz HC HD HS HI HE.
 pose proof(wn_start _ _ _ _ _ HC)as EA.
 pose proof(wn_start _ _ _ _ _ HD)as EB.
 pose proof(wn_sum_exact(pc_terms C)tm n ls rs a c b d ltac:(lia) HC HS)as EV.
 pose proof(pc_pair_exact tm n ls rs C a c d Hn Hz HC HS)as EP.
 assert(ED:Z.of_nat(pc_value n C d)=(Z.of_nat(pc_value n C c)+pc_delta tm C a b)%Z).
 {unfold pc_value,pc_delta;rewrite !Nat2Z.inj_add,EV,EP,<-EA,<-EB;ring. }
 destruct c as[q[[l h]r]],a as[p[[L x]R]].
 destruct(wn_heads n ls rs p L x R q l h r ltac:(lia) HC)as[-> [-> _]].
 cbn[pc_edge]in HE;cbn[cstep]in HS.
 destruct(tm q h)as[tr|]eqn:HT;[|discriminate].
 apply Z.leb_le in HE;injection HS as <-.
 assert(Hleft:l<>[])by(eapply pc_nonempty;exact HI).
 unfold pc_margin in HI|-*;apply Nat2Z.inj_lt;rewrite Nat2Z.inj_mul.
 apply Nat2Z.inj_lt in HI;rewrite Nat2Z.inj_mul in HI.
 destruct(t_dir tr)eqn:Edir;cbn[ctape_move pc_left]in *.
 - destruct l;[contradiction|];cbn[chd ctl length]in *.
   rewrite Nat2Z.inj_succ in HI;nia.
 - cbn[length]in *;rewrite Nat2Z.inj_succ;nia.
Qed.

Lemma pc_reach:forall tm n ls rs Sl target C cs,
 2<=n->closed_tr_b cconf cconf_enc(ng_succs tm ls rs)Sl=true->
 pc_ok tm ls rs Sl target C=true->forallb(wn_good Sl)cs=true->
 wl_ok(ng_succs tm ls rs)target Sl(map(wn_denote tm n)cs)=true->
 forall a c,In a Sl->ng_covers n ls rs a(lift c)->
 exists j e,stepn tm j(lift c)=Some e /\ instr_of e=target.
Proof.
 intros tm n ls rs Sl target C cs Hn Hcl HO HG HK a c HA HC.
 apply andb_prop in HO as[Hhead HO].
 apply andb_prop in Hhead as[Hscale Hzero].
 apply Nat.ltb_lt in Hscale;apply Nat.eqb_eq in Hzero.
 assert(Hn1:1<=n)by lia.
 assert(HS:forall a c,In a Sl->ng_covers n ls rs a(lift c)->
   exists d l b,cstep tm c=Some d /\ ng_succs tm ls rs a=Some l /\
   In b l /\ In b Sl /\ ng_covers n ls rs b(lift d)).
 { intros a1 c1 HA1 HC1.
   destruct(closed_step_tr tm cconf cconf_enc(ng_succs tm ls rs)(ng_covers n ls rs)
     cconf_enc_inj(fun a e H=>ng_succs_sound tm n ls rs a e Hn1 H)Sl a1(lift c1)Hcl HA1 HC1)
     as(e&l&b&HE&HB&Hin&HinS&Hcov).
   destruct(cstep_lift_rev tm c1 e HE)as(d&Hd&Heq);subst e.
   exists d,l,b;auto. }
 set(Inv:=fun c=>cinstr c=target \/
   (exists a,In a Sl /\ ng_covers n ls rs a(lift c) /\ pc_margin n C c)).
 assert(HInv:forall c d,Inv c->cinstr c<>target->cstep tm c=Some d->Inv d).
 { intros c1 d [Ht|(a1&Ha&Hcov&Hcap)] Hnt Hstep;[contradiction|].
   destruct(HS a1 c1 Ha Hcov)as(d1&next&b&Hstep1&HE&Hin&Hb&Hcovb).
   rewrite Hstep in Hstep1;injection Hstep1 as <-.
   destruct(instr_eqb(cinstr b)target)eqn:Et.
   - left;apply instr_eqb_spec in Et.
     rewrite <-(cinstr_lift d),<-(ng_covers_instr _ _ _ _ _ Hcovb);exact Et.
   - right;exists b;split;[exact Hb|split;[exact Hcovb|]].
     eapply(pc_margin_step tm n ls rs C a1 c1 b d);eauto.
     rewrite forallb_forall in HO;specialize(HO a1 Ha).
     destruct(instr_eqb(cinstr a1)target)eqn:Eu.
     + apply instr_eqb_spec in Eu;exfalso;apply Hnt.
       rewrite <-(cinstr_lift c1),<-(ng_covers_instr _ _ _ _ _ Hcov);exact Eu.
     + rewrite HE in HO;rewrite forallb_forall in HO;specialize(HO b Hin);rewrite Et in HO;exact HO. }
 assert(Hcomp:Forall(wl_sound tm(ng_succs tm ls rs)
   (fun a c=>ng_covers n ls rs a(lift c))Inv target Sl)(map(wn_denote tm n)cs)).
 { apply Forall_forall;intros k Hin;apply in_map_iff in Hin as(x&<-&Hx).
   apply wn_component;[exact Hn1| |].
   - intros q l h r tr [Ht|(b&Hb&Hcov&Hcap)] Hnt HT HD;
       [contradiction|eapply pc_nonempty;exact Hcap].
   - rewrite forallb_forall in HG;auto. }
 set(c':=wc_pad(S(pc_value n C c))c).
 assert(Hlift:lift c'=lift c)by(apply wc_pad_lift).
 assert(Hcov:ng_covers n ls rs a(lift c'))by(now rewrite Hlift).
 assert(Hinit:Inv c').
 { right;exists a;split;[exact HA|split;[exact Hcov|]]. apply pc_pad_margin;assumption. }
 destruct(wl_reach tm(ng_succs tm ls rs)(fun a c=>ng_covers n ls rs a(lift c))Inv target Sl
   (fun a c H=>eq_trans(ng_covers_instr n ls rs a(lift c)H)(cinstr_lift c))
   HS HInv(map(wn_denote tm n)cs)Hcomp HK c' a Hinit HA Hcov)as(j&d&HD&HT).
 exists j,(lift d);split;[rewrite <-Hlift;apply csteps_lift;exact HD|rewrite cinstr_lift;exact HT].
Qed.


Definition pc_graph_check tm n t (Sl:list cconf)(target:Instr) (C:PCapacity) (cs:list wncomp):bool :=
 if 2<=?n then match csteps tm t c0 with None=>false|Some cc=>
 let '(q,(l,h,r)):=cc in let a0:=ng_start n cc in
 let ls:=gadds(ng_seed_side n l ++ flat_map(fun c=>fst(ng_harvest tm c))Sl)gempty in
 let rs:=gadds(ng_seed_side n r ++ flat_map(fun c=>snd(ng_harvest tm c))Sl)gempty in
 if ng_seed_ok n ls rs cc then
 if closed_tr_b cconf cconf_enc(ng_succs tm ls rs)Sl then
 if mem_tr cconf cconf_enc a0 Sl then
 pc_ok tm ls rs Sl target C && forallb(wn_good Sl)cs &&
 wl_ok(ng_succs tm ls rs)target Sl(map(wn_denote tm n)cs)
 else false else false else false end else false.

Theorem pc_graph_check_sound:forall tm n t Sl target C cs,
 pc_graph_check tm n t Sl target C cs=true -> NonHalt tm /\
 forall N,exists k,N<=k /\ FiresAt tm target k.
Proof.
 intros tm n t Sl target C cs H;unfold pc_graph_check in H.
 destruct(2<=?n)eqn:Hn;[apply Nat.leb_le in Hn|discriminate].
 destruct(csteps tm t c0)as[[q[[l h]r]]|]eqn:Et;[|discriminate].
 set(ls:=gadds(ng_seed_side n l ++ flat_map(fun c=>fst(ng_harvest tm c))Sl)gempty)in *.
 set(rs:=gadds(ng_seed_side n r ++ flat_map(fun c=>snd(ng_harvest tm c))Sl)gempty)in *.
 set(cc:=(q,(l,h,r)):cconf)in *;set(a0:=ng_start n cc)in *.
 match type of H with(if ?b then _ else _)=true=>destruct b eqn:Hseed end;[|discriminate].
 match type of H with(if ?b then _ else _)=true=>destruct b eqn:Hcl end;[|discriminate].
 match type of H with(if ?b then _ else _)=true=>destruct b eqn:Hmem end;[|discriminate].
 assert(HIn:In a0 Sl)by(eapply mem_In_tr;[exact cconf_enc_inj|exact Hmem]).
 assert(Hcov:ng_covers n ls rs a0(lift cc))by(apply ng_start_covers;exact Hseed).
 assert(Hstart:stepn tm t InitES=Some(lift cc))by(rewrite <-lift_c0;apply csteps_lift;exact Et).
 assert(Hinv:forall k,exists d a,csteps tm k cc=Some d /\ In a Sl /\ ng_covers n ls rs a(lift d)).
 { eapply closure_invariant_c_tr;[exact cconf_enc_inj| |exact Hcl|exact HIn|exact Hcov].
   intros a c Hc;apply ng_succs_sound;[lia|assumption]. }
 split.
 - intros k Hnone. destruct(le_lt_dec t k).
   + destruct(Hinv(k-t))as(d&a&HD&_). replace k with(t+(k-t))in Hnone by lia.
     rewrite stepn_add,Hstart,(csteps_lift _ _ _ _ HD)in Hnone;discriminate.
   + destruct(stepn_prefix tm k t InitES(lift cc)ltac:(lia)Hstart)as(d&HD&_);congruence.
 - intro N. destruct(Hinv N)as(d&a&HD&HA&HC).
   repeat rewrite andb_true_iff in H;destruct H as[[HO HG]HK].
   destruct(pc_reach tm n ls rs Sl target C cs Hn Hcl HO HG HK a d HA HC)as(j&e&HE&HT).
   exists(t+N+j);split;[lia|]. exists e;split;[|exact HT].
   replace(t+N+j)with(t+(N+j))by lia;rewrite stepn_add,Hstart,stepn_add,(csteps_lift _ _ _ _ HD);exact HE.
Qed.

Print Assumptions pc_graph_check_sound.
