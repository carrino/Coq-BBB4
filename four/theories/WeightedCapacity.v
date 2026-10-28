(** A target-avoiding nonnegative count invariant can reserve a finite left
    boundary for binary rankings. Zero padding initializes an arbitrary reserve;
    all graph edges are checked again, including the invariant's exact deltas. *)
From Coq Require Import NArith Arith Lia Bool List ZArith.
From BBB24 Require Import Statement StatementTr CTape PosEnc Closure ClosureTr
 Bounds NGramCensus RankSearch WeightedNGram WeightedCensus.
From BBB24.Checkers Require Import NGram WeightedLex.
Import ListNotations.

Record WCapacity := mkWCapacity {
 wca_scale:nat;
 wca_terms:list(nat*ngmeas);
 wca_bias:cconf->nat
}.
Definition wca_value n C c := wn_sum(wca_terms C)c+wca_bias C(ng_start n c).
Definition wca_left(c:cconf):nat := let '(_,(l,_,_)):=c in length l.
Definition wca_margin n C c := wca_value n C c<wca_scale C*wca_left c.
Definition wca_delta tm C a b :=
 (wn_diff tm(wca_terms C)a b+Z.of_nat(wca_bias C b)-Z.of_nat(wca_bias C a))%Z.
Definition wca_edge tm C a b :=
 let '(q,(_,h,_)):=a in match tm q h with None=>false|Some tr=>
 (wca_delta tm C a b <=? match t_dir tr with
 |DL=> -Z.of_nat(wca_scale C)|DR=>Z.of_nat(wca_scale C)end)%Z end.
Definition wca_ok tm ls rs Sl target C :=
 (0<?wca_scale C) && forallb(fun a=>if instr_eqb(cinstr a)target then true else
 match ng_succs tm ls rs a with None=>false|Some next=>
 forallb(fun b=>if instr_eqb(cinstr b)target then true else wca_edge tm C a b)next end)Sl.

Lemma wca_count_pad:forall col l k,count1 col(l++repeat S0 k)=count1 col l.
Proof.
 intros col l;induction l;intro k;cbn[app count1].
 - induction k;cbn[repeat count1];[reflexivity|destruct col;exact IHk].
 - now rewrite IHl.
Qed.
Lemma wca_sum_pad:forall terms k c,wn_sum terms(wc_pad k c)=wn_sum terms c.
Proof.
 intros terms;induction terms as[|[v m]terms IH];intros k[q[[l h]r]];
 cbn[wn_sum];[reflexivity|]. rewrite IH. f_equal. f_equal.
 destruct m;cbn[ngm_val wc_pad];now rewrite ?wca_count_pad.
Qed.
Lemma wca_start_pad:forall n k c,ng_start n(wc_pad k c)=ng_start n c.
Proof.
 intros n k[q[[l h]r]]. cbn[ng_start wc_pad].
 assert(H:lift_side(l++repeat S0 k)=lift_side l).
 { pose proof(wc_pad_lift k(StA,(l,h,r)))as E.
   exact(f_equal(fun e=>t_left(snd e))E). }
 now rewrite H.
Qed.
Lemma wca_pad_margin:forall n C c,0<wca_scale C ->
 wca_margin n C(wc_pad(S(wca_value n C c))c).
Proof.
 intros n C[q[[l h]r]]HK. unfold wca_margin,wca_value.
 rewrite wca_sum_pad,wca_start_pad.
 cbn[wc_pad wca_left]. rewrite app_length,repeat_length. nia.
Qed.
Lemma wca_nonempty:forall n C q l h r,
 wca_margin n C(q,(l,h,r))->l<>[].
Proof. intros n C q l h r H ->;unfold wca_margin,wca_left in H;cbn in H;nia. Qed.

Lemma wca_margin_step:forall tm n ls rs C a c b d,
 1<=n->ng_covers n ls rs a(lift c)->ng_covers n ls rs b(lift d)->
 cstep tm c=Some d->wca_margin n C c->wca_edge tm C a b=true->wca_margin n C d.
Proof.
 intros tm n ls rs C a c b d Hn HC HD HS HI HE.
 pose proof(wn_start _ _ _ _ _ HC)as EA.
 pose proof(wn_start _ _ _ _ _ HD)as EB.
 pose proof(wn_sum_exact(wca_terms C)tm n ls rs a c b d Hn HC HS)as EV.
 assert(ED:Z.of_nat(wca_value n C d)=
  (Z.of_nat(wca_value n C c)+wca_delta tm C a b)%Z).
 { unfold wca_value,wca_delta. rewrite !Nat2Z.inj_add,EV,<-EA,<-EB;ring. }
 destruct c as[q[[l h]r]],a as[p[[L x]R]].
 destruct(wn_heads n ls rs p L x R q l h r Hn HC)as[-> [-> _]].
 cbn[wca_edge]in HE. cbn[cstep]in HS.
 destruct(tm q h)as[tr|]eqn:HT;[|discriminate].
 apply Z.leb_le in HE. injection HS as <-.
 assert(Hleft:l<>[])by(eapply wca_nonempty;exact HI).
 unfold wca_margin in HI|-*. apply Nat2Z.inj_lt. rewrite Nat2Z.inj_mul.
 apply Nat2Z.inj_lt in HI. rewrite Nat2Z.inj_mul in HI.
 destruct(t_dir tr)eqn:Edir;
 cbn[ctape_move wca_left]in *.
 - destruct l;[contradiction|]. cbn[chd ctl length]in *.
   rewrite Nat2Z.inj_succ in HI. nia.
 - cbn[length]in *. rewrite Nat2Z.inj_succ. nia.
Qed.

Lemma wca_reach:forall tm n ls rs Sl target C cs,
 1<=n->closed_tr_b cconf cconf_enc(ng_succs tm ls rs)Sl=true->
 wca_ok tm ls rs Sl target C=true->forallb(wn_good Sl)cs=true->
 wl_ok(ng_succs tm ls rs)target Sl(map(wn_denote tm n)cs)=true->
 forall a c,In a Sl->ng_covers n ls rs a(lift c)->
 exists j e,stepn tm j(lift c)=Some e /\ instr_of e=target.
Proof.
 intros tm n ls rs Sl target C cs Hn Hcl HO HG HK a c HA HC.
 apply andb_prop in HO as[Hscale HO];apply Nat.ltb_lt in Hscale.
 assert(HS:forall a c,In a Sl->ng_covers n ls rs a(lift c)->
   exists d l b,cstep tm c=Some d /\ ng_succs tm ls rs a=Some l /\
   In b l /\ In b Sl /\ ng_covers n ls rs b(lift d)).
 { intros a1 c1 HA1 HC1.
   destruct(closed_step_tr tm cconf cconf_enc(ng_succs tm ls rs)(ng_covers n ls rs)
     cconf_enc_inj(fun a e H=>ng_succs_sound tm n ls rs a e Hn H)Sl a1(lift c1)Hcl HA1 HC1)
     as(e&l&b&HE&HB&Hin&HinS&Hcov).
   destruct(cstep_lift_rev tm c1 e HE)as(d&Hd&Heq);subst e.
   exists d,l,b;auto. }
 set(Inv:=fun c=>cinstr c=target \/
   (exists a,In a Sl /\ ng_covers n ls rs a(lift c) /\ wca_margin n C c)).
 assert(HInv:forall c d,Inv c->cinstr c<>target->cstep tm c=Some d->Inv d).
 { intros c1 d [Ht|(a1&Ha&Hcov&Hcap)] Hnt Hstep;[contradiction|].
   destruct(HS a1 c1 Ha Hcov)as(d1&next&b&Hstep1&HE&Hin&Hb&Hcovb).
   rewrite Hstep in Hstep1;injection Hstep1 as <-.
   destruct(instr_eqb(cinstr b)target)eqn:Et.
   - left;apply instr_eqb_spec in Et.
     rewrite <-(cinstr_lift d),<-(ng_covers_instr _ _ _ _ _ Hcovb);exact Et.
   - right;exists b;split;[exact Hb|split;[exact Hcovb|]].
     eapply(wca_margin_step tm n ls rs C a1 c1 b d);eauto.
     rewrite forallb_forall in HO;specialize(HO a1 Ha).
     destruct(instr_eqb(cinstr a1)target)eqn:Eu.
     + apply instr_eqb_spec in Eu;exfalso;apply Hnt.
       rewrite <-(cinstr_lift c1),<-(ng_covers_instr _ _ _ _ _ Hcov);exact Eu.
     + rewrite HE in HO;rewrite forallb_forall in HO;specialize(HO b Hin);rewrite Et in HO;exact HO. }
 assert(Hcomp:Forall(wl_sound tm(ng_succs tm ls rs)
   (fun a c=>ng_covers n ls rs a(lift c))Inv target Sl)(map(wn_denote tm n)cs)).
 { apply Forall_forall;intros k Hin;apply in_map_iff in Hin as(x&<-&Hx).
   apply wn_component;[exact Hn| |].
   - intros q l h r tr [Ht|(b&Hb&Hcov&Hcap)] Hnt HT HD;
       [contradiction|eapply wca_nonempty;exact Hcap].
   - rewrite forallb_forall in HG;auto. }
 set(c':=wc_pad(S(wca_value n C c))c).
 assert(Hlift:lift c'=lift c)by(apply wc_pad_lift).
 assert(Hcov:ng_covers n ls rs a(lift c'))by(now rewrite Hlift).
 assert(Hinit:Inv c').
 { right;exists a;split;[exact HA|split;[exact Hcov|]]. apply wca_pad_margin;exact Hscale. }
 destruct(wl_reach tm(ng_succs tm ls rs)(fun a c=>ng_covers n ls rs a(lift c))Inv target Sl
   (fun a c H=>eq_trans(ng_covers_instr n ls rs a(lift c)H)(cinstr_lift c))
   HS HInv(map(wn_denote tm n)cs)Hcomp HK c' a Hinit HA Hcov)as(j&d&HD&HT).
 exists j,(lift d);split;[rewrite <-Hlift;apply csteps_lift;exact HD|rewrite cinstr_lift;exact HT].
Qed.

Definition wca_target tm n ls rs Sl target cert capacity :=
 match capacity with None=>wc_target tm n ls rs Sl target cert |Some C=>
 match cert with None=>false |Some W=>
 wca_ok tm ls rs Sl target C && forallb(wn_good Sl)(wc_components W) &&
 wl_ok(ng_succs tm ls rs)target Sl(map(wn_denote tm n)(wc_components W)) end end.
Lemma wca_target_reach:forall tm n ls rs Sl target cert capacity,
 1<=n->closed_tr_b cconf cconf_enc(ng_succs tm ls rs)Sl=true->
 wca_target tm n ls rs Sl target cert capacity=true->
 forall a c,In a Sl->ng_covers n ls rs a(lift c)->
 exists j e,stepn tm j(lift c)=Some e /\ instr_of e=target.
Proof.
 intros tm n ls rs Sl target cert capacity Hn Hcl H.
 destruct capacity as[C|];[destruct cert as[W|];[|discriminate]|eapply wc_reach;eauto].
 unfold wca_target in H;repeat rewrite andb_true_iff in H.
 destruct H as[[HO HG]HK];eapply wca_reach;eauto.
Qed.
Definition wca_graph_check bs bi tm n t (Sl:list cconf) (cert:Instr->option WCert)(capacity:Instr->option WCapacity):bool:=
 if 1<=?n then match csteps tm t c0 with None=>false|Some cc=>
 let '(q,(l,h,r)):=cc in let a0:=ng_start n cc in
 let ls:=gadds(ng_seed_side n l ++ flat_map(fun c=>fst(ng_harvest tm c))Sl)gempty in
 let rs:=gadds(ng_seed_side n r ++ flat_map(fun c=>snd(ng_harvest tm c))Sl)gempty in
 if ng_seed_ok n ls rs cc then
 if closed_tr_b cconf cconf_enc(ng_succs tm ls rs)Sl then
 if mem_tr cconf cconf_enc a0 Sl then
 if prefix_gate bs bi tm t(tail_states Sl)(tail_instrs Sl)then
 forallb(fun tg=>if tail_instrs Sl tg then wca_target tm n ls rs Sl tg(cert tg)(capacity tg)else true)all_Instr
 else false else false else false else false end else false.

Theorem wca_graph_check_sound:forall bs bi tm n t Sl cert capacity,
 wca_graph_check bs bi tm n t Sl cert capacity=true->NonHalt tm /\ Bounds bs bi tm.
Proof.
 intros bs bi tm n t Sl cert capacity H;unfold wca_graph_check in H.
 destruct(1<=?n)eqn:Hn;[apply Nat.leb_le in Hn|discriminate].
 destruct(csteps tm t c0)as[[q[[l h]r]]|]eqn:Et;[|discriminate].
 set(ls:=gadds(ng_seed_side n l ++ flat_map(fun c=>fst(ng_harvest tm c))Sl)gempty)in *.
 set(rs:=gadds(ng_seed_side n r ++ flat_map(fun c=>snd(ng_harvest tm c))Sl)gempty)in *.
 set(cc:=(q,(l,h,r)):cconf)in *;set(a0:=ng_start n cc)in *.
 match type of H with(if ?b then _ else _)=true=>destruct b eqn:Hseed end;[|discriminate].
 match type of H with(if ?b then _ else _)=true=>destruct b eqn:Hcl end;[|discriminate].
 match type of H with(if ?b then _ else _)=true=>destruct b eqn:Hmem end;[|discriminate].
 match type of H with(if ?b then _ else _)=true=>destruct b eqn:Hpre end;[|discriminate].
 assert(HIn:In a0 Sl)by(eapply mem_In_tr;[exact cconf_enc_inj|exact Hmem]).
 assert(Hcov:ng_covers n ls rs a0(lift cc))by(apply ng_start_covers;exact Hseed).
 assert(Hstart:stepn tm t InitES=Some(lift cc))by(rewrite <-lift_c0;apply csteps_lift;exact Et).
 assert(Hinv:forall k,exists d a,csteps tm k cc=Some d /\ In a Sl /\ ng_covers n ls rs a(lift d)).
 { eapply closure_invariant_c_tr;[exact cconf_enc_inj| |exact Hcl|exact HIn|exact Hcov].
   intros a c Hc;apply ng_succs_sound;assumption. }
 assert(Hrec:forall tg,tail_instrs Sl tg=true->forall N,exists k,N<=k /\ FiresAt tm tg k).
 { intros tg Happ N. destruct(Hinv N)as(d&a&HD&HA&HC).
   rewrite forallb_forall in H;specialize(H tg(all_Instr_complete tg));change ((if tail_instrs Sl tg then wca_target tm n ls rs Sl tg(cert tg)(capacity tg)else true)=true)in H;rewrite Happ in H.
   destruct(wca_target_reach tm n ls rs Sl tg(cert tg)(capacity tg)Hn Hcl H a d HA HC)as(j&e&HE&HT).
   exists(t+N+j);split;[lia|]. exists e;split;[|exact HT].
   replace(t+N+j)with(t+(N+j))by lia;rewrite stepn_add,Hstart,stepn_add,(csteps_lift _ _ _ _ HD);exact HE. }
 split.
 - intros k Hnone. destruct(le_lt_dec t k).
   + destruct(Hinv(k-t))as(d&a&HD&_). replace k with(t+(k-t))in Hnone by lia.
     rewrite stepn_add,Hstart,(csteps_lift _ _ _ _ HD)in Hnone;discriminate.
   + destruct(stepn_prefix tm k t InitES(lift cc)ltac:(lia)Hstart)as(d&HD&_);congruence.
 - eapply(tail_bounds bs bi);[exact Hpre| |exact Hrec].
   intros s tg Hts(e&HE&HT);destruct(Hinv(s-t))as(d&a&HD&HA&HC).
   replace s with(t+(s-t))in HE by lia;rewrite stepn_add,Hstart,(csteps_lift _ _ _ _ HD)in HE.
   injection HE as <-. apply existsb_exists;exists a;split;[exact HA|].
   apply instr_eqb_spec;rewrite <-(ng_covers_instr n ls rs a(lift d)HC)in HT;exact HT.
Qed.

Print Assumptions wca_graph_check_sound.
