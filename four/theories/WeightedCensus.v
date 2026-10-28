From Coq Require Import NArith Arith Lia Bool List ZArith.
From BBB24 Require Import Statement StatementTr CTape PosEnc Closure ClosureTr
 Bounds NGramCensus RankSearch WeightedNGram.
From BBB24.Checkers Require Import NGram WeightedLex FiniteWall.
Import ListNotations.

(** Compact certificate tables.  All entries are rechecked below. *)
Definition wc_table {A:Type}(default:A)(nodes:list cconf)(values:list A):cconf->A:=
 let m:=fold_left(fun m p=>PositiveMap.add(cconf_enc(fst p))(snd p)m)
   (combine nodes values)(PositiveMap.empty A)in
 fun a=>match PositiveMap.find(cconf_enc a)m with Some x=>x|None=>default end.
Definition wc_gate nodes active:cconf->bool:=
 wc_table false nodes(map(fun i=>existsb(Nat.eqb i)active)(seq 0(length nodes))).
Definition wc_score (a b c d:Z)(x:Sym):Z:=match x with S0=>a|S1=>b|S2=>c|S3=>d end.

Definition wc_entry tm target := flat_map(fun t:Instr=>
 if instr_eqb t target then [] else match tm(fst t)(snd t)with
 |Some tr=>match t_dir tr with DL=>[t_next tr]|DR=>[]end|None=>[]end)all_Instr.
Lemma wc_entry_complete:forall tm target q h tr,
 (q,h)<>target->tm q h=Some tr->t_dir tr=DL->In(t_next tr)(wc_entry tm target).
Proof.
 intros tm target q h tr HN HT HD. unfold wc_entry;apply in_flat_map.
 exists(q,h);split;[apply all_Instr_complete|].
 destruct(instr_eqb(q,h)target)eqn:E;[apply instr_eqb_spec in E;contradiction|].
 cbn[fst snd];rewrite HT,HD;cbn;auto.
Qed.
Record WCert:=mkWC{wc_k:nat;wc_guards:list(list Sym);wc_inside:list cconf;wc_components:list wncomp}.
Definition wc_target tm n ls rs Sl target cert:=
 match cert with
 |None=>lex_ok_tr cconf cinstr(ng_succs tm ls rs)Sl target
   (map(ng_comp_denote tm n)(rank_procedure tm ls rs Sl target))
 |Some C=>
   if forallb wn_linear (wc_components C) then
     wl_ok(ng_succs tm ls rs)target Sl(map(wn_denote tm n)(wc_components C))
   else wall_wmem(repeat S0(wc_k C))(wc_guards C) &&
   wall_check tm target(wc_entry tm target)(wc_guards C)(wc_inside C) &&
   forallb(wn_good Sl)(wc_components C) &&
   wl_ok(ng_succs tm ls rs)target Sl(map(wn_denote tm n)(wc_components C))
 end.
Definition wc_pad k(c:cconf):cconf:=let '(q,(L,h,R)):=c in(q,(L++repeat S0 k,h,R)).
Lemma wc_pad_lift:forall k c,lift(wc_pad k c)=lift c.
Proof.
 intros k[q[[L h]R]]. unfold wc_pad,lift,lift_tape;cbn[fst snd].
 assert(E:lift_side(L++repeat S0 k)=lift_side L).
 { apply lpad_eqb_lift. induction L as[|x L IH];cbn[lpad_eqb app].
   - induction k;cbn[lpad_eqb sym_eqb andb repeat];auto.
   - assert(sym_eqb x x=true)by(apply sym_eqb_spec;reflexivity);now rewrite H,IH. }
 now rewrite E.
Qed.

Lemma wc_linear_reach:forall tm n ls rs Sl target cs,
 1<=n -> closed_tr_b cconf cconf_enc(ng_succs tm ls rs)Sl=true ->
 forallb wn_linear cs=true ->
 wl_ok(ng_succs tm ls rs)target Sl(map(wn_denote tm n)cs)=true ->
 forall a c,In a Sl->ng_covers n ls rs a(lift c)->
 exists j e,stepn tm j(lift c)=Some e /\ instr_of e=target.
Proof.
 intros tm n ls rs Sl target cs Hn Hcl HL HO a c HA HC.
 assert(HS:forall a c,In a Sl->ng_covers n ls rs a(lift c)->
   exists d l b,cstep tm c=Some d /\ ng_succs tm ls rs a=Some l /\ In b l /\ In b Sl /\ ng_covers n ls rs b(lift d)).
 { intros a1 c1 HA1 HC1.
   destruct(closed_step_tr tm cconf cconf_enc(ng_succs tm ls rs)(ng_covers n ls rs)
     cconf_enc_inj(fun a e H=>ng_succs_sound tm n ls rs a e Hn H)Sl a1(lift c1)Hcl HA1 HC1)
     as(e&l&b&HE&HB&Hin&HinS&Hcov).
   destruct(cstep_lift_rev tm c1 e HE)as(d&Hd&Heq);subst e.
   exists d,l,b;auto. }
 assert(HK:Forall(wl_sound tm(ng_succs tm ls rs)(fun a c=>ng_covers n ls rs a(lift c))(fun _=>True)target Sl)
   (map(wn_denote tm n)cs)).
 { apply Forall_forall;intros k Hk;apply in_map_iff in Hk as(x&<-&Hx).
   apply wn_linear_component;[exact Hn|]. rewrite forallb_forall in HL;auto. }
 destruct(wl_reach tm(ng_succs tm ls rs)(fun a c=>ng_covers n ls rs a(lift c))(fun _=>True)target Sl
   (fun a c H=>eq_trans(ng_covers_instr n ls rs a(lift c)H)(cinstr_lift c))
   HS (fun _ _ _ _ _=>I)(map(wn_denote tm n)cs)HK HO c a I HA HC)as(j&d&HD&HT).
 exists j,(lift d);split;[apply csteps_lift;exact HD|rewrite cinstr_lift;exact HT].
Qed.

Theorem wc_reach:forall tm n ls rs Sl target cert,
 1<=n->closed_tr_b cconf cconf_enc(ng_succs tm ls rs)Sl=true->
 wc_target tm n ls rs Sl target cert=true->
 forall a c,In a Sl->ng_covers n ls rs a(lift c)->
 exists j e,stepn tm j(lift c)=Some e /\ instr_of e=target.
Proof.
 intros tm n ls rs Sl target cert Hn Hcl Hcheck a c HA HC.
 destruct cert as[C|].
 - unfold wc_target in Hcheck.
   destruct(forallb wn_linear(wc_components C))eqn:Hlinear.
   { eapply wc_linear_reach; eauto. }
   repeat rewrite andb_true_iff in Hcheck.
   destruct Hcheck as[[[HG HW]HK]HO].
   set(Inv:=wall_inv(wc_guards C)(wc_inside C)).
   set(c':=wc_pad(wc_k C)c).
   assert(HL:lift c'=lift c)by(apply wc_pad_lift).
   assert(HI:Inv c').
   { destruct c as[q[[L h]R]];apply wall_out. now apply wall_wmem_spec in HG. }
   assert(HC':ng_covers n ls rs a(lift c'))by(now rewrite HL).
   assert(HS:forall a c,In a Sl->ng_covers n ls rs a(lift c)->
     exists d l b,cstep tm c=Some d /\ ng_succs tm ls rs a=Some l /\ In b l /\ In b Sl /\ ng_covers n ls rs b(lift d)).
   { intros a1 c1 HA1 HC1.
     destruct(closed_step_tr tm cconf cconf_enc(ng_succs tm ls rs)(ng_covers n ls rs)
       cconf_enc_inj(fun a e H=>ng_succs_sound tm n ls rs a e Hn H)Sl a1(lift c1)Hcl HA1 HC1)
       as(e&l&b&HE&HB&Hin&HinS&Hcov).
     destruct(cstep_lift_rev tm c1 e HE)as(d&Hd&Heq);subst e.
     exists d,l,b;auto. }
   assert(HInv:forall c d,Inv c->cinstr c<>target->cstep tm c=Some d->Inv d).
   { intros;eapply wall_step;[exact HW|apply wc_entry_complete|eassumption|eassumption|eassumption]. }
   assert(HK':Forall(wl_sound tm(ng_succs tm ls rs)(fun a c=>ng_covers n ls rs a(lift c))Inv target Sl)
     (map(wn_denote tm n)(wc_components C))).
   { apply Forall_forall;intros k Hk;apply in_map_iff in Hk as(x&<-&Hx).
     apply wn_component;[exact Hn| |].
     - intros;eapply wall_left_nonempty;[exact HW|eassumption|eassumption|eassumption|eassumption].
     - rewrite forallb_forall in HK;auto. }
   destruct(wl_reach tm(ng_succs tm ls rs)(fun a c=>ng_covers n ls rs a(lift c))Inv target Sl
     (fun a c H=>eq_trans(ng_covers_instr n ls rs a(lift c)H)(cinstr_lift c))
     HS HInv(map(wn_denote tm n)(wc_components C))HK' HO c' a HI HA HC')as(j&d&HD&HT).
   exists j,(lift d);split;[rewrite <-HL;apply csteps_lift;exact HD|rewrite cinstr_lift;exact HT].
 - unfold wc_target in Hcheck.
   eapply(lex_reach_tr tm cconf cconf_enc cinstr(ng_succs tm ls rs)(ng_covers n ls rs)
      cconf_enc_inj(ng_covers_instr n ls rs)(fun a e H=>ng_succs_sound tm n ls rs a e Hn H)
      Sl target(map(ng_comp_denote tm n)(rank_procedure tm ls rs Sl target))Hcl Hcheck
      (ng_components_exact tm n ls rs _ Hn));
     [eapply lexlt_wf_len;reflexivity|reflexivity|exact HA|exact HC].
Qed.

Definition wc_check bs bi tm n t fuel rounds (cert:Instr->option WCert):bool:=
 if 1<=?n then match csteps tm t c0 with None=>false|Some cc=>
 let '(q,(l,h,r)):=cc in let a0:=ng_start n cc in
 let '(ls,rs):=ng_grow tm a0 fuel rounds(gadds(ng_seed_side n l)gempty)(gadds(ng_seed_side n r)gempty)in
 let Sl:=ng_explore tm ls rs fuel [] PositiveSet.empty[a0]in
 if ng_seed_ok n ls rs cc then
 if closed_tr_b cconf cconf_enc(ng_succs tm ls rs)Sl then
 if mem_tr cconf cconf_enc a0 Sl then
 if prefix_gate bs bi tm t(tail_states Sl)(tail_instrs Sl)then
 forallb(fun tg=>if tail_instrs Sl tg then wc_target tm n ls rs Sl tg(cert tg)else true)all_Instr
 else false else false else false else false end else false.

Theorem wc_check_sound:forall bs bi tm n t fuel rounds cert,
 wc_check bs bi tm n t fuel rounds cert=true->NonHalt tm /\ Bounds bs bi tm.
Proof.
 intros bs bi tm n t fuel rounds cert H;unfold wc_check in H.
 destruct(1<=?n)eqn:Hn;[apply Nat.leb_le in Hn|discriminate].
 destruct(csteps tm t c0)as[[q[[l h]r]]|]eqn:Et;[|discriminate].
 match type of H with(let '(_,_) := ?G in _)=true=>destruct G as[ls rs]end.
 cbv beta iota zeta in H.
 set(cc:=(q,(l,h,r)):cconf)in *;set(a0:=ng_start n cc)in *.
 set(Sl:=ng_explore tm ls rs fuel [] PositiveSet.empty[a0])in *.
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
   rewrite forallb_forall in H;specialize(H tg(all_Instr_complete tg));change ((if tail_instrs Sl tg then wc_target tm n ls rs Sl tg(cert tg)else true)=true)in H;rewrite Happ in H.
   destruct(wc_reach tm n ls rs Sl tg(cert tg)Hn Hcl H a d HA HC)as(j&e&HE&HT).
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


(** Replay a supplied closed graph without rerunning closure discovery.
    Gram sets include the directional windows harvested from the supplied
    contexts and every exact startup gram;
    seed coverage and all successor/liveness obligations are checked again. *)
Definition wc_graph_check bs bi tm n t (Sl:list cconf) (cert:Instr->option WCert):bool:=
 if 1<=?n then match csteps tm t c0 with None=>false|Some cc=>
 let '(q,(l,h,r)):=cc in let a0:=ng_start n cc in
 let ls:=gadds(ng_seed_side n l ++ flat_map(fun c=>fst(ng_harvest tm c))Sl)gempty in
 let rs:=gadds(ng_seed_side n r ++ flat_map(fun c=>snd(ng_harvest tm c))Sl)gempty in
 if ng_seed_ok n ls rs cc then
 if closed_tr_b cconf cconf_enc(ng_succs tm ls rs)Sl then
 if mem_tr cconf cconf_enc a0 Sl then
 if prefix_gate bs bi tm t(tail_states Sl)(tail_instrs Sl)then
 forallb(fun tg=>if tail_instrs Sl tg then wc_target tm n ls rs Sl tg(cert tg)else true)all_Instr
 else false else false else false else false end else false.

Theorem wc_graph_check_sound:forall bs bi tm n t Sl cert,
 wc_graph_check bs bi tm n t Sl cert=true->NonHalt tm /\ Bounds bs bi tm.
Proof.
 intros bs bi tm n t Sl cert H;unfold wc_graph_check in H.
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
   rewrite forallb_forall in H;specialize(H tg(all_Instr_complete tg));change ((if tail_instrs Sl tg then wc_target tm n ls rs Sl tg(cert tg)else true)=true)in H;rewrite Happ in H.
   destruct(wc_reach tm n ls rs Sl tg(cert tg)Hn Hcl H a d HA HC)as(j&e&HE&HT).
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
