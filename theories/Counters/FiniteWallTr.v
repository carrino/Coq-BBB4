(** Finite right walls with an opaque finite left context. *)
From Coq Require Import Arith Lia List Bool ZArith.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Counters Require Import NestCountTr LoopRunTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
Import ListNotations.
Fixpoint fw_word_eqb(a b:list Sym):bool:=match a,b with
|[],[]=>true|x::a,y::b=>sym_eqb x y&&fw_word_eqb a b|_,_=>false end.
Lemma fw_word_eq:forall a b,fw_word_eqb a b=true<->a=b.
Proof. induction a;destruct b;cbn;try (split;congruence). rewrite andb_true_iff,sym_eqb_spec,IHa;split;[intros[-> ->];reflexivity|intro E;injection E;auto]. Qed.
Definition fw_conf_eqb(a b:cconf):bool:=
 let '(q,(L,h,R)):=a in let '(q',(L',h',R')):=b in
 st_eqb q q'&&sym_eqb h h'&&fw_word_eqb L L'&&fw_word_eqb R R'.
Lemma fw_conf_eq:forall a b,fw_conf_eqb a b=true<->a=b.
Proof. intros[q[[L h]R]][q'[[L' h']R']];cbn[fw_conf_eqb]. rewrite !andb_true_iff,st_eqb_spec,sym_eqb_spec,!fw_word_eq. split;[intros[[[-> ->] ->] ->];reflexivity|intro E;injection E;auto]. Qed.
Definition fw_wmem(g:list Sym)(G:list(list Sym)):=existsb(fw_word_eqb g)G.
Definition fw_cmem(c:cconf)(I:list cconf):=existsb(fw_conf_eqb c)I.
Lemma fw_wmem_spec:forall g G,fw_wmem g G=true<->In g G.
Proof. intros;unfold fw_wmem;rewrite existsb_exists;split;[intros(w&Hw&E);apply fw_word_eq in E;subst;assumption|intro H;exists g;split;[assumption|apply fw_word_eq;reflexivity]]. Qed.
Lemma fw_cmem_spec:forall c I,fw_cmem c I=true<->In c I.
Proof. intros;unfold fw_cmem;rewrite existsb_exists;split;[intros(w&Hw&E);apply fw_conf_eq in E;subst;assumption|intro H;exists c;split;[assumption|apply fw_conf_eq;reflexivity]]. Qed.
Definition fw_ext(c:cconf)(U:list Sym):cconf:=let '(q,(L,h,R)):=c in(q,(L++U,h,R)).
Definition fw_entry(q:St)(g:list Sym):cconf:=(q,([],chd g,ctl g)).
Inductive fw_inv(G:list(list Sym))(I:list cconf):cconf->Prop:=
|fw_out:forall q L h R g,In g G->fw_inv G I(q,(L,h,R++g))
|fw_in:forall c U,In c I->fw_inv G I(fw_ext c U).
Definition fw_rule(tm:TM)(target:Instr)(G:list(list Sym))(I:list cconf)(c:cconf):bool:=
 if instr_eqb(cinstr c)target then true else
 let '(q,(L,h,R)):=c in
 match tm q h with
 |None=>false
 |Some tr=>match t_dir tr with
   |DL=>match L with []=>fw_wmem(t_write tr::R)G|_=>match cstep tm c with Some d=>fw_cmem d I|None=>false end end
   |DR=>match R with []=>false|_=>match cstep tm c with Some d=>fw_cmem d I|None=>false end end
   end end.
Definition fw_check(tm:TM)(target:Instr)(entry:list St)(G:list(list Sym))(I:list cconf):bool:=
 forallb(fun g=>match g with []=>false|_=>forallb(fun q=>fw_cmem(fw_entry q g)I)entry end)G
 &&forallb(fw_rule tm target G I)I.
Lemma fw_entries:forall tm target entry G I,fw_check tm target entry G I=true->
 forall g,In g G->g<>[] /\ forall q,In q entry->In(fw_entry q g)I.
Proof.
 intros tm target entry G I H g Hg. unfold fw_check in H;apply andb_true_iff in H as[H _].
 rewrite forallb_forall in H;specialize(H g Hg). destruct g;[discriminate|]. split;[discriminate|].
 intros q Hq;apply fw_cmem_spec. cbn in H;rewrite forallb_forall in H;auto.
Qed.
Lemma fw_rules:forall tm target entry G I,fw_check tm target entry G I=true->
 forall c,In c I->fw_rule tm target G I c=true.
Proof. intros tm target entry G I H;unfold fw_check in H;apply andb_true_iff in H as[_ H];now rewrite forallb_forall in H. Qed.
Lemma fw_step:forall tm target entry G I,
 fw_check tm target entry G I=true->
 (forall q h tr,tm q h=Some tr->t_dir tr=DR->In(t_next tr)entry)->
 forall c d,fw_inv G I c->cinstr c<>target->cstep tm c=Some d->fw_inv G I d.
Proof.
 intros tm target entry G I HC HE c d HI HN HS. inversion HI;subst.
 - cbn[cstep]in HS. destruct(tm q h)as[tr|]eqn:ET;[|discriminate].
   cbn[ctape_move]in HS. destruct(t_dir tr)eqn:ED.
   + destruct L as[|x L];injection HS as <-;cbn[ctape_move ctl chd];
     apply(fw_out G I _ _ _ (t_write tr::R) g);assumption.
   + destruct R as[|x R].
     * cbn[app]in HS;injection HS as <-. cbn[ctape_move].
       change(fw_inv G I(fw_ext(fw_entry(t_next tr)g)(t_write tr::L))).
       apply fw_in. apply(fw_entries _ _ _ _ _ HC _ H). apply HE with(q:=q)(h:=h)(tr:=tr);assumption.
     * injection HS as <-;cbn[ctape_move ctl chd app];apply fw_out;assumption.
 - destruct c0 as[q[[L h]R]]. cbn[fw_ext]in *.
   pose proof(fw_rules _ _ _ _ _ HC _ H)as HR.
   unfold fw_rule in HR. assert(EN:instr_eqb(cinstr(q,(L,h,R)))target=false).
   { destruct(instr_eqb _ _)eqn:E;[apply instr_eqb_spec in E;contradiction|reflexivity]. }
   unfold cinstr in EN,HR;cbn in EN,HR;rewrite EN in HR;cbn in HR. cbn[cstep]in HS.
   destruct(tm q h)as[tr|]eqn:ET;[|discriminate].
   cbn[ctape_move]in HS. destruct(t_dir tr)eqn:ED.
   + destruct L as[|x L].
     * cbn in HR;apply fw_wmem_spec in HR. injection HS as <-.
       destruct U;cbn[ctape_move chd ctl app];apply(fw_out G I _ _ _ [] (t_write tr::R));assumption.
     * cbn[ctape_move chd ctl]in HR.
       apply fw_cmem_spec in HR. injection HS as <-.
       change(fw_inv G I(fw_ext(t_next tr,(L,x,t_write tr::R))U));apply fw_in;assumption.
   + destruct R as[|x R];[discriminate|].
     cbn[ctape_move chd ctl]in HR.
     apply fw_cmem_spec in HR. injection HS as <-.
     change(fw_inv G I(fw_ext(t_next tr,(t_write tr::L,x,R))U));apply fw_in;assumption.
Qed.
Lemma fw_right_nonempty:forall tm target entry G I,
 fw_check tm target entry G I=true->
 forall q L h R tr,fw_inv G I(q,(L,h,R))->(q,h)<>target->
 tm q h=Some tr->t_dir tr=DR->R<>[].
Proof.
 intros tm target entry G I HC q L h R tr HI HN ET ED.
 inversion HI;subst.
 - destruct(fw_entries _ _ _ _ _ HC _ H0)as[HG _]. intro E;apply app_eq_nil in E as[_ E];contradiction.
 - destruct c as[q'[[L' h']R']];cbn[fw_ext]in H;injection H as <- <- <- <-.
   pose proof(fw_rules _ _ _ _ _ HC _ H0)as HR. unfold fw_rule in HR.
   assert(EN:instr_eqb(cinstr(q',(L',h',R')))target=false).
   { destruct(instr_eqb _ _)eqn:E;[apply instr_eqb_spec in E;contradiction|reflexivity]. }
   unfold cinstr in EN,HR;cbn in EN,HR;rewrite EN in HR;cbn in HR;rewrite ET,ED in HR. destruct R';[discriminate|discriminate].
Qed.

(** A binary tape potential, anchored at the explicit right endpoint. *)
Local Open Scope Z_scope.
Definition fw_bit(s:Sym):Z:=match s with S0=>0|S1=>1 end.
Fixpoint fw_pow(n:nat):Z:=match n with O=>1|S n=>2*fw_pow n end.
Fixpoint fw_left(L:list Sym):Z:=match L with []=>0|x::L=>fw_bit x+2*fw_left L end.
Fixpoint fw_right(R:list Sym):Z:=match R with []=>0|x::R=>fw_bit x*fw_pow(length R)+fw_right R end.
Definition fw_value(c:cconf):Z:=let '(_,(L,h,R)):=c in
 2*fw_pow(length R)*fw_left L+fw_bit h*fw_pow(length R)+fw_right R.
Definition fw_potential(w:Z)(b:St->Z)(c:cconf):Z:=let '(q,(_,_,R)):=c in
 w*fw_value c+b q*fw_pow(length R).
Definition fw_width(c:cconf):nat:=let '(_,(L,_,R)):=c in(length L+length R)%nat.
Definition fw_integer(w:Z)(b:St->Z)(K:Z)(c:cconf):Z:=
 K*fw_pow(fw_width c)+fw_potential w b c.
Definition fw_measure(w:Z)(b:St->Z)(K:Z)(c:cconf):nat:=Z.to_nat(fw_integer w b K c).
Lemma fw_pow_pos:forall n,0<fw_pow n.
Proof. induction n;cbn[fw_pow];lia. Qed.
Lemma fw_pow_mono:forall n m,(n<=m)%nat->fw_pow n<=fw_pow m.
Proof. intros n m H;induction H;[lia|cbn[fw_pow];pose proof(fw_pow_pos m);lia]. Qed.
Lemma fw_left_pos:forall L,0<=fw_left L.
Proof. induction L as[|[]L IH];cbn[fw_left fw_bit];lia. Qed.
Lemma fw_right_pos:forall R,0<=fw_right R.
Proof. induction R as[|[]R IH];cbn[fw_right fw_bit];try lia;pose proof(fw_pow_pos(length R));lia. Qed.
Lemma fw_value_pos:forall c,0<=fw_value c.
Proof. intros[q[[L h]R]];unfold fw_value;pose proof(fw_left_pos L);pose proof(fw_right_pos R);pose proof(fw_pow_pos(length R));destruct h;cbn[fw_bit];nia. Qed.
Lemma fw_integer_pos:forall w b K,
 0<=w->0<=K->(forall q,-K<=b q)->forall c,0<=fw_integer w b K c.
Proof.
 intros w b K Hw HK Hb [q[[L h]R]]. unfold fw_integer,fw_potential,fw_width.
 pose proof(fw_value_pos(q,(L,h,R)))as HV.
 pose proof(fw_pow_pos(length R))as HP.
 pose proof(fw_pow_mono(length R)(length L+length R)ltac:(lia))as HM.
 specialize(Hb q).
 assert(H1:0<=K*(fw_pow(length L+length R)-fw_pow(length R)))by(apply Z.mul_nonneg_nonneg;lia).
 assert(H2:0<=(b q+K)*fw_pow(length R))by(apply Z.mul_nonneg_nonneg;lia).
 assert(H3:0<=w*fw_value(q,(L,h,R)))by(apply Z.mul_nonneg_nonneg;lia).
 cbn[fw_value]in *. nia.
Qed.
Definition fw_delta(w:Z)(b:St->Z)(q:St)(h:Sym)(tr:Trans):Z:=
 match t_dir tr with
 |DL=>w*(fw_bit(t_write tr)-fw_bit h)+2*b(t_next tr)-b q
 |DR=>2*w*(fw_bit(t_write tr)-fw_bit h)+b(t_next tr)-2*b q end.
Lemma fw_measure_step:forall tm w b K,
 0<=w->0<=K->(forall q,-K<=b q)->
 forall q L h R tr,tm q h=Some tr->fw_delta w b q h tr<0->
 (t_dir tr=DL->L<>[])->(t_dir tr=DR->R<>[])->
 (fw_measure w b K(t_next tr,ctape_move(t_dir tr)(t_write tr)(L,h,R))
  <fw_measure w b K(q,(L,h,R)))%nat.
Proof.
 intros tm w b K Hw HK Hb q L h R tr ET HD HL HR.
 apply Z2Nat.inj_lt;try apply fw_integer_pos;try assumption.
 unfold fw_integer,fw_potential,fw_value,fw_width,fw_delta in *.
 destruct tr as[s d q'];cbn[t_write t_dir t_next]in *;destruct d.
 - destruct L as[|x L];[exfalso;apply(HL eq_refl);reflexivity|].
   cbn[ctape_move chd ctl length fw_left fw_right fw_pow].
   replace(length L+S(length R))%nat with(S(length L)+length R)%nat by lia.
   pose proof(fw_pow_pos(length R)). nia.
 - destruct R as[|x R];[exfalso;apply(HR eq_refl);reflexivity|].
   cbn[ctape_move chd ctl length fw_left fw_right fw_pow].
   replace(S(length L)+length R)%nat with(length L+S(length R))%nat by lia.
   pose proof(fw_pow_pos(length R)). nia.
Qed.
Local Close Scope Z_scope.

Lemma fw_instr_refl:forall t,instr_eqb t t=true.
Proof. intro;apply instr_eqb_spec;reflexivity. Qed.
Section WallTermination.
Variables(tm:TM)(target:Instr)(entry:list St)(G:list(list Sym))(I:list cconf).
Hypothesis HC:fw_check tm target entry G I=true.
Hypothesis HE:forall q h tr,tm q h=Some tr->t_dir tr=DR->In(t_next tr)entry.
Hypothesis HT:forall q h,exists tr,tm q h=Some tr.
Variables(w K:Z)(b:St->Z).
Hypotheses(Hw:(0<=w)%Z)(HK:(0<=K)%Z)(Hb:forall q,(-K<=b q)%Z).
Hypothesis HD:forall q h tr,(q,h)<>target->tm q h=Some tr->(fw_delta w b q h tr<0)%Z.
Hypothesis HL:forall q h R tr,(q,h)<>target->tm q h=Some tr->t_dir tr=DL->Fires tm(q,([],h,R))target.
Theorem fw_fires:forall c,fw_inv G I c->Fires tm c target.
Proof.
 refine(well_founded_induction_type(well_founded_ltof cconf(fw_measure w b K))
 (fun c=>fw_inv G I c->Fires tm c target) _).
 intros[q[[L h]R]]IH HI.
 destruct(instr_eqb(q,h)target)eqn:EN.
 - apply instr_eqb_spec in EN;apply fires_here;exact EN.
 - assert(HN:(q,h)<>target)by(intro E;subst;rewrite fw_instr_refl in EN;discriminate).
   destruct(HT q h)as(tr&ET).
   destruct(t_dir tr)eqn:ED.
   + destruct L as[|x L].
     * apply(HL q h R tr HN ET ED).
     * eapply fire_back with(b:=(t_next tr,ctape_move DL(t_write tr)(x::L,h,R))).
       -- eapply(r0_run _ 1);[cbn[csteps cstep];rewrite ET,ED;reflexivity|r0].
       -- apply IH.
          ++ unfold ltof. rewrite <-ED. apply(fw_measure_step tm w b K Hw HK Hb q(x::L)h R tr ET(HD q h tr HN ET));
             intros E;[discriminate|congruence].
          ++ eapply(fw_step _ _ _ _ _ HC HE);[exact HI|exact HN|]. cbn[cstep];rewrite ET,ED;reflexivity.
   + eapply fire_back with(b:=(t_next tr,ctape_move DR(t_write tr)(L,h,R))).
     * eapply(r0_run _ 1);[cbn[csteps cstep];rewrite ET,ED;reflexivity|r0].
     * apply IH.
       -- unfold ltof. rewrite <-ED. apply(fw_measure_step tm w b K Hw HK Hb q L h R tr ET(HD q h tr HN ET));
          intros E;[congruence|eapply(fw_right_nonempty _ _ _ _ _ HC);eauto].
       -- eapply(fw_step _ _ _ _ _ HC HE);[exact HI|exact HN|]. cbn[cstep];rewrite ET,ED;reflexivity.
Qed.
Lemma fw_first_hit:forall c,fw_inv G I c->Fires tm c target->
 exists d,fw_inv G I d /\ cinstr d=target /\ Reach0 tm c d.
Proof.
 intros c HI(n&e&HN&HEq). revert c HI HN.
 induction n;intros c HI HN.
 - cbn in HN;injection HN as <-. exists c;split;[exact HI|split;[exact HEq|r0]].
 - destruct(instr_eqb(cinstr c)target)eqn:ET.
   + apply instr_eqb_spec in ET. exists c;split;[exact HI|split;[exact ET|r0]].
   + assert(Hneq:cinstr c<>target)by(intro E;rewrite E,fw_instr_refl in ET;discriminate).
     cbn[csteps]in HN. destruct(cstep tm c)as[d|]eqn:ES;[|discriminate].
     destruct(IHn d (fw_step _ _ _ _ _ HC HE c d HI Hneq ES) HN)as(f&HF&HIq&HR).
     exists f;split;[exact HF|split;[exact HIq|eapply(r0_run _ 1);[rewrite csteps_1;exact ES|exact HR]]].
Qed.
Theorem fw_reaches:forall c,fw_inv G I c->
 exists d,fw_inv G I d /\ cinstr d=target /\ Reach0 tm c d.
Proof. intros;apply fw_first_hit;[assumption|apply fw_fires;assumption]. Qed.
End WallTermination.
