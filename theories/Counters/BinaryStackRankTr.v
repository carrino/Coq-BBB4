(** Signed binary weighted stack potentials for finite tape configurations.
    The score functions may inspect finite prefixes; their locality is not
    needed by this generic soundness theorem.  Finite certificates can
    discharge the local difference inequalities separately. *)
From Coq Require Import Arith Lia List ZArith.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Counters Require Import NestCountTr LoopRunTr FiniteWallTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
Import ListNotations.
Local Open Scope Z_scope.
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
Lemma bsr_pow_add:forall n m,fw_pow(n+m)=fw_pow n*fw_pow m.
Proof. induction n;intro m;cbn[fw_pow Nat.add];[ring|rewrite IHn;ring]. Qed.
Lemma bsr_left_bound:forall f K,(forall L,-K<=f L)->
 forall L,-K*(fw_pow(length L)-1)<=bsr_left f L.
Proof.
 intros f K HF;induction L as[|x L IH];cbn[bsr_left length fw_pow];[lia|].
 pose proof(HF(x::L));pose proof(fw_pow_pos(length L));nia.
Qed.
Lemma bsr_right_bound:forall f K,(forall R,-K<=f R)->
 forall R,-K*(fw_pow(length R)-1)<=bsr_right f R.
Proof.
 intros f K HF;induction R as[|x R IH];cbn[bsr_right length fw_pow];[lia|].
 pose proof(HF(x::R));lia.
Qed.
Lemma bsr_integer_pos:forall fl fr b KL KR KB,
 0<=KL->0<=KR->0<=KB->
 (forall L,-KL<=fl L)->(forall R,-KR<=fr R)->(forall c,-KB<=b c)->
 forall c,0<=bsr_integer fl fr b(KL+KR+KB)c.
Proof.
 intros fl fr b KL KR KB HKL HKR HKB HL HR HB [q[[L h]R]].
 unfold bsr_integer,bsr_potential,fw_width. rewrite bsr_pow_add.
 pose proof(bsr_left_bound fl KL HL L)as EL.
 pose proof(bsr_right_bound fr KR HR R)as ER.
 specialize(HB(q,(L,h,R))).
 pose proof(fw_pow_pos(length L))as PL;pose proof(fw_pow_pos(length R))as PR.
 set(l:=fw_pow(length L))in *;set(r:=fw_pow(length R))in *.
 set(vl:=bsr_left fl L)in *;set(vr:=bsr_right fr R)in *.
 assert(E1:0<=l*(vr+b(q,(L,h,R))+KR*(r-1)+KB))by(apply Z.mul_nonneg_nonneg;lia).
 assert(E2:0<=KL*l*(r-1))by(apply Z.mul_nonneg_nonneg;[apply Z.mul_nonneg_nonneg|];lia).
 assert(E3:0<=KB*l*(r-1))by(apply Z.mul_nonneg_nonneg;[apply Z.mul_nonneg_nonneg|];lia).
 unfold ctape,cconf in *. nia.
Qed.
Lemma bsr_measure_step:forall fl fr b KL KR KB,
 0<=KL->0<=KR->0<=KB->
 (forall L,-KL<=fl L)->(forall R,-KR<=fr R)->(forall c,-KB<=b c)->
 forall q L h R tr,bsr_delta fl fr b(q,(L,h,R))tr<0->
 (t_dir tr=DL->L<>[])->(t_dir tr=DR->R<>[])->
 (bsr_measure fl fr b(KL+KR+KB)(t_next tr,ctape_move(t_dir tr)(t_write tr)(L,h,R))
 <bsr_measure fl fr b(KL+KR+KB)(q,(L,h,R)))%nat.
Proof.
 intros fl fr b KL KR KB HKL HKR HKB HL HR HB q L h R tr HD Hleft Hright.
 apply Z2Nat.inj_lt;try(apply bsr_integer_pos;assumption).
 unfold bsr_integer,bsr_potential,fw_width,bsr_delta in *.
 destruct tr as[s dir q'];cbn[t_dir t_next t_write]in *;destruct dir.
 - destruct L as[|x L];[exfalso;apply(Hleft eq_refl);reflexivity|].
   cbn[ctape_move chd ctl length bsr_left bsr_right fw_pow]in HD|-*.
   replace(length L+S(length R))%nat with(S(length L)+length R)%nat by lia.
   pose proof(fw_pow_pos(length L));nia.
 - destruct R as[|x R];[exfalso;apply(Hright eq_refl);reflexivity|].
   cbn[ctape_move chd ctl length bsr_left bsr_right fw_pow]in HD|-*.
   replace(S(length L)+length R)%nat with(length L+S(length R))%nat by lia.
   pose proof(fw_pow_pos(length L));nia.
Qed.
Local Close Scope Z_scope.
Section Termination.
Variables(tm:TM)(target:Instr)(Inv:cconf->Prop).
Hypothesis Hclosed:forall c d,Inv c->cinstr c<>target->cstep tm c=Some d->Inv d.
Hypothesis Hright:forall q L h R tr,Inv(q,(L,h,R))->(q,h)<>target->tm q h=Some tr->t_dir tr=DR->R<>[].
Hypothesis Htotal:forall q h,exists tr,tm q h=Some tr.
Variables(fl fr:list Sym->Z)(b:cconf->Z)(KL KR KB:Z).
Hypotheses(HKL:(0<=KL)%Z)(HKR:(0<=KR)%Z)(HKB:(0<=KB)%Z).
Hypotheses(Hfl:forall L,(-KL<=fl L)%Z)(Hfr:forall R,(-KR<=fr R)%Z)(Hb:forall c,(-KB<=b c)%Z).
Hypothesis Hdelta:forall q L h R tr,Inv(q,(L,h,R))->(q,h)<>target->tm q h=Some tr->
 cinstr(t_next tr,ctape_move(t_dir tr)(t_write tr)(L,h,R))<>target->
 (bsr_delta fl fr b(q,(L,h,R))tr<0)%Z.
Hypothesis Hleft:forall q h R tr,Inv(q,([],h,R))->(q,h)<>target->tm q h=Some tr->t_dir tr=DL->
 Fires tm(q,([],h,R))target.
Theorem bsr_fires:forall c,Inv c->Fires tm c target.
Proof.
 refine(well_founded_induction_type(well_founded_ltof cconf(bsr_measure fl fr b(KL+KR+KB)))
 (fun c=>Inv c->Fires tm c target) _).
 intros[q[[L h]R]]IH HI. destruct(instr_eqb(q,h)target)eqn:EN.
 - apply instr_eqb_spec in EN;apply fires_here;exact EN.
 - assert(HN:(q,h)<>target)by(intro E;subst;rewrite fw_instr_refl in EN;discriminate).
   destruct(Htotal q h)as(tr&ET).
   set(d:=(t_next tr,ctape_move(t_dir tr)(t_write tr)(L,h,R))).
   assert(ES:cstep tm(q,(L,h,R))=Some d)by(unfold d;cbn[cstep];rewrite ET;reflexivity).
   destruct(instr_eqb(cinstr d)target)eqn:ED.
   + apply instr_eqb_spec in ED. exists 1,d;split;[rewrite csteps_1;exact ES|exact ED].
   + assert(HD:cinstr d<>target)by(intro E;rewrite E,fw_instr_refl in ED;discriminate).
     destruct(t_dir tr)eqn:EM.
     * destruct L as[|x L];[eapply Hleft;eauto|].
       eapply fire_back with(b:=d).
       -- eapply(r0_run _ 1);[rewrite csteps_1;exact ES|r0].
       -- apply IH.
          ++ unfold ltof,d. rewrite <-EM. apply(bsr_measure_step fl fr b KL KR KB HKL HKR HKB Hfl Hfr Hb).
             ** apply Hdelta;try assumption;rewrite EM;exact HD.
             ** intros;discriminate.
             ** congruence.
          ++ eapply Hclosed;eauto.
     * eapply fire_back with(b:=d).
       -- eapply(r0_run _ 1);[rewrite csteps_1;exact ES|r0].
       -- apply IH.
          ++ unfold ltof,d. rewrite <-EM. apply(bsr_measure_step fl fr b KL KR KB HKL HKR HKB Hfl Hfr Hb).
             ** apply Hdelta;try assumption;rewrite EM;exact HD.
             ** congruence.
             ** eapply Hright;eauto.
          ++ eapply Hclosed;eauto.
Qed.
Theorem bsr_reaches:forall c,Inv c->exists d,Inv d/\cinstr d=target/\Reach0 tm c d.
Proof.
 intros c HI. destruct(bsr_fires c HI)as(n&e&HN&HEq). revert c HI HN.
 induction n;intros c HI HN.
 - cbn in HN;injection HN as <-. exists c;split;[exact HI|split;[exact HEq|r0]].
 - destruct(instr_eqb(cinstr c)target)eqn:ET.
   + apply instr_eqb_spec in ET. exists c;split;[exact HI|split;[exact ET|r0]].
   + assert(Hneq:cinstr c<>target)by(intro E;rewrite E,fw_instr_refl in ET;discriminate).
     cbn[csteps]in HN;destruct(cstep tm c)as[d|]eqn:ES;[|discriminate].
     destruct(IHn d(Hclosed c d HI Hneq ES)HN)as(f&HF&HQ&HR).
     exists f;split;[exact HF|split;[exact HQ|eapply(r0_run _ 1);[rewrite csteps_1;exact ES|exact HR]]].
Qed.
End Termination.

Local Open Scope Z_scope.
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
Local Close Scope Z_scope.
Section PositiveTermination.
Variables(tm:TM)(target:Instr)(Inv:cconf->Prop).
Hypothesis Hclosed:forall c d,Inv c->cinstr c<>target->cstep tm c=Some d->Inv d.
Hypothesis Htotal:forall q h,exists tr,tm q h=Some tr.
Variables(fl fr:list Sym->Z)(b:cconf->Z).
Hypothesis Hfr0:fr []=0%Z.
Hypothesis Hpositive:forall c,Inv c->cinstr c<>target->(0<=bsr_potential fl fr b c)%Z.
Hypothesis Hdelta:forall q L h R tr,Inv(q,(L,h,R))->(q,h)<>target->tm q h=Some tr->
 cinstr(t_next tr,ctape_move(t_dir tr)(t_write tr)(L,h,R))<>target->
 (bsr_delta fl fr b(q,(L,h,R))tr<0)%Z.
Hypothesis Hleft:forall q h R tr,Inv(q,([],h,R))->(q,h)<>target->tm q h=Some tr->t_dir tr=DL->
 Fires tm(q,([],h,R))target.
Theorem bsr_positive_fires:forall c,Inv c->Fires tm c target.
Proof.
 refine(well_founded_induction_type(well_founded_ltof cconf(fun c=>Z.to_nat(bsr_potential fl fr b c)))
 (fun c=>Inv c->Fires tm c target) _).
 intros[q[[L h]R]]IH HI. destruct(instr_eqb(q,h)target)eqn:EN.
 - apply instr_eqb_spec in EN;apply fires_here;exact EN.
 - assert(HN:(q,h)<>target)by(intro E;subst;rewrite fw_instr_refl in EN;discriminate).
   destruct(Htotal q h)as(tr&ET).
   set(d:=(t_next tr,ctape_move(t_dir tr)(t_write tr)(L,h,R))).
   assert(ES:cstep tm(q,(L,h,R))=Some d)by(unfold d;cbn[cstep];rewrite ET;reflexivity).
   destruct(instr_eqb(cinstr d)target)eqn:ED.
   + apply instr_eqb_spec in ED. exists 1,d;split;[rewrite csteps_1;exact ES|exact ED].
   + assert(HD:cinstr d<>target)by(intro E;rewrite E,fw_instr_refl in ED;discriminate).
     assert(HI':Inv d)by(eapply Hclosed;eauto).
     assert(HS: (t_dir tr=DL->L<>[])->Fires tm(q,(L,h,R))target).
     { intro HL. eapply fire_back with(b:=d).
       - eapply(r0_run _ 1);[rewrite csteps_1;exact ES|r0].
       - apply IH;[|exact HI']. unfold ltof.
         apply Z2Nat.inj_lt;try(apply Hpositive;assumption).
         unfold d. apply bsr_potential_step;[exact Hfr0| |exact HL].
         apply Hdelta;assumption. }
     destruct(t_dir tr)eqn:EM.
     * destruct L as[|x L];[eapply Hleft;eauto|]. apply HS;intros;discriminate.
     * apply HS;congruence.
Qed.
Theorem bsr_positive_reaches:forall c,Inv c->exists d,Inv d/\cinstr d=target/\Reach0 tm c d.
Proof.
 intros c HI. destruct(bsr_positive_fires c HI)as(n&e&HN&HEq). revert c HI HN.
 induction n;intros c HI HN.
 - cbn in HN;injection HN as <-. exists c;split;[exact HI|split;[exact HEq|r0]].
 - destruct(instr_eqb(cinstr c)target)eqn:ET.
   + apply instr_eqb_spec in ET. exists c;split;[exact HI|split;[exact ET|r0]].
   + assert(Hneq:cinstr c<>target)by(intro E;rewrite E,fw_instr_refl in ET;discriminate).
     cbn[csteps]in HN;destruct(cstep tm c)as[d|]eqn:ES;[|discriminate].
     destruct(IHn d(Hclosed c d HI Hneq ES)HN)as(f&HF&HQ&HR).
     exists f;split;[exact HF|split;[exact HQ|eapply(r0_run _ 1);[rewrite csteps_1;exact ES|exact HR]]].
Qed.
End PositiveTermination.
