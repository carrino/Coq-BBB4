(** * Counters.BlockCoreMReturnTr: regular right-stack boundary for core M.

    Canonical table: [0RB1LD_1RC0RC_1LA1RA_1RA0LD]. The invariant combines
    a 19-state DFA of the finite right word with the nearest three left
    symbols. Its local closure is checked exhaustively; the untrusted
    backward pushdown search is reproduced by block_core_m_dfa.py.

    At an empty right word the invariant permits only A0, B0, and D1.
    A0 reaches B0 directly. All other B0-avoiding steps preserve the
    invariant and decrease the natural rank from BlockCoreMRankTr.
    An internal B0 takes one ordinary step; a boundary B0 resets to a
    D configuration with right word 110 in three steps, using one blank
    padding cell. Thus every marked B0 has a positive marked return.

    The final lemmas provide D0/D1 witnesses from A1, and C1 from B1
    within the invariant. The only axiom is functional_extensionality_dep.
*)
From Coq Require Import Arith Lia List Bool ZArith.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Counters Require Import WTape NestCountTr LoopRunTr BlockCoreMRankTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
Import ListNotations.
Definition bm_tm:TM:=fun q h=>Some(match q,h with
|StA,S0=>mkTrans S0 DR StB|StA,S1=>mkTrans S1 DL StD
|StB,S0=>mkTrans S1 DR StC|StB,S1=>mkTrans S0 DR StC
|StC,S0=>mkTrans S1 DL StA|StC,S1=>mkTrans S1 DR StA
|StD,S0=>mkTrans S1 DR StA|StD,S1=>mkTrans S0 DL StD end).
(* BEGIN GENERATED RIGHT-STACK CERTIFICATE *)
Inductive bm_dfa := M0 | M1 | M2 | M3 | M4 | M5 | M6 | M7 | M8 | M9 | M10 | M11 | M12 | M13 | M14 | M15 | M16 | M17 | M18.
Definition bm_cons(a:Sym)(s:bm_dfa):bm_dfa:=match a,s with
|S0,M0=>M1
|S1,M0=>M2
|S0,M1=>M3
|S1,M1=>M4
|S0,M2=>M2
|S1,M2=>M2
|S0,M3=>M5
|S1,M3=>M4
|S0,M4=>M6
|S1,M4=>M7
|S0,M5=>M1
|S1,M5=>M2
|S0,M6=>M8
|S1,M6=>M9
|S0,M7=>M10
|S1,M7=>M4
|S0,M8=>M11
|S1,M8=>M12
|S0,M9=>M13
|S1,M9=>M14
|S0,M10=>M10
|S1,M10=>M4
|S0,M11=>M6
|S1,M11=>M9
|S0,M12=>M12
|S1,M12=>M12
|S0,M13=>M15
|S1,M13=>M4
|S0,M14=>M14
|S1,M14=>M9
|S0,M15=>M16
|S1,M15=>M2
|S0,M16=>M17
|S1,M16=>M2
|S0,M17=>M18
|S1,M17=>M4
|S0,M18=>M16
|S1,M18=>M2
end.
Fixpoint bm_fold(R:list Sym):bm_dfa:=match R with []=>M0|a::R=>bm_cons a(bm_fold R)end.
Definition bm_ok(q:St)(h a b c:Sym)(s:bm_dfa):bool:=match q,h,s with
|StA,S0,M0=>true
|StA,S1,M0=>false
|StB,S0,M0=>true
|StB,S1,M0=>false
|StC,S0,M0=>false
|StC,S1,M0=>false
|StD,S0,M0=>false
|StD,S1,M0=>match a,b,c with |S0,S0,S0=>true |S0,S0,S1=>true |S0,S1,S0=>true |S0,S1,S1=>true |S1,S0,S0=>true |S1,S0,S1=>true |_,_,_=>false end
|StA,S0,M1=>true
|StA,S1,M1=>match a,b,c with |S0,S1,S0=>true |S1,S1,S0=>true |_,_,_=>false end
|StB,S0,M1=>false
|StB,S1,M1=>false
|StC,S0,M1=>match a,b,c with |S1,S0,S0=>true |S1,S0,S1=>true |S1,S1,S0=>true |S1,S1,S1=>true |_,_,_=>false end
|StC,S1,M1=>true
|StD,S0,M1=>true
|StD,S1,M1=>match a,b,c with |S0,S0,S0=>true |S0,S0,S1=>true |S0,S1,S0=>true |S0,S1,S1=>true |S1,S1,S0=>true |_,_,_=>false end
|StA,S0,M2=>false
|StA,S1,M2=>false
|StB,S0,M2=>false
|StB,S1,M2=>false
|StC,S0,M2=>false
|StC,S1,M2=>false
|StD,S0,M2=>false
|StD,S1,M2=>false
|StA,S0,M3=>false
|StA,S1,M3=>match a,b,c with |S0,S1,S0=>true |S1,S1,S0=>true |_,_,_=>false end
|StB,S0,M3=>true
|StB,S1,M3=>false
|StC,S0,M3=>match a,b,c with |S1,S0,S0=>true |S1,S0,S1=>true |S1,S1,S0=>true |S1,S1,S1=>true |_,_,_=>false end
|StC,S1,M3=>true
|StD,S0,M3=>true
|StD,S1,M3=>match a,b,c with |S1,S0,S0=>true |S1,S0,S1=>true |S1,S1,S0=>true |_,_,_=>false end
|StA,S0,M4=>false
|StA,S1,M4=>true
|StB,S0,M4=>true
|StB,S1,M4=>true
|StC,S0,M4=>match a,b,c with |S0,S0,S0=>true |S0,S0,S1=>true |S0,S1,S0=>true |S0,S1,S1=>true |_,_,_=>false end
|StC,S1,M4=>match a,b,c with |S1,S0,S0=>true |S1,S0,S1=>true |_,_,_=>false end
|StD,S0,M4=>match a,b,c with |S1,S0,S0=>true |S1,S0,S1=>true |_,_,_=>false end
|StD,S1,M4=>match a,b,c with |S1,S0,S0=>true |S1,S0,S1=>true |_,_,_=>false end
|StA,S0,M5=>true
|StA,S1,M5=>false
|StB,S0,M5=>true
|StB,S1,M5=>false
|StC,S0,M5=>false
|StC,S1,M5=>false
|StD,S0,M5=>false
|StD,S1,M5=>match a,b,c with |S0,S0,S0=>true |S0,S0,S1=>true |S0,S1,S0=>true |S0,S1,S1=>true |S1,S0,S0=>true |S1,S0,S1=>true |_,_,_=>false end
|StA,S0,M6=>true
|StA,S1,M6=>match a,b,c with |S0,S0,S0=>true |S0,S0,S1=>true |S1,S0,S0=>true |S1,S0,S1=>true |_,_,_=>false end
|StB,S0,M6=>false
|StB,S1,M6=>true
|StC,S0,M6=>match a,b,c with |S0,S0,S0=>true |S0,S0,S1=>true |S0,S1,S0=>true |S0,S1,S1=>true |_,_,_=>false end
|StC,S1,M6=>false
|StD,S0,M6=>false
|StD,S1,M6=>match a,b,c with |S0,S0,S0=>true |S0,S0,S1=>true |S0,S1,S0=>true |S0,S1,S1=>true |_,_,_=>false end
|StA,S0,M7=>true
|StA,S1,M7=>match a,b,c with |S0,S1,S0=>true |S1,S1,S0=>true |_,_,_=>false end
|StB,S0,M7=>match a,b,c with |S0,S0,S0=>true |S0,S0,S1=>true |S0,S1,S0=>true |S0,S1,S1=>true |_,_,_=>false end
|StB,S1,M7=>false
|StC,S0,M7=>match a,b,c with |S1,S0,S0=>true |S1,S0,S1=>true |S1,S1,S0=>true |S1,S1,S1=>true |_,_,_=>false end
|StC,S1,M7=>true
|StD,S0,M7=>true
|StD,S1,M7=>true
|StA,S0,M8=>false
|StA,S1,M8=>true
|StB,S0,M8=>false
|StB,S1,M8=>true
|StC,S0,M8=>true
|StC,S1,M8=>true
|StD,S0,M8=>true
|StD,S1,M8=>match a,b,c with |S1,S1,S0=>true |_,_,_=>false end
|StA,S0,M9=>true
|StA,S1,M9=>false
|StB,S0,M9=>false
|StB,S1,M9=>false
|StC,S0,M9=>match a,b,c with |S1,S0,S0=>true |S1,S1,S0=>true |_,_,_=>false end
|StC,S1,M9=>match a,b,c with |S0,S0,S0=>true |S0,S0,S1=>true |S0,S1,S0=>true |S0,S1,S1=>true |_,_,_=>false end
|StD,S0,M9=>match a,b,c with |S0,S0,S0=>true |S0,S0,S1=>true |S0,S1,S0=>true |S0,S1,S1=>true |_,_,_=>false end
|StD,S1,M9=>match a,b,c with |S0,S0,S0=>true |S0,S0,S1=>true |S0,S1,S0=>true |S0,S1,S1=>true |_,_,_=>false end
|StA,S0,M10=>true
|StA,S1,M10=>match a,b,c with |S0,S1,S0=>true |S1,S1,S0=>true |_,_,_=>false end
|StB,S0,M10=>true
|StB,S1,M10=>false
|StC,S0,M10=>match a,b,c with |S1,S0,S0=>true |S1,S0,S1=>true |S1,S1,S0=>true |S1,S1,S1=>true |_,_,_=>false end
|StC,S1,M10=>true
|StD,S0,M10=>true
|StD,S1,M10=>true
|StA,S0,M11=>false
|StA,S1,M11=>match a,b,c with |S0,S0,S0=>true |S0,S0,S1=>true |S1,S0,S0=>true |S1,S0,S1=>true |_,_,_=>false end
|StB,S0,M11=>true
|StB,S1,M11=>true
|StC,S0,M11=>match a,b,c with |S0,S0,S0=>true |S0,S0,S1=>true |S0,S1,S0=>true |S0,S1,S1=>true |_,_,_=>false end
|StC,S1,M11=>false
|StD,S0,M11=>false
|StD,S1,M11=>match a,b,c with |S1,S0,S0=>true |S1,S0,S1=>true |_,_,_=>false end
|StA,S0,M12=>true
|StA,S1,M12=>true
|StB,S0,M12=>true
|StB,S1,M12=>true
|StC,S0,M12=>true
|StC,S1,M12=>true
|StD,S0,M12=>true
|StD,S1,M12=>true
|StA,S0,M13=>false
|StA,S1,M13=>match a,b,c with |S0,S1,S0=>true |S1,S1,S0=>true |_,_,_=>false end
|StB,S0,M13=>match a,b,c with |S0,S0,S0=>true |S0,S0,S1=>true |S1,S0,S0=>true |S1,S0,S1=>true |_,_,_=>false end
|StB,S1,M13=>false
|StC,S0,M13=>match a,b,c with |S1,S0,S0=>true |S1,S0,S1=>true |S1,S1,S0=>true |S1,S1,S1=>true |_,_,_=>false end
|StC,S1,M13=>true
|StD,S0,M13=>true
|StD,S1,M13=>match a,b,c with |S1,S1,S0=>true |_,_,_=>false end
|StA,S0,M14=>false
|StA,S1,M14=>match a,b,c with |S0,S0,S0=>true |S0,S0,S1=>true |S1,S0,S0=>true |S1,S0,S1=>true |_,_,_=>false end
|StB,S0,M14=>false
|StB,S1,M14=>true
|StC,S0,M14=>match a,b,c with |S0,S0,S0=>true |S0,S0,S1=>true |S0,S1,S0=>true |S0,S1,S1=>true |_,_,_=>false end
|StC,S1,M14=>false
|StD,S0,M14=>false
|StD,S1,M14=>false
|StA,S0,M15=>match a,b,c with |S0,S0,S0=>true |S0,S0,S1=>true |S0,S1,S0=>true |S0,S1,S1=>true |_,_,_=>false end
|StA,S1,M15=>false
|StB,S0,M15=>true
|StB,S1,M15=>false
|StC,S0,M15=>false
|StC,S1,M15=>false
|StD,S0,M15=>false
|StD,S1,M15=>match a,b,c with |S1,S0,S0=>true |S1,S0,S1=>true |_,_,_=>false end
|StA,S0,M16=>true
|StA,S1,M16=>false
|StB,S0,M16=>false
|StB,S1,M16=>false
|StC,S0,M16=>false
|StC,S1,M16=>false
|StD,S0,M16=>false
|StD,S1,M16=>match a,b,c with |S0,S0,S0=>true |S0,S0,S1=>true |S0,S1,S0=>true |S0,S1,S1=>true |_,_,_=>false end
|StA,S0,M17=>false
|StA,S1,M17=>match a,b,c with |S0,S1,S0=>true |S1,S1,S0=>true |_,_,_=>false end
|StB,S0,M17=>false
|StB,S1,M17=>false
|StC,S0,M17=>match a,b,c with |S1,S0,S0=>true |S1,S0,S1=>true |S1,S1,S0=>true |S1,S1,S1=>true |_,_,_=>false end
|StC,S1,M17=>true
|StD,S0,M17=>true
|StD,S1,M17=>match a,b,c with |S1,S1,S0=>true |_,_,_=>false end
|StA,S0,M18=>false
|StA,S1,M18=>false
|StB,S0,M18=>true
|StB,S1,M18=>false
|StC,S0,M18=>false
|StC,S1,M18=>false
|StD,S0,M18=>false
|StD,S1,M18=>match a,b,c with |S1,S0,S0=>true |S1,S0,S1=>true |_,_,_=>false end
end.
(* END GENERATED RIGHT-STACK CERTIFICATE *)
Definition bm_inv(c:cconf):Prop:=let '(q,(L,h,R)):=c in
 bm_ok q h(chd L)(chd(ctl L))(chd(ctl(ctl L)))(bm_fold R)=true.
Definition bm_goodedge(q:St)(h a b c d r:Sym)(s:bm_dfa):bool:=
 let tr:=match bm_tm q h with Some tr=>tr|None=>mkTrans S0 DR StA end in
 match t_dir tr with
 |DL=>implb(bm_ok q h a b c s)(bm_ok(t_next tr)a b c d(bm_cons(t_write tr)s))
 |DR=>implb(bm_ok q h a b c(bm_cons r s))(bm_ok(t_next tr)r(t_write tr)a b s)
 end.
Lemma bm_edges:forall q h a b c d r s,bm_goodedge q h a b c d r s=true.
Proof. intros q h a b c d r s;destruct q,h,a,b,c,d,r,s;reflexivity. Qed.
Lemma bm_empty:forall q h a b c,bm_ok q h a b c M0=true->
 (q=StA /\ h=S0)\/(q=StB /\h=S0)\/(q=StD /\h=S1).
Proof. intros q h a b c;destruct q,h,a,b,c;cbn;intuition discriminate. Qed.
Lemma bm_Bempty:forall a b c,bm_ok StB S0 a b c M0=true.
Proof. intros;reflexivity. Qed.
Lemma bm_reset_inv:forall L,bm_inv(cL StD L [S1;S1;S0]).
Proof. intros L;unfold bm_inv,cL;cbn[bm_fold bm_cons];destruct(chd L),(chd(ctl L)),(chd(ctl(ctl L))),(chd(ctl(ctl(ctl L))));reflexivity. Qed.

Section Machine.
Variable tm:TM.
Hypothesis Htm:forall q h,tm q h=bm_tm q h.
Lemma bm_step:forall c d,cstep tm c=Some d->bm_inv c->
 cinstr c<>(StB,S0) \/ snd(snd c)<>[]->bm_inv d.
Proof.
 intros[q[[L h]R]] e HE HI HN.
 assert(HP:=bm_edges q h(chd L)(chd(ctl L))(chd(ctl(ctl L)))
   (chd(ctl(ctl(ctl L))))(chd R)(bm_fold R)).
 assert(HO:=bm_edges q h(chd L)(chd(ctl L))(chd(ctl(ctl L)))
   (chd(ctl(ctl(ctl L))))(chd R)(bm_fold(ctl R))).
 unfold bm_inv in HI;cbn in HN.
 unfold cstep in HE;rewrite Htm in HE.
 destruct q,h;cbn[bm_tm ctape_move t_dir t_write t_next]in HE;
 cbn[bm_goodedge bm_tm t_dir t_write t_next]in HP,HO.
 - destruct R as[|r R].
   + cbn[chd ctl]in HE;injection HE as <-. apply bm_Bempty.
   + injection HE as <-. unfold bm_inv;cbn[chd ctl].
     cbn[bm_fold]in HI. cbn[chd ctl]in HO. rewrite HI in HO;exact HO.
 - injection HE as <-. unfold bm_inv;cbn[chd ctl bm_fold].
   rewrite HI in HP;exact HP.
 - destruct R as[|r R].
   + destruct HN as[HN|HN];exfalso;apply HN;reflexivity.
   + injection HE as <-. unfold bm_inv;cbn[chd ctl].
     cbn[bm_fold]in HI. cbn[chd ctl]in HO. rewrite HI in HO;exact HO.
 - destruct R as[|r R].
   + apply bm_empty in HI;intuition discriminate.
   + injection HE as <-. unfold bm_inv;cbn[chd ctl].
     cbn[bm_fold]in HI. cbn[chd ctl]in HO. rewrite HI in HO;exact HO.
 - injection HE as <-. unfold bm_inv;cbn[chd ctl bm_fold].
   rewrite HI in HP;exact HP.
 - destruct R as[|r R].
   + apply bm_empty in HI;intuition discriminate.
   + injection HE as <-. unfold bm_inv;cbn[chd ctl].
     cbn[bm_fold]in HI. cbn[chd ctl]in HO. rewrite HI in HO;exact HO.
 - destruct R as[|r R].
   + apply bm_empty in HI;intuition discriminate.
   + injection HE as <-. unfold bm_inv;cbn[chd ctl].
     cbn[bm_fold]in HI. cbn[chd ctl]in HO. rewrite HI in HO;exact HO.
 - injection HE as <-. unfold bm_inv;cbn[chd ctl bm_fold].
   rewrite HI in HP;exact HP.
Qed.
Lemma bm_no_escape:forall c d,cstep tm c=Some d->bm_inv c->
 cinstr c<>(StB,S0)->cinstr d<>(StB,S0)->
 snd(snd c)=[]->bmr_delta(fst c)(snd(fst(snd c)))=(-1)%Z.
Proof.
 intros[q[[L h]R]] d HE HI HC HD HR;cbn in HR;subst R.
 apply bm_empty in HI. destruct HI as[[-> ->]|[[-> ->]|[-> ->]]].
 - cbn[cstep]in HE;rewrite Htm in HE;cbn[bm_tm ctape_move chd ctl t_dir t_next t_write]in HE.
   injection HE as <-. exfalso;apply HD;reflexivity.
 - exfalso;apply HC;reflexivity.
 - reflexivity.
Qed.
End Machine.
Definition bm_mark(c:cconf):Prop:=bm_inv c /\ cinstr c=(StB,S0).
Section Returns.
Variable tm:TM.
Hypothesis Htm:forall q h,tm q h=bm_tm q h.
Lemma bm_reaches:forall c,bm_inv c->exists d,bm_mark d /\ Reach0 tm c d.
Proof.
 intros c HI.
 assert(H:exists d,bm_inv d /\ cinstr d=(StB,S0) /\ Reach0 tm c d).
 { eapply(bmr_finite_hit tm
   (Htm StA S0)(Htm StA S1)(Htm StB S1)(Htm StC S0)(Htm StC S1)(Htm StD S0)(Htm StD S1)
   bm_inv).
   - intros x y HX HN HS;apply(bm_step tm Htm x y HS HX);left;exact HN.
   - intros q L h y HX HN HS HD;exact(bm_no_escape tm Htm _ _ HS HX HN HD eq_refl).
   - exact HI. }
 destruct H as(d&HD&HT&HR). exists d;split;[split;assumption|exact HR].
Qed.
Lemma bm_reset:forall L,Reach1 tm(StB,(L,S0,[]))(cL StD L [S1;S1;S0]).
Proof.
 intro L. eapply(r1_run tm 3 _ (cL StD L [S1;S1]));[lia| |].
 - repeat(cbn[csteps cstep];rewrite ?Htm;cbn[bm_tm ctape_move t_dir t_next t_write chd ctl cL]). reflexivity.
 - eapply reach0_lift_r;[|apply reach0_refl]. unfold cL.
   change(lift(StD,(ctl L,chd L,[S1;S1]++rep[S0]1))=lift(StD,(ctl L,chd L,[S1;S1]))).
   apply lift_padR.
Qed.
Lemma bm_return:forall c,bm_mark c->exists d,bm_mark d /\ Reach1 tm c d.
Proof.
 intros[q[[L h]R]][HI HT]. cbn[cinstr]in HT;injection HT as -> ->.
 destruct R as[|r R].
 - destruct(bm_reaches _ (bm_reset_inv L))as(d&HD&HR).
   exists d;split;[exact HD|eapply reach10;[apply bm_reset|exact HR]].
 - set(e:=(StC,(S1::L,r,R))).
   assert(HS:cstep tm(StB,(L,S0,r::R))=Some e).
   { cbn[cstep];rewrite Htm;reflexivity. }
   assert(HE:bm_inv e)by(apply(bm_step tm Htm _ _ HS HI);right;discriminate).
   destruct(bm_reaches _ HE)as(d&HD&HR). exists d;split;[exact HD|].
   eapply(r1_run _ 1 _ e);[lia|cbn[csteps cstep];rewrite Htm;reflexivity|exact HR].
Qed.
Lemma bm_mark_instr:forall c,bm_mark c->cinstr c=(StB,S0).
Proof. intros c[_ H];exact H. Qed.
Lemma bm_boot:stepn tm 1 InitES=Some(lift(StB,([S0],S0,[]))).
Proof. apply boot_ok;cbn[csteps cstep CTape.c0];rewrite Htm;reflexivity. Qed.
Lemma bm_boot_mark:bm_mark(StB,([S0],S0,[])).
Proof. split;reflexivity. Qed.
End Returns.
Section Witnesses.
Variable tm:TM.
Hypothesis Htm:forall q h,tm q h=bm_tm q h.
Lemma bm_D0:forall L R,Fires tm(cL StD L R)(StD,S0).
Proof.
 induction L as[|s L IH];intro R.
 - apply fires_here;reflexivity.
 - destruct s.
   + apply fires_here;reflexivity.
   + eapply fire_back;[|apply IH].
     eapply(r0_run _ 1);[cbn[csteps cstep cL];rewrite Htm;reflexivity|apply reach0_refl].
Qed.
Lemma bm_A1_D0:forall L R,Fires tm(StA,(L,S1,R))(StD,S0).
Proof.
 intros L R;eapply fire_back;[|apply bm_D0].
 eapply(r0_run _ 1);[cbn[csteps cstep];rewrite Htm;reflexivity|apply reach0_refl].
Qed.
Lemma bm_A1_D1:forall L R,Fires tm(StA,(L,S1,R))(StD,S1).
Proof.
 intros L R;destruct L as[|s L];[|destruct s].
 - eapply (fire_back tm _ (StD,([],S1,S1::R)));[|apply fires_here;reflexivity].
   eapply(r0_run _ 3);[repeat(cbn[csteps cstep];rewrite ?Htm;cbn[bm_tm ctape_move t_dir t_next t_write chd ctl]);reflexivity|apply reach0_refl].
 - eapply (fire_back tm _ (StD,(L,S1,S1::R)));[|apply fires_here;reflexivity].
   eapply(r0_run _ 3);[repeat(cbn[csteps cstep];rewrite ?Htm;cbn[bm_tm ctape_move t_dir t_next t_write chd ctl]);reflexivity|apply reach0_refl].
 - eapply (fire_back tm _ (StD,(L,S1,S1::R)));[|apply fires_here;reflexivity].
   eapply(r0_run _ 1);[cbn[csteps cstep];rewrite Htm;reflexivity|apply reach0_refl].
Qed.
Lemma bm_B1_C1:forall R L,bm_inv(StB,(L,S1,R))->Fires tm(StB,(L,S1,R))(StC,S1).
Proof.
 induction R as[|s R IH];intros L HI.
 - apply bm_empty in HI;intuition discriminate.
 - destruct s.
   + assert(HR:Reach0 tm(StB,(L,S1,S0::R))(StB,(S0::L,S1,R))).
     { eapply(r0_run _ 3);[repeat(cbn[csteps cstep];rewrite ?Htm;cbn[bm_tm ctape_move t_dir t_next t_write chd ctl]);reflexivity|apply reach0_refl]. }
     assert(HJ:bm_inv(StB,(S0::L,S1,R))).
     { assert(H1:bm_inv(StC,(S0::L,S0,R))).
       { eapply(bm_step tm Htm (StB,(L,S1,S0::R)));[cbn[cstep];rewrite Htm;reflexivity|exact HI|left;discriminate]. }
       assert(H2:bm_inv(StA,(L,S0,S1::R))).
       { eapply(bm_step tm Htm (StC,(S0::L,S0,R)));[cbn[cstep];rewrite Htm;reflexivity|exact H1|left;discriminate]. }
       eapply(bm_step tm Htm (StA,(L,S0,S1::R)));[cbn[cstep];rewrite Htm;reflexivity|exact H2|left;discriminate]. }
     eapply fire_back;[exact HR|apply IH;exact HJ].
   + eapply (fire_back tm _ (StC,(S0::L,S1,R)));[|apply fires_here;reflexivity].
     eapply(r0_run _ 1);[cbn[csteps cstep];rewrite Htm;reflexivity|apply reach0_refl].
Qed.
End Witnesses.
