(** Exhaustive trees may also reference separately proved machine bounds. *)
From Coq Require Import Arith Lia Bool List FunctionalExtensionality.
From SmallBB Require Import Statement StatementTr CTape Bounds Size Census.
Import ListNotations.
Definition trans_eqb (a b:option Trans) :=
 match a,b with None,None=>true|Some a,Some b=>
 sym_eqb(t_write a)(t_write b) && st_eqb(t_next a)(t_next b) &&
 match t_dir a,t_dir b with DL,DL|DR,DR=>true|_,_=>false end
 |_,_=>false end.
Lemma trans_eqb_spec : forall a b,trans_eqb a b=true<->a=b.
Proof. intros [[s d q]|][[s' d' q']|];try(simpl;split;congruence).
 destruct s,s',d,d',q,q';cbn;split;congruence. Qed.
Definition same_table a b := forallb(fun q=>forallb(fun s=>trans_eqb(a q s)(b q s))[S0;S1;S2])all_St.
Lemma same_table_sound : forall a b,same_table a b=true->a=b.
Proof.
 intros a b H;apply functional_extensionality;intro q;apply functional_extensionality;intro s.
 unfold same_table in H. rewrite forallb_forall in H. specialize(H q(all_St_complete q)).
 rewrite forallb_forall in H. apply trans_eqb_spec,H; destruct s; cbn; auto.
Qed.
Inductive KCert := KKnown(index:nat)|KLeaf(cert:Cert)|KBranch(n:nat)(children:list KCert).
Section Parameters.
Variables ns ms bs bi:nat.
Variable known:list TM.
Hypothesis known_sound : Forall(fun tm=>NonHalt tm /\ Bounds bs bi tm)known.
Fixpoint verify_known depth tm cert :=
 match depth with
 |0=>false
 |S d=>match cert with
  |KKnown i=>match nth_error known i with Some k=>same_table tm k|None=>false end
  |KLeaf c=>verify ns ms bs bi 1 tm c
  |KBranch n cs=>if n<?Nat.min bs bi then
    match csteps tm n c0 with
    |Some(q,(l,h,r))=>match tm q h with
      |None=>forallb(fun v=>verify_known d(update tm q h(nat_trans ns v))(nth v cs(KLeaf Invalid)))(seq 0(2*ns*ms))
      |Some _=>false end
    |None=>false end else false end end.
Hypothesis sizes_ok:supported ns ms.
Theorem verify_known_sound : forall depth tm cert,verify_known depth tm cert=true->
 forall tm',Admissible ns ms tm'->TM_le tm tm'->Bounds bs bi tm'.
Proof.
 induction depth as[|d IH];intros tm cert H tm' Had Hle;[discriminate|].
 destruct cert as[i|cert|n cs];cbn[verify_known]in H.
 - destruct(nth_error known i)as[k|]eqn:E;[|discriminate]. apply same_table_sound in H;subst tm.
   pose proof(nth_error_In known i E)as Hin. rewrite Forall_forall in known_sound.
   destruct(known_sound k Hin)as[Hnh Hb]. eapply extend_bounds;eauto.
 - eapply verify_sound;eauto.
 - destruct(n<?Nat.min bs bi)eqn:Hn;[apply Nat.ltb_lt in Hn|discriminate].
   destruct(csteps tm n c0)as[[q[[l h]r]]|]eqn:Et;[|discriminate].
   destruct(tm q h)as[tr|]eqn:E;[discriminate|].
   destruct(tm' q h)as[tr'|]eqn:E'.
   + destruct(codes_complete ns ms sizes_ok tr'(admissible_output ns ms tm' Had q h tr' E'))as(v&Hv&Htr).
     rewrite forallb_forall in H;specialize(H v Hv).
     eapply IH;[exact H|exact Had|]. eapply update_le;[exact Hle|exact E|]. rewrite Htr;exact E'.
   + assert(Hhalt:stepn tm'(S n)InitES=None).
     { assert(Hr:stepn tm' n InitES=Some(lift(q,(l,h,r)))).
       { eapply extend_steps;[exact Hle|]. rewrite <-lift_c0;apply csteps_lift;exact Et. }
       replace(S n)with(n+1)by lia;rewrite stepn_add,Hr.
       cbn[stepn step lift lift_tape fst snd t_head];rewrite E';reflexivity. }
     pose proof(Nat.le_min_l bs bi);pose proof(Nat.le_min_r bs bi).
     apply (halt_bounds bs bi tm' (S n));[lia|lia|exact Hhalt].
Qed.
Corollary known_census_complete : forall depth cert,verify_known depth empty cert=true->
 forall tm,Admissible ns ms tm->Bounds bs bi tm.
Proof. intros depth cert H tm Had;eapply verify_known_sound;[exact H|exact Had|]. intros q s;left;reflexivity. Qed.
End Parameters.
