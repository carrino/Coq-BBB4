(** A state needs one recurrent instruction, not recurrence of every instruction
    carrying that state. The supplied choice is checked by the existing weighted
    reachability theorem. This module exports no instruction bound. *)
From Coq Require Import NArith Arith Lia Bool List.
From BBB24 Require Import Statement StatementTr Spec CTape PosEnc Closure ClosureTr
  Bounds StateBounds NGramCensus WeightedNGram WeightedCensus.
From BBB24.Checkers Require Import NGram.
Import ListNotations.

Definition ws_graph_check bs tm n t (Sl:list cconf)
    (choice:St->Sym) (cert:Instr->option WCert) : bool :=
 if 1<=?n then match csteps tm t c0 with None=>false|Some cc=>
 let '(q,(l,h,r)):=cc in let a0:=ng_start n cc in
 let ls:=gadds(ng_seed_side n l ++ flat_map(fun c=>fst(ng_harvest tm c))Sl)gempty in
 let rs:=gadds(ng_seed_side n r ++ flat_map(fun c=>snd(ng_harvest tm c))Sl)gempty in
 if ng_seed_ok n ls rs cc then
 if closed_tr_b cconf cconf_enc(ng_succs tm ls rs)Sl then
 if mem_tr cconf cconf_enc a0 Sl then
 if state_prefix_gate bs tm t(tail_states Sl)then
 forallb(fun q=>if tail_states Sl q then
   wc_target tm n ls rs Sl (q,choice q)(cert(q,choice q)) else true)all_St
 else false else false else false else false end else false.

Theorem ws_graph_check_sound : forall bs tm n t Sl choice cert,
 ws_graph_check bs tm n t Sl choice cert=true ->
 NonHalt tm /\ QHBound (N.to_nat bs) tm.
Proof.
 intros bs tm n t Sl choice cert H; unfold ws_graph_check in H.
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
 assert(Hrec:forall state,tail_states Sl state=true ->
   forall N,exists k,N<=k /\ VisitsAt tm state k).
 { intros state Happ N. destruct(Hinv N)as(d&a&HD&HA&HC).
   rewrite forallb_forall in H;specialize(H state(all_St_complete state)).
   change ((if tail_states Sl state then
     wc_target tm n ls rs Sl (state,choice state)(cert(state,choice state))else true)=true)in H.
   rewrite Happ in H.
   destruct(wc_reach tm n ls rs Sl (state,choice state)
     (cert(state,choice state))Hn Hcl H a d HA HC)as(j&e&HE&HT).
   exists(t+N+j);split;[lia|].
   apply (fires_visits tm state (choice state) (t+N+j)).
   exists e;split;[|exact HT].
   replace(t+N+j)with(t+(N+j))by lia.
   rewrite stepn_add,Hstart,stepn_add,(csteps_lift _ _ _ _ HD);exact HE. }
 split.
 - intros k Hnone. destruct(le_lt_dec t k).
   + destruct(Hinv(k-t))as(d&a&HD&_). replace k with(t+(k-t))in Hnone by lia.
     rewrite stepn_add,Hstart,(csteps_lift _ _ _ _ HD)in Hnone;discriminate.
   + destruct(stepn_prefix tm k t InitES(lift cc)ltac:(lia)Hstart)as(d&HD&_);congruence.
 - eapply(state_tail_bound bs tm t Sl);[exact Hpre| |exact Hrec].
   intros s state Hts(e&HE&Hstate);destruct(Hinv(s-t))as(d&a&HD&HA&HC).
   replace s with(t+(s-t))in HE by lia.
   rewrite stepn_add,Hstart,(csteps_lift _ _ _ _ HD)in HE;injection HE as <-.
   apply existsb_exists;exists a;split;[exact HA|].
   apply st_eqb_spec.
   pose proof (f_equal (@fst St Sym) (ng_covers_instr n ls rs a(lift d)HC)) as E.
   change (fst a = fst (lift d)) in E. now rewrite E.
Qed.

Print Assumptions ws_graph_check_sound.
