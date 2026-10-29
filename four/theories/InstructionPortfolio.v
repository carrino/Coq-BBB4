(** Independently checked recurrence witnesses may use different orientations
    and different closed graphs for different instructions. A complete portfolio
    proves that no instruction, and hence no state, has a last occurrence. *)
From Coq Require Import Arith Lia Bool List NArith.
From BBB24 Require Import Statement StatementTr CTape Spec PosEnc Closure ClosureTr
 Bounds Instructions Mirror CycleCensus NGramCensus WeightedCensus.
From BBB24.Checkers Require Import NGram.
Import ListNotations.

Definition wp_graph_check tm n t (Sl:list cconf)(targets:list Instr)
 (cert:Instr->option WCert):bool :=
 if 1<=?n then match csteps tm t c0 with None=>false|Some cc=>
 let '(q,(l,h,r)):=cc in let a0:=ng_start n cc in
 let ls:=gadds(ng_seed_side n l ++ flat_map(fun c=>fst(ng_harvest tm c))Sl)gempty in
 let rs:=gadds(ng_seed_side n r ++ flat_map(fun c=>snd(ng_harvest tm c))Sl)gempty in
 if ng_seed_ok n ls rs cc then
 if closed_tr_b cconf cconf_enc(ng_succs tm ls rs)Sl then
 if mem_tr cconf cconf_enc a0 Sl then
 forallb(fun tg=>wc_target tm n ls rs Sl tg(cert tg))targets
 else false else false else false end else false.

Theorem wp_graph_check_sound:forall tm n t Sl targets cert,
 wp_graph_check tm n t Sl targets cert=true -> NonHalt tm /\
 forall tg,In tg targets->forall N,exists k,N<=k /\ FiresAt tm tg k.
Proof.
 intros tm n t Sl targets cert H;unfold wp_graph_check in H.
 destruct(1<=?n)eqn:Hn;[apply Nat.leb_le in Hn|discriminate].
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
   intros a c Hc;apply ng_succs_sound;assumption. }
 split.
 - intros k Hnone. destruct(le_lt_dec t k).
   + destruct(Hinv(k-t))as(d&a&HD&_). replace k with(t+(k-t))in Hnone by lia.
     rewrite stepn_add,Hstart,(csteps_lift _ _ _ _ HD)in Hnone;discriminate.
   + destruct(stepn_prefix tm k t InitES(lift cc)ltac:(lia)Hstart)as(d&HD&_);congruence.
 - intros tg Hin N. destruct(Hinv N)as(d&a&HD&HA&HC).
   rewrite forallb_forall in H;specialize(H tg Hin).
   destruct(wc_reach tm n ls rs Sl tg(cert tg)Hn Hcl H a d HA HC)as(j&e&HE&HT).
   exists(t+N+j);split;[lia|]. exists e;split;[|exact HT].
   replace(t+N+j)with(t+(N+j))by lia;rewrite stepn_add,Hstart,stepn_add,(csteps_lift _ _ _ _ HD);exact HE.
Qed.

Record WPart := mkWPart {
 wp_mirror:bool;
 wp_width:nat;
 wp_boot:nat;
 wp_nodes:list cconf;
 wp_targets:list Instr;
 wp_cert:Instr->option WCert
}.
Definition wp_part_check tm p :=
 wp_graph_check(if wp_mirror p then mirror_tm tm else tm)
   (wp_width p)(wp_boot p)(wp_nodes p)(wp_targets p)(wp_cert p).
Lemma wp_part_check_sound:forall tm p,wp_part_check tm p=true -> NonHalt tm /\
 forall tg,In tg(wp_targets p)->forall N,exists k,N<=k /\ FiresAt tm tg k.
Proof.
 intros tm[side n t Sl targets cert]H.
 unfold wp_part_check in H;cbn[wp_mirror wp_width wp_boot wp_nodes wp_targets wp_cert]in *.
 destruct side.
 - destruct(wp_graph_check_sound _ _ _ _ _ _ H)as[Hnh Hr].
   split;[apply mirror_nonhalt;exact Hnh|].
   intros tg Hin N;destruct(Hr tg Hin N)as(k&Hk&Hf).
   exists k;split;[exact Hk|apply mirror_fires;exact Hf].
 - exact(wp_graph_check_sound _ _ _ _ _ _ H).
Qed.

Lemma wp_all_recur_sound:forall tm,
 (forall tg N,exists k,N<=k /\ FiresAt tm tg k)->NonHalt tm /\ Bounds 0%N 0%N tm.
Proof.
 intros tm Hr;split.
 - intros n Hnone. destruct(Hr(StA,S0)n)as(k&Hk&c&Hstep&_).
   destruct(stepn_prefix tm n k InitES c Hk Hstep)as(d&Hd&_);congruence.
 - unfold Bounds;cbn;split.
   + intros q s[Hv Hquiet]. apply visits_fires in Hv as(a&Hf).
     destruct(Hr(q,a)(S s))as(k&Hk&Hf'). exfalso.
     apply(Hquiet k);[lia|eapply fires_visits;exact Hf'].
   + intros tg s[Hf Hquiet]. destruct(Hr tg(S s))as(k&Hk&Hf').
     exfalso;apply(Hquiet k);[lia|exact Hf'].
Qed.

Definition wp_portfolio_check tm (parts:list WPart) :=
 forallb(wp_part_check tm)parts &&
 forallb(fun tg=>existsb(fun p=>existsb(fun u=>instr_eqb u tg)(wp_targets p))parts)all_Instr.
Theorem wp_portfolio_check_sound:forall tm parts,
 wp_portfolio_check tm parts=true->NonHalt tm /\ Bounds 0%N 0%N tm.
Proof.
 intros tm parts H;unfold wp_portfolio_check in H;apply andb_prop in H as[Hp Hcover].
 apply wp_all_recur_sound;intros tg N.
 apply forallb_forall with(x:=tg)in Hcover;[|apply all_Instr_complete].
 apply existsb_exists in Hcover as(p&Hin&Htarget).
 apply existsb_exists in Htarget as(u&Huin&Heq);apply instr_eqb_spec in Heq;subst u.
 apply forallb_forall with(x:=p)in Hp;[|exact Hin].
 exact(proj2(wp_part_check_sound tm p Hp)tg Huin N).
Qed.
Print Assumptions wp_portfolio_check_sound.
