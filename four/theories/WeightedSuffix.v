(** A checked target boot may enter a weighted closure proved with a different
    transition table. Agreement is required on every instruction represented
    in that closure; transient target entries may differ freely. All closure,
    ranking, prefix and agreement conditions are replayed, not assumed. *)
From Coq Require Import Arith Lia Bool List NArith.
From BBB24 Require Import Statement StatementTr Spec Bounds Census CTape PosEnc
  Closure ClosureTr Closeout NGramCensus WeightedNGram WeightedCensus WeightedReuse
  Mirror CycleCensus FamilyTransport.
From BBB24.Checkers Require Import NGram.
Import ListNotations.

Definition suffix_agrees (source target:TM) (Sl:list cconf) :=
  forallb (fun a => let '(q,s):=cinstr a in cell_leb (source q s) (target q s)) Sl.

Lemma suffix_step : forall source target Sl n ls rs a c d,
  suffix_agrees source target Sl=true -> In a Sl ->
  ng_covers n ls rs a (lift c) -> cstep source c=Some d ->
  cstep target c=Some d.
Proof.
  intros source target Sl n ls rs a c d Hag Ha Hcov Hstep.
  unfold suffix_agrees in Hag. apply forallb_forall with (x:=a) in Hag; [|exact Ha].
  pose proof (ng_covers_instr n ls rs a (lift c) Hcov) as E.
  rewrite cinstr_lift in E. rewrite E in Hag.
  destruct c as [q[[l h]r]]. cbn [cinstr] in Hag.
  change (cell_leb (source q h) (target q h)=true) in Hag.
  cbn [cstep] in Hstep |- *. destruct (source q h) as [tr|] eqn:Es; [|discriminate].
  apply cell_leb_spec in Hag. destruct Hag as [H|H]; [discriminate|].
  rewrite H. exact Hstep.
Qed.

Lemma suffix_runs : forall source target Sl n ls rs cc,
  suffix_agrees source target Sl=true ->
  (forall k,exists d a,csteps source k cc=Some d /\ In a Sl /\ ng_covers n ls rs a(lift d)) ->
  forall k, csteps target k cc=csteps source k cc.
Proof.
  intros source target Sl n ls rs cc Hag Hinv k. induction k; [reflexivity|].
  replace (S k) with (k+1) by lia. rewrite !csteps_add, IHk.
  destruct (Hinv k) as (d&a&Hd&Ha&Hcov). rewrite Hd. cbn [csteps].
  destruct (cstep source d) as [e|] eqn:E.
  - rewrite (suffix_step source target Sl n ls rs a d e Hag Ha Hcov E). reflexivity.
  - destruct (Hinv (k+1)) as (e&b&Hnext&_).
    rewrite csteps_add,Hd in Hnext. cbn [csteps] in Hnext. rewrite E in Hnext. discriminate.
Qed.

Definition weighted_suffix_check bs bi (target source:TM) n t (Sl:list cconf) cert :=
  if suffix_agrees source target Sl then
  if 1<=?n then match csteps target t c0 with None=>false|Some cc=>
  let '(q,(l,h,r)):=cc in let a0:=ng_start n cc in
  let ls:=gadds(ng_seed_side n l ++ flat_map(fun c=>fst(ng_harvest source c))Sl)gempty in
  let rs:=gadds(ng_seed_side n r ++ flat_map(fun c=>snd(ng_harvest source c))Sl)gempty in
  if ng_seed_ok n ls rs cc then
  if closed_tr_b cconf cconf_enc(ng_succs source ls rs)Sl then
  if mem_tr cconf cconf_enc a0 Sl then
  if prefix_gate bs bi target t(tail_states Sl)(tail_instrs Sl)then
  forallb(fun tg=>if tail_instrs Sl tg then wc_target source n ls rs Sl tg(cert tg)else true)all_Instr
  else false else false else false else false end else false else false.

Theorem weighted_suffix_sound : forall bs bi target source n t Sl cert,
  weighted_suffix_check bs bi target source n t Sl cert=true ->
  NonHalt target /\ Bounds bs bi target.
Proof.
  intros bs bi target source n t Sl cert H. unfold weighted_suffix_check in H.
  destruct (suffix_agrees source target Sl) eqn:Hag; [|discriminate].
  destruct (1<=?n) eqn:Hn; [apply Nat.leb_le in Hn|discriminate].
  destruct (csteps target t c0) as [[q[[l h]r]]|] eqn:Et; [|discriminate].
  set(ls:=gadds(ng_seed_side n l ++ flat_map(fun c=>fst(ng_harvest source c))Sl)gempty)in *.
  set(rs:=gadds(ng_seed_side n r ++ flat_map(fun c=>snd(ng_harvest source c))Sl)gempty)in *.
  set(cc:=(q,(l,h,r)):cconf)in *;set(a0:=ng_start n cc)in *.
  match type of H with(if ?b then _ else _)=true=>destruct b eqn:Hseed end;[|discriminate].
  match type of H with(if ?b then _ else _)=true=>destruct b eqn:Hcl end;[|discriminate].
  match type of H with(if ?b then _ else _)=true=>destruct b eqn:Hmem end;[|discriminate].
  match type of H with(if ?b then _ else _)=true=>destruct b eqn:Hpre end;[|discriminate].
  assert(HIn:In a0 Sl)by(eapply mem_In_tr;[exact cconf_enc_inj|exact Hmem]).
  assert(Hcov:ng_covers n ls rs a0(lift cc))by(apply ng_start_covers;exact Hseed).
  assert(Hstart:stepn target t InitES=Some(lift cc))by(rewrite <-lift_c0;apply csteps_lift;exact Et).
  assert(Hinv:forall k,exists d a,csteps source k cc=Some d /\ In a Sl /\ ng_covers n ls rs a(lift d)).
  { eapply closure_invariant_c_tr;[exact cconf_enc_inj| |exact Hcl|exact HIn|exact Hcov].
    intros a c Hc;apply ng_succs_sound;assumption. }
  assert(Htail:forall k,stepn target(t+k)InitES=stepn source k(lift cc)).
  { intro k. rewrite stepn_add,Hstart. destruct(Hinv k)as(d&a&HD&_).
    rewrite(csteps_lift _ _ _ _ HD).
    apply csteps_lift. rewrite(suffix_runs source target Sl n ls rs cc Hag Hinv k). exact HD. }
  assert(Hrec:forall tg,tail_instrs Sl tg=true->forall N,exists k,N<=k /\ FiresAt target tg k).
  { intros tg Happ N. destruct(Hinv N)as(d&a&HD&HA&HC).
    rewrite forallb_forall in H;specialize(H tg(all_Instr_complete tg)).
    change ((if tail_instrs Sl tg then wc_target source n ls rs Sl tg(cert tg)else true)=true)in H;rewrite Happ in H.
    destruct(wc_reach source n ls rs Sl tg(cert tg)Hn Hcl H a d HA HC)as(j&e&HE&HT).
    exists(t+N+j);split;[lia|]. exists e;split;[|exact HT].
    replace(t+N+j)with(t+(N+j))by lia. rewrite Htail,stepn_add,(csteps_lift _ _ _ _ HD). exact HE. }
  split.
  - intros k Hnone. destruct(le_lt_dec t k).
    + destruct(Hinv(k-t))as(d&a&HD&_). replace k with(t+(k-t))in Hnone by lia.
      rewrite Htail,(csteps_lift _ _ _ _ HD)in Hnone;discriminate.
    + destruct(stepn_prefix target k t InitES(lift cc)ltac:(lia)Hstart)as(d&HD&_);congruence.
  - eapply(tail_bounds bs bi);[exact Hpre| |exact Hrec].
    intros s tg Hts(e&HE&HT);destruct(Hinv(s-t))as(d&a&HD&HA&HC).
    replace s with(t+(s-t))in HE by lia. rewrite Htail,(csteps_lift _ _ _ _ HD)in HE.
    injection HE as <-. apply existsb_exists;exists a;split;[exact HA|].
    apply instr_eqb_spec;rewrite <-(ng_covers_instr n ls rs a(lift d)HC)in HT;exact HT.
Qed.

Definition weighted_suffix_row_check bs bi source n Sl cert row :=
  weighted_suffix_check bs bi (reuse_actual row) source n (reuse_boot row) Sl cert.
Theorem weighted_suffix_row_sound : forall bs bi source n Sl cert row,
  weighted_suffix_row_check bs bi source n Sl cert row=true ->
  NonHalt (reuse_tm row) /\ Bounds bs bi (reuse_tm row).
Proof.
  intros bs bi source n Sl cert row H.
  destruct(weighted_suffix_sound _ _ _ _ _ _ _ _ H)as[Hnh Hb].
  unfold reuse_actual in Hnh,Hb. destruct(reuse_mirrored row).
  - split;[apply mirror_nonhalt;exact Hnh|apply mirror_bounds;exact Hb].
  - split;assumption.
Qed.
Theorem weighted_suffix_batch_sound : forall bs bi source n Sl cert rows,
  forallb (weighted_suffix_row_check bs bi source n Sl cert) rows=true ->
  StrongBoard bs bi (map reuse_tm rows).
Proof.
  intros bs bi source n Sl cert rows H tm Hin.
  apply in_map_iff in Hin as(row&<-&Hin).
  apply forallb_forall with(x:=row)in H;[|exact Hin].
  eapply weighted_suffix_row_sound;exact H.
Qed.

Print Assumptions weighted_suffix_sound.
Print Assumptions weighted_suffix_batch_sound.
