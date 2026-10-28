(** Reusable weighted tails. A supplied closure and all its rankings are
    checked once independently of target boots. Each target then checks local
    table agreement, its seed, and its prefix. The hybrid batch keeps the
    original separate-table suffix checker as an independently sound fallback. *)
From Coq Require Import Arith Lia Bool List NArith.
From BBB24 Require Import Statement StatementTr Spec Bounds Census CTape PosEnc
  Closure ClosureTr Closeout NGramCensus WeightedNGram WeightedCensus WeightedReuse
  WeightedSuffix Mirror CycleCensus FamilyTransport.
From BBB24.Checkers Require Import NGram.
Import ListNotations.

Record WeightedTail := weighted_tail {
  wt_source : TM;
  wt_width : nat;
  wt_left : gset;
  wt_right : gset;
  wt_nodes : list cconf;
  wt_cert : Instr -> option WCert
}.
Definition wt_ready tail :=
  let source:=wt_source tail in let n:=wt_width tail in
  let ls:=wt_left tail in let rs:=wt_right tail in let Sl:=wt_nodes tail in
  if 1<=?n then
  if closed_tr_b cconf cconf_enc(ng_succs source ls rs)Sl then
  forallb(fun tg=>if tail_instrs Sl tg then wc_target source n ls rs Sl tg(wt_cert tail tg)else true)all_Instr
  else false else false.
Definition wt_use_check bs bi tail target t :=
  let source:=wt_source tail in let n:=wt_width tail in
  let ls:=wt_left tail in let rs:=wt_right tail in let Sl:=wt_nodes tail in
  if suffix_agrees source target Sl then
  match csteps target t c0 with None=>false|Some cc=>
  if ng_seed_ok n ls rs cc then
  if mem_tr cconf cconf_enc(ng_start n cc)Sl then
  prefix_gate bs bi target t(tail_states Sl)(tail_instrs Sl)
  else false else false end else false.

Theorem wt_use_sound : forall bs bi tail target t,
  wt_ready tail=true -> wt_use_check bs bi tail target t=true ->
  NonHalt target /\ Bounds bs bi target.
Proof.
  intros bs bi [source n ls rs Sl cert] target t H Huse.
  unfold wt_ready in H;cbn [wt_source wt_width wt_left wt_right wt_nodes wt_cert] in H.
  destruct (1<=?n) eqn:Hn;[apply Nat.leb_le in Hn|discriminate].
  destruct (closed_tr_b cconf cconf_enc(ng_succs source ls rs)Sl) eqn:Hcl;[|discriminate].
  unfold wt_use_check in Huse;cbn [wt_source wt_width wt_left wt_right wt_nodes] in Huse.
  destruct (suffix_agrees source target Sl) eqn:Hag;[|discriminate].
  destruct (csteps target t c0) as [cc|] eqn:Et;[|discriminate].
  destruct (ng_seed_ok n ls rs cc) eqn:Hseed;[|discriminate].
  set(a0:=ng_start n cc)in *.
  destruct (mem_tr cconf cconf_enc a0 Sl) eqn:Hmem;[|discriminate].
  rename Huse into Hpre.
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

Definition wt_row_check bs bi tail row :=
  wt_use_check bs bi tail (reuse_actual row) (reuse_boot row).
Theorem wt_row_sound : forall bs bi tail row,
  wt_ready tail=true -> wt_row_check bs bi tail row=true ->
  NonHalt(reuse_tm row) /\ Bounds bs bi(reuse_tm row).
Proof.
  intros bs bi tail row Hready H.
  destruct(wt_use_sound _ _ _ _ _ Hready H)as[Hnh Hb].
  unfold reuse_actual in Hnh,Hb. destruct(reuse_mirrored row).
  - split;[apply mirror_nonhalt;exact Hnh|apply mirror_bounds;exact Hb].
  - split;assumption.
Qed.
Definition wt_hybrid_row bs bi tail ready row :=
  if ready && wt_row_check bs bi tail row then true else
  weighted_suffix_row_check bs bi(wt_source tail)(wt_width tail)(wt_nodes tail)(wt_cert tail)row.
Definition wt_hybrid_results bs bi tail rows :=
  let ready:=wt_ready tail in map(wt_hybrid_row bs bi tail ready)rows.
Definition wt_hybrid_check bs bi tail rows :=
  let ready:=wt_ready tail in forallb(wt_hybrid_row bs bi tail ready)rows.
Theorem wt_hybrid_batch_sound : forall bs bi tail rows,
  wt_hybrid_check bs bi tail rows=true ->
  StrongBoard bs bi(map reuse_tm rows).
Proof.
  intros bs bi tail rows H tm Hin. apply in_map_iff in Hin as(row&<-&Hin).
  unfold wt_hybrid_check in H.
  apply forallb_forall with(x:=row)in H;[|exact Hin].
  unfold wt_hybrid_row in H.
  destruct(wt_ready tail && wt_row_check bs bi tail row)eqn:E.
  - apply andb_true_iff in E as[Hr Hu]. eapply wt_row_sound;eassumption.
  - eapply weighted_suffix_row_sound;exact H.
Qed.

Print Assumptions wt_use_sound.
Print Assumptions wt_hybrid_batch_sound.
