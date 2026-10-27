(** A source tail can also be entered with the two control states exchanged.
    The finite prefix is run in the actual target machine before normalizing
    its configuration; no equality of blank A-start and B-start runs is used. *)
From Coq Require Import Arith Lia Bool List NArith.
From BBB24 Require Import Statement StatementTr Spec CTape PosEnc Closure ClosureTr
 Bounds Census NGramCensus WeightedCensus WeightedTail WeightedSuffix ReadyReuse
 Symmetry Shadow Mirror CycleCensus FamilyTransport.
From BBB24.Checkers Require Import NGram.
Import ListNotations.

Definition ready_swap_cconf(c:cconf):cconf := (swap_state(fst c),snd c).
Lemma ready_swap_lift : forall c,
 swap_config(lift(ready_swap_cconf c))=lift c.
Proof. intros[q[[l h]r]];destruct q;reflexivity. Qed.

Definition ready_swap_check bs bi tail target t :=
 let source:=wt_source tail in let n:=wt_width tail in
 let ls:=wt_left tail in let rs:=wt_right tail in let Sl:=wt_nodes tail in
 if suffix_agrees source(swap_tm target)Sl then
 match csteps target t c0 with None=>false|Some cc=>
 let normalized:=ready_swap_cconf cc in
 if ng_seed_ok n ls rs normalized then
 if mem_tr cconf cconf_enc(ng_start n normalized)Sl then
 prefix_gate bs bi target t(tail_states Sl)(tail_instrs Sl)
 else false else false end else false.

Theorem ready_swap_sound : forall bs bi tail target t,
 wt_ready tail=true -> ready_swap_check bs bi tail target t=true ->
 NonHalt target /\ Bounds bs bi target.
Proof.
 intros bs bi [source n ls rs Sl cert] target t Hr Huse.
 unfold wt_ready in Hr;cbn[wt_source wt_width wt_left wt_right wt_nodes wt_cert]in Hr.
 destruct(1<=?n)eqn:Hn;[apply Nat.leb_le in Hn|discriminate].
 destruct(closed_tr_b cconf cconf_enc(ng_succs source ls rs)Sl)eqn:Hcl;[|discriminate].
 unfold ready_swap_check in Huse;cbn[wt_source wt_width wt_left wt_right wt_nodes]in Huse.
 destruct(suffix_agrees source(swap_tm target)Sl)eqn:Hag;[|discriminate].
 destruct(csteps target t c0)as[cc|]eqn:Et;[|discriminate].
 set(start:=ready_swap_cconf cc)in *.
 destruct(ng_seed_ok n ls rs start)eqn:Hseed;[|discriminate].
 set(a0:=ng_start n start)in *.
 destruct(mem_tr cconf cconf_enc a0 Sl)eqn:Hmem;[|discriminate].
 rename Huse into Hpre.
 assert(HIn:In a0 Sl)by(eapply mem_In_tr;[exact cconf_enc_inj|exact Hmem]).
 assert(Hcov:ng_covers n ls rs a0(lift start))by(apply ng_start_covers;exact Hseed).
 assert(Hstart:stepn target t InitES=Some(lift cc))by(rewrite <-lift_c0;apply csteps_lift;exact Et).
 assert(Hinv:forall k,exists d a,csteps source k start=Some d /\ In a Sl /\ ng_covers n ls rs a(lift d)).
 { eapply closure_invariant_c_tr;[exact cconf_enc_inj| |exact Hcl|exact HIn|exact Hcov].
   intros a c Hc;apply ng_succs_sound;assumption. }
 assert(Htail:forall k,stepn target(t+k)InitES=
   option_map swap_config(stepn source k(lift start))).
 { intro k;rewrite stepn_add,Hstart.
   assert(E:stepn(swap_tm target)k(lift start)=stepn source k(lift start)).
   { destruct(Hinv k)as(d&a&HD&_). rewrite(csteps_lift _ _ _ _ HD).
     apply csteps_lift. rewrite(suffix_runs source(swap_tm target)Sl n ls rs start Hag Hinv k). exact HD. }
   rewrite <-E. unfold start. rewrite <-ready_swap_lift at 1. apply swap_stepn. }
 assert(Hrec:forall tg,tail_instrs Sl tg=true->forall N,exists k,N<=k /\ FiresAt target(swap_instr tg)k).
 { intros tg Happ N. destruct(Hinv N)as(d&a&HD&HA&HC).
   rewrite forallb_forall in Hr;specialize(Hr tg(all_Instr_complete tg)).
   change((if tail_instrs Sl tg then wc_target source n ls rs Sl tg(cert tg)else true)=true)in Hr.
   rewrite Happ in Hr.
   destruct(wc_reach source n ls rs Sl tg(cert tg)Hn Hcl Hr a d HA HC)as(j&e&HE&HT).
   exists(t+N+j);split;[lia|]. exists(swap_config e);split.
   - replace(t+N+j)with(t+(N+j))by lia.
     rewrite Htail,stepn_add,(csteps_lift _ _ _ _ HD),HE;reflexivity.
   - now rewrite swap_config_instr,HT. }
 assert(Hcover:forall s tg,t<=s->FiresAt target tg s->tail_instrs Sl(swap_instr tg)=true).
 { intros s tg Hts(e&HE&HT). destruct(Hinv(s-t))as(d&a&HD&HA&HC).
   replace s with(t+(s-t))in HE by lia.
   rewrite Htail,(csteps_lift _ _ _ _ HD)in HE;injection HE as <-.
   apply existsb_exists;exists a;split;[exact HA|].
   apply instr_eqb_spec;rewrite(ng_covers_instr n ls rs a(lift d)HC).
   now rewrite <-HT,swap_config_instr,swap_instr_involutive. }
 split.
 - intros k Hnone. destruct(le_lt_dec t k).
   + destruct(Hinv(k-t))as(d&a&HD&_). replace k with(t+(k-t))in Hnone by lia.
     rewrite Htail,(csteps_lift _ _ _ _ HD)in Hnone;discriminate.
   + destruct(stepn_prefix target k t InitES(lift cc)ltac:(lia)Hstart)as(d&HD&_);congruence.
 - unfold prefix_gate in Hpre;apply andb_prop in Hpre as[Hs Hi].
   apply N.leb_le in Hs,Hi. unfold Bounds;split.
   + intros q s[Hv Hquiet]. destruct(lt_dec s t);[lia|].
     apply visits_fires in Hv as(a&Hf).
     destruct(Hrec _ (Hcover s(q,a)ltac:(lia)Hf)(S s))as(k&Hk&Hfire).
     rewrite swap_instr_involutive in Hfire.
     exfalso;apply(Hquiet k);[lia|eapply fires_visits;exact Hfire].
   + intros tg s[Hf Hquiet]. destruct(lt_dec s t);[lia|].
     destruct(Hrec _ (Hcover s tg ltac:(lia)Hf)(S s))as(k&Hk&Hfire).
     rewrite swap_instr_involutive in Hfire.
     exfalso;apply(Hquiet k);[lia|exact Hfire].
Qed.

Record ReadyMixedRow := ready_mixed_row {
 rm_row : ReadyReuseRow;
 rm_swapped : bool
}.
Definition rm_tm row := rr_tm(rm_row row).
Definition ready_mixed_check bs bi tail row :=
 if rm_swapped row then
 ready_swap_check bs bi tail(rr_actual(rm_row row))(rr_boot(rm_row row))
 else ready_reuse_check bs bi tail(rm_row row).
Theorem ready_mixed_sound : forall bs bi tail row,
 wt_ready tail=true -> ready_mixed_check bs bi tail row=true ->
 NonHalt(rm_tm row) /\ Bounds bs bi(rm_tm row).
Proof.
 intros bs bi tail[row swapped]Hr H;unfold ready_mixed_check,rm_tm in *;cbn[rm_row rm_swapped]in *.
 destruct swapped;[|eapply ready_reuse_sound;eassumption].
 destruct(ready_swap_sound _ _ _ _ _ Hr H)as[Hnh Hb].
 unfold rr_actual in Hnh,Hb;apply perm_nonhalt in Hnh;apply perm_bounds in Hb.
 destruct(rr_mirrored row);[split;[apply mirror_nonhalt;exact Hnh|apply mirror_bounds;exact Hb]|auto].
Qed.
Theorem ready_mixed_batch_sound : forall bs bi tail rows,
 wt_ready tail=true -> forallb(ready_mixed_check bs bi tail)rows=true ->
 StrongBoard bs bi(map rm_tm rows).
Proof.
 intros bs bi tail rows Hr H tm Hin.
 apply in_map_iff in Hin as[row[<- Hin]].
 apply forallb_forall with(x:=row)in H;[|exact Hin].
 eapply ready_mixed_sound;eassumption.
Qed.
Print Assumptions ready_swap_sound.
Print Assumptions ready_mixed_batch_sound.
