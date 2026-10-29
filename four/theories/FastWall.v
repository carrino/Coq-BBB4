(** Finite-wall checks with shared trie membership. This is an extensionally
    equal implementation of the existing checker, including rejected inputs. *)
From Coq Require Import Arith Bool List PArith.
From BBB24 Require Import Statement StatementTr CTape PosEnc Bounds Closure ClosureTr
  WeightedCensus WeightedNGram WeightedTail WeightedSuffix NGramCensus RankSearch.
From BBB24.Checkers Require Import NGram FiniteWall WeightedLex.
Import ListNotations.

Lemma fast_forallb_ext : forall (A:Type)(f g:A->bool) l,
 (forall x,f x=g x)->forallb f l=forallb g l.
Proof. intros A f g l H;induction l;cbn;[reflexivity|now rewrite H,IHl]. Qed.

Lemma fast_pset_acc_complete : forall (A:Type) (enc:A->positive) l s a,
  In a l \/ PositiveSet.mem (enc a) s=true ->
  PositiveSet.mem (enc a)
    (fold_left (fun s a=>pset_add A enc a s) l s)=true.
Proof.
  intros A enc l; induction l as[|x l IH]; intros s a H; cbn in *.
  - tauto.
  - apply IH. destruct H as[[<-|H]|H];[right|now left|right];
      apply PositiveSet.mem_spec, PositiveSet.add_spec.
    + now left.
    + right. now apply PositiveSet.mem_spec.
Qed.
Lemma fast_pset_complete : forall (A:Type) (enc:A->positive) l a,
  In a l -> pset_mem A enc a (pset_of A enc l)=true.
Proof. intros; apply fast_pset_acc_complete; now left. Qed.

Lemma fast_cmem_eq : forall c I,
  pset_mem cconf cconf_enc c (pset_of cconf cconf_enc I)=wall_cmem c I.
Proof.
  intros c I. destruct(pset_mem cconf cconf_enc c(pset_of cconf cconf_enc I))eqn:E,
    (wall_cmem c I)eqn:F;try reflexivity.
  - apply(pset_of_mem cconf cconf_enc cconf_enc_inj)in E.
    apply wall_cmem_spec in E;congruence.
  - apply wall_cmem_spec in F. apply(fast_pset_complete cconf cconf_enc)in F;congruence.
Qed.
Lemma fast_wmem_eq : forall g G,
  pset_mem (list Sym) syms_enc g (pset_of (list Sym) syms_enc G)=wall_wmem g G.
Proof.
  intros g G. destruct(pset_mem (list Sym) syms_enc g(pset_of (list Sym) syms_enc G))eqn:E,
    (wall_wmem g G)eqn:F;try reflexivity.
  - apply(pset_of_mem (list Sym) syms_enc syms_enc_inj)in E.
    apply wall_wmem_spec in E;congruence.
  - apply wall_wmem_spec in F. apply(fast_pset_complete (list Sym) syms_enc)in F;congruence.
Qed.

Definition fast_wall_rule tm target gs is (c:cconf) :=
 if instr_eqb (cinstr c) target then true else
 let '(q,(L,h,R)):=c in match tm q h with
 | None=>false
 | Some tr=>match t_dir tr with
   | DR=>match R with
     | []=>pset_mem (list Sym) syms_enc (t_write tr::L) gs
     | _=>match cstep tm c with
       |Some d=>pset_mem cconf cconf_enc d is|None=>false end end
   | DL=>match L with
     | []=>false
     | _=>match cstep tm c with
       |Some d=>pset_mem cconf cconf_enc d is|None=>false end end
   end end.
Lemma fast_wall_rule_eq : forall tm target G I c,
 fast_wall_rule tm target (pset_of (list Sym) syms_enc G)
   (pset_of cconf cconf_enc I)c=wall_rule tm target G I c.
Proof.
 intros tm target G I [q[[L h]R]]. unfold fast_wall_rule,wall_rule.
 destruct(instr_eqb _ _);[reflexivity|].
 destruct(tm q h)as[tr|];[|reflexivity].
 destruct(t_dir tr);destruct L;destruct R;cbv beta iota zeta;
   try reflexivity;try apply fast_wmem_eq;
   match goal with |- context[cstep ?m ?c]=>destruct(cstep m c)as[d|] end;
   try apply fast_cmem_eq;reflexivity.
Qed.
Definition fast_wall_check tm target entry G I :=
 let gs:=pset_of (list Sym) syms_enc G in
 let is:=pset_of cconf cconf_enc I in
 forallb(fun g=>match g with []=>false|_=>
   forallb(fun q=>pset_mem cconf cconf_enc (wall_entry q g)is)entry end)G
 && forallb(fast_wall_rule tm target gs is)I.
Lemma fast_wall_check_eq : forall tm target entry G I,
 fast_wall_check tm target entry G I=wall_check tm target entry G I.
Proof.
 intros. unfold fast_wall_check,wall_check. f_equal.
 - apply fast_forallb_ext. intros [|g gs];[reflexivity|].
   apply fast_forallb_ext;intro q;apply fast_cmem_eq.
 - apply fast_forallb_ext;intro c;apply fast_wall_rule_eq.
Qed.

Definition fast_wc_target tm n ls rs Sl target cert:=
 match cert with
 |None=>lex_ok_tr cconf cinstr(ng_succs tm ls rs)Sl target
   (map(ng_comp_denote tm n)(rank_procedure tm ls rs Sl target))
 |Some C=>
   if forallb wn_linear (wc_components C) then
     wl_ok(ng_succs tm ls rs)target Sl(map(wn_denote tm n)(wc_components C))
   else wall_wmem(repeat S0(wc_k C))(wc_guards C) &&
   fast_wall_check tm target(wc_entry tm target)(wc_guards C)(wc_inside C) &&
   forallb(wn_good Sl)(wc_components C) &&
   wl_ok(ng_succs tm ls rs)target Sl(map(wn_denote tm n)(wc_components C))
 end.
Lemma fast_wc_target_eq : forall tm n ls rs Sl target cert,
 fast_wc_target tm n ls rs Sl target cert=wc_target tm n ls rs Sl target cert.
Proof.
 intros;unfold fast_wc_target,wc_target;destruct cert;[|reflexivity].
 now rewrite fast_wall_check_eq.
Qed.
Definition fast_wt_ready tail :=
 let source:=wt_source tail in let n:=wt_width tail in
 let ls:=wt_left tail in let rs:=wt_right tail in let Sl:=wt_nodes tail in
 if 1<=?n then
 if closed_tr_b cconf cconf_enc(ng_succs source ls rs)Sl then
 forallb(fun tg=>if tail_instrs Sl tg then
   fast_wc_target source n ls rs Sl tg(wt_cert tail tg)else true)all_Instr
 else false else false.
Lemma fast_wt_ready_eq : forall tail,fast_wt_ready tail=wt_ready tail.
Proof.
 intros [source n ls rs Sl cert];unfold fast_wt_ready,wt_ready;
 cbn[wt_source wt_width wt_left wt_right wt_nodes wt_cert].
 destruct(1<=?n);[|reflexivity].
 destruct(closed_tr_b _ _ _ _);[|reflexivity].
 apply fast_forallb_ext;intro tg. destruct(tail_instrs Sl tg);[apply fast_wc_target_eq|reflexivity].
Qed.
Definition fast_wt_hybrid_check bs bi tail rows :=
 let ready:=fast_wt_ready tail in forallb(wt_hybrid_row bs bi tail ready)rows.
Lemma fast_wt_hybrid_check_eq : forall bs bi tail rows,
 fast_wt_hybrid_check bs bi tail rows=wt_hybrid_check bs bi tail rows.
Proof. intros;unfold fast_wt_hybrid_check,wt_hybrid_check;now rewrite fast_wt_ready_eq. Qed.


Definition fast_wc_graph_check bs bi tm n t (Sl:list cconf) (cert:Instr->option WCert):bool:=
 if 1<=?n then match csteps tm t c0 with None=>false|Some cc=>
 let '(q,(l,h,r)):=cc in let a0:=ng_start n cc in
 let ls:=gadds(ng_seed_side n l ++ flat_map(fun c=>fst(ng_harvest tm c))Sl)gempty in
 let rs:=gadds(ng_seed_side n r ++ flat_map(fun c=>snd(ng_harvest tm c))Sl)gempty in
 if ng_seed_ok n ls rs cc then
 if closed_tr_b cconf cconf_enc(ng_succs tm ls rs)Sl then
 if mem_tr cconf cconf_enc a0 Sl then
 if prefix_gate bs bi tm t(tail_states Sl)(tail_instrs Sl)then
 forallb(fun tg=>if tail_instrs Sl tg then fast_wc_target tm n ls rs Sl tg(cert tg)else true)all_Instr
 else false else false else false else false end else false.

Definition fast_weighted_suffix_check bs bi (target source:TM) n t (Sl:list cconf) cert :=
  if suffix_agrees source target Sl then
  if 1<=?n then match csteps target t c0 with None=>false|Some cc=>
  let '(q,(l,h,r)):=cc in let a0:=ng_start n cc in
  let ls:=gadds(ng_seed_side n l ++ flat_map(fun c=>fst(ng_harvest source c))Sl)gempty in
  let rs:=gadds(ng_seed_side n r ++ flat_map(fun c=>snd(ng_harvest source c))Sl)gempty in
  if ng_seed_ok n ls rs cc then
  if closed_tr_b cconf cconf_enc(ng_succs source ls rs)Sl then
  if mem_tr cconf cconf_enc a0 Sl then
  if prefix_gate bs bi target t(tail_states Sl)(tail_instrs Sl)then
  forallb(fun tg=>if tail_instrs Sl tg then fast_wc_target source n ls rs Sl tg(cert tg)else true)all_Instr
  else false else false else false else false end else false else false.

Lemma fast_wc_graph_check_eq : forall bs bi tm n t Sl cert,
 fast_wc_graph_check bs bi tm n t Sl cert=wc_graph_check bs bi tm n t Sl cert.
Proof.
 intros;unfold fast_wc_graph_check,wc_graph_check.
 destruct(1<=?n);[|reflexivity].
 destruct(csteps tm t c0)as[[q[[l h]r]]|];[|reflexivity].
 cbv beta iota zeta.
 repeat match goal with |- (if ?b then _ else _)=_=>destruct b end;
   try reflexivity.
 apply fast_forallb_ext;intro tg;destruct(tail_instrs Sl tg);
   [apply fast_wc_target_eq|reflexivity].
Qed.
Lemma fast_weighted_suffix_check_eq : forall bs bi target source n t Sl cert,
 fast_weighted_suffix_check bs bi target source n t Sl cert=
 weighted_suffix_check bs bi target source n t Sl cert.
Proof.
 intros;unfold fast_weighted_suffix_check,weighted_suffix_check.
 destruct(suffix_agrees source target Sl);[|reflexivity].
 destruct(1<=?n);[|reflexivity].
 destruct(csteps target t c0)as[[q[[l h]r]]|];[|reflexivity].
 cbv beta iota zeta.
 repeat match goal with |- (if ?b then _ else _)=_=>destruct b end;
   try reflexivity.
 apply fast_forallb_ext;intro tg;destruct(tail_instrs Sl tg);
   [apply fast_wc_target_eq|reflexivity].
Qed.

Print Assumptions fast_wall_check_eq.
Print Assumptions fast_wt_hybrid_check_eq.
Print Assumptions fast_wc_graph_check_eq.
Print Assumptions fast_weighted_suffix_check_eq.
