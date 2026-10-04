(** Exact capped fuel and nonnegative pattern/extent combinations.

    Extent is the distance to the farthest nonblank on one side, with
    value zero for an entirely blank side. Exact count classes decide
    which case applies, giving exact deltas even at the tape boundary.
    Subtracting a pattern count remains nonnegative by the occurrence
    bound in PatternComplementTr. Every proposed sum and finite node
    potential is checked by the existing lexicographic fuel engine. *)
From Coq Require Import Arith Lia Bool List ZArith Ring.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape PosEnc Records Closure ClosureTr.
From BBB4.Checkers Require Import NGram NGramTr FuelClass FuelWide FuelWideTr FuelSCCTr
 FuelMixTr FuelMixPartialTr FuelExactTr FuelExtentTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
Import ListNotations.
Inductive xfmmeasure:Type:=
| XFPatt(p:list Sym)(rg:ngreg)
| XFExtent(side:bool)
| XFComplement(side:bool)(p:list Sym).
Definition xfm_ok(n:nat)(m:xfmmeasure):bool:=match m with
|XFPatt p rg=>pm_ok n p rg|XFExtent _=>true|XFComplement side p=>pm_ok n p(xe_reg side)end.
Definition xfm_val(m:xfmmeasure)(cc:cconf):nat:=match m with
|XFPatt p rg=>pm_val p rg cc|XFExtent side=>xe_val side cc|XFComplement side p=>xe_complement_val side p cc end.
Definition xfm_delta(tm:TM)(m:xfmmeasure)(a a':fcconf):Z:=match m with
|XFPatt p rg=>pm_delta tm p rg(fst a)(fst a')
|XFExtent side=>xe_delta tm side a
|XFComplement side p=>(xe_delta tm side a-pm_delta tm p(xe_reg side)(fst a)(fst a'))%Z end.
Lemma xfm_exact:forall tm n ls rs m a cc a' cc',
 xfm_ok n m=true->xf_covers n ls rs a(lift cc)->cstep tm cc=Some cc'->
 Z.of_nat(xfm_val m cc')=(Z.of_nat(xfm_val m cc)+xfm_delta tm m a a')%Z.
Proof.
 intros tm n ls rs m a cc a' cc' Hok Hc Hs.
 pose proof(proj1(xf_as_fw _ _ _ _ _ Hc))as Hg.
 pose proof(xf_covers_counts _ _ _ _ _ Hc)as Hcls.
 destruct m as[p rg|side|side p];cbn[xfm_val xfm_delta xfm_ok]in *.
 - apply(pm_exact tm n ls rs p rg(fst a)cc(fst a')cc');try assumption.
   + unfold pm_ok in Hok;apply andb_prop in Hok as[H _].
     apply existsb_exists in H as(x&Hin&E);apply sym_eqb_spec in E;subst;exact Hin.
   + unfold pm_ok in Hok;apply andb_prop in Hok as[_ H];destruct rg;apply Nat.leb_le;exact H.
 - eapply xe_exact_base;eauto.
 - pose proof(xe_complement_exact_base tm n ls rs side p a cc a' cc' Hok Hg Hcls Hs);lia.
Qed.
Definition xfmterm:Type:=(nat*xfmmeasure)%type.
Fixpoint xfm_sum(terms:list xfmterm)(cc:cconf):nat:=match terms with
|[]=>0|(w,m)::rest=>w*xfm_val m cc+xfm_sum rest cc end.
Fixpoint xfm_change(tm:TM)(terms:list xfmterm)(a a':fcconf):Z:=match terms with
|[]=>0%Z|(w,m)::rest=>(Z.of_nat w*xfm_delta tm m a a'+xfm_change tm rest a a')%Z end.
Lemma xfm_sum_exact:forall tm n ls rs terms a cc a' cc',
 forallb(fun term=>xfm_ok n(snd term))terms=true->xf_covers n ls rs a(lift cc)->cstep tm cc=Some cc'->
 Z.of_nat(xfm_sum terms cc')=(Z.of_nat(xfm_sum terms cc)+xfm_change tm terms a a')%Z.
Proof.
 intros tm n ls rs terms;induction terms as[|[w m]rest IH];intros a cc a' cc' Hok Hc Hs;[reflexivity|].
 cbn[forallb snd]in Hok;apply andb_prop in Hok as[Hm Hr].
 pose proof(xfm_exact tm n ls rs m a cc a' cc' Hm Hc Hs)as Hm'.
 specialize(IH a cc a' cc' Hr Hc Hs).
 cbn[xfm_sum xfm_change];rewrite !Nat2Z.inj_add,!Nat2Z.inj_mul,Hm',IH;ring.
Qed.
Inductive xfmcomp:Type:=
|XFMRk(phi:list(positive*nat))
|XFMSum(terms:list xfmterm)(K:nat)(phi:list(positive*nat))(gate:list positive).
Definition xfm_denote(tm:TM)(n:nat)(c:xfmcomp):lexcomp fcconf:=
 match c with
 |XFMRk phi=>LexRank fcconf(fpmape_get(pmape_of phi))
 |XFMSum terms K phi gate=>
   if forallb(fun term=>xfm_ok n(snd term))terms then
    LexMeas fcconf(xfm_sum terms)(xfm_change tm terms)K(fpmape_get(pmape_of phi))
     (fun a=>PositiveSet.mem(fcconf_enc a)(psete_of gate))
   else LexRank fcconf(fun _=>0)
 end.
Definition xfm_cert(tm:TM)(n:nat)(c:list xfmcomp*list positive):list(lexcomp fcconf)*(fcconf->bool):=
 (map(xfm_denote tm n)(fst c),fun a=>PositiveSet.mem(fcconf_enc a)(psete_of(snd c))).
Lemma xfm_comp_exact:forall tm n ls rs c,
 comp_exact tm fcconf(xf_succs tm ls rs)(xf_covers n ls rs)(xfm_denote tm n c).
Proof.
 intros tm n ls rs [phi|terms K phi gate];cbn[xfm_denote];[exact I|].
 destruct(forallb(fun term=>xfm_ok n(snd term))terms)eqn:Hok;[|exact I].
 intros a cc a' cc' sl Hc Hc' Hs Es Hin;eapply xfm_sum_exact;eauto.
Qed.
Definition ngram_check_neverqh_fuelexactmixtr_except (tm : TM) (n t fuel rounds : nat) (skip : Instr -> bool)
    (cert : Instr -> list xfmcomp * list positive) : bool :=
  (1 <=? n) &&
  match csteps tm t c0 with
  | Some cc =>
      let '(q, (l, h, r)) := cc in
      let lset0 := gadds (ng_seed_side n l) gempty in
      let rset0 := gadds (ng_seed_side n r) gempty in
      let a0 := ng_start n cc in
      let '(lset, rset) := ng_grow tm a0 fuel rounds lset0 rset0 in
      ng_seed_ok n lset rset cc &&
      closure_check_neverqh_fuelscctr_except tm fcconf fcconf_enc fw_instr
        (xf_succs tm lset rset)
        (fwnode_moves_right tm) fwnode_rfuel_ge1
        t fuel (fw_start n cc) skip
        (fun q => xfm_cert tm n (cert q))
  | None => false
  end.

Theorem ngram_check_neverqh_fuelexactmixtr_except_sound : forall tm n t fuel rounds skip cert,
  (forall q, skip q = true -> forall N, exists j, N <= j /\ FiresAt tm q j) ->
  ngram_check_neverqh_fuelexactmixtr_except tm n t fuel rounds skip cert = true ->
  NeverQuasiHaltsTr tm.
Proof.
  intros tm n t fuel rounds skip cert Hmanual H.
  unfold ngram_check_neverqh_fuelexactmixtr_except in H.
  apply andb_prop in H as [Hn H]. apply Nat.leb_le in Hn.
  destruct (csteps tm t c0) as [[q [[l h] r]]|] eqn:Et; [|discriminate].
  match type of H with
  | (let '(_, _) := ?G in _) = true => destruct G as [lset rset] eqn:Eg
  end.
  cbv beta iota zeta in H.
  apply andb_prop in H as [Hseed Hcheck].
  apply (closure_check_neverqh_fuelscctr_except_sound tm fcconf fcconf_enc fw_instr
           (xf_succs tm lset rset)
           (fwnode_moves_right tm) fwnode_rfuel_ge1
           (xf_covers n lset rset)) in Hcheck;
    [assumption | | | | | | | |].
  - exact fcconf_enc_inj.
  - intros a c Hc. eapply fw_covers_instr;apply xf_as_fw;exact Hc.
  - intros a c Hc. apply xf_succs_sound; assumption.
  - intros a c Hmr Hc. eapply fwnode_moves_right_sound;[exact Hmr|apply xf_as_fw;exact Hc].
  - intros a c Hrf Hc. eapply fwnode_rfuel_ge1_sound;[exact Hrf|apply xf_as_fw;exact Hc].
  - exact Hmanual.
  - intros ct' Hct'. rewrite Et in Hct'. injection Hct' as <-.
    apply xf_start. exact Hseed.
  - intros q0. apply Forall_forall. intros comp Hin.
    cbn [xfm_cert fst] in Hin.
    apply in_map_iff in Hin. destruct Hin as (c & <- & _).
    apply xfm_comp_exact.
Qed.
