(** Parity-refined fuel contexts with exact pattern and extent measures. *)
From Coq Require Import Arith Lia Bool List ZArith Ring.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape PosEnc Records Closure ClosureTr.
From BBB4.Checkers Require Import NGram NGramTr FuelClass FuelWide FuelWideTr FuelSCCTr
 FuelMixTr FuelMixPartialTr FuelExactTr FuelExtentTr FuelExactMixTr FuelParityTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
Import ListNotations.
Definition fp_instr(a:fpconf):Instr:=fw_instr(fp_project a).
Definition fp_moves_right(tm:TM)(a:fpconf):bool:=fwnode_moves_right tm(fp_project a).
Definition fp_rfuel_ge1(a:fpconf):bool:=fwnode_rfuel_ge1(fp_project a).
Definition fp_mape_get(m:PositiveMap.tree nat)(a:fpconf):nat:=
 match PositiveMap.find(fpconf_enc a)m with Some v=>v|None=>0 end.
Definition fpm_denote(tm:TM)(n:nat)(c:xfmcomp):lexcomp fpconf:=
 match c with
 |XFMRk phi=>LexRank fpconf(fp_mape_get(pmape_of phi))
 |XFMSum terms K phi gate=>
   if forallb(fun term=>xfm_ok n(snd term))terms then
    LexMeas fpconf(xfm_sum terms)(fun a a'=>xfm_change tm terms(fp_project a)(fp_project a'))K(fp_mape_get(pmape_of phi))
     (fun a=>PositiveSet.mem(fpconf_enc a)(psete_of gate))
   else LexRank fpconf(fun _=>0)
 end.
Definition fpm_cert(tm:TM)(n:nat)(c:list xfmcomp*list positive):list(lexcomp fpconf)*(fpconf->bool):=
 (map(fpm_denote tm n)(fst c),fun a=>PositiveSet.mem(fpconf_enc a)(psete_of(snd c))).
Lemma fpm_comp_exact:forall tm n ls rs c,
 comp_exact tm fpconf(fp_succs tm ls rs)(fp_covers n ls rs)(fpm_denote tm n c).
Proof.
 intros tm n ls rs [phi|terms K phi gate];cbn[fpm_denote];[exact I|].
 destruct(forallb(fun term=>xfm_ok n(snd term))terms)eqn:Hok;[|exact I].
 intros a cc a' cc' sl Hc Hc' Hs Es Hin;eapply xfm_sum_exact;eauto using fp_as_xf.
Qed.
Definition ngram_check_neverqh_fuelparitymixtr_except (tm : TM) (n t fuel rounds : nat) (skip : Instr -> bool)
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
      closure_check_neverqh_fuelscctr_except tm fpconf fpconf_enc fp_instr
        (fp_succs tm lset rset)
        (fp_moves_right tm) fp_rfuel_ge1
        t fuel (fp_start n cc) skip
        (fun q => fpm_cert tm n (cert q))
  | None => false
  end.

Theorem ngram_check_neverqh_fuelparitymixtr_except_sound : forall tm n t fuel rounds skip cert,
  (forall q, skip q = true -> forall N, exists j, N <= j /\ FiresAt tm q j) ->
  ngram_check_neverqh_fuelparitymixtr_except tm n t fuel rounds skip cert = true ->
  NeverQuasiHaltsTr tm.
Proof.
  intros tm n t fuel rounds skip cert Hmanual H.
  unfold ngram_check_neverqh_fuelparitymixtr_except in H.
  apply andb_prop in H as [Hn H]. apply Nat.leb_le in Hn.
  destruct (csteps tm t c0) as [[q [[l h] r]]|] eqn:Et; [|discriminate].
  match type of H with
  | (let '(_, _) := ?G in _) = true => destruct G as [lset rset] eqn:Eg
  end.
  cbv beta iota zeta in H.
  apply andb_prop in H as [Hseed Hcheck].
  apply (closure_check_neverqh_fuelscctr_except_sound tm fpconf fpconf_enc fp_instr
           (fp_succs tm lset rset)
           (fp_moves_right tm) fp_rfuel_ge1
           (fp_covers n lset rset)) in Hcheck;
    [assumption | | | | | | | |].
  - exact fpconf_enc_inj.
  - intros a c Hc. eapply fw_covers_instr;apply xf_as_fw,fp_as_xf;exact Hc.
  - intros a c Hc. apply fp_succs_sound; assumption.
  - intros a c Hmr Hc. eapply fwnode_moves_right_sound;[exact Hmr|apply xf_as_fw,fp_as_xf;exact Hc].
  - intros a c Hrf Hc. eapply fwnode_rfuel_ge1_sound;[exact Hrf|apply xf_as_fw,fp_as_xf;exact Hc].
  - exact Hmanual.
  - intros ct' Hct'. rewrite Et in Hct'. injection Hct' as <-.
    apply fp_start_sound. exact Hseed.
  - intros q0. apply Forall_forall. intros comp Hin.
    cbn [fpm_cert fst] in Hin.
    apply in_map_iff in Hin. destruct Hin as (c & <- & _).
    apply fpm_comp_exact.
Qed.
