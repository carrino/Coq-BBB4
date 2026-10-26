(** Normalized symbolic replay with tape-stream equality for local rules.
    The representation changes are proved to preserve arbitrary suffixes. *)
From Coq Require Import Arith ZArith Lia Bool List Setoid.
From SmallBB Require Import Statement CTape.
From SmallBB.Checkers.IRules Require Import Expr RLE Engine Rules RulesK EngineK
 RulesBlk EngineKS RulesBlkPfx.
Import ListNotations.
Open Scope Z_scope.
Definition s23_normside lo rs:=match bmerge_adj lo rs with Some rs'=>rs'|None=>rs end.
Definition s23_normcfg lo c:=mkBCfg(b_st c)(b_hs c)(s23_normside lo(b_L c))(s23_normside lo(b_R c)).
Lemma s23_normside_den:forall tbl lo rs nu,bge lo nu->bdside tbl nu(s23_normside lo rs)=bdside tbl nu rs.
Proof.
 intros tbl lo rs nu H;unfold s23_normside.
 destruct(bmerge_adj lo rs)as[rs'|]eqn:E;[exact(bmerge_adj_den tbl lo rs rs' nu E H)|reflexivity].
Qed.
Lemma s23_normcfg_den:forall tbl lo c nu XL XR,bge lo nu->
 bsemX tbl nu(s23_normcfg lo c)XL XR=bsemX tbl nu c XL XR.
Proof. intros;unfold bsemX,s23_normcfg;cbn[b_st b_hs b_L b_R];rewrite !s23_normside_den by assumption;reflexivity. Qed.
Lemma s23_end_eq:forall tbl lo c want nu XL XR,raw_ok tbl->bge lo nu->
 bend_eqb tbl lo c want=true->bsemX tbl nu c XL XR=bsemX tbl nu want XL XR.
Proof.
 intros tbl lo c want nu XL XR Hraw Hb H;unfold bend_eqb in H.
 apply orb_prop in H as[H|H];[apply bscfg_eqb_bsemX;exact H|].
 repeat rewrite andb_true_iff in H;destruct H as[[[Hq Hh]HL]HR].
 apply st_eqb_spec in Hq;apply sym_eqb_spec in Hh.
 unfold bsemX;rewrite Hq,Hh;
 rewrite(bstreams_eq_sound tbl lo _ _ nu Hraw Hb HL),(bstreams_eq_sound tbl lo _ _ nu Hraw Hb HR);reflexivity.
Qed.
Fixpoint s23_replay (tm : TM) (tbl : BTbl) (blks : list (nat * list Sym))
    (lo : list Z) (cfuel : nat) (rules : list (BRuleP * list Tr))
    (endt : BCfg -> bool) (sent : bool * bool) (fuel : nat)
    (stepped : bool) (c : BCfg) : option (BCfg * list Tr) :=
  match fuel with
  | O => None
  | S fuel' =>
      if stepped && endt c then Some (c, [])
      else
        match try_rulesBlkP lo sent rules c with
        | Some (c', F) =>
            match s23_replay tm tbl blks lo cfuel rules endt sent fuel'
                    stepped (s23_normcfg lo c') with
            | Some (cend, F') => Some (cend, tr_union F F')
            | None => None
            end
        | None =>
            match beng_stepS tm tbl blks lo (fst sent) (snd sent) cfuel c with
            | Some (c', F) =>
                match s23_replay tm tbl blks lo cfuel rules endt sent fuel'
                        true (s23_normcfg lo (bcanon lo tbl blks c')) with
                | Some (cend, F') => Some (cend, tr_union F F')
                | None => None
                end
            | None => None
            end
        end
  end.

Lemma s23_replay_sound : forall tm tbl blks lo cfuel rules endt sent fuel
                               stepped c cend F,
  raw_ok tbl ->
  s23_replay tm tbl blks lo cfuel rules endt sent fuel stepped c
    = Some (cend, F) ->
  forall nu XL XR, bge lo nu ->
  (fst sent = false -> XL = []) -> (snd sent = false -> XR = []) ->
  (forall r Fr c1 c2, In (r, Fr) rules ->
     ruleBlkPfx_apply lo sent r c1 = Some c2 ->
     exists n, (1 <= n)%nat /\
       Reach tm Fr n (bsemX tbl nu c1 XL XR) (bsemX tbl nu c2 XL XR)) ->
  endt cend = true /\
  exists n, Reach tm F n (bsemX tbl nu c XL XR) (bsemX tbl nu cend XL XR) /\
            (stepped = false -> (1 <= n)%nat).
Proof.
  intros tm tbl blks lo cfuel rules endt sent fuel.
  induction fuel as [|fuel IH]; intros stepped c cend F Hraw H nu XL XR Hb
    HXL HXR Happ; simpl in H; [discriminate|].
  destruct (stepped && endt c) eqn:Hend.
  - injection H as <- <-.
    apply andb_prop in Hend as [Hst Hendc].
    split; [exact Hendc|].
    exists O. split; [apply Reach_refl|].
    intro Hf; rewrite Hf in Hst; discriminate.
  - destruct (try_rulesBlkP lo sent rules c) as [[c' Fr]|] eqn:Htry.
    + destruct (s23_replay tm tbl blks lo cfuel rules endt sent fuel
                  stepped (s23_normcfg lo c'))
        as [[cend' F']|] eqn:Hrec; [|discriminate].
      injection H as <- <-.
      destruct (IH stepped (s23_normcfg lo c') cend' F' Hraw Hrec nu XL XR Hb HXL HXR Happ)
        as (Hende & n2 & HR2 & _).
      assert (Hget : exists r0, In (r0, Fr) rules /\
                     ruleBlkPfx_apply lo sent r0 c = Some c').
      { clear -Htry. induction rules as [|[r0 F0] rest IHr];
          simpl in Htry; [discriminate|].
        destruct (ruleBlkPfx_apply lo sent r0 c) eqn:Ha.
        - injection Htry as <- <-. exists r0. split; [left|]; auto.
        - destruct (IHr Htry) as (r1 & Hin & Ha1).
          exists r1. split; [right|]; assumption. }
      destruct Hget as (r0 & Hin & Ha).
      destruct (Happ r0 Fr c c' Hin Ha) as (n1 & Hn1 & HR1).
      rewrite s23_normcfg_den in HR2 by exact Hb.
      split; [exact Hende|].
      exists (n1 + n2)%nat. split.
      * eapply (Reach_set _ _ (Fr ++ F'));
          [intro t; rewrite tr_union_in, in_app_iff; tauto|].
        exact (Reach_compose _ _ _ _ _ _ _ _ HR1 HR2).
      * intro; lia.
    + destruct (beng_stepS tm tbl blks lo (fst sent) (snd sent) cfuel c)
        as [[c' Fe]|] eqn:Hstep; [|discriminate].
      destruct (s23_replay tm tbl blks lo cfuel rules endt sent fuel true
                  (s23_normcfg lo (bcanon lo tbl blks c')))
        as [[cend' F']|] eqn:Hrec; [|discriminate].
      injection H as <- <-.
      destruct (IH true (s23_normcfg lo (bcanon lo tbl blks c')) cend' F' Hraw Hrec nu XL XR
                  Hb HXL HXR Happ)
        as (Hende & n2 & HR2 & _).
      destruct (beng_stepS_sound tm tbl blks lo (fst sent) (snd sent) cfuel
                  c c' Fe Hraw Hstep nu XL XR Hb HXL HXR)
        as (n1 & Hn1 & HR1).
      rewrite s23_normcfg_den in HR2 by exact Hb.
      rewrite <- (bcanon_bsemX lo tbl blks c' nu XL XR Hraw Hb) in HR1.
      split; [exact Hende|].
      exists (n1 + n2)%nat. split.
      * eapply (Reach_set _ _ (Fe ++ F'));
          [intro t; rewrite tr_union_in, in_app_iff; tauto|].
        exact (Reach_compose _ _ _ _ _ _ _ _ HR1 HR2).
      * intro; lia.
Qed.

Definition s23_rule_check (tm : TM) (tbl : BTbl)
    (blks : list (nat * list Sym)) (cfuel fuel : nat)
    (prior : list (BRuleP * list Tr)) (r : BRuleP) : option (list Tr) :=
  match s23_replay tm tbl blks (brule_lbsP r) cfuel prior
          (fun c => bend_eqb tbl (brule_lbsP r) c (brulep_end_cfg r)) (brp_pfx r)
          fuel false (brulep_start_cfg r) with
  | Some (_, F) => Some F
  | None => None
  end.

Lemma s23_rule_check_sound : forall tm tbl blks cfuel fuel prior r F,
  raw_ok tbl ->
  (forall r' F', In (r', F') prior -> brule_semP tm tbl r' F') ->
  s23_rule_check tm tbl blks cfuel fuel prior r = Some F ->
  brule_semP tm tbl r F.
Proof.
  intros tm tbl blks cfuel fuel prior r F Hraw Hprior H u Hu YL YR HYL HYR.
  unfold s23_rule_check in H.
  destruct (s23_replay tm tbl blks (brule_lbsP r) cfuel prior
              (fun c => bend_eqb tbl (brule_lbsP r) c (brulep_end_cfg r)) (brp_pfx r)
              fuel false (brulep_start_cfg r)) as [[cend F']|] eqn:Hrep;
    [|discriminate].
  injection H as <-.
  destruct (s23_replay_sound tm tbl blks (brule_lbsP r) cfuel prior _
              (brp_pfx r) fuel false
              (brulep_start_cfg r) cend F' Hraw Hrep u YL YR Hu HYL HYR
              (fun r0 Fr c1 c2 Hin Happ =>
                 ruleBlkPfx_apply_sound tm tbl (brule_lbsP r) r0 Fr c1 c2
                   (brp_pfx r) Hraw Happ (Hprior r0 Fr Hin) u Hu YL YR
                   HYL HYR))
    as (Hend & n & HR & Hpos).
  exists n. split; [apply Hpos; reflexivity|].
  rewrite <- (s23_end_eq tbl (brule_lbsP r) cend (brulep_end_cfg r) u YL YR Hraw Hu Hend).
  exact HR.
Qed.

Fixpoint s23_rules_aux (tm : TM) (tbl : BTbl)
    (blks : list (nat * list Sym)) (cfuel fuel : nat)
    (acc : list (BRuleP * list Tr)) (rules : list BRuleP)
  : option (list (BRuleP * list Tr)) :=
  match rules with
  | [] => Some acc
  | r :: rest =>
      match s23_rule_check tm tbl blks cfuel fuel acc r with
      | Some F =>
          s23_rules_aux tm tbl blks cfuel fuel (acc ++ [(r, F)]) rest
      | None => None
      end
  end.

Definition s23_rules (tm : TM) (tbl : BTbl)
    (blks : list (nat * list Sym)) (cfuel fuel : nat) (rules : list BRuleP)
  : option (list (BRuleP * list Tr)) :=
  s23_rules_aux tm tbl blks cfuel fuel [] rules.

Lemma s23_rules_aux_sound : forall tm tbl blks cfuel fuel rules acc
                                         vrules,
  raw_ok tbl ->
  s23_rules_aux tm tbl blks cfuel fuel acc rules = Some vrules ->
  (forall r F, In (r, F) acc -> brule_semP tm tbl r F) ->
  forall r F, In (r, F) vrules -> brule_semP tm tbl r F.
Proof.
  intros tm tbl blks cfuel fuel rules. induction rules as [|r0 rest IH];
    intros acc vrules Hraw H Hacc; simpl in H.
  - injection H as <-. exact Hacc.
  - destruct (s23_rule_check tm tbl blks cfuel fuel acc r0) as [F0|] eqn:Hc;
      [|discriminate].
    apply (IH (acc ++ [(r0, F0)]) vrules Hraw H).
    intros r F Hin. apply in_app_or in Hin as [Hin | Hin].
    + apply Hacc; exact Hin.
    + destruct Hin as [Heq | []]. injection Heq as <- <-.
      exact (s23_rule_check_sound tm tbl blks cfuel fuel acc r0 F0 Hraw
               Hacc Hc).
Qed.

Theorem s23_rules_sound : forall tm tbl blks cfuel fuel rules vrules,
  raw_ok tbl ->
  s23_rules tm tbl blks cfuel fuel rules = Some vrules ->
  forall r F, In (r, F) vrules -> brule_semP tm tbl r F.
Proof.
  intros tm tbl blks cfuel fuel rules vrules Hraw H.
  apply (s23_rules_aux_sound tm tbl blks cfuel fuel rules [] vrules
           Hraw H).
  intros r F [].
Qed.
