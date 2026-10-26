(** The polynomial (2,3) instruction case, with a proved phase rotation. *)
From Coq Require Import Arith ZArith Lia Bool List Setoid.
From SmallBB Require Import Statement StatementTr CTape Size Bounds AbstractCensus Symbolic23Replay.
From SmallBB.Checkers Require Import Cycle.
From SmallBB.Checkers.IRules Require Import AnchorVisits AnchorVisitsTr MetaTr
 Expr RLE Engine Rules Meta RulesK EngineK RulesBlk MetaBlk EngineKS RulesBlkPfx MetaBlkPfx.
Import ListNotations.
Open Scope Z_scope.
Definition symbolic23_tm:TM:=machine_of_codes 2 3 [5;11;3;6;8;3]%nat.
Definition symbolic23_cert:BIRCertP:=mkBIRCertP 1561%nat (8) (8) (1) (1) StB S0 [(3%nat, [S1; S2; S2; S2; S2]);
   (4%nat, [S0; S2; S1; S0; S0]);
   (5%nat, [S0; S0; S0; S2; S1]);
   (6%nat, [S2; S2; S2; S2; S1]);
   (7%nat, [S2; S1; S2; S2; S2])] [] [(3%nat, (1), (0)); (1%nat, (0), (1))] [mkBRuleP StB S0 [(5%nat, BV (1) (1)); (0%nat, BC (2)); (2%nat, BC (1)); (1%nat, BC (1))] [(1%nat, BC (1)); (2%nat, BC (5)); (3%nat, BV (-1) (2)); (1%nat, BC (1))] (true, true);
   mkBRuleP StA S0 [(1%nat, BC (1)); (0%nat, BC (1)); (2%nat, BC (1)); (1%nat, BC (1)); (5%nat, BV (-1) (2)); (0%nat, BC (2)); (2%nat, BC (1)); (1%nat, BC (1))] [(6%nat, BV (1) (1))] (true, true)].
Definition symbolic23_blocks:=cp_blks symbolic23_cert.
Definition symbolic23_table:=mk_tbl symbolic23_blocks.
Definition symbolic23_rules:=match s23_rules symbolic23_tm symbolic23_table symbolic23_blocks 10000 10000(cp_rules symbolic23_cert)with Some rs=>rs|None=>[]end.
Definition symbolic23_F:list Tr:=[(StA,S2);(StB,S0);(StA,S1);(StB,S2);(StB,S1);(StA,S0)].
Definition symbolic23_end:=mkBCfg StB S0 [] [(1%nat,econst 1);(2%nat,econst 3);(7%nat,evar 0);(2%nat,econst 1);(1%nat,econst 1)].
Definition symbolic23_start:=btplp_cfg symbolic23_cert.
Definition symbolic23_family K:=bsem symbolic23_table(fun _=>K)symbolic23_start.
Lemma symbolic23_rules_checked:s23_rules symbolic23_tm symbolic23_table symbolic23_blocks 10000 10000(cp_rules symbolic23_cert)=Some symbolic23_rules.
Proof. native_compute;reflexivity. Qed.
Lemma symbolic23_replay_checked:s23_replay symbolic23_tm symbolic23_table symbolic23_blocks [8]10000 symbolic23_rules
 (fun c=>bend_eqb symbolic23_table[8]c symbolic23_end)(false,false)10000 false symbolic23_start=Some(symbolic23_end,symbolic23_F).
Proof. native_compute;reflexivity. Qed.
Lemma symbolic23_rotation:forall n,
 [S1;S2;S2;S2]++nreps[S2;S1;S2;S2;S2]n++[S2;S1]=nreps[S1;S2;S2;S2;S2](S n)++[S1].
Proof.
 induction n;[reflexivity|].
 change (([S1;S2;S2;S2;S2]++([S1;S2;S2;S2]++nreps[S2;S1;S2;S2;S2]n++[S2;S1]))=
 ([S1;S2;S2;S2;S2]++(nreps[S1;S2;S2;S2;S2](S n)++[S1]))).
 now rewrite IHn.
Qed.
Lemma symbolic23_end_family:forall K,0<=K->
 bsem symbolic23_table(fun _=>K)symbolic23_end=symbolic23_family(K+1).
Proof.
 intros K HK.
 unfold symbolic23_family,symbolic23_start,symbolic23_end,bsem,bdcfg.
 cbn [btplp_cfg symbolic23_cert cp_st cp_hs cp_TL cp_TR btpl_start b_st b_hs b_L b_R bdside cnt eval dot econst evar unit_cf e_c0 e_cf].
 unfold bdside,btpl_start;cbn [flat_map map fst snd].
 unfold cnt;rewrite ?eval_econst,?eval_evar.
 cbn [eval dot e_c0 e_cf].
 replace (eval (fun _ : nat => K+1) (mkExpr 0 [1])) with (K+1) by (unfold eval;cbn[dot e_c0 e_cf];ring).
 replace (eval (fun _ : nat => K+1) (mkExpr 1 [0])) with 1 by (unfold eval;cbn[dot e_c0 e_cf];ring).
 replace (Z.to_nat(K+1)) with (S(Z.to_nat K)) by(rewrite Z2Nat.inj_add by lia;cbn;lia).
 change ((lift(StB,([],S0,[S1;S2;S2;S2]++nreps[S2;S1;S2;S2;S2](Z.to_nat K)++[S2;S1])))=
 (lift(StB,([],S0,nreps[S1;S2;S2;S2;S2](S(Z.to_nat K))++[S1])))).
 now rewrite symbolic23_rotation.
Qed.
Lemma symbolic23_cycle:forall K,8<=K->exists n,(1<=n)%nat /\
 Reach symbolic23_tm symbolic23_F n (symbolic23_family K)(symbolic23_family(K+1)).
Proof.
 intros K HK.
 assert(Hraw:raw_ok symbolic23_table)by(apply mk_tbl_raw).
 assert(Hb:bge [8](fun _=>K))by(apply bge_kmin;lia).
 destruct(s23_replay_sound symbolic23_tm symbolic23_table symbolic23_blocks [8]10000 symbolic23_rules _
   (false,false)10000 false symbolic23_start symbolic23_end symbolic23_F Hraw symbolic23_replay_checked
   (fun _=>K)[][] Hb (fun _=>eq_refl)(fun _=>eq_refl))as(Hend&n&HR&Hpos).
 { intros r Fr c1 c2 Hin Happ.
   exact(ruleBlkPfx_apply_sound symbolic23_tm symbolic23_table[8]r Fr c1 c2(false,false)Hraw Happ
    (s23_rules_sound symbolic23_tm symbolic23_table symbolic23_blocks 10000 10000 _ _ Hraw symbolic23_rules_checked r Fr Hin)
    (fun _=>K)Hb[][](fun _=>eq_refl)(fun _=>eq_refl)). }
 exists n;split;[apply Hpos;reflexivity|].
 rewrite !bsemX_nil in HR.
 rewrite symbolic23_end_family in HR by lia;exact HR.
Qed.
Lemma symbolic23_anchor:stepn symbolic23_tm 1561 InitES=Some(symbolic23_family 8).
Proof.
 assert(H:csteps symbolic23_tm 1561 c0=Some(bdcfg symbolic23_table(fun _=>8)symbolic23_start))by(native_compute;reflexivity).
 rewrite <-lift_c0;exact(csteps_lift _ _ _ _ H).
Qed.
Lemma symbolic23_prefix:prefix_gate 59 67 symbolic23_tm 1561
 (tail_states(labels(fun x:Instr=>x)symbolic23_F))
 (tail_instrs(labels(fun x:Instr=>x)symbolic23_F))=true.
Proof. native_compute;reflexivity. Qed.
Theorem symbolic23_bound:NonHalt symbolic23_tm /\ Bounds 59 67 symbolic23_tm.
Proof.
 assert(Htiles:forall i,exists N K,(1561+i<=N)%nat /\ 8<=K /\
   stepn symbolic23_tm N InitES=Some(symbolic23_family K) /\
   forall m,(1561<=m)%nat->(m<N)%nat->
   exists cm,stepn symbolic23_tm m InitES=Some cm /\ In(trans_of cm)symbolic23_F).
 { induction i as[|i IH].
   - exists 1561%nat,8;split;[lia|];split;[lia|];split;[exact symbolic23_anchor|].
     intros m Hm1 Hm2;lia.
   - destruct IH as(N&K&HN&HK&Hstep&Hcov).
     destruct(symbolic23_cycle K HK)as(n&Hn1&HS&HC&_).
     exists(N+n)%nat,(K+1);split;[lia|];split;[lia|];split.
     + rewrite stepn_add,Hstep;exact HS.
     + intros m Hm1 Hm2;destruct(Nat.lt_ge_cases m N)as[Hlt|Hge].
       * exact(Hcov m Hm1 Hlt).
       * destruct(HC(m-N)%nat ltac:(lia))as(cm&Hcm&Hin).
         exists cm;split;[|exact Hin].
         replace m with(N+(m-N))%nat by lia;rewrite stepn_add,Hstep;exact Hcm. }
 assert(Hrec:forall t,In t symbolic23_F->forall B,
   exists m cm,(B<=m)%nat /\ stepn symbolic23_tm m InitES=Some cm /\ trans_of cm=t).
 { intros t Hin B;destruct(Htiles B)as(N&K&HN&HK&Hstep&_).
   destruct(symbolic23_cycle K HK)as(n&Hn1&_&_&HX).
   destruct(HX t Hin)as(m'&cm&Hm'&Hcm&Htr).
   exists(N+m')%nat,cm;split;[lia|];split;[|exact Htr].
   rewrite stepn_add,Hstep;exact Hcm. }
 split.
 - intros n Hnone;destruct(Htiles n)as(N&K&HN&HK&Hrun&_).
   destruct(stepn_prefix symbolic23_tm n N InitES _ ltac:(lia)Hrun)as(c&Hc&_);congruence.
 - eapply(tail_bounds 59 67 symbolic23_tm 1561);[exact symbolic23_prefix| |].
   + intros s tg Hs(c&Hrun&Htg).
     destruct(Htiles(s+1-1561)%nat)as(N&K&HN&HK&Hstep&Hcov).
     destruct(Hcov s Hs ltac:(lia))as(cm&Hcm&Hin).
     rewrite Hrun in Hcm;injection Hcm as <-.
     rewrite trans_of_instr_of,Htg in Hin.
     rewrite labels_instr;apply existsb_exists;exists tg;split;[exact Hin|apply instr_eqb_spec;reflexivity].
   + intros tg Htg N;rewrite labels_instr in Htg.
     apply existsb_exists in Htg as(u&Hu&Eu);apply instr_eqb_spec in Eu;subst u.
     destruct(Hrec tg Hu N)as(m&c&Hm&Hc&Htr).
     exists m;split;[exact Hm|];exists c;split;[exact Hc|].
     rewrite <-trans_of_instr_of;exact Htr.
Qed.
Print Assumptions symbolic23_bound.
