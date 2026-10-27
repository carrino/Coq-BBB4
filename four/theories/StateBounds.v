From Coq Require Import NArith Arith Lia Bool List PArith.
From BBB24 Require Import Statement StatementTr Spec CTape PosEnc Closure ClosureTr Bounds AbstractCensus.
From BBB24.Checkers Require Import Cycle.
Import ListNotations.

Definition state_prefix_gate (bs:N) (tm:TM) (t:nat) (states:St->bool) :=
 (N.of_nat t <=? bs)%N.
Lemma state_tail_bound : forall bs tm t Sl,
 state_prefix_gate bs tm t (tail_states Sl)=true ->
 (forall s q, t<=s -> VisitsAt tm q s -> tail_states Sl q=true) ->
 (forall q, tail_states Sl q=true -> forall N, exists k, N<=k /\ VisitsAt tm q k) ->
 QHBound (N.to_nat bs) tm.
Proof.
 intros bs tm t Sl Hpre Hcover Hrec q s [Hv Hquiet].
 unfold state_prefix_gate in Hpre. apply N.leb_le in Hpre.
 destruct (lt_dec s t); [lia|].
 specialize (Hcover s q ltac:(lia) Hv).
 destruct (Hrec q Hcover (S s)) as (k & Hk & Hq).
 exfalso; apply (Hquiet k); [lia|exact Hq].
Qed.

Section Abstract.
Variable tm : TM.
Variable A : Type.
Variable enc : A -> positive.
Variable ai : A -> Instr.
Variable succs : A -> option (list A).
Variable covers : A -> ExecState -> Prop.
Hypothesis enc_inj : forall x y, enc x=enc y -> x=y.
Hypothesis covers_instr : forall a c, covers a c -> ai a=instr_of c.
Hypothesis succs_sound : forall a c, covers a c ->
 match succs a,step tm c with
 | Some l,Some c' => exists a',In a' l /\ covers a' c'
 | Some _,None => False | None,_ => True end.
Lemma labels_states : forall Sl q,
 tail_states (labels ai Sl) q = appears A (fun a=>fst(ai a)) Sl q.
Proof. intros Sl q; unfold tail_states,labels,appears. induction Sl; cbn; [reflexivity|rewrite IHSl; reflexivity]. Qed.
Lemma covers_state : forall a c, covers a c -> fst(ai a)=fst c.
Proof. intros a c H; rewrite (covers_instr a c H); reflexivity. Qed.
Theorem abstract_state_bound : forall bs t cc a0 Sl cert,
 csteps tm t c0=Some cc -> covers a0 (lift cc) ->
 closed_b A enc succs Sl=true -> mem A enc a0 Sl=true ->
 (forall q,Forall (comp_exact tm A succs covers) (cert q)) ->
 live_lex_ok A enc (fun a=>fst(ai a)) succs Sl cert=true ->
 state_prefix_gate bs tm t (tail_states (labels ai Sl))=true ->
 NonHalt tm /\ QHBound (N.to_nat bs) tm.
Proof.
 intros bs t cc a0 Sl cert Et Hcov Hcl Hmem Hex Hlive Hpre.
 assert (Hin:In a0 Sl) by (eapply mem_In; eauto).
 assert (Hstart:stepn tm t InitES=Some (lift cc)) by (rewrite <-lift_c0; apply csteps_lift; exact Et).
 assert (Hinv:forall k,exists c a,stepn tm k (lift cc)=Some c /\ In a Sl /\ covers a c).
 { eapply closure_invariant; eauto. }
 split.
 - intros k Hnone. destruct (le_lt_dec t k).
   + destruct (Hinv (k-t)) as (c & a & Hr & _).
     replace k with (t+(k-t)) in Hnone by lia. rewrite stepn_add,Hstart,Hr in Hnone; discriminate.
   + destruct (stepn_prefix tm k t InitES (lift cc) ltac:(lia) Hstart) as (c & Hr & _); congruence.
 - eapply state_tail_bound; [exact Hpre| |].
   + intros s q Hts (c & Hr & Hq).
     destruct (Hinv (s-t)) as (c' & a & Hr' & Ha & Hca).
     replace s with (t+(s-t)) in Hr by lia. rewrite stepn_add,Hstart,Hr' in Hr; injection Hr as <-.
     unfold tail_states,labels. apply existsb_exists. exists (fst (ai a),([],snd (ai a),[])). split.
     * apply in_map_iff; exists a; split; [reflexivity|exact Ha].
     * apply st_eqb_spec. simpl. rewrite (covers_instr a c' Hca). exact Hq.
   + intros q Happ N. rewrite labels_states in Happ.
     destruct (live_appears_recur_lex tm A enc (fun a=>fst(ai a)) succs covers
       enc_inj covers_state succs_sound Sl cert a0 cc q Hcl (Hex q) Hlive Hin Hcov Happ N)
       as (k & c & Hk & Hr & Hq).
     exists (t+k); split; [lia|]. exists c; split; [rewrite stepn_add,Hstart; exact Hr|exact Hq].
Qed.
End Abstract.
