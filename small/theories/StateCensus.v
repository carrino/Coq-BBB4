From Coq Require Import Arith Lia Bool List.
From SmallBB Require Import Statement StatementTr CTape Bounds Size Census StateCheckers CycleCensus FiniteCensus HistCensus.
Import ListNotations.
Lemma extend_state_bound : forall bs tm tm',
 NonHalt tm -> QHBound bs tm -> TM_le tm tm' -> QHBound bs tm'.
Proof.
 intros bs tm tm' Hnh Hb Hle q s [Hv Hq]. apply (Hb q s).
 assert (Hr:forall k,stepn tm' k InitES=stepn tm k InitES) by (apply extend_run; assumption).
 split.
 - destruct Hv as (c & Hc & Hcq); exists c; rewrite <-Hr; auto.
 - intros k Hk (c & Hc & Hcq). apply (Hq k Hk); exists c; rewrite Hr; auto.
Qed.
Section Parameters.
Variable ns ms bs : nat.
Fixpoint verify_state (depth : nat) (tm : TM) (cert : Cert) : bool :=
  match depth with
  | 0 => false
  | S d => match cert with
    | Invalid => false
    | Cycle m t p W => cycle_check bs (t+p+1) tm m t p W
    | NGram n t => ng_state_check bs tm n t 4096 32
    | RepWL L T t fuel => rw_state_check bs tm L T t fuel
    | FiniteNGram n t fuel rounds => fn_check_mode true bs bs tm n t fuel rounds
    | HistNGram k n t fuel rounds => hn_check_mode true bs bs tm k n t fuel rounds
    | Branch n children =>
      if n <? bs then
      match csteps tm n c0 with
      | Some (q,(l,h,r)) =>
        match tm q h with
        | Some _ => false
        | None => forallb (fun v => verify_state d (update tm q h (nat_trans ns v))
                                      (nth v children Invalid)) (seq 0 (2*ns*ms))
        end
      | None => false
      end else false
    end
  end.

Hypothesis sizes_ok : supported ns ms.

Theorem verify_state_sound : forall depth tm cert,
  verify_state depth tm cert = true -> forall tm', Admissible ns ms tm' -> TM_le tm tm' -> QHBound bs tm'.
Proof.
  induction depth as [|d IH]; intros tm cert H tm' Had Hle; [discriminate|].
  destruct cert as [|n children|m t p W|n t|L T t fuel|n t fuel rounds|k n t fuel rounds]; cbn [verify_state] in H; try discriminate.
  - destruct (n <? bs) eqn:Hn; [apply Nat.ltb_lt in Hn|discriminate].
    destruct (csteps tm n c0) as [[q [[l h] r]]|] eqn:Et; [|discriminate].
    destruct (tm q h) as [tr|] eqn:E; [discriminate|].
    destruct (tm' q h) as [tr'|] eqn:E'.
    + destruct (codes_complete ns ms sizes_ok tr' (admissible_output ns ms tm' Had q h tr' E')) as (v & Hv & Htr).
      rewrite forallb_forall in H. specialize (H v Hv).
      eapply IH; [exact H|exact Had|]. eapply update_le; [exact Hle|exact E|]. rewrite Htr. exact E'.
    + assert (Hhalt:stepn tm' (S n) InitES=None).
      {
      assert (Hr : stepn tm' n InitES = Some (lift (q,(l,h,r)))).
      { eapply extend_steps; [exact Hle|]. rewrite <- lift_c0. apply csteps_lift; exact Et. }
      replace (S n) with (n+1) by lia. rewrite stepn_add,Hr.
      cbn [stepn step lift lift_tape fst snd t_head]. rewrite E'. reflexivity. }
      exact (proj1 (halt_bounds bs bs tm' (S n) ltac:(lia) ltac:(lia) Hhalt)).
  - apply cycle_check_sound in H as [Hnh [Hb _]]. eapply extend_state_bound; eauto.
  - apply ng_state_check_sound in H as [Hnh Hb]. eapply extend_state_bound; eauto.
  - apply rw_state_check_sound in H as [Hnh Hb]. eapply extend_state_bound; eauto.
  - apply (fn_check_mode_sound true) in H as [Hnh Hb]. eapply extend_state_bound; eauto.
  - apply (hn_check_mode_sound true) in H as [Hnh Hb]. eapply extend_state_bound; eauto.
Qed.

Corollary state_census_complete : forall depth cert,
  verify_state depth empty cert = true -> forall tm, Admissible ns ms tm -> QHBound bs tm.
Proof.
  intros depth cert H tm Had. eapply verify_state_sound; [exact H|exact Had|]. intros q s. left; reflexivity.
Qed.

End Parameters.
