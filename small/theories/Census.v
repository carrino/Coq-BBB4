From Coq Require Import Arith Lia Bool List.
From SmallBB Require Import Statement StatementTr CTape Bounds Size NGramCensus CycleCensus RepWLCensus FiniteCensus HistCensus.
Import ListNotations.
Section Parameters.
Variable ns ms bs bi : nat.

Definition TM_le (tm tm' : TM) :=
  forall q s, tm q s = None \/ tm' q s = tm q s.
Definition update (tm : TM) q s v : TM :=
  fun q' s' => if st_eqb q q' && sym_eqb s s' then v else tm q' s'.
Definition empty : TM := fun _ _ => None.

Lemma extend_step : forall tm tm' c c',
  TM_le tm tm' -> step tm c = Some c' -> step tm' c = Some c'.
Proof.
  intros tm tm' [q tp] c' Hle H. simpl in *.
  destruct (Hle q (t_head tp)) as [E|E]; rewrite E in *; [discriminate|exact H].
Qed.
Lemma extend_steps : forall tm tm' n c c',
  TM_le tm tm' -> stepn tm n c = Some c' -> stepn tm' n c = Some c'.
Proof.
  intros tm tm' n. induction n; intros c c' Hle H; simpl in *; [exact H|].
  destruct (step tm c) as [cm|] eqn:E; [|discriminate].
  rewrite (extend_step tm tm' c cm Hle E). eapply IHn; eauto.
Qed.
Lemma extend_run : forall tm tm', NonHalt tm -> TM_le tm tm' ->
  forall n, stepn tm' n InitES = stepn tm n InitES.
Proof.
  intros tm tm' Hnh Hle n. destruct (stepn tm n InitES) as [c|] eqn:E.
  - eapply extend_steps; eauto.
  - exfalso. exact (Hnh n E).
Qed.
Lemma extend_bounds : forall tm tm',
  NonHalt tm -> Bounds bs bi tm -> TM_le tm tm' -> Bounds bs bi tm'.
Proof.
  intros tm tm' Hnh [Hs Hi] Hle.
  assert (Hv : forall q n, VisitsAt tm' q n <-> VisitsAt tm q n).
  { intros q n. unfold VisitsAt. rewrite (extend_run tm tm' Hnh Hle n). tauto. }
  assert (Hf : forall tg n, FiresAt tm' tg n <-> FiresAt tm tg n).
  { intros tg n. unfold FiresAt. rewrite (extend_run tm tm' Hnh Hle n). tauto. }
  split.
  - intros q s [Hq Hquiet]. apply (Hs q s). split; [apply Hv; exact Hq|].
    intros n Hn Hqn. apply (Hquiet n Hn). apply Hv; exact Hqn.
  - intros tg s [Hq Hquiet]. apply (Hi tg s). split; [apply Hf; exact Hq|].
    intros n Hn Hqn. apply (Hquiet n Hn). apply Hf; exact Hqn.
Qed.
Lemma update_le : forall tm tm' q s tr,
  TM_le tm tm' -> tm q s = None -> tm' q s = tr ->
  TM_le (update tm q s tr) tm'.
Proof.
  intros tm tm' q s tr Hle Hu Hv p a. unfold update.
  destruct (st_eqb q p && sym_eqb s a) eqn:E.
  - apply andb_prop in E as [Eq Ea]. apply st_eqb_spec in Eq.
    apply sym_eqb_spec in Ea. subst p a. right; exact Hv.
  - exact (Hle p a).
Qed.
Lemma halt_bounds : forall tm k,
  k <= bs -> k <= bi -> stepn tm k InitES = None -> Bounds bs bi tm.
Proof.
  intros tm k Hk Hki Hnone.
  assert (Hr : forall n, k <= n -> stepn tm n InitES = None).
  { intros n Hn. replace n with (k+(n-k)) by lia. rewrite stepn_add,Hnone. reflexivity. }
  split; intros q s [(c & Hc & _) _]; destruct (le_lt_dec k s).
  - rewrite (Hr s l) in Hc. discriminate.
  - lia.
  - rewrite (Hr s l) in Hc. discriminate.
  - lia.
Qed.
Inductive Cert := Invalid | Branch (n : nat) (children : list Cert)
  | Cycle (mirrored : bool) (t p W : nat)
  | NGram (n t : nat) | RepWL (L T t fuel : nat) | FiniteNGram (n t fuel rounds : nat) | HistNGram (k n t fuel rounds : nat).
Fixpoint verify (depth : nat) (tm : TM) (cert : Cert) : bool :=
  match depth with
  | 0 => false
  | S d => match cert with
    | Invalid => false
    | Cycle m t p W => cycle_check bs bi tm m t p W
    | NGram n t => ng_check bs bi tm n t 4096 32
    | RepWL L T t fuel => rw_check bs bi tm L T t fuel
    | FiniteNGram n t fuel rounds => fn_check_mode false bs bi tm n t fuel rounds
    | HistNGram k n t fuel rounds => hn_check_mode false bs bi tm k n t fuel rounds
    | Branch n children =>
      if n <? Nat.min bs bi then
      match csteps tm n c0 with
      | Some (q,(l,h,r)) =>
        match tm q h with
        | Some _ => false
        | None => forallb (fun v => verify d (update tm q h (nat_trans ns v))
                                      (nth v children Invalid)) (seq 0 (2*ns*ms))
        end
      | None => false
      end else false
    end
  end.

Hypothesis sizes_ok : supported ns ms.

Theorem verify_sound : forall depth tm cert,
  verify depth tm cert = true -> forall tm', Admissible ns ms tm' -> TM_le tm tm' -> Bounds bs bi tm'.
Proof.
  induction depth as [|d IH]; intros tm cert H tm' Had Hle; [discriminate|].
  destruct cert as [|n children|m t p W|n t|L T t fuel|n t fuel rounds|k n t fuel rounds]; cbn [verify] in H; try discriminate.
  - destruct (n <? Nat.min bs bi) eqn:Hn; [apply Nat.ltb_lt in Hn|discriminate].
    destruct (csteps tm n c0) as [[q [[l h] r]]|] eqn:Et; [|discriminate].
    destruct (tm q h) as [tr|] eqn:E; [discriminate|].
    destruct (tm' q h) as [tr'|] eqn:E'.
    + destruct (codes_complete ns ms sizes_ok tr' (admissible_output ns ms tm' Had q h tr' E')) as (v & Hv & Htr).
      rewrite forallb_forall in H. specialize (H v Hv).
      eapply IH; [exact H|exact Had|]. eapply update_le; [exact Hle|exact E|]. rewrite Htr. exact E'.
    + pose proof (Nat.le_min_l bs bi). pose proof (Nat.le_min_r bs bi).
      apply (halt_bounds tm' (S n)); [lia|lia|].
      assert (Hr : stepn tm' n InitES = Some (lift (q,(l,h,r)))).
      { eapply extend_steps; [exact Hle|]. rewrite <- lift_c0. apply csteps_lift; exact Et. }
      replace (S n) with (n+1) by lia. rewrite stepn_add,Hr.
      cbn [stepn step lift lift_tape fst snd t_head]. rewrite E'. reflexivity.
  - apply cycle_check_sound in H as [Hnh Hb]. eapply extend_bounds; eauto.
  - apply ng_check_sound in H as [Hnh Hb]. eapply extend_bounds; eauto.
  - apply rw_check_sound in H as [Hnh Hb]. eapply extend_bounds; eauto.
  - apply (fn_check_mode_sound false) in H as [Hnh Hb]. eapply extend_bounds; eauto.
  - apply (hn_check_mode_sound false) in H as [Hnh Hb]. eapply extend_bounds; eauto.
Qed.

Corollary census_complete : forall depth cert,
  verify depth empty cert = true -> forall tm, Admissible ns ms tm -> Bounds bs bi tm.
Proof.
  intros depth cert H tm Had. eapply verify_sound; [exact H|exact Had|]. intros q s. left; reflexivity.
Qed.

End Parameters.
