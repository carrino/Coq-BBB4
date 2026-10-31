From Coq Require Import Arith Lia Bool List NArith.
From BBB24 Require Import Statement StatementTr CTape Spec Bounds CycleCensus.
Import ListNotations.
Section Parameters.
Variables bs bi : N.

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
  k <= N.to_nat bs -> k <= N.to_nat bi -> stepn tm k InitES = None -> Bounds bs bi tm.
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

Definition st_index q := match q with StA=>0 | StB=>1 end.
Definition sym_index s := match s with S0=>0 | S1=>1 | S2=>2 | S3=>3 end.
Definition nat_trans v : option Trans :=
  if v<?16 then Some (mkTrans
    (match v/4 with 0=>S0 | 1=>S1 | 2=>S2 | _=>S3 end)
    (if Nat.even (v/2) then DL else DR)
    (if Nat.eqb (v mod 2) 0 then StA else StB)) else None.
Lemma codes_complete : forall tr, exists v, In v (seq 0 16) /\ nat_trans v=Some tr.
Proof.
  intros [s d q]. exists (4*sym_index s + (match d with DL=>0 | DR=>2 end) + st_index q).
  destruct s,d,q.
  all: split; [apply in_seq; cbn; lia|reflexivity].
Qed.

Inductive Cert := Invalid | Deferred | Branch (n:nat) (children:list Cert)
  | Cycle (mirrored:bool) (t p W:nat).
Fixpoint verify depth tm cert : bool :=
  match depth with
  | 0=>false
  | S d=>match cert with
    | Invalid=>false | Deferred=>true
    | Cycle m t p W=>cycle_check bs bi tm m t p W
    | Branch n cs=>
      if (N.of_nat n <? N.min bs bi)%N then
        match csteps tm n c0 with
        | Some(q,(l,h,r))=>match tm q h with
          | None=>forallb (fun v=>verify d (update tm q h (nat_trans v)) (nth v cs Invalid)) (seq 0 16)
          | Some _=>false end
        | None=>false end
      else false end
  end.
(** Deferred leaves represent ALL completions of that partial table. *)
Fixpoint residue depth tm cert : list TM :=
  match depth with
  | 0=>[]
  | S d=>match cert with
    | Deferred=>[tm]
    | Branch n cs=>match csteps tm n c0 with
      | Some(q,(l,h,r))=>concat (map (fun v=>residue d (update tm q h (nat_trans v)) (nth v cs Invalid)) (seq 0 16))
      | None=>[] end
    | _=>[] end
  end.
Definition Pending (xs:list TM) tm := exists leaf, In leaf xs /\ TM_le leaf tm.

Theorem verify_cover : forall depth tm cert,
  verify depth tm cert=true -> forall complete, TM_le tm complete ->
  Bounds bs bi complete \/ Pending (residue depth tm cert) complete.
Proof.
  induction depth as [|d IH]; intros tm cert H complete Hle; [discriminate|].
  destruct cert as [| |n cs|m t p W]; cbn [verify residue] in *; try discriminate.
  - right. exists tm. split; [left; reflexivity|exact Hle].
  - destruct (N.of_nat n <? N.min bs bi)%N eqn:Hn; [|discriminate].
    apply N.ltb_lt in Hn.
    destruct (csteps tm n c0) as [[q[[l h]r]]|] eqn:Et; [|discriminate].
    destruct (tm q h) as [tr|] eqn:E; [discriminate|].
    destruct (complete q h) as [tr'|] eqn:E'.
    + destruct (codes_complete tr') as (v&Hv&Htr).
      rewrite forallb_forall in H. specialize (H v Hv).
      assert (Hext: TM_le (update tm q h (nat_trans v)) complete).
      { eapply update_le; [exact Hle|exact E|]. now rewrite Htr. }
      destruct (IH _ _ H complete Hext) as [Hb|(leaf&Hin&Hleaf)]; [left;exact Hb|].
      right. exists leaf; split; [|exact Hleaf].
      apply in_concat. exists (residue d (update tm q h (nat_trans v)) (nth v cs Invalid)).
      split; [apply in_map_iff; exists v; auto|exact Hin].
    + left. apply (halt_bounds complete (S n)).
      * pose proof (N.le_min_l bs bi); lia.
      * pose proof (N.le_min_r bs bi); lia.
      * assert (Hr:stepn complete n InitES=Some(lift(q,(l,h,r)))).
        { eapply extend_steps; [exact Hle|]. rewrite <-lift_c0; apply csteps_lift; exact Et. }
        replace (S n) with (n+1) by lia. rewrite stepn_add,Hr.
        cbn [stepn step lift lift_tape fst snd t_head]. rewrite E'; reflexivity.
  - left. apply cycle_check_sound in H as [Hnh Hb]. eapply extend_bounds; eauto.
Qed.
Corollary census_coverage : forall depth cert,
  verify depth empty cert=true -> forall tm,
  Bounds bs bi tm \/ Pending (residue depth empty cert) tm.
Proof.
  intros depth cert H tm. eapply verify_cover; [exact H|]. intros q s; left; reflexivity.
Qed.
Corollary census_upper_if_residue : forall depth cert,
  verify depth empty cert=true ->
  (forall tm,Pending (residue depth empty cert) tm->Bounds bs bi tm) ->
  forall tm,Bounds bs bi tm.
Proof.
  intros depth cert H Hr tm. destruct (census_coverage _ _ H tm); auto.
Qed.
End Parameters.

(** Finite table-family bookkeeping. A branch fixes one previously undefined
    cell: one halting choice plus sixteen defined transition choices. *)
Fixpoint table_count slots : N :=
  match slots with 0=>1%N | S k=>(17*table_count k)%N end.
Definition add_counts (a b:N*N) := ((fst a+fst b)%N,(snd a+snd b)%N).
Fixpoint counts slots cert : N*N :=
  match cert with
  | Invalid=>(0,0)%N | Deferred=>(0,table_count slots)%N
  | Cycle _ _ _ _=>(table_count slots,0)%N
  | Branch _ cs=>match slots with
    | 0=>(0,0)%N
    | S k=>fold_right add_counts (table_count k,0)%N
      (map (fun v=>counts k (nth v cs Invalid)) (seq 0 16)) end
  end.
