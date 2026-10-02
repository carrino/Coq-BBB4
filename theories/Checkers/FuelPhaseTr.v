(** * FuelPhaseTr: parity-indexed tail grammars for transition recurrence.

    Each node records the head position parity. Left and right tail
    grammars distinguish the parity of the window's nearest cell. Both
    move directions toggle the head parity, so donated windows use the
    opposite parity and newly consumed windows use the old head parity.

    Covering also retains FuelWide's ordinary invariant over the union
    of the two grammars. Thus the existing fuel and exact pattern-count
    proofs apply unchanged; only the parity-filtered successor and the
    tail invariant preservation require new proofs. Gram sets and node
    certificates are supplied as untrusted data and fully checked. *)
From Coq Require Import Arith Lia Bool List ZArith.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape PosEnc
  Records Closure.
From BBB4.Checkers Require Import ExactClosure NGram NGramTr Fuel FuelClass
  FuelWide FuelSCCTr FuelWideTr FuelMixTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
Import ListNotations.

Fixpoint phase_at (p : bool) (d : nat) : bool :=
  match d with 0 => p | S k => negb (phase_at p k) end.

Lemma phase_at_flip : forall p d,
  phase_at (negb p) d = negb (phase_at p d).
Proof. intros p d. induction d; simpl; [reflexivity|now rewrite IHd]. Qed.
Lemma phase_at_cancel : forall p d, phase_at (negb p) (S d) = phase_at p d.
Proof. intros. simpl. rewrite phase_at_flip, negb_involutive. reflexivity. Qed.

Lemma phase_at_two : forall p d, phase_at p (S (S d)) = phase_at p d.
Proof. intros. simpl. apply negb_involutive. Qed.

Definition phasesets : Type := bool -> gset.
Definition phase_union (s : phasesets) : gset := PositiveSet.union (s false) (s true).
Definition phase_tail (n : nat) (sets : phasesets) (p : bool) (f : nat -> Sym) :=
  forall d, 1 <= d -> gmem (win f d n) (sets (phase_at p (S d))) = true.

Definition phaseconf : Type := (fcconf * bool)%type.
Definition phase_enc (a : phaseconf) : positive :=
  if snd a then (fcconf_enc (fst a))~1 else (fcconf_enc (fst a))~0.
Lemma phase_enc_inj : forall a b, phase_enc a = phase_enc b -> a = b.
Proof.
  intros [a p] [b q]. destruct p,q; unfold phase_enc; simpl; intro H;
    try discriminate; injection H as H; apply fcconf_enc_inj in H; now subst.
Qed.
Definition phase_instr (a : phaseconf) : Instr := fw_instr (fst a).
Definition phase_covers (n : nat) (ls rs : phasesets) (a : phaseconf) (c : ExecState) :=
  fw_covers n (phase_union ls) (phase_union rs) (fst a) c /\
  phase_tail n ls (snd a) (t_left (snd c)) /\
  phase_tail n rs (snd a) (t_right (snd c)).
Lemma phase_covers_instr : forall n ls rs a c,
  phase_covers n ls rs a c -> phase_instr a = instr_of c.
Proof. intros n ls rs a c [H _]. apply (fw_covers_instr _ _ _ _ _ H). Qed.

Definition phase_accept (d : Dir) (ls rs : phasesets) (p : bool) (a : fcconf) : bool :=
  let '(_, (lw, _, rw)) := fst a in
  match d with DL => gmem lw (ls p) | DR => gmem rw (rs p) end.
Definition phase_succs (tm : TM) (ls rs : phasesets) (a : phaseconf)
    : option (list phaseconf) :=
  let '(base, p) := a in
  let '(q, (lw, s, rw)) := fst base in
  match tm q s with
  | None => None
  | Some tr =>
    if match t_dir tr with
       | DL => gmem rw (rs (negb p))
       | DR => gmem lw (ls (negb p))
       end
    then match fw_succs tm (phase_union ls) (phase_union rs) base with
         | None => None
         | Some sl => Some (map (fun b => (b, negb p))
                                 (filter (phase_accept (t_dir tr) ls rs p) sl))
         end
    else None
  end.

Lemma phase_succs_sound : forall tm n ls rs a c,
  1 <= n -> phase_covers n ls rs a c ->
  match phase_succs tm ls rs a, step tm c with
  | Some l, Some c' => exists a', In a' l /\ phase_covers n ls rs a' c'
  | Some _, None => False
  | None, _ => True
  end.
Proof.
  intros tm n ls rs [[[q [[lw s] rw]] [fl fr]] p] [qc [L h R]] Hn [Hfw [HL HR]].
  cbn [fst snd] in Hfw, HL, HR.
  pose proof Hfw as Hbase.
  destruct Hbase as [[Hq [Hh [Hlw [Hrw _]]]] _].
  cbn [fst snd t_head t_left t_right] in Hq, Hh, Hlw, Hrw.
  subst qc h lw rw.
  unfold phase_succs; cbn [fst snd].
  destruct (tm q s) as [tr|] eqn:Etr; [|exact I].
  destruct (t_dir tr) eqn:Ed.
  - destruct (gmem (win R 0 n) (rs (negb p))) eqn:Egr; [|exact I].
    cbn [fst snd].
    match goal with
    | |- context [fw_succs ?tt ?ll ?rr ?aa] =>
      pose proof (fw_succs_sound tt n ll rr aa (q, mkTape L s R) Hn Hfw) as Hsound;
      destruct (fw_succs tt ll rr aa) as [sl|] eqn:Es
    end; [|exact I].
    assert (Estep : step tm (q, mkTape L s R) = Some (t_next tr,
      mkTape (tail_side L) (L 0) (push_side (t_write tr) R))).
    { unfold step; simpl. rewrite Etr, Ed. reflexivity. }
    rewrite Estep in Hsound |- *.
    destruct Hsound as (b & Hb & Hbc).
    exists (b, negb p). split.
    + apply in_map_iff. exists b. split; [reflexivity|].
      apply filter_In. split; [assumption|].
      destruct b as [[qb [[lwb sb] rwb]] [flb frb]].
      destruct Hbc as [[_ [_ [Hlb _]]] _].
      cbn [fst snd t_left] in Hlb.
      cbn [phase_accept fst]. rewrite Hlb, win_tail.
      specialize (HL 1 ltac:(lia)). cbn [phase_at] in HL.
      now rewrite negb_involutive in HL.
    + split; [exact Hbc|]. cbn [fst snd t_left t_right]. split.
      * intros d Hd. rewrite win_tail, phase_at_cancel.
        rewrite <- (phase_at_two p d).
        apply HL. lia.
      * intros d Hd. destruct d as [|d]; [lia|].
        rewrite win_push_S, phase_at_cancel.
        destruct d as [|d].
        -- exact Egr.
        -- apply HR. lia.
  - destruct (gmem (win L 0 n) (ls (negb p))) eqn:Egl; [|exact I].
    cbn [fst snd].
    match goal with
    | |- context [fw_succs ?tt ?ll ?rr ?aa] =>
      pose proof (fw_succs_sound tt n ll rr aa (q, mkTape L s R) Hn Hfw) as Hsound;
      destruct (fw_succs tt ll rr aa) as [sl|] eqn:Es
    end; [|exact I].
    assert (Estep : step tm (q, mkTape L s R) = Some (t_next tr,
      mkTape (push_side (t_write tr) L) (R 0) (tail_side R))).
    { unfold step; simpl. rewrite Etr, Ed. reflexivity. }
    rewrite Estep in Hsound |- *.
    destruct Hsound as (b & Hb & Hbc).
    exists (b, negb p). split.
    + apply in_map_iff. exists b. split; [reflexivity|].
      apply filter_In. split; [assumption|].
      destruct b as [[qb [[lwb sb] rwb]] [flb frb]].
      destruct Hbc as [[_ [_ [_ [Hrb _]]]] _].
      cbn [fst snd t_right] in Hrb.
      cbn [phase_accept fst]. rewrite Hrb, win_tail.
      specialize (HR 1 ltac:(lia)). cbn [phase_at] in HR.
      now rewrite negb_involutive in HR.
    + split; [exact Hbc|]. cbn [fst snd t_left t_right]. split.
      * intros d Hd. destruct d as [|d]; [lia|].
        rewrite win_push_S, phase_at_cancel.
        destruct d as [|d].
        -- exact Egl.
        -- apply HL. lia.
      * intros d Hd. rewrite win_tail, phase_at_cancel.
        rewrite <- (phase_at_two p d).
        apply HR. lia.
Qed.

Definition phase_moves_right (tm : TM) (a : phaseconf) := fwnode_moves_right tm (fst a).
Definition phase_rfuel (a : phaseconf) := fwnode_rfuel_ge1 (fst a).
Lemma phase_moves_right_sound : forall tm n ls rs a c,
  phase_moves_right tm a = true -> phase_covers n ls rs a c -> steps_right tm c.
Proof. intros tm n ls rs a c H [Hc _]. eapply fwnode_moves_right_sound; eauto. Qed.
Lemma phase_rfuel_sound : forall n ls rs a c,
  phase_rfuel a = true -> phase_covers n ls rs a c -> has_right_nonblank (snd c).
Proof. intros n ls rs a c H [Hc _]. eapply fwnode_rfuel_ge1_sound; eauto. Qed.

Definition phase_pmap_get (m : PositiveMap.tree nat) (a : phaseconf) : nat :=
  match PositiveMap.find (phase_enc a) m with Some v => v | None => 0 end.
Definition phase_comp_denote (tm : TM) (n : nat) (c : fmxcomp) : lexcomp phaseconf :=
  match c with
  | FMRankE phi => LexRank phaseconf (phase_pmap_get (pmape_of phi))
  | FMPattSumE terms K phi gate =>
      if fmx_ok n terms then
        let pm := pmape_of phi in
        let gs := psete_of gate in
        LexMeas phaseconf (fmx_val terms)
          (fun a a' => fmx_delta tm terms (fst (fst a)) (fst (fst a'))) K
          (phase_pmap_get pm) (fun a => PositiveSet.mem (phase_enc a) gs)
      else LexRank phaseconf (fun _ => 0)
  end.
Definition phase_cert_denote (tm : TM) (n : nat)
    (ct : list fmxcomp * list positive)
    : list (lexcomp phaseconf) * (phaseconf -> bool) :=
  (map (phase_comp_denote tm n) (fst ct),
   let gs := psete_of (snd ct) in fun a => PositiveSet.mem (phase_enc a) gs).
Lemma phase_comp_exact : forall tm n ls rs c,
  comp_exact tm phaseconf (phase_succs tm ls rs) (phase_covers n ls rs)
    (phase_comp_denote tm n c).
Proof.
  intros tm n ls rs [phi | terms K phi gate]; simpl; [exact I|].
  destruct (fmx_ok n terms) eqn:Hok; [|exact I].
  intros a cc a' cc' sl Hca Hca' Hstep Es HInl.
  exact (fmx_exact tm n (phase_union ls) (phase_union rs) terms
    (fst (fst a)) cc (fst (fst a')) cc' Hok (proj1 (proj1 Hca)) Hstep).
Qed.

Definition phase_seed_ok (n : nat) (ls rs : phasesets) : bool :=
  ng_seed_ok n (phase_union ls) (phase_union rs) c0 &&
  forallb (fun p => gmem (repeat S0 n) (ls p) && gmem (repeat S0 n) (rs p))
    [false; true].
Lemma phase_seed_sound : forall n ls rs,
  phase_seed_ok n ls rs = true ->
  phase_covers n ls rs (fw_start n c0, false) (lift c0).
Proof.
  intros n ls rs H. apply andb_prop in H as [Hng Hp].
  assert (Hblank : forall p, gmem (repeat S0 n) (ls p) = true /\
                            gmem (repeat S0 n) (rs p) = true).
  { intros p. apply andb_prop.
    rewrite forallb_forall in Hp. apply Hp. destruct p; simpl; auto. }
  split; [apply fw_start_covers; exact Hng|]. split; intros d Hd.
  - change (gmem (win (lift_side []) d n) (ls (phase_at false (S d))) = true).
    rewrite win_blank by (simpl; lia). apply Hblank.
  - change (gmem (win (lift_side []) d n) (rs (phase_at false (S d))) = true).
    rewrite win_blank by (simpl; lia). apply Hblank.
Qed.

Definition phase_sets (grams0 grams1 : list (list Sym)) : phasesets :=
  fun p => gadds (if p then grams1 else grams0) gempty.
Definition ngram_check_neverqh_phase2tr (tm : TM) (n fuel : nat)
    (l0 l1 r0 r1 : list (list Sym))
    (cert : Instr -> list fmxcomp * list positive) : bool :=
  let ls := phase_sets l0 l1 in
  let rs := phase_sets r0 r1 in
  (1 <=? n) && phase_seed_ok n ls rs &&
  closure_check_neverqh_fuelscctr tm phaseconf phase_enc phase_instr
    (phase_succs tm ls rs) (phase_moves_right tm) phase_rfuel
    0 fuel (fw_start n c0, false) (fun q => phase_cert_denote tm n (cert q)).

Theorem ngram_check_neverqh_phase2tr_sound : forall tm n fuel l0 l1 r0 r1 cert,
  ngram_check_neverqh_phase2tr tm n fuel l0 l1 r0 r1 cert = true ->
  NeverQuasiHaltsTr tm.
Proof.
  intros tm n fuel l0 l1 r0 r1 cert H.
  unfold ngram_check_neverqh_phase2tr in H.
  apply andb_prop in H as [H Hcheck]. apply andb_prop in H as [Hn Hseed].
  apply Nat.leb_le in Hn.
  apply (closure_check_neverqh_fuelscctr_sound tm phaseconf phase_enc phase_instr
    (phase_succs tm (phase_sets l0 l1) (phase_sets r0 r1))
    (phase_moves_right tm) phase_rfuel
    (phase_covers n (phase_sets l0 l1) (phase_sets r0 r1))) in Hcheck;
    [assumption | | | | | | |].
  - exact phase_enc_inj.
  - intros a c Hc. eapply phase_covers_instr; eauto.
  - intros a c Hc. apply phase_succs_sound; assumption.
  - intros a c Hmv Hc. eapply phase_moves_right_sound; eauto.
  - intros a c Hrf Hc. eapply phase_rfuel_sound; eauto.
  - intros ct Hct. cbn [csteps] in Hct. injection Hct as <-.
    apply phase_seed_sound. exact Hseed.
  - intros q. apply Forall_forall. intros comp Hin.
    cbn [phase_cert_denote fst] in Hin.
    apply in_map_iff in Hin. destruct Hin as (c & <- & _).
    apply phase_comp_exact.
Qed.
