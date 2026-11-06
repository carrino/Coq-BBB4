(** First visits are bounded by the global LAST-visit value.
    Stopping on first observation stays on the same four-state carrier.
    This says nothing about return times of previously visited targets. *)
From Coq Require Import Arith Lia Bool.
From BBB4 Require Import BBB4_Statement BBB4_Spec BBBT4_Statement BBBT4_Spec.
From BBB4.Census Require Import TNF_QH.

Definition stop_when (tm : TM) (hit : St -> Sym -> bool) : TM :=
 fun q a=>if hit q a then None else tm q a.
Definition config_hit (hit : St -> Sym -> bool) (c : ExecState) := hit (fst c) (t_head (snd c)).
Definition stop_state tm target := stop_when tm (fun q _=>st_eqb q target).
Definition stop_instruction tm target := stop_when tm (fun q a=>instr_eqb (q,a) target).

Lemma stop_when_le : forall tm hit, TM_le (stop_when tm hit) tm.
Proof.
 intros tm hit q a; unfold stop_when; destruct(hit q a); [left|right]; reflexivity.
Qed.

Lemma stopped_first_hit : forall tm hit n c cq,
 stepn tm n c=Some cq -> config_hit hit cq=true ->
 exists k ck, k<=n /\ stepn (stop_when tm hit) k c=Some ck /\ config_hit hit ck=true.
Proof.
 intros tm hit n; induction n as [|n IH]; intros c cq HR HQ.
 - cbn [stepn] in HR; injection HR as <-; exists 0,c; auto.
 - destruct (config_hit hit c) eqn:HC.
   + exists 0,c; split; [lia|]; split; [reflexivity|exact HC].
   + cbn [stepn] in HR; destruct(step tm c) as [c1|] eqn:HS; [|discriminate].
     destruct(IH c1 cq HR HQ) as(k & ck & Hk & HK & HH).
     exists(S k),ck; split; [lia|]; split; [|exact HH].
     cbn [stepn].
     assert(HS' : step (stop_when tm hit) c=Some c1).
     { destruct c as[q tp]; unfold config_hit in HC; cbn [fst snd] in HC.
       unfold step,stop_when; cbn; rewrite HC; exact HS. }
     rewrite HS'; exact HK.
Qed.

Lemma stopped_hit_halts : forall tm hit k c,
 stepn (stop_when tm hit) k InitES=Some c -> config_hit hit c=true ->
 forall n, k<n -> stepn (stop_when tm hit) n InitES=None.
Proof.
 intros tm hit k [q tp] HK HH n Hn.
 replace n with(k+S(n-k-1)) by lia; rewrite stepn_add,HK.
 cbn [stepn]; unfold step,stop_when; cbn; unfold config_hit in HH; cbn [fst snd] in HH.
 rewrite HH; reflexivity.
Qed.

Lemma stopped_hit_last_state : forall tm hit k c,
 stepn (stop_when tm hit) k InitES=Some c -> config_hit hit c=true ->
 QuietAfter (stop_when tm hit) (fst c) k.
Proof.
 intros tm hit k c HK HH; split.
 - exists c; auto.
 - intros n Hn (cn & Hrun & _).
   rewrite (stopped_hit_halts tm hit k c HK HH n Hn) in Hrun; discriminate.
Qed.
Lemma stopped_hit_last_instruction : forall tm hit k c,
 stepn (stop_when tm hit) k InitES=Some c -> config_hit hit c=true ->
 QuietAfterTr (stop_when tm hit) (instr_of c) k.
Proof.
 intros tm hit k c HK HH; split.
 - exists c; auto.
 - intros n Hn (cn & Hrun & _).
   rewrite (stopped_hit_halts tm hit k c HK HH n Hn) in Hrun; discriminate.
Qed.

Theorem first_hit_before_BBB : forall B, BBB4_is B -> forall tm hit,
 (exists n c, stepn tm n InitES=Some c /\ config_hit hit c=true) ->
 exists k c, k<B /\ stepn tm k InitES=Some c /\ config_hit hit c=true.
Proof.
 intros B [_ Hmax] tm hit(n & c & HR & HH).
 destruct(stopped_first_hit tm hit n InitES c HR HH) as(k & ck & _ & HK & HHk).
 assert(Hscore : Attains (stop_when tm hit) (S k)).
 { exists(fst ck),k; split; [eapply stopped_hit_last_state; eauto|reflexivity]. }
 pose proof(Hmax _ _ Hscore) as Hbound.
 exists k,ck; split; [lia|]; split; [eapply TM_le_stepn; [apply stop_when_le|exact HK]|exact HHk].
Qed.
Theorem first_hit_before_BBBT : forall B, BBBT4_is B -> forall tm hit,
 (exists n c, stepn tm n InitES=Some c /\ config_hit hit c=true) ->
 exists k c, k<B /\ stepn tm k InitES=Some c /\ config_hit hit c=true.
Proof.
 intros B [_ Hmax] tm hit(n & c & HR & HH).
 destruct(stopped_first_hit tm hit n InitES c HR HH) as(k & ck & _ & HK & HHk).
 assert(Hscore : AttainsTr (stop_when tm hit) (S k)).
 { exists(instr_of ck),k; split; [eapply stopped_hit_last_instruction; eauto|reflexivity]. }
 pose proof(Hmax _ _ Hscore) as Hbound.
 exists k,ck; split; [lia|]; split; [eapply TM_le_stepn; [apply stop_when_le|exact HK]|exact HHk].
Qed.

Theorem visited_before_BBB : forall B, BBB4_is B -> forall tm q,
 Visited tm q -> exists t, t<B /\ VisitsAt tm q t.
Proof.
 intros B HB tm q(n & c & HR & Hq).
 assert(HH : config_hit (fun s _=>st_eqb s q) c=true).
 { unfold config_hit; rewrite Hq; apply st_eqb_spec; reflexivity. }
 destruct(first_hit_before_BBB B HB tm (fun s _=>st_eqb s q)
   (ex_intro _ n (ex_intro _ c (conj HR HH)))) as(t & ct & Ht & HT & HHt).
 exists t; split; [exact Ht|exists ct; split; [exact HT|]].
 unfold config_hit in HHt; apply st_eqb_spec in HHt; exact HHt.
Qed.

Corollary no_early_state_means_never : forall B, BBB4_is B -> forall tm q,
 (forall n,n<B -> ~VisitsAt tm q n) -> forall n,~VisitsAt tm q n.
Proof.
 intros B HB tm q Hnone n HV.
 destruct(visited_before_BBB B HB tm q (ex_intro _ n HV)) as(t & Ht & HT).
 exact(Hnone t Ht HT).
Qed.

Theorem fired_before_BBBT : forall B, BBBT4_is B -> forall tm ins,
 FiredTr tm ins -> exists t,t<B /\ FiresAt tm ins t.
Proof.
 intros B HB tm ins(n & c & HR & Hq).
 assert(HH : config_hit (fun s a=>instr_eqb(s,a) ins) c=true).
 { change(instr_eqb(instr_of c) ins=true); apply instr_eqb_spec; exact Hq. }
 destruct(first_hit_before_BBBT B HB tm (fun s a=>instr_eqb(s,a) ins)
   (ex_intro _ n (ex_intro _ c (conj HR HH)))) as(t & ct & Ht & HT & HHt).
 exists t; split; [exact Ht|exists ct; split; [exact HT|]].
 change(instr_eqb(instr_of ct) ins=true) in HHt; now apply instr_eqb_spec in HHt.
Qed.
Corollary no_early_instruction_means_never : forall B, BBBT4_is B -> forall tm ins,
 (forall n,n<B -> ~FiresAt tm ins n) -> forall n,~FiresAt tm ins n.
Proof.
 intros B HB tm ins Hnone n HV.
 destruct(fired_before_BBBT B HB tm ins (ex_intro _ n HV)) as(t & Ht & HT).
 exact(Hnone t Ht HT).
Qed.

(** In fact the state-level global bound alone also bounds first instruction
    observations, since stopping there gives a last STATE visit as well. *)
Corollary fired_before_state_BBB : forall B, BBB4_is B -> forall tm ins,
 FiredTr tm ins -> exists t,t<B /\ FiresAt tm ins t.
Proof.
 intros B HB tm ins(n & c & HR & Hq).
 assert(HH : config_hit (fun s a=>instr_eqb(s,a) ins) c=true).
 { change(instr_eqb(instr_of c) ins=true); apply instr_eqb_spec; exact Hq. }
 destruct(first_hit_before_BBB B HB tm (fun s a=>instr_eqb(s,a) ins)
   (ex_intro _ n (ex_intro _ c (conj HR HH)))) as(t & ct & Ht & HT & HHt).
 exists t; split; [exact Ht|exists ct; split; [exact HT|]].
 change(instr_eqb(instr_of ct) ins=true) in HHt; now apply instr_eqb_spec in HHt.
Qed.

Print Assumptions visited_before_BBB.
Print Assumptions no_early_state_means_never.
Print Assumptions fired_before_BBBT.
Print Assumptions fired_before_state_BBB.

Module FirstVisitRegression.
Definition alternating : TM := fun q _=>Some(mkTrans S0 DR
 (match q with StA=>StB|_=>StA end)).
Definition at_B := (StB,tape_move DR S0 (snd InitES)).
Example stop_B_preserves_first_visit : stepn (stop_state alternating StB) 1 InitES=Some at_B.
Proof. reflexivity. Qed.
Example stop_B_halts_immediately_after : stepn (stop_state alternating StB) 2 InitES=None.
Proof. reflexivity. Qed.
Example stopped_B_last_score_is_two : Attains (stop_state alternating StB) 2.
Proof.
 exists StB,1; split; [|reflexivity].
 exact(stopped_hit_last_state alternating (fun q _=>st_eqb q StB) 1 at_B eq_refl eq_refl).
Qed.
Example original_can_return_later : VisitsAt alternating StB 3.
Proof. eexists; split; reflexivity. Qed.
Example instruction_stop_at_initial_configuration :
 stepn (stop_instruction alternating (StA,S0)) 1 InitES=None.
Proof. reflexivity. Qed.
Example first_B_strictly_before_any_global_bound : forall B, BBB4_is B ->
 exists t,t<B /\ VisitsAt alternating StB t.
Proof.
 intros B HB; apply(visited_before_BBB B HB alternating StB).
 exists 1; eexists; split; reflexivity.
Qed.

(** A target may already have been visited and then remain silent forever.
    The first-visit theorem does not turn such post-cutoff silence into a
    never-visited classification. *)
Definition quiet_A : TM := fun _ _=>Some(mkTrans S0 DR StB).
Example quiet_A_was_visited : Visited quiet_A StA.
Proof. exists 0,InitES; split; reflexivity. Qed.
Example quiet_A_is_eventually_silent : QuietAfter quiet_A StA 0.
Proof.
 split; [exists InitES; split; reflexivity|].
 intros n Hn (c & HR & Hq).
 replace n with((n-1)+1) in HR by lia; rewrite stepn_add in HR.
 destruct(stepn quiet_A (n-1) InitES) as [[s tp]|] eqn:HP; [|discriminate].
 cbn [stepn step quiet_A] in HR; injection HR as <-; discriminate Hq.
Qed.
End FirstVisitRegression.
