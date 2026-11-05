(** Binary-fuel finite scans. No unary fuel is evaluated by the checker. *)
From Coq Require Import Arith Lia Bool List NArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Checkers Require Import TCyclerN.

Definition scan_body (tm : TM) (hit : cconf -> bool)
    (s : option cconf * bool) : option cconf * bool :=
  match s with
  | (Some c, seen) => (cstep tm c, seen || hit c)
  | (None, seen) => (None, seen)
  end.
Definition scanN tm hit (n : N) (c : cconf) :=
  N.iter n (scan_body tm hit) (Some c, false).

Fixpoint visits (tm : TM) (hit : cconf -> bool) (n : nat) (c : cconf) : bool :=
  match n with
  | 0 => false
  | S m => hit c || match cstep tm c with
                    | Some d => visits tm hit m d | None => false end
  end.

Lemma scan_fst : forall tm hit n oc b,
  fst (Nat.iter n (scan_body tm hit) (oc,b)) =
  match oc with Some c => csteps tm n c | None => None end.
Proof.
  intros tm hit n; induction n; intros oc b.
  - destruct oc; reflexivity.
  - rewrite Nat.iter_succ_r. destruct oc as [c|]; cbn [scan_body].
    + rewrite IHn. simpl. destruct (cstep tm c); reflexivity.
    + apply IHn.
Qed.
Lemma scan_snd : forall tm hit n oc b,
  snd (Nat.iter n (scan_body tm hit) (oc,b)) =
  b || match oc with Some c => visits tm hit n c | None => false end.
Proof.
  intros tm hit n; induction n; intros oc b.
  - destruct oc; simpl; now rewrite orb_false_r.
  - rewrite Nat.iter_succ_r. destruct oc as [c|]; cbn [scan_body].
    + rewrite IHn. cbn [visits].
      destruct (cstep tm c); rewrite ?orb_assoc; reflexivity.
    + rewrite IHn. now rewrite orb_false_r.
Qed.
Lemma scanN_fst : forall tm hit n c,
  fst (scanN tm hit n c) = csteps tm (N.to_nat n) c.
Proof. intros; unfold scanN; rewrite N2Nat.inj_iter, scan_fst; reflexivity. Qed.
Lemma scanN_snd : forall tm hit n c,
  snd (scanN tm hit n c) = visits tm hit (N.to_nat n) c.
Proof. intros; unfold scanN; rewrite N2Nat.inj_iter, scan_snd; reflexivity. Qed.
Lemma visits_complete : forall tm hit n c i d,
  i < n -> csteps tm i c = Some d -> hit d = true -> visits tm hit n c = true.
Proof.
  intros tm hit n; induction n; intros c i d Hi Hs Hh; [lia|].
  simpl. destruct i.
  - simpl in Hs. injection Hs as <-. rewrite Hh. reflexivity.
  - simpl in Hs. destruct (cstep tm c) eqn:E; [|discriminate].
    apply orb_true_intro; right. eapply IHn; eauto; lia.
Qed.

(** The scan checks indices [B,B+L) and its final configuration at B+L. *)
Definition first_hitN tm hit (B L : N) : bool :=
  match cstepsN tm B c0 with
  | None => false
  | Some c =>
      let '(oc,seen) := scanN tm hit L c in
      negb seen && match oc with Some d => hit d | None => false end
  end.

Theorem first_hitN_sound : forall tm hit B L,
  first_hitN tm hit B L = true ->
  (exists d, csteps tm (N.to_nat B + N.to_nat L) c0 = Some d /\ hit d = true) /\
  (forall n d, N.to_nat B <= n < N.to_nat B + N.to_nat L ->
     csteps tm n c0 = Some d -> hit d = false).
Proof.
  intros tm hit B L H. unfold first_hitN in H.
  rewrite cstepsN_nat in H.
  destruct (csteps tm (N.to_nat B) c0) as [c|] eqn:HB; [|discriminate].
  destruct (scanN tm hit L c) as [oc seen] eqn:HS.
  apply andb_true_iff in H as [Hseen Hhit].
  apply negb_true_iff in Hseen.
  pose proof (scanN_fst tm hit L c) as HF.
  pose proof (scanN_snd tm hit L c) as HV.
  rewrite HS in HF, HV. simpl in HF, HV. rewrite Hseen in HV.
  destruct oc as [d|]; [|discriminate]. split.
  - exists d. split; [rewrite csteps_add, HB; symmetry; exact HF|exact Hhit].
  - intros n e Hn HE. replace n with (N.to_nat B + (n-N.to_nat B)) in HE by lia.
    rewrite csteps_add, HB in HE.
    destruct (hit e) eqn:E; [|reflexivity].
    assert (visits tm hit (N.to_nat L) c = true).
    { eapply visits_complete; eauto; lia. }
    congruence.
Qed.
