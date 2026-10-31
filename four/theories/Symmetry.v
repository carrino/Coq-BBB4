(** Blank-preserving symbol relabeling.  These six permutations fix the initial
    state and blank symbol, so they preserve every configuration index.  This
    is the semantic transport needed by the exploratory symbol-orbit grouping;
    it does not by itself certify that inventory's enumeration or shadow links. *)
From Coq Require Import Arith Lia List NArith FunctionalExtensionality.
From BBB24 Require Import Statement StatementTr Spec Bounds Census.
Import ListNotations.

(** The digits give the images of symbols 1, 2, and 3, respectively. *)
Inductive SymPerm := P123 | P132 | P213 | P231 | P312 | P321.
Definition all_SymPerm := [P123; P132; P213; P231; P312; P321].
Definition perm_sym (p : SymPerm) (s : Sym) : Sym :=
  match s with
  | S0 => S0
  | S1 => match p with P123 | P132 => S1 | P213 | P231 => S2 | _ => S3 end
  | S2 => match p with P213 | P312 => S1 | P123 | P321 => S2 | _ => S3 end
  | S3 => match p with P231 | P321 => S1 | P132 | P312 => S2 | _ => S3 end
  end.
Definition inverse_perm p :=
  match p with P231 => P312 | P312 => P231 | _ => p end.

Lemma all_SymPerm_complete : forall p, In p all_SymPerm.
Proof. destruct p; cbn; tauto. Qed.
Lemma perm_sym_blank : forall p, perm_sym p S0 = S0.
Proof. reflexivity. Qed.
Lemma perm_sym_inverse : forall p s,
  perm_sym (inverse_perm p) (perm_sym p s) = s.
Proof. destruct p,s; reflexivity. Qed.
Lemma perm_sym_inverse' : forall p s,
  perm_sym p (perm_sym (inverse_perm p) s) = s.
Proof. destruct p,s; reflexivity. Qed.
Lemma perm_sym_injective : forall p s t, perm_sym p s = perm_sym p t -> s=t.
Proof.
  intros p s t H. apply (f_equal (perm_sym (inverse_perm p))) in H.
  now rewrite !perm_sym_inverse in H.
Qed.

(** Every injective blank-preserving map of the four symbols is listed. *)
Lemma perm_sym_complete : forall f : Sym -> Sym,
  f S0 = S0 -> (forall s t, f s = f t -> s=t) ->
  exists p, forall s, perm_sym p s = f s.
Proof.
  intros f H0 Hi.
  assert (H1 : f S1 <> S0) by (intro H; assert (S1=S0) by (apply Hi; congruence); discriminate).
  assert (H2 : f S2 <> S0) by (intro H; assert (S2=S0) by (apply Hi; congruence); discriminate).
  assert (H3 : f S3 <> S0) by (intro H; assert (S3=S0) by (apply Hi; congruence); discriminate).
  assert (H12 : f S1 <> f S2) by (intro H; apply Hi in H; discriminate).
  assert (H13 : f S1 <> f S3) by (intro H; apply Hi in H; discriminate).
  assert (H23 : f S2 <> f S3) by (intro H; apply Hi in H; discriminate).
  destruct (f S1) eqn:E1, (f S2) eqn:E2, (f S3) eqn:E3;
    try contradiction.
  all: first [solve [exists P123; destruct s; cbn; congruence]
    | solve [exists P132; destruct s; cbn; congruence]
    | solve [exists P213; destruct s; cbn; congruence]
    | solve [exists P231; destruct s; cbn; congruence]
    | solve [exists P312; destruct s; cbn; congruence]
    | solve [exists P321; destruct s; cbn; congruence]].
Qed.

Definition perm_trans p tr := mkTrans (perm_sym p (t_write tr)) (t_dir tr) (t_next tr).
Definition perm_tm p (tm : TM) : TM := fun q s =>
  option_map (perm_trans p) (tm q (perm_sym (inverse_perm p) s)).
Definition perm_tape p (tp : Tape) : Tape :=
  mkTape (fun n => perm_sym p (t_left tp n)) (perm_sym p (t_head tp))
    (fun n => perm_sym p (t_right tp n)).
Definition perm_config p (c : ExecState) : ExecState := (fst c, perm_tape p (snd c)).
Definition perm_instr p (tg : Instr) : Instr := (fst tg, perm_sym p (snd tg)).

Lemma perm_tm_at : forall p tm q s,
  perm_tm p tm q (perm_sym p s) = option_map (perm_trans p) (tm q s).
Proof. intros; unfold perm_tm; now rewrite perm_sym_inverse. Qed.
Lemma perm_trans_inverse : forall p tr,
  perm_trans (inverse_perm p) (perm_trans p tr) = tr.
Proof. intros p [s d q]; unfold perm_trans; cbn; now rewrite perm_sym_inverse. Qed.
Lemma perm_instr_inverse : forall p tg,
  perm_instr (inverse_perm p) (perm_instr p tg) = tg.
Proof. intros p [q s]; unfold perm_instr; cbn; now rewrite perm_sym_inverse. Qed.
Lemma perm_instr_injective : forall p x y, perm_instr p x=perm_instr p y -> x=y.
Proof.
  intros p x y H. apply (f_equal (perm_instr (inverse_perm p))) in H.
  now rewrite !perm_instr_inverse in H.
Qed.
Lemma perm_config_state : forall p c, fst (perm_config p c) = fst c.
Proof. reflexivity. Qed.
Lemma perm_config_instr : forall p c,
  instr_of (perm_config p c) = perm_instr p (instr_of c).
Proof. reflexivity. Qed.
Lemma perm_init : forall p, perm_config p InitES = InitES.
Proof. reflexivity. Qed.
Lemma perm_move : forall p d w tp,
  tape_move d (perm_sym p w) (perm_tape p tp) = perm_tape p (tape_move d w tp).
Proof.
  intros p d w [l h r]. destruct d; unfold tape_move,perm_tape; cbn;
    f_equal; apply functional_extensionality; intros [|n]; reflexivity.
Qed.
Lemma perm_step : forall p tm c,
  step (perm_tm p tm) (perm_config p c) = option_map (perm_config p) (step tm c).
Proof.
  intros p tm [q tp]. unfold step,perm_config; cbn.
  rewrite perm_tm_at. destruct (tm q (t_head tp)) as [[w d q']|]; cbn; [|reflexivity].
  now rewrite perm_move.
Qed.
Theorem perm_stepn : forall p tm n c,
  stepn (perm_tm p tm) n (perm_config p c) =
  option_map (perm_config p) (stepn tm n c).
Proof.
  intros p tm n; induction n; intro c; cbn [stepn]; [reflexivity|].
  rewrite perm_step. destruct (step tm c); cbn; [apply IHn|reflexivity].
Qed.
Theorem perm_blank_run : forall p tm n,
  stepn (perm_tm p tm) n InitES = option_map (perm_config p) (stepn tm n InitES).
Proof. intros; rewrite <- (perm_init p) at 1; apply perm_stepn. Qed.

Theorem perm_visits : forall p tm q n,
  VisitsAt (perm_tm p tm) q n <-> VisitsAt tm q n.
Proof.
  intros p tm q n. unfold VisitsAt. rewrite perm_blank_run.
  destruct (stepn tm n InitES) as [c|]; cbn.
  - split; intros (c' & Hc & Hq); inversion Hc; subst; eexists; split; eauto.
  - split; intros (c & H & _); discriminate.
Qed.
Theorem perm_fires : forall p tm tg n,
  FiresAt (perm_tm p tm) (perm_instr p tg) n <-> FiresAt tm tg n.
Proof.
  intros p tm tg n. unfold FiresAt. rewrite perm_blank_run.
  destruct (stepn tm n InitES) as [c|]; cbn.
  - split; intros (c' & Hc & Hq); injection Hc as E; subst c'.
    + exists c. split; [reflexivity|]. rewrite perm_config_instr in Hq.
      now apply perm_instr_injective in Hq.
    + exists (perm_config p c). split; [reflexivity|].
      now rewrite perm_config_instr,Hq.
  - split; intros (c & H & _); discriminate.
Qed.
Theorem perm_nonhalt : forall p tm, NonHalt (perm_tm p tm) <-> NonHalt tm.
Proof.
  intros p tm. unfold NonHalt. setoid_rewrite perm_blank_run.
  split; intros H n E; specialize (H n); destruct (stepn tm n InitES); cbn in *; congruence.
Qed.
Theorem perm_quiet : forall p tm q n,
  QuietAfter (perm_tm p tm) q n <-> QuietAfter tm q n.
Proof. intros; unfold QuietAfter; setoid_rewrite perm_visits; reflexivity. Qed.
Theorem perm_quiet_tr : forall p tm tg n,
  QuietAfterTr (perm_tm p tm) (perm_instr p tg) n <-> QuietAfterTr tm tg n.
Proof. intros; unfold QuietAfterTr; setoid_rewrite perm_fires; reflexivity. Qed.

Theorem perm_attains_state : forall p tm B,
  AttainsSt (perm_tm p tm) B <-> AttainsSt tm B.
Proof. intros; unfold AttainsSt; setoid_rewrite perm_quiet; reflexivity. Qed.
Theorem perm_attains_instruction : forall p tm B,
  AttainsTr (perm_tm p tm) B <-> AttainsTr tm B.
Proof.
  intros p tm B; split; intros (tg & n & Hq & HB).
  - exists (perm_instr (inverse_perm p) tg), n; split; [|exact HB].
    apply (proj1 (perm_quiet_tr p tm _ n)).
    destruct p,tg as [q s]; destruct s; exact Hq.
  - exists (perm_instr p tg), n; split; [apply perm_quiet_tr; exact Hq|exact HB].
Qed.
Theorem perm_bounds : forall p tm bs bi,
  Bounds bs bi (perm_tm p tm) <-> Bounds bs bi tm.
Proof.
  intros p tm bs bi. unfold Bounds,QHBound,QHBoundTr.
  split; intros [Hs Hi]; split.
  - intros q n H; apply (Hs q n); now apply perm_quiet.
  - intros tg n H; apply (Hi (perm_instr p tg) n); now apply perm_quiet_tr.
  - intros q n H; apply (Hs q n); now apply perm_quiet in H.
  - intros tg n H. apply (Hi (perm_instr (inverse_perm p) tg) n).
    apply (proj1 (perm_quiet_tr p tm _ n)).
    destruct p,tg as [q s]; destruct s; exact H.
Qed.
Theorem perm_extends : forall p tm tm',
  TM_le tm tm' -> TM_le (perm_tm p tm) (perm_tm p tm').
Proof.
  intros p tm tm' H q s. unfold perm_tm.
  destruct (H q (perm_sym (inverse_perm p) s)) as [E|E]; rewrite E; auto.
Qed.
Theorem perm_completion_bounds : forall p tm complete bs bi,
  NonHalt tm -> Bounds bs bi tm -> TM_le (perm_tm p tm) complete ->
  Bounds bs bi complete.
Proof.
  intros p tm complete bs bi Hnh Hb Hle.
  eapply extend_bounds; [apply perm_nonhalt; exact Hnh|apply perm_bounds; exact Hb|exact Hle].
Qed.
