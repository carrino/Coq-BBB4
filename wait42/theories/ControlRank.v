(** Reflective scalar count/control ranks for quantitative waiting bounds.
    Search certificates are untrusted; the checker rechecks the short anchor,
    control invariant closure, every avoiding edge, and binary numeric bounds.
    G counts all finite-tape ones; X/Y count head plus the left/right side.
    No finite bound on the measure or simulation to the cutoff is assumed. *)
From Coq Require Import Arith Lia Bool List ZArith NArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Checkers Require Import RepWL.
From BBB4.Census Require Import TNF_QH.
From BBBWait42 Require Import Spec Transport InvariantTimedRank.
Import ListNotations.

Inductive cr_measure := CrG | CrX | CrY.
Record cr_rank := mkCRank {
 cr_kind : cr_measure; cr_scale : nat; cr_phi : St -> nat }.
Definition cr_count (m : cr_measure) (c : cconf) : nat :=
 let '(_, (l,h,r)) := c in
 match m with
 | CrG => countnb l + zc h + countnb r
 | CrX => countnb l + zc h
 | CrY => zc h + countnb r end.
Definition cr_value (c : cr_rank) (cc : cconf) : nat :=
 cr_scale c * cr_count (cr_kind c) cc + cr_phi c (fst cc).
Definition cr_delta (m : cr_measure) (h : Sym) (tr : Trans) : Z :=
 match m,t_dir tr with
 | CrG,_ => (Z.of_nat (zc (t_write tr)) - Z.of_nat (zc h))%Z
 | CrX,DL | CrY,DR => (- Z.of_nat (zc h))%Z
 | CrX,DR | CrY,DL => (Z.of_nat (zc (t_write tr)) + 1 - Z.of_nat (zc h))%Z
 end.
Definition cr_phi_max (c : cr_rank) :=
 Nat.max (cr_phi c StA) (Nat.max (cr_phi c StB)
   (Nat.max (cr_phi c StC) (cr_phi c StD))).
Lemma cr_phi_bounded : forall c s, cr_phi c s <= cr_phi_max c.
Proof.
 intros c s; unfold cr_phi_max; destruct s;
 pose proof (Nat.le_max_l (cr_phi c StA)
   (Nat.max (cr_phi c StB) (Nat.max (cr_phi c StC) (cr_phi c StD))));
 pose proof (Nat.le_max_r (cr_phi c StA)
   (Nat.max (cr_phi c StB) (Nat.max (cr_phi c StC) (cr_phi c StD))));
 pose proof (Nat.le_max_l (cr_phi c StB) (Nat.max (cr_phi c StC) (cr_phi c StD)));
 pose proof (Nat.le_max_r (cr_phi c StB) (Nat.max (cr_phi c StC) (cr_phi c StD)));
 pose proof (Nat.le_max_l (cr_phi c StC) (cr_phi c StD));
 pose proof (Nat.le_max_r (cr_phi c StC) (cr_phi c StD)); lia.
Qed.
Lemma cr_count_bounded : forall m cc, cr_count m cc <= cr_count CrG cc.
Proof. intros m [s [[l h] r]]; destruct m; cbv [cr_count]; lia. Qed.
Lemma cr_value_bounded : forall c cc,
 cr_value c cc <= cr_scale c * cr_count CrG cc + cr_phi_max c.
Proof.
 intros c cc. unfold cr_value.
 pose proof (cr_count_bounded (cr_kind c) cc).
 pose proof (cr_phi_bounded c (fst cc)).
 apply Nat.add_le_mono; [apply Nat.mul_le_mono_l; assumption|assumption].
Qed.

Lemma cr_count_move_delta : forall m s l h r dir w,
 (Z.of_nat (cr_count m (s,ctape_move dir w (l,h,r))) <=
 Z.of_nat (cr_count m (s,(l,h,r))) + cr_delta m h (mkTrans w dir s))%Z.
Proof.
 intros m s l h r dir w.
 pose proof (countnb_hd l) as HL. pose proof (countnb_hd r) as HR.
 assert (Hlh : zc (chd l) <= 1) by (destruct (chd l); cbn [zc]; lia).
 assert (Hrh : zc (chd r) <= 1) by (destruct (chd r); cbn [zc]; lia).
 destruct m,dir; cbv beta iota zeta delta [cr_count ctape_move cr_delta t_dir t_write];
 repeat rewrite countnb_cons; lia.
Qed.
Lemma cr_count_growth : forall tm cc cc', cstep tm cc = Some cc' ->
 cr_count CrG cc' <= cr_count CrG cc + 1.
Proof.
 intros tm [s [[l h] r]] cc' Hstep. unfold cstep in Hstep.
 destruct (tm s h) as [[w dir s']|] eqn:E; [|discriminate].
 injection Hstep as <-.
 pose proof (cr_count_move_delta CrG s' l h r dir w) as Hd.
 assert (Hw : zc w <= 1) by (destruct w; cbn [zc]; lia).
 cbv beta iota zeta delta [cr_delta t_write t_dir] in Hd.
 change (cr_count CrG (s',ctape_move dir w (l,h,r)) <=
   cr_count CrG (s',(l,h,r)) + 1). lia.
Qed.

Definition cr_symbols := [S0;S1].
Lemma cr_symbols_complete : forall h, In h cr_symbols.
Proof. destruct h; simpl; auto. Qed.
Definition cr_closed_ok (tm : TM) (inv : St -> bool) :=
 forallb (fun s => if inv s then forallb (fun h =>
  match tm s h with Some tr => inv (t_next tr) | None => false end)
  cr_symbols else true) all_St.
Definition cr_edge_ok (c : cr_rank) (q s : St) (h : Sym) (tr : Trans) :=
 if st_eqb s q || st_eqb (t_next tr) q then true else
 Z.ltb ((Z.of_nat (cr_scale c) * cr_delta (cr_kind c) h tr +
   Z.of_nat (cr_phi c (t_next tr)))%Z) (Z.of_nat (cr_phi c s)).
Definition cr_ranks_ok (tm : TM) (inv : St -> bool) (cert : St -> cr_rank) :=
 forallb (fun q => if inv q then forallb (fun s => if inv s then
 forallb (fun h => match tm s h with
 | Some tr => cr_edge_ok (cert q) q s h tr | None => false end)
 cr_symbols else true) all_St else true) all_St.
Definition cr_bound_ok (inv : St -> bool) (cert : St -> cr_rank)
 (initial anchor : nat) (B w : N) :=
 forallb (fun q => if inv q then
 N.leb (1 + N.of_nat (cr_scale (cert q)) *
   (N.of_nat initial + (B - N.of_nat anchor)) +
   N.of_nat (cr_phi_max (cert q)))%N w else true) all_St.
Definition control_rank_check (tm : TM) (inv : St -> bool)
 (cert : St -> cr_rank) (anchor : nat) (B w : N) :=
 N.leb (N.of_nat anchor) B &&
 match csteps tm anchor c0 with
 | Some seed => inv (fst seed) && cr_closed_ok tm inv &&
   cr_ranks_ok tm inv cert &&
   cr_bound_ok inv cert (cr_count CrG seed) anchor B w
 | None => false end.

Lemma cr_closed_step : forall tm inv,
 cr_closed_ok tm inv = true -> forall s h,
 inv s = true -> exists tr, tm s h = Some tr /\ inv (t_next tr) = true.
Proof.
 intros tm inv H s h HI. unfold cr_closed_ok in H.
 rewrite forallb_forall in H. specialize (H s (all_St_complete s)); rewrite HI in H.
 rewrite forallb_forall in H. specialize (H h (cr_symbols_complete h)).
 destruct (tm s h) as [tr|] eqn:E; [exists tr; auto|discriminate].
Qed.
Lemma cr_invariant_closed : forall tm inv,
 cr_closed_ok tm inv = true -> forall cc cc',
 inv (fst cc) = true -> cstep tm cc = Some cc' -> inv (fst cc') = true.
Proof.
 intros tm inv H [s [[l h] r]] cc' HI Hstep.
 destruct (cr_closed_step tm inv H s h HI) as (tr & Et & HI').
 unfold cstep in Hstep. rewrite Et in Hstep. injection Hstep as <-. exact HI'.
Qed.
Lemma cr_edge_decreases : forall tm inv cert,
 cr_ranks_ok tm inv cert = true -> forall q cc cc', inv q = true ->
 inv (fst cc) = true -> cstep tm cc = Some cc' ->
 fst cc <> q -> fst cc' <> q -> cr_value (cert q) cc' < cr_value (cert q) cc.
Proof.
 intros tm inv cert H q [s [[l h] r]] cc' Hq HI Hstep Hs Hs'.
 unfold cr_ranks_ok in H. rewrite forallb_forall in H.
 specialize (H q (all_St_complete q)). rewrite Hq in H.
 rewrite forallb_forall in H. specialize (H s (all_St_complete s)).
 cbn [fst] in HI,Hs. rewrite HI in H.
 rewrite forallb_forall in H. specialize (H h (cr_symbols_complete h)).
 unfold cstep in Hstep. destruct (tm s h) as [[w dir s']|] eqn:Et; [|discriminate].
 injection Hstep as <-. cbn [fst] in Hs'.
 unfold cr_edge_ok in H. cbn [t_next] in H.
 assert (Es : st_eqb s q = false) by (destruct (st_eqb s q) eqn:E; auto; apply st_eqb_spec in E; contradiction).
 assert (Es' : st_eqb s' q = false) by (destruct (st_eqb s' q) eqn:E; auto; apply st_eqb_spec in E; contradiction).
 rewrite Es,Es' in H. apply Z.ltb_lt in H.
 pose proof (cr_count_move_delta (cr_kind (cert q)) s' l h r dir w) as Hd.
 assert (Hmul : (Z.of_nat (cr_scale (cert q)) *
   Z.of_nat (cr_count (cr_kind (cert q)) (s',ctape_move dir w (l,h,r))) <=
   Z.of_nat (cr_scale (cert q)) *
   (Z.of_nat (cr_count (cr_kind (cert q)) (s',(l,h,r))) +
     cr_delta (cr_kind (cert q)) h (mkTrans w dir s')))%Z).
 { apply Z.mul_le_mono_nonneg_l; [lia|exact Hd]. }
 unfold cr_value. cbn [fst].
 change (cr_scale (cert q) * cr_count (cr_kind (cert q)) (s',ctape_move dir w (l,h,r)) + cr_phi (cert q) s' <
   cr_scale (cert q) * cr_count (cr_kind (cert q)) (s',(l,h,r)) + cr_phi (cert q) s).
 nia.
Qed.

Lemma cr_N_le_nat : forall a b, (a <= b)%N -> N.to_nat a <= N.to_nat b.
Proof.
 intros a b H. apply Nat.compare_le_iff; rewrite <- N2Nat.inj_compare;
 apply N.compare_le_iff; exact H.
Qed.
Lemma cr_bound_sound : forall inv cert initial anchor B w,
 cr_bound_ok inv cert initial anchor B w = true -> forall q, inv q = true ->
 S (cr_scale (cert q) * (initial + 1*(N.to_nat B-anchor)) + cr_phi_max (cert q)) <= N.to_nat w.
Proof.
 intros inv cert initial anchor B w H q HI.
 unfold cr_bound_ok in H; rewrite forallb_forall in H.
 specialize (H q (all_St_complete q)); rewrite HI in H.
 apply N.leb_le in H. apply cr_N_le_nat in H.
 rewrite N2Nat.inj_add, N2Nat.inj_add, N2Nat.inj_mul, N2Nat.inj_add,
   N2Nat.inj_sub in H.
 repeat rewrite Nat2N.id in H. cbn [N.to_nat] in H. lia.
Qed.

Theorem control_rank_check_sound : forall tm inv cert anchor B w,
 control_rank_check tm inv cert anchor B w = true ->
 NonHalt tm /\ WindowBound tm (N.to_nat B) (N.to_nat w).
Proof.
 intros tm inv cert anchor B w H. unfold control_rank_check in H.
 apply andb_true_iff in H as [Hanchor H]. apply N.leb_le in Hanchor.
 apply cr_N_le_nat in Hanchor. rewrite Nat2N.id in Hanchor.
 destruct (csteps tm anchor c0) as [seed|] eqn:HA; [|discriminate].
 apply andb_true_iff in H as [H Hb]. apply andb_true_iff in H as [H Hr].
 apply andb_true_iff in H as [HI Hc].
 assert (HC : forall c c', inv (fst c) = true -> cstep tm c = Some c' -> inv (fst c') = true).
 { exact (cr_invariant_closed tm inv Hc). }
 split.
 - intros n Hnone.
   assert (Hrun : forall k c, inv (fst c) = true -> exists d, csteps tm k c = Some d).
   { induction k as [|k IH]; intros [s [[l h] r]] HIs.
     - eexists; reflexivity.
     - destruct (cr_closed_step tm inv Hc s h HIs) as (tr & Et & HIt).
       destruct (IH (t_next tr,ctape_move (t_dir tr) (t_write tr) (l,h,r)) HIt) as [d Hd].
       exists d. cbn [csteps cstep]. rewrite Et. exact Hd. }
   destruct (Hrun n seed HI) as [d Hd].
   assert (Hlong : stepn tm (anchor+n) InitES = Some (lift d)).
   { rewrite <- lift_c0. apply csteps_lift. rewrite csteps_add,HA. exact Hd. }
   replace (anchor+n) with (n+anchor) in Hlong by lia.
   rewrite stepn_add,Hnone in Hlong. discriminate.
 - eapply (c_invariant_active_ranks_window_bound tm (fun c => inv (fst c) = true)
     (fun q => inv q = true) (fun q => cr_value (cert q)) (cr_count CrG)
     1 (cr_count CrG seed) (fun q => cr_scale (cert q))
     (fun q => cr_phi_max (cert q)) anchor seed (N.to_nat B) (N.to_nat w)).
   + exact HA.
   + exact HI.
   + exact Hanchor.
   + exact HC.
   + intros c HIs. exact HIs.
   + intros q Hq c c' HIs Hstep Hneq Hneq'. eapply cr_edge_decreases; eauto.
   + intros c c' _ Hstep. apply cr_count_growth in Hstep. exact Hstep.
   + lia.
   + intros q _ c _. exact (cr_value_bounded (cert q) c).
   + exact (cr_bound_sound inv cert (cr_count CrG seed) anchor B w Hb).
Qed.
Theorem control_rank_check_completion : forall tm inv cert anchor B w,
 control_rank_check tm inv cert anchor B w = true ->
 forall tm', TM_le tm tm' -> NonHalt tm' /\ WindowBound tm' (N.to_nat B) (N.to_nat w).
Proof.
 intros tm inv cert anchor B w H tm' Hle.
 destruct (control_rank_check_sound tm inv cert anchor B w H) as [HN HW].
 split; [eapply nonhalt_le; eauto|].
 apply (proj2 (window_bound_completion tm tm' (N.to_nat B) (N.to_nat w) HN Hle)). exact HW.
Qed.
Print Assumptions control_rank_check_completion.

Module ControlRankRegression.
Definition machine : TM := fun q h => match q,h with
 | StA,S0 => Some (mkTrans S0 DR StB) | StA,S1 => None
 | StB,S0 => Some (mkTrans S0 DL StC) | StB,S1 => Some (mkTrans S0 DR StB)
 | StC,S0 => Some (mkTrans S1 DL StD) | StC,S1 => Some (mkTrans S1 DR StD)
 | StD,S0 => Some (mkTrans S1 DR StB) | StD,S1 => Some (mkTrans S0 DL StD) end.
Definition inv q := negb (st_eqb q StA).
Definition phi q s := match q,s with
 | StB,StC | StC,StD => 2 | StD,StB => 1 | _,_ => 0 end.
Definition cert q := mkCRank CrG 1 (phi q).
Definition no_potential (_ : St) := mkCRank CrG 1 (fun _ => 0).
Example accepts_linear_counter : control_rank_check machine inv cert 2 10%N 11%N = true.
Proof. vm_compute. reflexivity. Qed.
Example rejects_short_width : control_rank_check machine inv cert 2 10%N 10%N = false.
Proof. vm_compute. reflexivity. Qed.
Example rejects_wrong_potential : control_rank_check machine inv no_potential 2 10%N 11%N = false.
Proof. vm_compute. reflexivity. Qed.
Example rejects_missing_invariant_state :
 control_rank_check machine (fun q => st_eqb q StC || st_eqb q StD) cert 2 10%N 11%N = false.
Proof. vm_compute. reflexivity. Qed.
Example rejects_hole_in_invariant :
 control_rank_check machine (fun _ => true) cert 2 10%N 11%N = false.
Proof. vm_compute. reflexivity. Qed.
Example rejects_late_anchor : control_rank_check machine inv cert 2 1%N 11%N = false.
Proof. vm_compute. reflexivity. Qed.
Example zero_rank_target_edge :
 cr_edge_ok (mkCRank CrG 0 (fun _ => 0)) StB StA S0 (mkTrans S0 DR StB) = true.
Proof. reflexivity. Qed.
Example zero_rank_avoiding_edge_rejected :
 cr_edge_ok (mkCRank CrG 0 (fun _ => 0)) StB StC S0 (mkTrans S0 DR StD) = false.
Proof. reflexivity. Qed.
Example reflected_counter_window : forall tm', TM_le machine tm' ->
 NonHalt tm' /\ WindowBound tm' (N.to_nat 10%N) (N.to_nat 11%N).
Proof.
 intros tm' Hle. exact (control_rank_check_completion machine inv cert 2 10%N 11%N
  accepts_linear_counter tm' Hle).
Qed.
End ControlRankRegression.

(** Batch membership is checked data membership, with no implication of
    completeness of an external census or discovery manifest. *)
Record cr_case := mkCRCase {
 cr_machine : TM; cr_inv : St -> bool; cr_cert : St -> cr_rank; cr_anchor : nat }.
Definition control_rank_batch_check (entries : list cr_case) (B w : N) :=
 forallb (fun e => control_rank_check (cr_machine e) (cr_inv e)
   (cr_cert e) (cr_anchor e) B w) entries.
Theorem control_rank_batch_completion : forall entries B w,
 control_rank_batch_check entries B w = true ->
 forall e, In e entries -> forall tm', TM_le (cr_machine e) tm' ->
 NonHalt tm' /\ WindowBound tm' (N.to_nat B) (N.to_nat w).
Proof.
 intros entries B w H e Hin tm' Hle.
 unfold control_rank_batch_check in H. rewrite forallb_forall in H.
 exact (control_rank_check_completion (cr_machine e) (cr_inv e)
   (cr_cert e) (cr_anchor e) B w (H e Hin) tm' Hle).
Qed.
Print Assumptions control_rank_batch_completion.
