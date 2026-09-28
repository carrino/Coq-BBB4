(** * SweepGlueTr: sweep counters, a TWO-INDEX lap glue, decided by one
    boolean checker.

    A sweep counter (SCOPING_INSTR.md 7.4.QC, 485 rows of class QH) keeps
    a block of units with one travelling hole.  Each hole step is one
    full sweep of the block's far side, and when the hole reaches the
    end the block grows and the hole restarts.  The anchor is two-index:

      [swC i k] = [(q, (Lpre ++ rep uL i ++ Lpost, h, Rpre ++ rep uR k ++ Rpost))]

    with [i] units already behind the hole and [k] still ahead of it.

    - INNER lap [(i, S k) -> (S i, k)]: one sweep over the [k] units
      ahead and back.  The [i] units behind are never touched, so they
      are the OPAQUE left tail of a [LapDecider] chain whose index is
      [k]: one [srun] ([sw_chi]) from [swA0] covers every [i] and [k].
    - OUTER lap [(i, 0) -> (e, i + d)]: the grow step.  It crosses the
      whole block behind the hole, so it is a chain with index [i] and
      both tails known empty ([sw_cho], from [swB0]).

    Neither lap alone is a counter lap in the [cview] sense (the counter
    alphabets are positional); the glue here is the two-index induction:
    the anchors are enumerated along [sw_nxt] ([swCf p] is the [p]-th),
    which turns both laps into the single-index [Hlap] that
    [LapGlueQHTr.glue_qhboundtr] consumes.  The per-instruction fires come
    from chain prefixes ([srun_instr]) of either lap; an inner-lap fire
    is reached from any anchor through at most two grow steps, an
    outer-lap fire through [k] inner laps ([sw_reach_zero]).

    As in the QC boards, the laps run on the machine WRAPPED at the
    quiet instructions ([sw_pins]) and the boot on the original machine,
    so the conclusion is the quasihalting triple [coversTr_qh3] takes.

    Everything a board supplies is DATA ([swcert]); [sweep_check] is
    evaluated by [vm_compute] and [sweep_sound] is proved once. *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape ClosureTr Mirror.
From BBB4.Checkers Require Import WrapTr LapDecider TCyclerQHTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
From BBB4.Counters Require Import WTape LapCertGlueLift LapGlueTr.
From BBB4.CensusTr Require Import TNF_QHTr QHConveyorTr.
Import ListNotations.

(** ** The certificate *)

Record swcert := mkSW {
  sw_pins  : list Instr;     (** quiet after the boot (and the undefined ones) *)
  sw_q     : St;
  sw_h     : Sym;
  sw_Lpre  : list Sym;
  sw_uL    : list Sym;
  sw_Lpost : list Sym;
  sw_Rpre  : list Sym;
  sw_uR    : list Sym;
  sw_Rpost : list Sym;
  sw_e     : nat;            (** the grow step lands on [(e, i + d)] *)
  sw_d     : nat;
  sw_chi   : list lstep;     (** inner lap, from [swA0] *)
  sw_cho   : list lstep;     (** outer lap, from [swB0] *)
  sw_fires : list (bool * list lstep);  (** (outer?, chain prefix) *)
  sw_t0    : nat;            (** boot index, on the original machine *)
  sw_i0    : nat;
  sw_k0    : nat
}.

Definition swC (w : swcert) (i k : nat) : cconf :=
  (sw_q w, (sw_Lpre w ++ rep (sw_uL w) i ++ sw_Lpost w, sw_h w,
            sw_Rpre w ++ rep (sw_uR w) k ++ sw_Rpost w)).

(** the inner lap's start: left tail opaque, [S k] units ahead (one of
    them unrolled into the prefix, so the chain can step onto it) *)
Definition swA0 (w : swcert) : sconf :=
  mkC (sw_q w) (sflat (sw_Lpre w)) (sw_h w)
      (mkS (sw_Rpre w ++ sw_uR w) (sw_uR w) 1 0 (sw_Rpost w)).

(** the outer lap's start: [i] units behind, none ahead *)
Definition swB0 (w : swcert) : sconf :=
  mkC (sw_q w) (mkS (sw_Lpre w) (sw_uL w) 1 0 (sw_Lpost w)) (sw_h w)
      (sflat (sw_Rpre w ++ sw_Rpost w)).

(** ** The checker *)

Definition sside_flat_is (s : sside) (x : list Sym) : bool :=
  syms_eqb (s_pre s) x && syms_eqb (s_u s) [] && syms_eqb (s_post s) [].

Definition sside_rep_is (s : sside) (pre u : list Sym) (b : nat)
                        (post : list Sym) : bool :=
  syms_eqb (s_pre s) pre && syms_eqb (s_u s) u && Nat.eqb (s_a s) 1
  && Nat.eqb (s_b s) b && lpad_eqb (s_post s) post.

Definition sw_inner_ok (tmw : TM) (w : swcert) : bool :=
  match srun tmw false true (sw_chi w) (swA0 w) with
  | Some (c1, _, cb) =>
      st_eqb (c_st c1) (sw_q w) && sym_eqb (c_h c1) (sw_h w)
      && sside_flat_is (c_l c1) (sw_Lpre w ++ sw_uL w)
      && sside_rep_is (c_r c1) (sw_Rpre w) (sw_uR w) 0 (sw_Rpost w)
      && (0 <? cb)
  | None => false
  end.

Definition sw_outer_ok (tmw : TM) (w : swcert) : bool :=
  match srun tmw true true (sw_cho w) (swB0 w) with
  | Some (c1, _, cb) =>
      st_eqb (c_st c1) (sw_q w) && sym_eqb (c_h c1) (sw_h w)
      && syms_eqb (s_u (c_l c1)) [] && syms_eqb (s_post (c_l c1)) []
      && lpad_eqb (s_pre (c_l c1))
                  (sw_Lpre w ++ rep (sw_uL w) (sw_e w) ++ sw_Lpost w)
      && sside_rep_is (c_r c1) (sw_Rpre w) (sw_uR w) (sw_d w) (sw_Rpost w)
      && (0 <? cb)
  | None => false
  end && (1 <=? sw_e w + sw_d w).

Definition sw_fire_ok (tmw : TM) (w : swcert) (t : Instr)
                      (f : bool * list lstep) : bool :=
  match (if fst f then srun_instr tmw true true (snd f) (swB0 w)
         else srun_instr tmw false true (snd f) (swA0 w)) with
  | Some t' => instr_eqb t' t
  | None => false
  end.

Definition sw_fires_ok (tmw : TM) (w : swcert) : bool :=
  forallb (fun t => tr_inb t (sw_pins w)
                    || existsb (sw_fire_ok tmw w t) (sw_fires w)) all_Instr.

Definition sw_boot_ok (tm : TM) (w : swcert) : bool :=
  match csteps tm (sw_t0 w) c0 with
  | Some c => ceqb c (swC w (sw_i0 w) (sw_k0 w))
  | None => false
  end.

(** boots are short (the quiet instructions of the class stop by step
    133); the cap keeps the unary [32779478] out of every board *)
Definition sw_boot_cap : nat := 4096.

Definition sweep_check (tm : TM) (w : swcert) : bool :=
  let tmw := tm_wrap_trs tm (sw_pins w) in
  sw_boot_ok tm w
  && existsb (fun tg => cfires tm c0 (sw_t0 w) tg) (sw_pins w)
  && (sw_t0 w <=? sw_boot_cap)
  && sw_inner_ok tmw w && sw_outer_ok tmw w && sw_fires_ok tmw w.

(** ** Soundness *)

Lemma sw_cap_le : forall n, (n <=? sw_boot_cap) = true -> (n <=? 32779478) = true.
Proof.
  intros n H. apply Nat.leb_le in H. apply Nat.leb_le.
  apply (Nat.le_trans _ _ _ H). apply Nat.leb_le. vm_compute. reflexivity.
Qed.

Lemma lpad_eqb_refl : forall x, lpad_eqb x x = true.
Proof.
  induction x as [|a x IH]; [reflexivity|].
  cbn [lpad_eqb]. rewrite IH, andb_true_r. apply sym_eqb_spec. reflexivity.
Qed.

Lemma lpad_eqb_app : forall x a b, lpad_eqb a b = true ->
  lpad_eqb (x ++ a) (x ++ b) = true.
Proof.
  induction x as [|y x IH]; intros a b H; [exact H|].
  cbn [app lpad_eqb]. rewrite (IH a b H), andb_true_r.
  apply sym_eqb_spec. reflexivity.
Qed.

Lemma lift_lpad : forall q l l' h r r',
  lpad_eqb l l' = true -> lpad_eqb r r' = true ->
  lift (q, (l, h, r)) = lift (q, (l', h, r')).
Proof.
  intros q l l' h r r' Hl Hr. unfold lift, lift_tape; cbn [fst snd].
  rewrite (lpad_eqb_lift _ _ Hl), (lpad_eqb_lift _ _ Hr). reflexivity.
Qed.

Section Sound.

Variable tm : TM.
Variable w : swcert.

Let tmw := tm_wrap_trs tm (sw_pins w).

Hypothesis Hin : sw_inner_ok tmw w = true.
Hypothesis Hout : sw_outer_ok tmw w = true.
Hypothesis Hfires : sw_fires_ok tmw w = true.

(** the anchors ARE the chain starts' denotations *)
Lemma swA0_den : forall i k,
  cden (rep (sw_uL w) i ++ sw_Lpost w) [] k (swA0 w) = swC w i (S k).
Proof.
  intros i k. unfold cden, swA0, swC, sden, sflat; cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
  replace (1 * k + 0) with k by lia. cbn [rep]. rewrite !app_nil_r, <- !app_assoc.
  reflexivity.
Qed.

Lemma swB0_den : forall i, cden [] [] i (swB0 w) = swC w i 0.
Proof.
  intros i. unfold cden, swB0, swC, sden, sflat; cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia. cbn [rep]. rewrite !app_nil_r. reflexivity.
Qed.

Lemma sw_inner_lap : forall i k, exists n c',
  csteps tmw n (swC w i (S k)) = Some c' /\
  lift c' = lift (swC w (S i) k) /\ 0 < n.
Proof.
  intros i k. pose proof Hin as H. unfold sw_inner_ok in H.
  destruct (srun tmw false true (sw_chi w) (swA0 w)) as [[[c1 ca] cb]|] eqn:E;
    [|discriminate].
  destruct c1 as [q1 [lp lu la lb lq] h1 [rp ru ra rb rq]].
  unfold sside_flat_is, sside_rep_is in H; cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post] in H.
  apply andb_prop in H as [H Hcb].
  apply andb_prop in H as [H Hr].
  apply andb_prop in H as [H Hl].
  apply andb_prop in H as [Hq Hh].
  apply andb_prop in Hr as [Hr Hrq].
  apply andb_prop in Hr as [Hr Hrb].
  apply andb_prop in Hr as [Hr Hra].
  apply andb_prop in Hr as [Hrp Hru].
  apply andb_prop in Hl as [Hl Hlq].
  apply andb_prop in Hl as [Hlp Hlu].
  apply st_eqb_spec in Hq; apply sym_eqb_spec in Hh.
  apply syms_eqb_eq in Hrp, Hru, Hlp, Hlu, Hlq.
  apply Nat.eqb_eq in Hra, Hrb. apply Nat.ltb_lt in Hcb. subst.
  exists (ca * k + cb),
    (cden (rep (sw_uL w) i ++ sw_Lpost w) [] k
          (mkC (sw_q w) (mkS (sw_Lpre w ++ sw_uL w) [] la lb []) (sw_h w)
               (mkS (sw_Rpre w) (sw_uR w) 1 0 rq))).
  split; [| split; [| lia]].
  - rewrite <- swA0_den.
    exact (srun_sound tmw false true (sw_chi w) (swA0 w) _ ca cb E
             (rep (sw_uL w) i ++ sw_Lpost w) [] k
             ltac:(discriminate) ltac:(reflexivity)).
  - unfold cden, swC, sden; cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post rep].
    rewrite rep_nil. replace (1 * k + 0) with k by lia.
    rewrite !app_nil_r, <- !app_assoc. cbn [app].
    apply lift_lpad; [apply lpad_eqb_refl |].
    apply lpad_eqb_app, lpad_eqb_app. exact Hrq.
Qed.

Lemma sw_outer_lap : forall i, exists n c',
  csteps tmw n (swC w i 0) = Some c' /\
  lift c' = lift (swC w (sw_e w) (i + sw_d w)) /\ 0 < n.
Proof.
  intros i. pose proof Hout as H. unfold sw_outer_ok in H.
  apply andb_prop in H as [H _].
  destruct (srun tmw true true (sw_cho w) (swB0 w)) as [[[c1 ca] cb]|] eqn:E;
    [|discriminate].
  destruct c1 as [q1 [lp lu la lb lq] h1 [rp ru ra rb rq]].
  unfold sside_rep_is in H; cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post] in H.
  apply andb_prop in H as [H Hcb].
  apply andb_prop in H as [H Hr].
  apply andb_prop in H as [H Hlp].
  apply andb_prop in H as [H Hlq].
  apply andb_prop in H as [H Hlu].
  apply andb_prop in H as [Hq Hh].
  apply andb_prop in Hr as [Hr Hrq].
  apply andb_prop in Hr as [Hr Hrb].
  apply andb_prop in Hr as [Hr Hra].
  apply andb_prop in Hr as [Hrp Hru].
  apply st_eqb_spec in Hq; apply sym_eqb_spec in Hh.
  apply syms_eqb_eq in Hrp, Hru, Hlu, Hlq.
  apply Nat.eqb_eq in Hra, Hrb. apply Nat.ltb_lt in Hcb. subst.
  exists (ca * i + cb),
    (cden [] [] i
          (mkC (sw_q w) (mkS lp [] la lb []) (sw_h w)
               (mkS (sw_Rpre w) (sw_uR w) 1 (sw_d w) rq))).
  split; [| split; [| lia]].
  - rewrite <- swB0_den.
    exact (srun_sound tmw true true (sw_cho w) (swB0 w) _ ca cb E [] [] i
             ltac:(reflexivity) ltac:(reflexivity)).
  - unfold cden, swC, sden; cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    rewrite rep_nil. replace (1 * i + sw_d w) with (i + sw_d w) by lia.
    rewrite !app_nil_r.
    apply lift_lpad; [exact Hlp |].
    apply lpad_eqb_app, lpad_eqb_app. exact Hrq.
Qed.

Lemma sw_e_d : 1 <= sw_e w + sw_d w.
Proof.
  pose proof Hout as H. unfold sw_outer_ok in H.
  apply andb_prop in H as [_ H]. apply Nat.leb_le in H. exact H.
Qed.

(** ** The enumeration: both laps become one [Hlap] *)

Definition sw_nxt (ik : nat * nat) : nat * nat :=
  match ik with
  | (i, S k) => (S i, k)
  | (i, 0) => (sw_e w, i + sw_d w)
  end.

Definition swCp (ik : nat * nat) : cconf := swC w (fst ik) (snd ik).

Lemma sw_lap_nxt : forall ik, exists n c',
  csteps tmw n (swCp ik) = Some c' /\ lift c' = lift (swCp (sw_nxt ik)) /\ 0 < n.
Proof.
  intros [i [|k]]; unfold swCp; cbn [sw_nxt fst snd].
  - apply sw_outer_lap.
  - apply sw_inner_lap.
Qed.

Definition swCf (p : positive) : cconf :=
  swCp (Nat.iter (Nat.pred (Pos.to_nat p)) sw_nxt (sw_i0 w, sw_k0 w)).

Lemma swCf_succ : forall p, swCf (Pos.succ p) =
  swCp (sw_nxt (Nat.iter (Nat.pred (Pos.to_nat p)) sw_nxt (sw_i0 w, sw_k0 w))).
Proof.
  intros p. unfold swCf. rewrite Pos2Nat.inj_succ.
  destruct (Pos2Nat.is_succ p) as (m & Hm). rewrite Hm. reflexivity.
Qed.

(** ** Fires, in [stepn] space over [lift] *)

Definition FiresFrom (c : cconf) (t : Instr) : Prop :=
  exists k e, stepn tmw k (lift c) = Some e /\ instr_of e = t.

Lemma lap_stepn : forall x y n c',
  csteps tmw n x = Some c' -> lift c' = lift y ->
  stepn tmw n (lift x) = Some (lift y).
Proof. intros x y n c' H Hl. rewrite <- Hl. apply csteps_lift. exact H. Qed.

Lemma fires_back : forall x y n t,
  stepn tmw n (lift x) = Some (lift y) -> FiresFrom y t -> FiresFrom x t.
Proof.
  intros x y n t H (k & e & Hk & Ht). exists (n + k), e.
  split; [rewrite stepn_add, H; exact Hk | exact Ht].
Qed.

Lemma fires_inner_back : forall x y t,
  (exists n c', csteps tmw n x = Some c' /\ lift c' = lift y /\ 0 < n) ->
  FiresFrom y t -> FiresFrom x t.
Proof.
  intros x y t (n & c' & H & Hl & _). apply (fires_back x y n t).
  exact (lap_stepn x y n c' H Hl).
Qed.

Lemma sw_reach_zero : forall k i, exists n,
  stepn tmw n (lift (swC w i k)) = Some (lift (swC w (i + k) 0)).
Proof.
  induction k as [|k IH]; intros i.
  - exists 0. rewrite Nat.add_0_r. reflexivity.
  - destruct (sw_inner_lap i k) as (n1 & c1 & H1 & Hl1 & _).
    destruct (IH (S i)) as (n2 & H2).
    exists (n1 + n2). rewrite stepn_add, (lap_stepn _ _ _ _ H1 Hl1).
    replace (i + S k) with (S i + k) by lia. exact H2.
Qed.

Lemma fire_inner : forall ch t,
  srun_instr tmw false true ch (swA0 w) = Some t ->
  forall i k, FiresFrom (swC w i (S k)) t.
Proof.
  intros ch t H i k.
  apply fire_lift_of_csteps with (Cc := fun _ => swC w i (S k)) (p := xH).
  exact (fire_of_run_instr tmw (fun _ => swC w i (S k)) false true ch (swA0 w)
           xH k (rep (sw_uL w) i ++ sw_Lpost w) [] t H
           ltac:(discriminate) ltac:(reflexivity) (eq_sym (swA0_den i k))).
Qed.

Lemma fire_outer : forall ch t,
  srun_instr tmw true true ch (swB0 w) = Some t ->
  forall i, FiresFrom (swC w i 0) t.
Proof.
  intros ch t H i.
  apply fire_lift_of_csteps with (Cc := fun _ => swC w i 0) (p := xH).
  exact (fire_of_run_instr tmw (fun _ => swC w i 0) true true ch (swB0 w)
           xH i [] [] t H
           ltac:(reflexivity) ltac:(reflexivity) (eq_sym (swB0_den i))).
Qed.

(** an inner-lap fire, from ANY anchor: at most two grow steps reach
    one with a unit ahead ([1 <= e + d]) *)
Lemma fire_inner_any : forall ch t,
  srun_instr tmw false true ch (swA0 w) = Some t ->
  forall i k, FiresFrom (swC w i k) t.
Proof.
  intros ch t H i [|k]; [| exact (fire_inner ch t H i k)].
  apply (fires_inner_back _ _ t (sw_outer_lap i)).
  destruct (i + sw_d w) as [|m] eqn:Em; [| exact (fire_inner ch t H _ m)].
  apply (fires_inner_back _ _ t (sw_outer_lap (sw_e w))).
  pose proof sw_e_d as Hed.
  destruct (sw_e w + sw_d w) as [|m] eqn:Em'; [lia|].
  exact (fire_inner ch t H _ m).
Qed.

(** an outer-lap fire, from ANY anchor: [k] inner laps first *)
Lemma fire_outer_any : forall ch t,
  srun_instr tmw true true ch (swB0 w) = Some t ->
  forall i k, FiresFrom (swC w i k) t.
Proof.
  intros ch t H i k.
  destruct (sw_reach_zero k i) as (n & Hn).
  exact (fires_back _ _ n t Hn (fire_outer ch t H (i + k))).
Qed.

Lemma sw_fire_any : forall t, ~ In t (sw_pins w) ->
  forall i k, FiresFrom (swC w i k) t.
Proof.
  intros t Hnin i k.
  pose proof Hfires as H. unfold sw_fires_ok in H.
  rewrite forallb_forall in H.
  specialize (H t (all_Instr_complete t)).
  apply orb_prop in H as [H | H].
  { exfalso. apply Hnin, tr_inb_spec, H. }
  apply existsb_exists in H as ([o ch] & _ & Hf).
  unfold sw_fire_ok in Hf; cbn [fst snd] in Hf.
  destruct o.
  - destruct (srun_instr tmw true true ch (swB0 w)) as [t'|] eqn:E; [|discriminate].
    apply instr_eqb_spec in Hf. subst t'.
    exact (fire_outer_any ch t E i k).
  - destruct (srun_instr tmw false true ch (swA0 w)) as [t'|] eqn:E; [|discriminate].
    apply instr_eqb_spec in Hf. subst t'.
    exact (fire_inner_any ch t E i k).
Qed.

End Sound.

Theorem sweep_sound : forall tm w, sweep_check tm w = true ->
  NonHalt tm /\ QHBoundTr 32779478 tm /\ QuasiHaltsTr tm.
Proof.
  intros tm w H. unfold sweep_check in H.
  apply andb_prop in H as [H Hf].
  apply andb_prop in H as [H Ho].
  apply andb_prop in H as [H Hi].
  apply andb_prop in H as [H Hcap].
  apply andb_prop in H as [Hb Hwit].
  apply (lap_qh_stage tm (sw_pins w) (swCf w) xH (sw_t0 w) 32779478).
  - unfold sw_boot_ok in Hb.
    destruct (csteps tm (sw_t0 w) c0) as [c|] eqn:E; [|discriminate].
    rewrite <- lift_c0, (csteps_lift _ _ _ _ E).
    f_equal. exact (ceqb_lift _ _ Hb).
  - intros p _. rewrite swCf_succ. apply (sw_lap_nxt tm w Hi Ho).
  - intros t Hnin p _.
    apply fire_csteps_of_lift.
    unfold swCf, swCp.
    exact (sw_fire_any tm w Hi Ho Hf t Hnin _ _).
  - exact Hwit.
  - exact (sw_cap_le _ Hcap).
Qed.

(** the hole moves LEFT: certify the mirror *)
Theorem sweep_sound_mirror : forall tm w, sweep_check (mirror_tm tm) w = true ->
  NonHalt tm /\ QHBoundTr 32779478 tm /\ QuasiHaltsTr tm.
Proof.
  intros tm w H.
  destruct (sweep_sound (mirror_tm tm) w H) as (Hnh & Hb & (t & (n & Hn) & N & HN)).
  split; [exact (mirror_nonhalt tm Hnh) |].
  split; [exact (qhboundtr_mirror 32779478 tm Hb) |].
  exists t. split.
  - exists n. apply mirror_fires. exact Hn.
  - exists N. intros m Hm Hf. apply (HN m Hm). apply mirror_fires. exact Hf.
Qed.
