(** * HybridCtr2Tr: [HybridCtrTr] with a TWO-LAP OVERFLOW.

    [HybridCtrTr]'s counter steps once per lap: every carry case, the
    overflow included, turns [Dm^j ++ T (hi - 1)] into [D0^(j+1) ++ T lo] in
    one counter half.  §7.4.HY2's residue has hybrids that do not: at an
    all-[b - 1] counter the machine first writes a MARKER past the MSB and
    sweeps the block WITHOUT carrying (the low digits stay [b - 1]), and
    carries on the next lap ([0RB0LC_1LC1RD_1LA1LB_1RC0RB]: exit state 2
    instead of 0).  That lap does not increment, so it is outside the
    one-rank-per-lap anchor.

    Here a phase may carry a HOLD: its overflow is a two-lap composite

      [Dm^j ++ T (hi-1)]  --keep chain, exit X1, sweep-->  hold anchor [Ph]
                                          on [Dm^j ++ Th]
      [Dm^j ++ Th]        --overflow chain K2, exit X2, sweep-->  next phase
                                          on [D0^(j+1) ++ T lo]

    where the held top word [Th] is the table entry [hcT hi] (one entry past
    the top window), the keep chain is a carry case whose digits come back
    [Dm] instead of [D0], and [Ph] is an anchor shape of its own (state,
    prefixes, block unit).  The numeration, the ranks, the phase of a rank
    and the fire families are [HybridCtrTr]'s unchanged: the composite is
    ONE step of the enumeration.  New fire kinds 4 and 5 witness the
    instructions of the second lap (a chain prefix of [K2], of [X2]'s
    sweep), reached from the members of the overflow's top family.

    Nothing in [HybridCtrTr] is edited; its definitions are reused as is.
    Axiom footprint: [functional_extensionality_dep] (via [CTape.lift]). *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape ClosureTr Mirror.
From BBB4.Checkers Require Import WrapTr LapDecider TCyclerQHTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
From BBB4.Counters Require Import WTape MonoCounter LapCertGlue LapCertGlueLift
                                  LapGlueTr SweepGlueTr HybridGlueTr HybridCtrTr.
From BBB4.CensusTr Require Import TNF_QHTr QHConveyorTr.
Import ListNotations.

(** ** The certificate: [HybridCtrTr]'s, plus the holds *)

Record h2cert := mkH2C {
  h2_w     : hccert;
  h2_holds : list (nat * hcphase)   (** (phase, the hold anchor shape) *)
}.

Fixpoint h2_lookup (i : nat) (l : list (nat * hcphase)) : option hcphase :=
  match l with
  | [] => None
  | (k, Ph) :: l' => if k =? i then Some Ph else h2_lookup i l'
  end.

(** the keep chain's end: [Mpre ++ Dm^(c + j) ++ post] (a far end known) *)
Definition h2_kend_ok (w : hccert) (X : hcexit) (c : nat) (post : list Sym) (c1 : sconf) : bool :=
  st_eqb (c_st c1) (he_q2 X) && sym_eqb (c_h c1) (he_h2 X) && sside_nil (c_r c1)
  && syms_eqb (s_u (c_l c1)) (hcDm w) && Nat.eqb (s_a (c_l c1)) 1
  && (s_b (c_l c1) <=? c)
  && existsb (fun x => syms_eqb (s_pre (c_l c1)) (he_Mpre X ++ rep (hcDm w) x)
                       && lpad_eqb (s_post (c_l c1))
                                   (rep (hcDm w) (c - s_b (c_l c1) - x) ++ post))
             (seq 0 (S (c - s_b (c_l c1)))).

Section Defs2.

Variable W : h2cert.

Local Notation w := (h2_w W).

Definition h2_hold (i : nat) : option hcphase := h2_lookup i (h2_holds W).

(** the overflow top case of a phase *)
Definition h2_ovf (P : hcphase) : hcase := nth (hchi w - hclo w - 1) (hc_top P) hk_dflt.

(** the keep chain: [Dm^j ++ T (hi-1) -> Dm^j ++ Th] onto its exit *)
Definition h2_keep_ok (tmw : TM) (P : hcphase) (K : hcase) : bool :=
  let X := hcX P (hk_ex K) in
  let Ps := hcT w (pred (hchi w)) in
  let Pe := hcT w (hchi w) in
  (hk_ex K <? length (hc_exits P))
  && hy_run_ok tmw true false (hk_ch K) (hcK0 w P K Ps) (h2_kend_ok w X (hk_nu K) Pe)
  && hy_list_ok (fun j ch => hy_run_ok tmw true false ch (hcKB w P Ps j)
                   (hc_cbase_ok X true (he_Mpre X ++ rep (hcDm w) j ++ Pe)))
                0 (hk_base K)
  && (hk_nu K <=? length (hk_base K)).

Definition h2_K2 (Ph : hcphase) : hcase := nth 0 (hc_top Ph) hk_dflt.

Definition h2_hold_ok (tmw : TM) (P Ph P' : hcphase) : bool :=
  let K1 := h2_ovf P in
  let X1 := hcX P (hk_ex K1) in
  let K2 := h2_K2 Ph in
  let X2 := hcX Ph (hk_ex K2) in
  h2_keep_ok tmw P K1
  && hc_sweep_ok P tmw X1 Ph && (hc_nmin Ph <=? he_c X1)
  && hc_case_ok w Ph tmw true 1 (hcT w (hchi w)) (hcT w (hclo w)) K2
  && hc_sweep_ok Ph tmw X2 P' && (hc_nmin P' <=? he_c X2).

Definition h2_phase_ok (tmw : TM) (i : nat) : bool :=
  let P := hcph w i in
  let P' := hcph w (hcnx w i) in
  match h2_hold i with
  | None => hc_phase_ok w tmw i
  | Some Ph =>
      let x1 := hk_ex (h2_ovf P) in
      forallb (hc_int_ok w P tmw) (seq 0 (hcb w - 1))
      && forallb (hc_top_ok w P tmw) (seq 0 (hchi w - hclo w - 1))
      && h2_hold_ok tmw P Ph P'
      && forallb (fun x => (x =? x1) || (hc_sweep_ok P tmw (hcX P x) P'
                                         && (hc_nmin P' <=? he_c (hcX P x))))
                 (seq 0 (length (hc_exits P)))
      && forallb (fun d => negb (hk_ex (nth d (hc_int P) hk_dflt) =? x1)) (seq 0 (hcb w - 1))
      && forallb (fun e => negb (hk_ex (nth e (hc_top P) hk_dflt) =? x1))
                 (seq 0 (hchi w - hclo w - 1))
  end.

Definition h2_phases_ok (tmw : TM) : bool :=
  (1 <=? hcL w) && forallb (h2_phase_ok tmw) (seq 0 (hcL w)).

(** kinds 0-3 are [HybridCtrTr]'s; kind 4: a chain prefix of the hold's
    overflow chain [K2], kind 5: of its exit's sweep; both at the ranks of
    the overflow's top family *)
Definition h2_fire_ok (tmw : TM) (t : Instr) (f : hcfire) : bool :=
  if hcf_kind f <=? 3 then hc_fire_ok w tmw t f
  else
    let e := hchi w - hclo w - 1 in
    (hcf_ph f <? hcL w) &&
    match h2_hold (hcf_ph f) with
    | None => false
    | Some Ph =>
        let K2 := h2_K2 Ph in
        match hcf_kind f with
        | 4 => match srun_instr tmw true false (hcf_ch f) (hcK0 w Ph K2 (hcT w (hchi w))) with
               | Some t' => instr_eqb t' t && (hk_nu K2 <=? hcf_a f)
                            && hc_top_fam_ok w (hcf_ph f) e (hcf_a f) (hcf_b f)
               | None => false
               end
        | 5 => match srun_instr tmw false true (hcf_ch f) (hcS0 Ph (hcX Ph (hk_ex K2))) with
               | Some t' => instr_eqb t' t
                            && hc_top_fam_ok w (hcf_ph f) e (hcf_a f) (hcf_b f)
               | None => false
               end
        | _ => false
        end
    end.

Definition h2_fires_ok (tmw : TM) : bool :=
  forallb (fun t => tr_inb t (hcc_pins w) || existsb (h2_fire_ok tmw t) (hcc_fires w))
          all_Instr.

Definition h2_core_ok (tmw : TM) : bool :=
  (2 <=? hcb w) && (hclo w <? hchi w) && hc_canon0 w
  && h2_phases_ok tmw && h2_fires_ok tmw
  && (hcc_i0 w <? hcL w) && (hc_nmin (hcph w (hcc_i0 w)) <=? hcc_n0 w).

End Defs2.

Definition h2_check_nqh (tm : TM) (W : h2cert) : bool :=
  let tmw := tm_wrap_trs tm (hcc_pins (h2_w W)) in
  hc_boot_ok (h2_w W) tmw && h2_core_ok W tmw.

(** ** The keep chain *)

Lemma h2_kend_den : forall w X c post c1 XR j,
  h2_kend_ok w X c post c1 = true ->
  lift (cden [] XR j c1)
  = lift (he_q2 X, (he_Mpre X ++ rep (hcDm w) (c + j) ++ post, he_h2 X, XR)).
Proof.
  intros w X c post [q1 [lp lu la lb lq] h1 r1] XR j H.
  unfold h2_kend_ok in H; cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post] in H.
  apply andb_prop in H as [H Hx].
  apply andb_prop in H as [H Hb].
  apply andb_prop in H as [H Ha].
  apply andb_prop in H as [H Hu].
  apply andb_prop in H as [H Hr].
  apply andb_prop in H as [Hq Hh].
  apply existsb_exists in Hx as (x & Hxin & Hx).
  apply in_seq in Hxin.
  apply andb_prop in Hx as [Hp Hpost].
  apply st_eqb_spec in Hq; apply sym_eqb_spec in Hh.
  apply syms_eqb_eq in Hp, Hu. apply Nat.eqb_eq in Ha. apply Nat.leb_le in Hb.
  subst.
  unfold cden; cbn [c_st c_l c_h c_r].
  rewrite (sside_nil_den r1 XR j Hr).
  apply lift_lpad; [| apply lpad_eqb_refl].
  unfold sden; cbn [s_pre s_u s_a s_b s_post].
  rewrite !app_nil_r.
  replace (c + j) with (x + ((1 * j + lb) + (c - lb - x))) by lia.
  rewrite !rep_add, <- !app_assoc.
  repeat apply lpad_eqb_app. exact Hpost.
Qed.

Lemma h2_keep_sound : forall tmw W P K, h2_keep_ok W tmw P K = true ->
  let w := h2_w W in
  let X := hcX P (hk_ex K) in
  In X (hc_exits P) /\
  forall j n, exists N c',
    csteps tmw N (hcKc w P (hcT w (pred (hchi w))) [] j n) = Some c' /\
    lift c' = lift (he_q2 X, (he_Mpre X ++ rep (hcDm w) j ++ hcT w (hchi w),
                              he_h2 X, rep (hc_w P) n ++ hc_Rpost P)).
Proof.
  intros tmw W P K H w X. unfold h2_keep_ok in H. fold w X in H.
  apply andb_prop in H as [H Hlen]. apply andb_prop in H as [H Hl].
  apply andb_prop in H as [Hex Hm].
  apply Nat.leb_le in Hlen. apply Nat.ltb_lt in Hex.
  split; [exact (nth_In _ _ Hex) |].
  intros j n.
  destruct (lt_dec j (hk_nu K)) as [Hj | Hj].
  - destruct (nth_error (hk_base K) j) as [ch|] eqn:Ech.
    2: { apply nth_error_None in Ech. lia. }
    pose proof (hy_list_ok_nth _ _ 0 Hl j ch Ech) as Hj0. cbn [Nat.add] in Hj0.
    destruct (hy_run_sound _ _ _ _ _ _ Hj0) as (c1 & ca & cb & Hrun & Hok).
    exists (ca * 0 + cb), (cden [] (rep (hc_w P) n ++ hc_Rpost P) 0 c1). split.
    + rewrite <- hcKB_den.
      exact (srun_sound tmw true false _ _ _ ca cb Hrun _ _ 0 ltac:(reflexivity)
               ltac:(discriminate)).
    + rewrite (hc_cbase_den X true _ c1 _ _ 0 Hok ltac:(reflexivity)), !app_nil_r.
      reflexivity.
  - destruct (hy_run_sound _ _ _ _ _ _ Hm) as (c1 & ca & cb & Hrun & Hok).
    exists (ca * (j - hk_nu K) + cb),
      (cden [] (rep (hc_w P) n ++ hc_Rpost P) (j - hk_nu K) c1). split.
    + replace (hcKc w P (hcT w (pred (hchi w))) [] j n)
        with (hcKc w P (hcT w (pred (hchi w))) [] (hk_nu K + (j - hk_nu K)) n)
        by (f_equal; lia).
      rewrite <- hcK0_den.
      exact (srun_sound tmw true false _ _ _ ca cb Hrun _ _ _ ltac:(reflexivity)
               ltac:(discriminate)).
    + rewrite (h2_kend_den w X _ _ c1 _ _ Hok).
      replace (hk_nu K + (j - hk_nu K)) with j by lia. reflexivity.
Qed.

(** ** Soundness *)

Section Sound.

Variable tmw : TM.
Variable W : h2cert.

Local Notation w := (h2_w W).

Hypothesis Hcore : h2_core_ok W tmw = true.

Local Notation b := (hcb w).
Local Notation lo := (hclo w).
Local Notation hi := (hchi w).

Lemma h2_core_parts : 2 <= b /\ lo < hi /\ hc_canon0 w = true /\ h2_phases_ok W tmw = true
  /\ h2_fires_ok W tmw = true /\ hcc_i0 w < hcL w /\ hc_nmin (hcph w (hcc_i0 w)) <= hcc_n0 w.
Proof.
  pose proof Hcore as H. unfold h2_core_ok in H.
  apply andb_prop in H as [H Hn]. apply andb_prop in H as [H Hi].
  apply andb_prop in H as [H Hf]. apply andb_prop in H as [H Hp].
  apply andb_prop in H as [H Hc]. apply andb_prop in H as [Hb Hl].
  apply Nat.leb_le in Hb, Hn. apply Nat.ltb_lt in Hi, Hl. tauto.
Qed.

Lemma h2_b2 : 2 <= b. Proof. apply h2_core_parts. Qed.
Lemma h2_lh : lo < hi. Proof. apply h2_core_parts. Qed.

Lemma h2_L_pos : 1 <= hcL w.
Proof.
  destruct h2_core_parts as (_ & _ & _ & H & _). unfold h2_phases_ok in H.
  apply andb_prop in H as [H _]. apply Nat.leb_le in H. exact H.
Qed.

Lemma h2_phase_true : forall i, i < hcL w -> h2_phase_ok W tmw i = true.
Proof.
  intros i Hi. destruct h2_core_parts as (_ & _ & _ & H & _). unfold h2_phases_ok in H.
  apply andb_prop in H as [_ H]. rewrite forallb_forall in H.
  apply H, in_seq. lia.
Qed.

(** the anchor, as a carry case's start *)
Lemma h2_anchor_max : forall P j tv n, hc_m P <= n ->
  hcC w P (repeat (b - 1) j, tv) n = hcKc w P (hcT w tv) [] j (n - hc_m P).
Proof.
  intros P j tv n Hn. unfold hcC, hcKc. rewrite hcE_max, app_nil_r.
  replace (hc_m P + (n - hc_m P)) with n by lia. reflexivity.
Qed.

Lemma h2_m_le : forall P, hc_m P <= hc_nmin P.
Proof. intros P. pose proof (nminX_le P 0). unfold hc_nminX in *. lia. Qed.

(** the first half of a hold: from the overflow anchor to the hold anchor *)
Lemma h2_hold_first : forall i Ph, i < hcL w -> h2_hold W i = Some Ph ->
  forall j n, hc_nmin (hcph w i) <= n ->
  let P := hcph w i in
  let X1 := hcX P (hk_ex (h2_ovf W P)) in
  hc_nmin Ph <= n - hc_nminX P X1 + he_c X1 /\
  (exists N, stepn tmw N (lift (hcC w P (repeat (b - 1) j, pred hi) n))
             = Some (lift (hcM w P X1 (repeat (b - 1) j, hi)
                                (he_na X1 + (n - hc_nminX P X1) + he_nb X1)))) /\
  exists N, 0 < N /\ stepn tmw N (lift (hcC w P (repeat (b - 1) j, pred hi) n))
             = Some (lift (hcC w Ph (repeat (b - 1) j, hi) (n - hc_nminX P X1 + he_c X1))).
Proof.
  intros i Ph Hi Hh j n Hn P X1.
  pose proof (h2_phase_true i Hi) as H. unfold h2_phase_ok in H. rewrite Hh in H.
  fold P in H.
  apply andb_prop in H as [H _]. apply andb_prop in H as [H _].
  apply andb_prop in H as [H _]. apply andb_prop in H as [_ Hhold].
  unfold h2_hold_ok in Hhold.
  apply andb_prop in Hhold as [Hhold _]. apply andb_prop in Hhold as [Hhold _].
  apply andb_prop in Hhold as [Hhold _]. apply andb_prop in Hhold as [Hhold Hn1].
  apply andb_prop in Hhold as [Hk Hs1]. apply Nat.leb_le in Hn1. fold X1 in Hs1, Hn1.
  destruct (h2_keep_sound tmw W P _ Hk) as (_ & Hks). fold X1 in Hks.
  pose proof (nminX_le P (hk_ex (h2_ovf W P))) as Hle. fold X1 in Hle.
  unfold hc_nminX in Hle. fold P in Hn.
  assert (Hm : hc_m P <= n) by (pose proof (h2_m_le P); lia).
  destruct (Hks j (n - hc_m P)) as (N1 & c1 & H1 & Hl1).
  assert (Hmid : stepn tmw N1 (lift (hcC w P (repeat (b - 1) j, pred hi) n))
             = Some (lift (hcM w P X1 (repeat (b - 1) j, hi)
                                (he_na X1 + (n - hc_nminX P X1) + he_nb X1)))).
  { rewrite h2_anchor_max by exact Hm.
    apply (lap_stepn _ _ _ _ _ H1). rewrite Hl1. unfold hcM. rewrite hcE_max.
    unfold hc_nminX. do 3 f_equal. f_equal. f_equal. lia. }
  split; [unfold hc_nminX; lia |]. split; [exists N1; exact Hmid |].
  destruct (hc_sweep_main tmw w P X1 Ph Hs1 (repeat (b - 1) j, hi) (n - hc_nminX P X1))
    as (N2 & c2 & H2 & Hl2 & HN2).
  exists (N1 + N2). split; [lia |].
  rewrite stepn_add, Hmid, (lap_stepn _ _ _ _ _ H2 Hl2). reflexivity.
Qed.

(** the second half: from the hold anchor to the next phase *)
Lemma h2_hold_second : forall i Ph, i < hcL w -> h2_hold W i = Some Ph ->
  forall j n, hc_nmin Ph <= n ->
  let P' := hcph w (hcnx w i) in
  let X2 := hcX Ph (hk_ex (h2_K2 Ph)) in
  hc_nmin P' <= n - hc_nminX Ph X2 + he_c X2 /\
  (exists N, stepn tmw N (lift (hcC w Ph (repeat (b - 1) j, hi) n))
             = Some (lift (hcM w Ph X2 (repeat 0 (S j), lo)
                                (he_na X2 + (n - hc_nminX Ph X2) + he_nb X2)))) /\
  exists N, 0 < N /\ stepn tmw N (lift (hcC w Ph (repeat (b - 1) j, hi) n))
             = Some (lift (hcC w P' (repeat 0 (S j), lo) (n - hc_nminX Ph X2 + he_c X2))).
Proof.
  intros i Ph Hi Hh j n Hn P' X2.
  pose proof (h2_phase_true i Hi) as H. unfold h2_phase_ok in H. rewrite Hh in H.
  fold P' in H.
  apply andb_prop in H as [H _]. apply andb_prop in H as [H _].
  apply andb_prop in H as [H _]. apply andb_prop in H as [_ Hhold].
  unfold h2_hold_ok in Hhold. fold P' in Hhold.
  apply andb_prop in Hhold as [Hhold Hn2]. apply andb_prop in Hhold as [Hhold Hs2].
  apply andb_prop in Hhold as [_ Hc2]. fold X2 in Hs2, Hn2. apply Nat.leb_le in Hn2.
  destruct (hc_case_sound tmw w Ph _ _ _ _ _ Hc2) as (_ & Hcs). fold X2 in Hcs.
  pose proof (nminX_le Ph (hk_ex (h2_K2 Ph))) as Hle. fold X2 in Hle.
  unfold hc_nminX in Hle.
  assert (Hm : hc_m Ph <= n) by (pose proof (h2_m_le Ph); lia).
  destruct (Hcs j [] (n - hc_m Ph) ltac:(reflexivity)) as (N1 & c1 & H1 & Hl1).
  assert (Hmid : stepn tmw N1 (lift (hcC w Ph (repeat (b - 1) j, hi) n))
             = Some (lift (hcM w Ph X2 (repeat 0 (S j), lo)
                                (he_na X2 + (n - hc_nminX Ph X2) + he_nb X2)))).
  { rewrite h2_anchor_max by exact Hm.
    apply (lap_stepn _ _ _ _ _ H1). rewrite Hl1. unfold hcM. rewrite hcE_zero, app_nil_r.
    rewrite Nat.add_1_r. unfold hc_nminX. do 3 f_equal. f_equal. f_equal. lia. }
  split; [unfold hc_nminX; lia |]. split; [exists N1; exact Hmid |].
  destruct (hc_sweep_main tmw w Ph X2 P' Hs2 (repeat 0 (S j), lo) (n - hc_nminX Ph X2))
    as (N2 & c2 & H2 & Hl2 & HN2).
  exists (N1 + N2). split; [lia |].
  rewrite stepn_add, Hmid, (lap_stepn _ _ _ _ _ H2 Hl2). reflexivity.
Qed.

(** a phase with a hold, off the overflow: [HybridCtrTr]'s counter half and
    sweep, per case *)
Definition h2_is_hold_ovf (i : nat) (c : list nat * nat) : bool :=
  match h2_hold W i with
  | Some _ => match firstlow b (fst c) with
              | Some _ => false
              | None => S (snd c) =? hi
              end
  | None => false
  end.

(** the block count after one step of the enumeration *)
Definition h2_nn (i : nat) (c : list nat * nat) (n : nat) : nat :=
  let P := hcph w i in
  let X := hc_exit_of w P c in
  let n1 := n - hc_nminX P X + he_c X in
  match h2_hold W i with
  | Some Ph =>
      if h2_is_hold_ovf i c
      then let X2 := hcX Ph (hk_ex (h2_K2 Ph)) in n1 - hc_nminX Ph X2 + he_c X2
      else n1
  | None => n1
  end.

(** the ordinary lap, for a case that is not a hold's overflow *)
Lemma h2_plain : forall i c n, i < hcL w -> canon b lo hi c -> hc_nmin (hcph w i) <= n ->
  h2_is_hold_ovf i c = false ->
  let P := hcph w i in
  let X := hc_exit_of w P c in
  In X (hc_exits P) /\
  hc_sweep_ok P tmw X (hcph w (hcnx w i)) = true /\
  hc_nmin (hcph w (hcnx w i)) <= he_c X /\
  exists N, stepn tmw N (lift (hcC w P c n))
            = Some (lift (hcM w P X (csucc b lo hi c) (he_na X + (n - hc_nminX P X) + he_nb X))).
Proof.
  intros i c n Hi Hc Hn Hno P X. fold P in Hn.
  assert (HmP : hc_m P <= n) by (pose proof (h2_m_le P); lia).
  pose proof (h2_phase_true i Hi) as H. unfold h2_phase_ok in H. fold P in H.
  destruct (h2_hold W i) as [Ph|] eqn:Eh.
  - (* a hold phase, a case that is not the overflow *)
    set (x1 := hk_ex (h2_ovf W P)) in H.
    apply andb_prop in H as [H Hte]. apply andb_prop in H as [H Hie].
    apply andb_prop in H as [H Hx]. apply andb_prop in H as [H _].
    apply andb_prop in H as [Hint Htop].
    rewrite forallb_forall in Hint, Htop, Hte, Hie, Hx.
    destruct c as [low tv]. destruct Hc as (Hf & Hl & Hh); cbn [fst snd] in *.
    pose proof h2_b2 as Hb2. pose proof h2_lh as Hlh.
    destruct (low_shape b lo hi Hb2 Hlh low Hf) as [(j & d & r & -> & Hd) | Hm].
    + unfold X, hc_exit_of, hc_kase; cbn [fst snd].
      rewrite (firstlow_int b j d r ltac:(lia) Hd).
      rewrite csucc_int by (lia || exact Hd).
      specialize (Hint d ltac:(apply in_seq; lia)). unfold hc_int_ok in Hint.
      specialize (Hie d ltac:(apply in_seq; lia)). apply negb_true_iff, Nat.eqb_neq in Hie.
      destruct (hc_case_sound _ _ _ _ _ _ _ _ Hint) as (Hin & Hs).
      pose proof (nminX_le P (hk_ex (nth d (hc_int P) hk_dflt))) as Hle.
      unfold hc_nminX in Hle.
      split; [exact Hin |].
      assert (Hxs : hc_sweep_ok P tmw (hcX P (hk_ex (nth d (hc_int P) hk_dflt)))
                      (hcph w (hcnx w i)) = true
                    /\ hc_nmin (hcph w (hcnx w i))
                       <= he_c (hcX P (hk_ex (nth d (hc_int P) hk_dflt)))).
      { apply In_nth_error in Hin. unfold hc_case_ok in Hint.
        apply andb_prop in Hint as [Hint _]. apply andb_prop in Hint as [Hint _].
        apply andb_prop in Hint as [Hlt _]. apply Nat.ltb_lt in Hlt.
        specialize (Hx (hk_ex (nth d (hc_int P) hk_dflt)) ltac:(apply in_seq; lia)).
        apply orb_prop in Hx as [Hx | Hx]; [apply Nat.eqb_eq in Hx; contradiction |].
        apply andb_prop in Hx as [Hx1 Hx2]. apply Nat.leb_le in Hx2. auto. }
      destruct Hxs as [Hxs1 Hxs2]. split; [exact Hxs1 |]. split; [exact Hxs2 |].
      destruct (Hs j (hcE w (r, tv)) (n - hc_m P) ltac:(discriminate)) as (N & c' & H1 & H2).
      exists N. apply (lap_stepn _ _ _ _ c').
      * unfold hcC. rewrite hcE_int. unfold hcKc in H1.
        replace (hc_m P + (n - hc_m P)) with n in H1 by lia. exact H1.
      * rewrite H2. unfold hcM. rewrite hcE_zint, Nat.add_0_r.
        unfold hc_nminX. do 3 f_equal. f_equal. f_equal. lia.
    + unfold h2_is_hold_ovf in Hno. rewrite Eh in Hno. cbn [fst snd] in Hno.
      unfold X, hc_exit_of, hc_kase; cbn [fst snd].
      rewrite Hm in Hno |- *. set (j := length low) in *.
      rewrite (firstlow_max b j ltac:(lia)) in Hno |- *. apply Nat.eqb_neq in Hno.
      assert (Hts : S tv < hi) by lia.
      specialize (Htop (tv - lo) ltac:(apply in_seq; lia)). unfold hc_top_ok in Htop.
      replace (lo + (tv - lo)) with tv in Htop by lia.
      replace (S tv <? hi) with true in Htop by (symmetry; apply Nat.ltb_lt; lia).
      specialize (Hte (tv - lo) ltac:(apply in_seq; lia)).
      apply negb_true_iff, Nat.eqb_neq in Hte.
      rewrite csucc_top by (lia || exact Hts).
      destruct (hc_case_sound _ _ _ _ _ _ _ _ Htop) as (Hin & Hs).
      pose proof (nminX_le P (hk_ex (nth (tv - lo) (hc_top P) hk_dflt))) as Hle.
      unfold hc_nminX in Hle.
      split; [exact Hin |].
      assert (Hxs : hc_sweep_ok P tmw (hcX P (hk_ex (nth (tv - lo) (hc_top P) hk_dflt)))
                      (hcph w (hcnx w i)) = true
                    /\ hc_nmin (hcph w (hcnx w i))
                       <= he_c (hcX P (hk_ex (nth (tv - lo) (hc_top P) hk_dflt)))).
      { unfold hc_case_ok in Htop.
        apply andb_prop in Htop as [Htop _]. apply andb_prop in Htop as [Htop _].
        apply andb_prop in Htop as [Hlt _]. apply Nat.ltb_lt in Hlt.
        specialize (Hx (hk_ex (nth (tv - lo) (hc_top P) hk_dflt)) ltac:(apply in_seq; lia)).
        apply orb_prop in Hx as [Hx | Hx]; [apply Nat.eqb_eq in Hx; contradiction |].
        apply andb_prop in Hx as [Hx1 Hx2]. apply Nat.leb_le in Hx2. auto. }
      destruct Hxs as [Hxs1 Hxs2]. split; [exact Hxs1 |]. split; [exact Hxs2 |].
      destruct (Hs j [] (n - hc_m P) ltac:(reflexivity)) as (N & c' & H1 & H2).
      exists N. apply (lap_stepn _ _ _ _ c').
      * rewrite h2_anchor_max by lia. exact H1.
      * rewrite H2. unfold hcM. rewrite hcE_zero, Nat.add_0_r, app_nil_r.
        unfold hc_nminX. do 3 f_equal. f_equal. f_equal. lia.
  - (* no hold: HybridCtrTr's phase *)
    unfold hc_phase_ok in H. fold P in H.
    apply andb_prop in H as [Hctr Hx]. rewrite forallb_forall in Hx.
    destruct (hc_to_mid tmw w P Hctr h2_b2 h2_lh c n Hc Hn) as (Hin & N & HN).
    fold X in Hin, HN.
    destruct (andb_prop _ _ (Hx X Hin)) as [Hs Hm]. apply Nat.leb_le in Hm.
    split; [exact Hin |]. split; [exact Hs |]. split; [exact Hm |].
    exists N. exact HN.
Qed.

(** one step of the enumeration *)
Lemma h2_lap_at : forall i c n, i < hcL w -> canon b lo hi c -> hc_nmin (hcph w i) <= n ->
  hc_nmin (hcph w (hcnx w i)) <= h2_nn i c n /\
  exists N, 0 < N /\
  stepn tmw N (lift (hcC w (hcph w i) c n))
  = Some (lift (hcC w (hcph w (hcnx w i)) (csucc b lo hi c) (h2_nn i c n))).
Proof.
  intros i c n Hi Hc Hn.
  destruct (h2_is_hold_ovf i c) eqn:Eo.
  - unfold h2_is_hold_ovf in Eo.
    destruct (h2_hold W i) as [Ph|] eqn:Eh; [| discriminate].
    destruct c as [low tv]. cbn [fst snd] in Eo.
    destruct (firstlow b low) eqn:Ef; [discriminate |].
    apply Nat.eqb_eq in Eo.
    destruct Hc as (Hf & Hl & Hh); cbn [fst snd] in *.
    pose proof h2_b2 as Hb2. pose proof h2_lh as Hlh.
    assert (Hm : low = repeat (b - 1) (length low)).
    { destruct (low_shape b lo hi Hb2 Hlh low Hf) as [(j & d & r & -> & Hd) | Hm];
        [| exact Hm].
      rewrite (firstlow_int b j d r ltac:(lia) Hd) in Ef. discriminate. }
    set (j := length low) in Hm. rewrite Hm.
    assert (Etv : tv = pred hi) by lia. subst tv.
    unfold h2_nn, h2_is_hold_ovf. rewrite Eh. cbn [fst snd].
    rewrite (firstlow_max b j ltac:(lia)).
    replace (S (pred hi) =? hi) with true by (symmetry; apply Nat.eqb_eq; lia).
    assert (EX : hc_exit_of w (hcph w i) (repeat (b - 1) j, pred hi)
                 = hcX (hcph w i) (hk_ex (h2_ovf W (hcph w i)))).
    { unfold hc_exit_of, hc_kase; cbn [fst snd]. rewrite (firstlow_max b j ltac:(lia)).
      unfold h2_ovf. do 3 f_equal. lia. }
    rewrite EX.
    rewrite csucc_ovf by (lia || (cbn; lia)).
    destruct (h2_hold_first i Ph Hi Eh j n Hn) as (Hn1 & _ & N1 & HN1 & H1).
    destruct (h2_hold_second i Ph Hi Eh j _ Hn1) as (Hn2 & _ & N2 & HN2 & H2).
    split; [exact Hn2 |].
    exists (N1 + N2). split; [lia |].
    rewrite stepn_add, H1, H2. reflexivity.
  - destruct (h2_plain i c n Hi Hc Hn Eo) as (_ & Hs & Hm & N1 & H1).
    set (X := hc_exit_of w (hcph w i) c) in *.
    assert (En : h2_nn i c n = n - hc_nminX (hcph w i) X + he_c X).
    { unfold h2_nn. fold X. destruct (h2_hold W i); [rewrite Eo |]; reflexivity. }
    rewrite En. split; [lia |].
    destruct (hc_sweep_main tmw w _ X _ Hs (csucc b lo hi c) (n - hc_nminX (hcph w i) X))
      as (N2 & c2 & H2 & Hl2 & HN2).
    exists (N1 + N2). split; [lia |].
    rewrite stepn_add, H1, (lap_stepn _ _ _ _ _ H2 Hl2). reflexivity.
Qed.

(** from an anchor, the mid of the case's exit (with some counter) *)
Lemma h2_to_mid : forall i c n, i < hcL w -> canon b lo hi c -> hc_nmin (hcph w i) <= n ->
  let X := hc_exit_of w (hcph w i) c in
  exists c'' k N, stepn tmw N (lift (hcC w (hcph w i) c n))
                  = Some (lift (hcM w (hcph w i) X c'' (he_na X + k + he_nb X))).
Proof.
  intros i c n Hi Hc Hn X.
  destruct (h2_is_hold_ovf i c) eqn:Eo.
  - unfold h2_is_hold_ovf in Eo.
    destruct (h2_hold W i) as [Ph|] eqn:Eh; [| discriminate].
    destruct c as [low tv]. cbn [fst snd] in Eo.
    destruct (firstlow b low) eqn:Ef; [discriminate |].
    apply Nat.eqb_eq in Eo.
    destruct Hc as (Hf & Hl & Hh); cbn [fst snd] in *.
    pose proof h2_b2 as Hb2. pose proof h2_lh as Hlh.
    assert (Hm : low = repeat (b - 1) (length low)).
    { destruct (low_shape b lo hi Hb2 Hlh low Hf) as [(j & d & r & -> & Hd) | Hm];
        [| exact Hm].
      rewrite (firstlow_int b j d r ltac:(lia) Hd) in Ef. discriminate. }
    assert (Etv : tv = pred hi) by lia. subst tv.
    assert (EX : X = hcX (hcph w i) (hk_ex (h2_ovf W (hcph w i)))).
    { unfold X, hc_exit_of, hc_kase; cbn [fst snd]. rewrite Ef.
      unfold h2_ovf. do 3 f_equal. lia. }
    rewrite EX. rewrite Hm.
    destruct (h2_hold_first i Ph Hi Eh (length low) n Hn) as (_ & (N & HN) & _).
    eexists _, _, N. exact HN.
  - destruct (h2_plain i c n Hi Hc Hn Eo) as (_ & _ & _ & N & HN).
    eexists _, _, N. exact HN.
Qed.

Definition h2S : Type := ((list nat * nat) * nat * nat)%type.

Definition h2A (s : h2S) : cconf :=
  let '(c, n, i) := s in hcC w (hcph w i) c n.

Definition h2_good (s : h2S) : Prop :=
  let '(c, n, i) := s in
  canon b lo hi c /\ hcv0 w <= cval b lo hi c /\ i = hc_phase_of w (cval b lo hi c)
  /\ hc_nmin (hcph w i) <= n.

Definition h2_nxt (s : h2S) : h2S :=
  let '(c, n, i) := s in (csucc b lo hi c, h2_nn i c n, hcnx w i).

Lemma h2_phase_lt : forall x, hc_phase_of w x < hcL w.
Proof. intros x. unfold hc_phase_of. apply Nat.mod_upper_bound. pose proof h2_L_pos. lia. Qed.

Lemma h2_phase_succ : forall x, hcv0 w <= x ->
  hc_phase_of w (S x) = hcnx w (hc_phase_of w x).
Proof.
  intros x Hx. pose proof h2_L_pos as HL.
  unfold hc_phase_of, hcnx.
  replace (hcc_i0 w + (S x - hcv0 w)) with (1 + (hcc_i0 w + (x - hcv0 w))) by lia.
  symmetry. exact (Nat.Div0.add_mod_idemp_r 1 _ _).
Qed.

Lemma h2_phase_cong : forall x y, hcv0 w <= x -> hcv0 w <= y ->
  x mod hcL w = y mod hcL w -> hc_phase_of w x = hc_phase_of w y.
Proof.
  intros x y Hx Hy H. pose proof h2_L_pos as HL. unfold hc_phase_of.
  apply (mod_cancel_r (hcL w) _ _ (hcv0 w)); [lia |].
  replace (hcc_i0 w + (x - hcv0 w) + hcv0 w) with (hcc_i0 w + x) by lia.
  replace (hcc_i0 w + (y - hcv0 w) + hcv0 w) with (hcc_i0 w + y) by lia.
  rewrite (Nat.Div0.add_mod (hcc_i0 w) x), (Nat.Div0.add_mod (hcc_i0 w) y), H.
  reflexivity.
Qed.

Lemma h2_step : forall s, h2_good s -> h2_good (h2_nxt s) /\ exists N, 0 < N /\
  stepn tmw N (lift (h2A s)) = Some (lift (h2A (h2_nxt s))).
Proof.
  intros [[c n] i] (Hc & Hv & Hi & Hn). cbn [h2_nxt h2A h2_good].
  assert (Hil : i < hcL w) by (rewrite Hi; apply h2_phase_lt).
  destruct (h2_lap_at i c n Hil Hc Hn) as (Hm & HL).
  destruct (canon_succ b lo hi h2_b2 h2_lh c Hc) as (Hc' & Hv').
  split; [| exact HL].
  split; [exact Hc' |]. rewrite Hv'. split; [lia |].
  split; [rewrite Hi; symmetry; exact (h2_phase_succ _ Hv) | exact Hm].
Qed.

Lemma h2_reach : forall D s, h2_good s ->
  exists T s', h2_good s' /\ cval b lo hi (fst (fst s')) = cval b lo hi (fst (fst s)) + D /\
    stepn tmw T (lift (h2A s)) = Some (lift (h2A s')).
Proof.
  induction D as [|D IH]; intros s Hg.
  - exists 0, s. split; [exact Hg |]. split; [lia | reflexivity].
  - destruct (IH s Hg) as (T & s' & Hg' & Hv & HT).
    destruct (h2_step s' Hg') as (Hg'' & N & _ & HN).
    exists (T + N), (h2_nxt s'). split; [exact Hg'' |]. split.
    + destruct s' as [[c1 n1] i1]. cbn [h2_nxt fst] in *.
      destruct Hg' as (Hc1 & _).
      rewrite (proj2 (canon_succ b lo hi h2_b2 h2_lh c1 Hc1)). lia.
    + rewrite stepn_add, HT. exact HN.
Qed.

Lemma h2_reach_at : forall s c', h2_good s -> canon b lo hi c' ->
  cval b lo hi (fst (fst s)) <= cval b lo hi c' ->
  exists T n', hc_nmin (hcph w (hc_phase_of w (cval b lo hi c'))) <= n' /\
    stepn tmw T (lift (h2A s))
    = Some (lift (hcC w (hcph w (hc_phase_of w (cval b lo hi c'))) c' n')).
Proof.
  intros s c' Hg Hc' Hle.
  destruct (h2_reach (cval b lo hi c' - cval b lo hi (fst (fst s))) s Hg)
    as (T & [[c1 n1] i1] & (Hc1 & Hv1 & Hi1 & Hn1) & He & HT).
  cbn [fst] in He.
  assert (Ec : c1 = c').
  { apply (canon_inj b lo hi h2_b2 h2_lh _ _ Hc1 Hc'). lia. }
  subst c1 i1. exists T, n1. auto.
Qed.

Lemma h2_int_member : forall i d j H0, hc_int_fam_ok w i d j H0 = true ->
  forall s, h2_good s -> exists r tv,
  let c' := (repeat (b - 1) j ++ d :: r, tv) in
  canon b lo hi c' /\ S d < b /\ cval b lo hi (fst (fst s)) <= cval b lo hi c'
  /\ hc_phase_of w (cval b lo hi c') = i.
Proof.
  intros i d j H0 Hf s Hg.
  pose proof h2_L_pos as HL. pose proof h2_b2 as Hb2.
  unfold hc_int_fam_ok in Hf.
  apply andb_prop in Hf as [Hf Hph]. apply andb_prop in Hf as [Hd Hx].
  apply Nat.ltb_lt in Hd. apply Nat.leb_le in Hx. apply Nat.eqb_eq in Hph.
  set (x0 := cval b lo hi (fst (fst s))).
  destruct (canon_exists b lo hi h2_b2 h2_lh (H0 + hcL w * x0)) as ([r tv] & Hr & Hrv).
  exists r, tv. cbv zeta.
  assert (Hc' : canon b lo hi (repeat (b - 1) j ++ d :: r, tv)).
  { destruct Hr as (Hrf & Hrl & Hrh). split; [| exact (conj Hrl Hrh)].
    cbn [fst]. apply Forall_app. split; [apply forall_repeat; lia | constructor; [lia | exact Hrf]]. }
  assert (Hcv : cval b lo hi (repeat (b - 1) j ++ d :: r, tv)
                = ((hi - lo) * G b (S j) + (b ^ j - 1) + b ^ j * d + b ^ S j * H0)
                  + (b ^ S j * x0) * hcL w).
  { rewrite (cval_int _ _ _ h2_b2 h2_lh), Hrv. nia. }
  pose proof (Nat.pow_nonzero b (S j) ltac:(lia)) as Hpz.
  split; [exact Hc' |]. split; [exact Hd |]. split; [rewrite Hcv; nia |].
  rewrite <- Hph. apply h2_phase_cong; [lia | exact Hx |].
  rewrite Hcv. apply Nat.Div0.mod_add.
Qed.

Lemma h2_top_member : forall i e j0 TT, hc_top_fam_ok w i e j0 TT = true ->
  forall s, h2_good s -> exists j, j0 <= j /\
  let c' := (repeat (b - 1) j, lo + e) in
  canon b lo hi c' /\ cval b lo hi (fst (fst s)) <= cval b lo hi c'
  /\ hc_phase_of w (cval b lo hi c') = i.
Proof.
  intros i e j0 TT Hf s Hg.
  pose proof h2_L_pos as HL. pose proof h2_b2 as Hb2. pose proof h2_lh as Hlh.
  unfold hc_top_fam_ok in Hf.
  apply andb_prop in Hf as [Hf Hph]. apply andb_prop in Hf as [Hf Hx].
  apply andb_prop in Hf as [Hf Hper]. apply andb_prop in Hf as [He HT].
  apply Nat.ltb_lt in He. apply Nat.leb_le in HT, Hx. apply Nat.eqb_eq in Hph, Hper.
  rewrite !ytop_mod_spec in Hper by lia.
  set (x0 := cval b lo hi (fst (fst s))).
  set (j := j0 + TT * x0).
  exists j. split; [lia |]. cbv zeta.
  assert (Hc' : canon b lo hi (repeat (b - 1) j, lo + e)).
  { unfold canon; cbn [fst snd]. split; [apply forall_repeat; lia | lia]. }
  assert (Hcv : forall k, cval b lo hi (repeat (b - 1) k, lo + e) = ytop b lo hi e k - 1).
  { intros k. rewrite (cval_max _ _ _ h2_b2 h2_lh). unfold ytop.
    pose proof (Nat.pow_nonzero b k ltac:(lia)).
    replace (lo + e - lo) with e by lia. nia. }
  assert (Hmono : forall k n, ytop b lo hi e k <= ytop b lo hi e (k + n)).
  { intros k n. induction n as [|n IHn]; [rewrite Nat.add_0_r; lia |].
    rewrite Nat.add_succ_r, ytop_S. nia. }
  assert (Hpj : x0 < b ^ j).
  { apply (Nat.lt_le_trans _ (b ^ x0)); [apply Nat.pow_gt_lin_r; lia |].
    apply Nat.pow_le_mono_r; [lia | nia]. }
  split; [exact Hc' |]. split; [rewrite Hcv; unfold ytop; nia |].
  rewrite <- Hph. rewrite Hcv.
  pose proof (Hmono j0 (TT * x0)) as Hm0. fold j in Hm0.
  apply h2_phase_cong; [lia | exact Hx |].
  pose proof (ytop_period b lo hi (hcL w) e j0 TT ltac:(lia) Hper x0) as Hm.
  fold j in Hm.
  set (Z := ytop b lo hi e j) in *. set (Z0 := ytop b lo hi e j0) in *.
  assert (HZ1 : 1 <= Z0) by (unfold Z0, ytop; pose proof (Nat.pow_nonzero b j0 ltac:(lia)); nia).
  pose proof (Nat.div_mod Z (hcL w) ltac:(lia)) as HZd.
  pose proof (Nat.div_mod Z0 (hcL w) ltac:(lia)) as HZ0d.
  assert (Hd : Z0 / hcL w <= Z / hcL w) by (apply Nat.Div0.div_le_mono; lia).
  replace (Z - 1) with ((Z0 - 1) + (Z / hcL w - Z0 / hcL w) * hcL w) by nia.
  apply Nat.Div0.mod_add.
Qed.

Lemma h2_fire_case_at : forall i c' Ps XL K ch t el j, i < hcL w ->
  srun_instr tmw el false ch (hcK0 w (hcph w i) K Ps) = Some t ->
  (el = true -> XL = []) -> hk_nu K <= j ->
  hc_Lpre (hcph w i) ++ hcE w c' = hc_Lpre (hcph w i) ++ rep (hcDm w) j ++ Ps ++ XL ->
  forall s, h2_good s -> canon b lo hi c' -> cval b lo hi (fst (fst s)) <= cval b lo hi c' ->
  hc_phase_of w (cval b lo hi c') = i -> FiresFrom tmw (h2A s) t.
Proof.
  intros i c' Ps XL K ch t el j Hi H HX Hj HE s Hg Hc' Hge Hp.
  destruct (h2_reach_at s c' Hg Hc' Hge) as (T & n' & Hn' & HT).
  rewrite Hp in Hn', HT.
  apply (fires_back tmw _ _ T t HT).
  assert (Hm : hc_m (hcph w i) <= n') by (pose proof (h2_m_le (hcph w i)); lia).
  assert (E : hcC w (hcph w i) c' n'
              = hcKc w (hcph w i) Ps XL (hk_nu K + (j - hk_nu K)) (n' - hc_m (hcph w i))).
  { unfold hcC, hcKc. rewrite HE.
    replace (hk_nu K + (j - hk_nu K)) with j by lia.
    replace (hc_m (hcph w i) + (n' - hc_m (hcph w i))) with n' by lia. reflexivity. }
  rewrite E. exact (fire_case tmw w _ el K _ ch t H _ _ _ HX).
Qed.

Lemma h2_fire_exit_at : forall i c' ch t, i < hcL w ->
  srun_instr tmw false true ch (hcS0 (hcph w i) (hc_exit_of w (hcph w i) c')) = Some t ->
  forall s, h2_good s -> canon b lo hi c' -> cval b lo hi (fst (fst s)) <= cval b lo hi c' ->
  hc_phase_of w (cval b lo hi c') = i -> FiresFrom tmw (h2A s) t.
Proof.
  intros i c' ch t Hi H s Hg Hc' Hge Hp.
  destruct (h2_reach_at s c' Hg Hc' Hge) as (T & n' & Hn' & HT).
  rewrite Hp in Hn', HT.
  apply (fires_back tmw _ _ T t HT).
  destruct (h2_to_mid i c' n' Hi Hc' Hn') as (c'' & k & N & HN).
  apply (fires_back tmw _ _ N t HN).
  exact (hc_fire_sweep tmw w _ _ ch t H c'' k).
Qed.

(** the second lap of a hold, reached from a member of the overflow family *)
Lemma h2_fire_hold : forall i Ph ch t j0 TT kind, i < hcL w -> h2_hold W i = Some Ph ->
  hc_top_fam_ok w i (hi - lo - 1) j0 TT = true ->
  (kind = 4 /\ srun_instr tmw true false ch (hcK0 w Ph (h2_K2 Ph) (hcT w hi)) = Some t
             /\ hk_nu (h2_K2 Ph) <= j0
   \/ kind = 5 /\ srun_instr tmw false true ch (hcS0 Ph (hcX Ph (hk_ex (h2_K2 Ph)))) = Some t) ->
  forall s, h2_good s -> FiresFrom tmw (h2A s) t.
Proof.
  intros i Ph ch t j0 TT kind Hi Eh Hf Hk s Hg.
  destruct (h2_top_member i _ j0 TT Hf s Hg) as (j & Hjj & Hc' & Hge & Hp).
  replace (lo + (hi - lo - 1)) with (pred hi) in Hc', Hge, Hp by (pose proof h2_lh; lia).
  destruct (h2_reach_at s _ Hg Hc' Hge) as (T & n' & Hn' & HT).
  rewrite Hp in Hn', HT.
  apply (fires_back tmw _ _ T t HT).
  destruct (h2_hold_first i Ph Hi Eh j n' Hn') as (Hn1 & _ & N1 & _ & H1).
  apply (fires_back tmw _ _ N1 t H1).
  set (n1 := n' - hc_nminX (hcph w i) (hcX (hcph w i) (hk_ex (h2_ovf W (hcph w i))))
             + he_c (hcX (hcph w i) (hk_ex (h2_ovf W (hcph w i))))) in *.
  destruct Hk as [(_ & H & Hnu) | (_ & H)].
  - assert (Hm : hc_m Ph <= n1) by (pose proof (h2_m_le Ph); lia).
    rewrite h2_anchor_max by exact Hm.
    replace j with (hk_nu (h2_K2 Ph) + (j - hk_nu (h2_K2 Ph))) by lia.
    exact (fire_case tmw w Ph true (h2_K2 Ph) _ ch t H _ [] _ ltac:(reflexivity)).
  - destruct (h2_hold_second i Ph Hi Eh j n1 Hn1) as (_ & (N2 & H2) & _).
    apply (fires_back tmw _ _ N2 t H2).
    exact (hc_fire_sweep tmw w _ _ ch t H _ _).
Qed.

Lemma h2_fire_any : forall t, ~ In t (hcc_pins w) ->
  forall s, h2_good s -> FiresFrom tmw (h2A s) t.
Proof.
  intros t Hnin s Hg.
  pose proof h2_b2 as Hb2.
  destruct h2_core_parts as (_ & _ & _ & _ & H & _). unfold h2_fires_ok in H.
  rewrite forallb_forall in H.
  specialize (H t (all_Instr_complete t)).
  apply orb_prop in H as [H | H].
  { exfalso. apply Hnin, tr_inb_spec, H. }
  apply existsb_exists in H as ([i k d a bb ch] & _ & Hf).
  unfold h2_fire_ok in Hf; cbn [hcf_ph hcf_kind hcf_k hcf_a hcf_b hcf_ch] in Hf.
  destruct (k <=? 3) eqn:Ek.
  2: { apply andb_prop in Hf as [Hi Hf]. apply Nat.ltb_lt in Hi.
       destruct (h2_hold W i) as [Ph|] eqn:Eh; [| discriminate].
       destruct k as [|[|[|[|[|[|k]]]]]]; try discriminate.
       - destruct (srun_instr tmw true false ch (hcK0 w Ph (h2_K2 Ph) (hcT w hi)))
           as [t'|] eqn:E; [|discriminate].
         apply andb_prop in Hf as [Hf Hfam]. apply andb_prop in Hf as [Ht Hj].
         apply instr_eqb_spec in Ht. apply Nat.leb_le in Hj. subst t'.
         exact (h2_fire_hold i Ph ch t a bb 4 Hi Eh Hfam
                  (or_introl (conj eq_refl (conj E Hj))) s Hg).
       - destruct (srun_instr tmw false true ch (hcS0 Ph (hcX Ph (hk_ex (h2_K2 Ph)))))
           as [t'|] eqn:E; [|discriminate].
         apply andb_prop in Hf as [Ht Hfam].
         apply instr_eqb_spec in Ht. subst t'.
         exact (h2_fire_hold i Ph ch t a bb 5 Hi Eh Hfam
                  (or_intror (conj eq_refl E)) s Hg). }
  unfold hc_fire_ok in Hf; cbn [hcf_ph hcf_kind hcf_k hcf_a hcf_b hcf_ch] in Hf.
  apply andb_prop in Hf as [Hi Hf]. apply Nat.ltb_lt in Hi.
  set (KI := nth d (hc_int (hcph w i)) hk_dflt) in *.
  set (KT := nth d (hc_top (hcph w i)) hk_dflt) in *.
  destruct k as [|[|[|k]]].
  - destruct (srun_instr tmw false false ch (hcK0 w (hcph w i) KI (hcD w d))) as [t'|] eqn:E;
      [|discriminate].
    apply andb_prop in Hf as [Hf Hfam]. apply andb_prop in Hf as [Ht Hj].
    apply instr_eqb_spec in Ht. apply Nat.leb_le in Hj. subst t'.
    destruct (h2_int_member i d a bb Hfam s Hg) as (r & tv & Hc' & Hd & Hge & Hp).
    refine (h2_fire_case_at i _ (hcD w d) (hcE w (r, tv)) KI ch t false a Hi E
              ltac:(discriminate) Hj _ s Hg Hc' Hge Hp).
    rewrite hcE_int. reflexivity.
  - destruct (srun_instr tmw true false ch (hcK0 w (hcph w i) KT (hcT w (hclo w + d))))
      as [t'|] eqn:E; [|discriminate].
    apply andb_prop in Hf as [Hf Hfam]. apply andb_prop in Hf as [Ht Hj].
    apply instr_eqb_spec in Ht. apply Nat.leb_le in Hj. subst t'.
    destruct (h2_top_member i d a bb Hfam s Hg) as (j & Hjj & Hc' & Hge & Hp).
    refine (h2_fire_case_at i _ (hcT w (hclo w + d)) [] KT ch t true j Hi E
              ltac:(reflexivity) ltac:(lia) _ s Hg Hc' Hge Hp).
    rewrite hcE_max, app_nil_r. reflexivity.
  - destruct (srun_instr tmw false true ch (hcS0 (hcph w i) (hcX (hcph w i) (hk_ex KI))))
      as [t'|] eqn:E; [|discriminate].
    apply andb_prop in Hf as [Ht Hfam].
    apply instr_eqb_spec in Ht. subst t'.
    destruct (h2_int_member i d a bb Hfam s Hg) as (r & tv & Hc' & Hd & Hge & Hp).
    refine (h2_fire_exit_at i _ ch t Hi _ s Hg Hc' Hge Hp).
    unfold hc_exit_of, hc_kase; cbn [fst].
    rewrite (firstlow_int (hcb w) a d r ltac:(lia) Hd). exact E.
  - destruct (srun_instr tmw false true ch (hcS0 (hcph w i) (hcX (hcph w i) (hk_ex KT))))
      as [t'|] eqn:E; [|discriminate].
    apply andb_prop in Hf as [Ht Hfam].
    apply instr_eqb_spec in Ht. subst t'.
    destruct (h2_top_member i d a bb Hfam s Hg) as (j & _ & Hc' & Hge & Hp).
    refine (h2_fire_exit_at i _ ch t Hi _ s Hg Hc' Hge Hp).
    unfold hc_exit_of, hc_kase; cbn [fst snd].
    rewrite (firstlow_max (hcb w) j ltac:(lia)).
    replace (hclo w + d - hclo w) with d by lia. exact E.
Qed.

(** ** The enumeration *)

Definition h2_s0 : h2S := ((hcc_low0 w, hcc_tv0 w), hcc_n0 w, hcc_i0 w).

Lemma h2_good_s0 : h2_good h2_s0.
Proof.
  destruct h2_core_parts as (_ & _ & Hc & _ & _ & Hi & Hn).
  unfold hc_canon0 in Hc.
  apply andb_prop in Hc as [Hc Hh]. apply andb_prop in Hc as [Hf Hl].
  rewrite forallb_forall in Hf. apply Nat.leb_le in Hl. apply Nat.ltb_lt in Hh.
  cbn [h2_s0 h2_good]. split; [| split; [unfold hcv0; lia | split; [| exact Hn]]].
  - split; [| cbn [snd]; auto]. cbn [fst].
    apply Forall_forall. intros x Hx. apply Nat.ltb_lt, Hf, Hx.
  - unfold hc_phase_of, hcv0. rewrite Nat.sub_diag, Nat.add_0_r. symmetry.
    apply Nat.mod_small. exact Hi.
Qed.

Definition h2_st (k : nat) : h2S := Nat.iter k h2_nxt h2_s0.

Lemma h2_st_good : forall k, h2_good (h2_st k).
Proof.
  induction k as [|k IH]; [exact h2_good_s0 |].
  cbn [h2_st Nat.iter nat_rect]. exact (proj1 (h2_step _ IH)).
Qed.

Definition h2Cf (p : positive) : cconf := h2A (h2_st (Pos.to_nat p - 1)).

Lemma h2_Hlap : forall p, (1 <= p)%positive ->
  exists n c', csteps tmw n (h2Cf p) = Some c' /\
               lift c' = lift (h2Cf (Pos.succ p)) /\ 0 < n.
Proof.
  intros p _.
  destruct (h2_step _ (h2_st_good (Pos.to_nat p - 1))) as (_ & N & HN & H).
  destruct (stepn_csteps_at tmw N (h2Cf p) _ H) as (c' & Hc & Hl).
  exists N, c'. split; [exact Hc |]. split; [| exact HN].
  rewrite Hl. unfold h2Cf. f_equal. f_equal.
  rewrite Pos2Nat.inj_succ. pose proof (Pos2Nat.is_pos p).
  replace (S (Pos.to_nat p) - 1) with (S (Pos.to_nat p - 1)) by lia.
  reflexivity.
Qed.

Lemma h2_Hfire : forall t, ~ In t (hcc_pins w) -> forall p, (1 <= p)%positive ->
  exists k c, csteps tmw k (h2Cf p) = Some c /\ cinstr c = t.
Proof.
  intros t Hnin p _. apply fire_csteps_of_lift.
  exact (h2_fire_any t Hnin _ (h2_st_good _)).
Qed.

End Sound.

Lemma h2_boot : forall tm W, hc_boot_ok (h2_w W) tm = true ->
  stepn tm (hcc_t0 (h2_w W)) InitES = Some (lift (h2Cf W xH)).
Proof.
  intros tm W Hb. unfold hc_boot_ok in Hb.
  destruct (csteps tm (hcc_t0 (h2_w W)) c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E).
  f_equal. unfold h2Cf. cbn [Pos.to_nat Pos.iter_op Nat.sub].
  cbn [h2_st Nat.iter nat_rect h2_s0 h2A].
  exact (ceqb_lift _ _ Hb).
Qed.

Theorem h2_sound_nqh : forall tm W, h2_check_nqh tm W = true -> NeverQuasiHaltsTr tm.
Proof.
  intros tm W H. unfold h2_check_nqh in H.
  apply andb_prop in H as [Hb Hc].
  apply (glue_neverqhtr tm (hcc_pins (h2_w W)) (h2Cf W) xH).
  - exists (hcc_t0 (h2_w W)). exact (h2_boot _ W Hb).
  - exact (h2_Hlap _ W Hc).
  - exact (h2_Hfire _ W Hc).
Qed.

(** the counter sits on the RIGHT: certify the mirror *)
Theorem h2_sound_nqh_mirror : forall tm W, h2_check_nqh (mirror_tm tm) W = true ->
  NeverQuasiHaltsTr tm.
Proof.
  intros tm W H. exact (neverqhtr_mirror tm (h2_sound_nqh _ W H)).
Qed.
