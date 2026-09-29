(** * SweepGlueNeverTr: the never-quasihalting sweep counters, by a
    multi-family two-index lap glue.

    [SweepGlueTr] settles the QUIET sweep counters (class QH) with one
    anchor family [swC i k] and a boot on the original machine.  The dense
    sweep counters of class DN (SCOPING_INSTR.md 7.4.DX, 7.4.SW) keep
    every defined instruction firing, so the conclusion here is
    [NeverQuasiHaltsTr] through [LapGlueTr.glue_neverqhtr], the pins are
    the instructions claimed NEVER to fire (the undefined ones), and the
    boot runs on the wrapped machine.  Two shapes the one-family glue
    cannot express are common among them:

    - BEHIND sweeps.  The inner lap [(i, S k) -> (S i, k)] may sweep the
      [i] units BEHIND the hole (the growing side, out to the tape's end
      and back) while the [k] units ahead stay untouched: the chain's
      index is [i] and its RIGHT tail is opaque ([sb_inner_ok], from
      [swAb]; the anchors with fewer than [na + nb] units behind take the
      concrete [f_base] chains).  The AHEAD sweep is [SweepGlueTr]'s own
      inner lap, reused through [fam_sw].
    - PARITY.  When the block grows by one cell per round but the units
      are two cells, consecutive rounds use different anchor splits
      ([Lpost]/[Rpost] alternate).  So a certificate carries a CYCLE of
      anchor families [f_0 .. f_(P-1)]: the inner lap stays in its family,
      and the outer lap of [f_j] lands on [f_(j+1 mod P)] at
      [(e_j, i + d_j)].  The block size [i + k] never shrinks, and grows
      by [e_0 + d_0 >= 1] each time family 0 closes a round.

    The glue is the enumeration of the anchors [(j, i, k)] along [sn_nxt];
    the fires come from chain prefixes of any family's inner or outer lap,
    reached from every visited anchor by cycling the families until the
    block is large enough ([sn_reach_fam]).  A certificate is data
    ([swncert]), [sweep_nqh_check] is one boolean under [vm_compute], and
    a board row is one line: [apply coversTr_nqh, (sweep_nqh_sound _ (mkSWN
    ...))] ([sweep_nqh_sound_mirror] when the hole moves left). *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape Mirror.
From BBB4.Checkers Require Import WrapTr LapDecider.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
From BBB4.Counters Require Import WTape LapCertGlueLift LapGlueTr SweepGlueTr.
From BBB4.CensusTr Require Import TNF_QHTr.
Import ListNotations.

(** ** The certificate *)

Record swfam := mkF {
  f_q      : St;
  f_h      : Sym;
  f_Lpre   : list Sym;
  f_uL     : list Sym;
  f_Lpost  : list Sym;
  f_Rpre   : list Sym;
  f_uR     : list Sym;
  f_Rpost  : list Sym;
  f_behind : bool;           (** the inner lap sweeps the units behind *)
  f_na     : nat;            (** inner start: units unrolled at the near end *)
  f_nb     : nat;            (** ... and at the far end *)
  f_chi    : list lstep;     (** inner lap, from [swA0] (ahead) or [swAb] (behind) *)
  f_base   : list (list lstep);  (** the inner laps too short for [f_chi] *)
  f_ma     : nat;            (** outer start: units unrolled at the near end *)
  f_mb     : nat;            (** ... and at the far end *)
  f_cho    : list lstep;     (** outer lap, from [swOB], onto the next family *)
  f_e      : nat;            (** ... landing on [(e, i + d)] *)
  f_d      : nat
}.

Record swncert := mkSWN {
  sn_pins  : list Instr;     (** claimed never to fire (the undefined ones) *)
  sn_fams  : list swfam;     (** the cycle of anchor families *)
  sn_M     : nat;            (** every visited anchor has [i + k >= M] *)
  sn_fires : list (nat * bool * list lstep);  (** (family, outer?, chain prefix) *)
  sn_t0    : nat;            (** boot index, on the wrapped machine *)
  sn_j0    : nat;
  sn_i0    : nat;
  sn_k0    : nat
}.

Definition fC (f : swfam) (i k : nat) : cconf :=
  (f_q f, (f_Lpre f ++ rep (f_uL f) i ++ f_Lpost f, f_h f,
           f_Rpre f ++ rep (f_uR f) k ++ f_Rpost f)).

(** a family as [SweepGlueTr]'s certificate: its ahead inner lap is
    [sw_inner_lap] verbatim *)
Definition fam_sw (pins : list Instr) (f : swfam) : swcert :=
  mkSW pins (f_q f) (f_h f) (f_Lpre f) (f_uL f) (f_Lpost f)
       (f_Rpre f) (f_uR f) (f_Rpost f) (f_e f) (f_d f) (f_na f) (f_nb f)
       (f_chi f) (f_base f) (f_ma f) (f_mb f) (f_cho f) [] 0 0 0.

(** the behind inner lap's start: [na + i + nb] units behind (a chain
    with index [i]), the first unit ahead concrete, the rest of the right
    side the opaque tail *)
Definition swAb (f : swfam) : sconf :=
  mkC (f_q f) (mkS (f_Lpre f ++ rep (f_uL f) (f_na f)) (f_uL f) 1 0
                   (rep (f_uL f) (f_nb f) ++ f_Lpost f)) (f_h f)
      (sflat (f_Rpre f ++ f_uR f)).

Definition swBb (f : swfam) (i : nat) : sconf :=
  mkC (f_q f) (sflat (f_Lpre f ++ rep (f_uL f) i ++ f_Lpost f)) (f_h f)
      (sflat (f_Rpre f ++ f_uR f)).

(** the outer lap's start: [ma + i + mb] units behind, none ahead *)
Definition swOB (f : swfam) : sconf :=
  mkC (f_q f) (mkS (f_Lpre f ++ rep (f_uL f) (f_ma f)) (f_uL f) 1 0
                   (rep (f_uL f) (f_mb f) ++ f_Lpost f)) (f_h f)
      (sflat (f_Rpre f ++ f_Rpost f)).

(** the ahead inner lap's start ([SweepGlueTr.swA0]) *)
Definition swAa (f : swfam) : sconf :=
  mkC (f_q f) (sflat (f_Lpre f)) (f_h f)
      (mkS (f_Rpre f ++ rep (f_uR f) (f_na f)) (f_uR f) 1 0
           (rep (f_uR f) (f_nb f) ++ f_Rpost f)).

(** ** The checker *)

Definition sb_inner_ok (tmw : TM) (f : swfam) : bool :=
  match srun tmw true false (f_chi f) (swAb f) with
  | Some (c1, _, cb) =>
      st_eqb (c_st c1) (f_q f) && sym_eqb (c_h c1) (f_h f)
      && sside_flat_is (c_r c1) (f_Rpre f)
      && sside_end_is (c_l c1) (f_Lpre f) (f_uL f)
                      (f_na f + f_nb f + 1) (f_Lpost f)
      && (0 <? cb)
  | None => false
  end.

Definition sb_base1_ok (tmw : TM) (f : swfam) (i : nat) (ch : list lstep) : bool :=
  match srun tmw true false ch (swBb f i) with
  | Some (c1, _, cb) =>
      st_eqb (c_st c1) (f_q f) && sym_eqb (c_h c1) (f_h f)
      && sside_flat_is (c_r c1) (f_Rpre f)
      && syms_eqb (s_u (c_l c1)) [] && syms_eqb (s_post (c_l c1)) []
      && lpad_eqb (s_pre (c_l c1)) (f_Lpre f ++ rep (f_uL f) (S i) ++ f_Lpost f)
      && (0 <? cb)
  | None => false
  end.

Fixpoint sb_base_from (tmw : TM) (f : swfam) (i : nat) (l : list (list lstep)) : bool :=
  match l with
  | [] => true
  | ch :: l' => sb_base1_ok tmw f i ch && sb_base_from tmw f (S i) l'
  end.

Definition sb_base_ok (tmw : TM) (f : swfam) : bool :=
  sb_base_from tmw f 0 (f_base f) && (f_na f + f_nb f <=? length (f_base f)).

Definition sn_outer_ok (tmw : TM) (f g : swfam) : bool :=
  match srun tmw true true (f_cho f) (swOB f) with
  | Some (c1, _, cb) =>
      st_eqb (c_st c1) (f_q g) && sym_eqb (c_h c1) (f_h g)
      && syms_eqb (s_u (c_l c1)) [] && syms_eqb (s_post (c_l c1)) []
      && lpad_eqb (s_pre (c_l c1)) (f_Lpre g ++ rep (f_uL g) (f_e f) ++ f_Lpost g)
      && sside_end_is (c_r c1) (f_Rpre g) (f_uR g)
                      (f_ma f + f_mb f + f_d f) (f_Rpost g)
      && (0 <? cb)
  | None => false
  end.

Definition sn_inner_ok (tmw : TM) (pins : list Instr) (f : swfam) : bool :=
  if f_behind f then sb_inner_ok tmw f && sb_base_ok tmw f
  else sw_inner_ok tmw (fam_sw pins f) && sw_base_ok tmw (fam_sw pins f).

Definition sn_fam (w : swncert) (j : nat) : swfam :=
  nth j (sn_fams w) (mkF StA S0 [] [] [] [] [] [] false 0 0 [] [] 0 0 [] 0 0).

Definition sn_P (w : swncert) : nat := length (sn_fams w).

Definition sn_fnxt (w : swncert) (j : nat) : nat :=
  if S j <? sn_P w then S j else 0.

Definition sn_fams_ok (tmw : TM) (w : swncert) : bool :=
  forallb (fun j => sn_inner_ok tmw (sn_pins w) (sn_fam w j)
                    && sn_outer_ok tmw (sn_fam w j) (sn_fam w (sn_fnxt w j))
                    && (f_ma (sn_fam w j) + f_mb (sn_fam w j) <=? sn_M w))
          (seq 0 (sn_P w)).

Definition sn_fire_ok (tmw : TM) (w : swncert) (t : Instr)
                      (x : nat * bool * list lstep) : bool :=
  let '(j, o, ch) := x in
  let f := sn_fam w j in
  (j <? sn_P w) &&
  match (if o then srun_instr tmw true true ch (swOB f)
         else if f_behind f then srun_instr tmw true false ch (swAb f)
         else srun_instr tmw false true ch (swAa f)) with
  | Some t' => instr_eqb t' t
  | None => false
  end.

Definition sn_fires_ok (tmw : TM) (w : swncert) : bool :=
  forallb (fun t => tr_inb t (sn_pins w)
                    || existsb (sn_fire_ok tmw w t) (sn_fires w)) all_Instr.

Definition sn_boot_ok (tmw : TM) (w : swncert) : bool :=
  match csteps tmw (sn_t0 w) c0 with
  | Some c => ceqb c (fC (sn_fam w (sn_j0 w)) (sn_i0 w) (sn_k0 w))
  | None => false
  end.

Definition sweep_nqh_check (tm : TM) (w : swncert) : bool :=
  let tmw := tm_wrap_trs tm (sn_pins w) in
  (1 <=? sn_P w) && (sn_j0 w <? sn_P w)
  && (sn_M w <=? sn_i0 w + sn_k0 w)
  && (1 <=? f_e (sn_fam w 0) + f_d (sn_fam w 0))
  && sn_boot_ok tmw w && sn_fams_ok tmw w && sn_fires_ok tmw w.

(** ** Soundness *)

Ltac sn_split :=
  repeat match goal with
  | H : _ && _ = true |- _ => apply andb_prop in H as [? ?]
  end.

Ltac sn_props :=
  repeat match goal with
  | H : st_eqb _ _ = true |- _ => apply st_eqb_spec in H
  | H : sym_eqb _ _ = true |- _ => apply sym_eqb_spec in H
  | H : syms_eqb _ _ = true |- _ => apply syms_eqb_eq in H
  | H : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in H
  | H : Nat.leb _ _ = true |- _ => apply Nat.leb_le in H
  | H : Nat.ltb _ _ = true |- _ => apply Nat.ltb_lt in H
  end.

(** *** One family *)

Section Fam.

Variable tmw : TM.
Variable f : swfam.

Lemma swAb_den : forall n k,
  cden [] (rep (f_uR f) k ++ f_Rpost f) n (swAb f)
  = fC f (f_na f + n + f_nb f) (S k).
Proof.
  intros n k. unfold cden, swAb, fC, sden, sflat;
    cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post rep].
  replace (1 * n + 0) with n by lia. rewrite rep_nil, !app_nil_r.
  rewrite !rep_add, <- !app_assoc. reflexivity.
Qed.

Lemma swBb_den : forall i k,
  cden [] (rep (f_uR f) k ++ f_Rpost f) 0 (swBb f i) = fC f i (S k).
Proof.
  intros i k. unfold cden, swBb, fC, sden, sflat;
    cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post rep].
  rewrite !app_nil_r, <- !app_assoc. reflexivity.
Qed.

Lemma swOB_den : forall i,
  cden [] [] i (swOB f) = fC f (f_ma f + i + f_mb f) 0.
Proof.
  intros i. unfold cden, swOB, fC, sden, sflat;
    cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post rep].
  replace (1 * i + 0) with i by lia. rewrite !app_nil_r.
  rewrite !rep_add, <- !app_assoc. reflexivity.
Qed.

Lemma swAa_den : forall i k,
  cden (rep (f_uL f) i ++ f_Lpost f) [] k (swAa f)
  = fC f i (f_na f + k + f_nb f).
Proof.
  intros i k. unfold cden, swAa, fC, sden, sflat;
    cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post rep].
  replace (1 * k + 0) with k by lia. rewrite !app_nil_r.
  rewrite !rep_add, <- !app_assoc. reflexivity.
Qed.

(** the behind inner lap, [na + n + nb] units behind *)
Lemma sb_inner_main : sb_inner_ok tmw f = true -> forall n k, exists m c',
  csteps tmw m (fC f (f_na f + n + f_nb f) (S k)) = Some c' /\
  lift c' = lift (fC f (S (f_na f + n + f_nb f)) k) /\ 0 < m.
Proof.
  intros H n k. unfold sb_inner_ok in H.
  destruct (srun tmw true false (f_chi f) (swAb f)) as [[[c1 ca] cb]|] eqn:E;
    [|discriminate].
  destruct c1 as [q1 [lp lu la lb lq] h1 [rp ru ra rb rq]].
  unfold sside_flat_is, sside_end_is in H;
    cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post] in H.
  sn_split.
  match goal with Hx : existsb _ _ = true |- _ =>
    apply existsb_exists in Hx as (x & Hxin & Hx) end.
  apply in_seq in Hxin.
  sn_split. sn_props. subst.
  set (c := f_na f + f_nb f + 1) in *.
  exists (ca * n + cb),
    (cden [] (rep (f_uR f) k ++ f_Rpost f) n
          (mkC (f_q f) (mkS (f_Lpre f ++ rep (f_uL f) x) (f_uL f) 1 lb lq) (f_h f)
               (mkS (f_Rpre f) [] ra rb []))).
  split; [| split; [| lia]].
  - rewrite <- swAb_den.
    exact (srun_sound tmw true false (f_chi f) (swAb f) _ ca cb E
             [] (rep (f_uR f) k ++ f_Rpost f) n
             ltac:(reflexivity) ltac:(discriminate)).
  - unfold cden, fC, sden; cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    rewrite rep_nil, !app_nil_r.
    apply lift_lpad; [| apply lpad_eqb_refl].
    replace (S (f_na f + n + f_nb f))
      with (x + ((1 * n + lb) + (c - lb - x))) by lia.
    rewrite !rep_add, <- !app_assoc.
    repeat apply lpad_eqb_app. assumption.
Qed.

Lemma sb_base_from_nth : forall l i0, sb_base_from tmw f i0 l = true ->
  forall i ch, nth_error l i = Some ch -> sb_base1_ok tmw f (i0 + i) ch = true.
Proof.
  induction l as [|ch0 l IH]; intros i0 H i ch Hi.
  - destruct i; discriminate.
  - cbn [sb_base_from] in H. apply andb_prop in H as [H0 H].
    destruct i as [|i]; cbn in Hi.
    + injection Hi as <-. rewrite Nat.add_0_r. exact H0.
    + replace (i0 + S i) with (S i0 + i) by lia. exact (IH (S i0) H i ch Hi).
Qed.

(** a concrete behind inner lap: [i < na + nb] units behind *)
Lemma sb_inner_base : sb_base_ok tmw f = true -> forall i k,
  i < f_na f + f_nb f -> exists m c',
  csteps tmw m (fC f i (S k)) = Some c' /\ lift c' = lift (fC f (S i) k) /\ 0 < m.
Proof.
  intros Hb i k Hi. unfold sb_base_ok in Hb.
  apply andb_prop in Hb as [Hb Hlen]. apply Nat.leb_le in Hlen.
  destruct (nth_error (f_base f) i) as [ch|] eqn:Ech.
  2: { apply nth_error_None in Ech. lia. }
  pose proof (sb_base_from_nth _ 0 Hb i ch Ech) as H. cbn [Nat.add] in H.
  unfold sb_base1_ok in H.
  destruct (srun tmw true false ch (swBb f i)) as [[[c1 ca] cb]|] eqn:E;
    [|discriminate].
  destruct c1 as [q1 [lp lu la lb lq] h1 [rp ru ra rb rq]].
  unfold sside_flat_is in H; cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post] in H.
  sn_split. sn_props. subst.
  exists (ca * 0 + cb),
    (cden [] (rep (f_uR f) k ++ f_Rpost f) 0
          (mkC (f_q f) (mkS lp [] la lb []) (f_h f) (mkS (f_Rpre f) [] ra rb []))).
  split; [| split; [| lia]].
  - rewrite <- swBb_den.
    exact (srun_sound tmw true false ch (swBb f i) _ ca cb E
             [] (rep (f_uR f) k ++ f_Rpost f) 0
             ltac:(reflexivity) ltac:(discriminate)).
  - unfold cden, fC, sden; cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    rewrite !rep_nil, !app_nil_r.
    apply lift_lpad; [assumption | apply lpad_eqb_refl].
Qed.

Lemma sb_inner_lap : sb_inner_ok tmw f = true -> sb_base_ok tmw f = true ->
  forall i k, exists m c',
  csteps tmw m (fC f i (S k)) = Some c' /\ lift c' = lift (fC f (S i) k) /\ 0 < m.
Proof.
  intros Hin Hb i k.
  destruct (lt_dec i (f_na f + f_nb f)) as [Hlt | Hge].
  - exact (sb_inner_base Hb i k Hlt).
  - destruct (sb_inner_main Hin (i - (f_na f + f_nb f)) k) as (m & c' & H1 & H2 & H3).
    replace (f_na f + (i - (f_na f + f_nb f)) + f_nb f) with i in H1, H2 by lia.
    exists m, c'. auto.
Qed.

End Fam.

(** the outer lap, from family [f] onto family [g] *)
Lemma sn_outer_main : forall tmw f g, sn_outer_ok tmw f g = true -> forall i,
  exists n c',
  csteps tmw n (fC f (f_ma f + i + f_mb f) 0) = Some c' /\
  lift c' = lift (fC g (f_e f) (i + (f_ma f + f_mb f + f_d f))) /\ 0 < n.
Proof.
  intros tmw f g H i. unfold sn_outer_ok in H.
  destruct (srun tmw true true (f_cho f) (swOB f)) as [[[c1 ca] cb]|] eqn:E;
    [|discriminate].
  destruct c1 as [q1 [lp lu la lb lq] h1 [rp ru ra rb rq]].
  unfold sside_end_is in H; cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post] in H.
  sn_split.
  match goal with Hx : existsb _ _ = true |- _ =>
    apply existsb_exists in Hx as (x & Hxin & Hx) end.
  apply in_seq in Hxin.
  sn_split. sn_props. subst.
  set (c := f_ma f + f_mb f + f_d f) in *.
  exists (ca * i + cb),
    (cden [] [] i
          (mkC (f_q g) (mkS lp [] la lb []) (f_h g)
               (mkS (f_Rpre g ++ rep (f_uR g) x) (f_uR g) 1 rb rq))).
  split; [| split; [| lia]].
  - rewrite <- swOB_den.
    exact (srun_sound tmw true true (f_cho f) (swOB f) _ ca cb E [] [] i
             ltac:(reflexivity) ltac:(reflexivity)).
  - unfold cden, fC, sden; cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    rewrite rep_nil, !app_nil_r.
    apply lift_lpad; [assumption |].
    replace (i + c) with (x + ((1 * i + rb) + (c - rb - x))) by lia.
    rewrite !rep_add, <- !app_assoc.
    repeat apply lpad_eqb_app. assumption.
Qed.

(** *** The cycle of families *)

Section Sound.

Variable tm : TM.
Variable w : swncert.

Local Notation tmw := (tm_wrap_trs tm (sn_pins w)).
Local Notation P := (sn_P w).
Local Notation M := (sn_M w).
Local Notation F := (sn_fam w).
Local Notation fnxt := (sn_fnxt w).

Hypothesis HP : 1 <= P.
Hypothesis Hgrow : 1 <= f_e (F 0) + f_d (F 0).
Hypothesis Hfams : sn_fams_ok tmw w = true.
Hypothesis Hfires : sn_fires_ok tmw w = true.

Lemma sn_fam_ok : forall j, j < P ->
  sn_inner_ok tmw (sn_pins w) (F j) = true /\
  sn_outer_ok tmw (F j) (F (fnxt j)) = true /\
  f_ma (F j) + f_mb (F j) <= M.
Proof.
  intros j Hj. pose proof Hfams as H. unfold sn_fams_ok in H.
  rewrite forallb_forall in H.
  specialize (H j ltac:(apply in_seq; lia)).
  sn_split. sn_props. auto.
Qed.

Lemma fnxt_lt : forall j, fnxt j < P.
Proof.
  intros j. unfold sn_fnxt.
  destruct (S j <? P) eqn:E; [apply Nat.ltb_lt in E; exact E | lia].
Qed.

(** the inner lap of any family, at any anchor with a unit ahead *)
Lemma sn_inner_lap : forall j i k, j < P -> exists n c',
  csteps tmw n (fC (F j) i (S k)) = Some c' /\
  lift c' = lift (fC (F j) (S i) k) /\ 0 < n.
Proof.
  intros j i k Hj. destruct (sn_fam_ok j Hj) as (Hin & _ & _).
  unfold sn_inner_ok in Hin. destruct (f_behind (F j)).
  - apply andb_prop in Hin as [Hi Hb]. exact (sb_inner_lap tmw (F j) Hi Hb i k).
  - apply andb_prop in Hin as [Hi Hb].
    exact (sw_inner_lap tm (fam_sw (sn_pins w) (F j)) Hi Hb i k).
Qed.

Lemma sn_outer_lap : forall j s, j < P -> M <= s -> exists n c',
  csteps tmw n (fC (F j) s 0) = Some c' /\
  lift c' = lift (fC (F (fnxt j)) (f_e (F j)) (s + f_d (F j))) /\ 0 < n.
Proof.
  intros j s Hj Hs. destruct (sn_fam_ok j Hj) as (_ & Ho & Hm).
  destruct (sn_outer_main tmw _ _ Ho (s - (f_ma (F j) + f_mb (F j))))
    as (n & c' & H1 & H2 & H3).
  replace (f_ma (F j) + (s - (f_ma (F j) + f_mb (F j))) + f_mb (F j)) with s in H1 by lia.
  replace (s - (f_ma (F j) + f_mb (F j)) + (f_ma (F j) + f_mb (F j) + f_d (F j)))
    with (s + f_d (F j)) in H2 by lia.
  exists n, c'. auto.
Qed.

(** the anchors: [(j, i, k)], family [j], [i] units behind, [k] ahead *)
Definition sn_anc (x : nat * nat * nat) : cconf :=
  let '(j, i, k) := x in fC (F j) i k.

Definition sn_nxt (x : nat * nat * nat) : nat * nat * nat :=
  match x with
  | (j, i, S k) => (j, S i, k)
  | (j, i, 0) => (fnxt j, f_e (F j), i + f_d (F j))
  end.

Definition sn_good (x : nat * nat * nat) : Prop :=
  let '(j, i, k) := x in j < P /\ M <= i + k.

Lemma sn_nxt_good : forall x, sn_good x -> sn_good (sn_nxt x).
Proof.
  intros [[j i] [|k]] [Hj Hs]; cbn [sn_nxt sn_good].
  - split; [apply fnxt_lt | lia].
  - split; [exact Hj | lia].
Qed.

Lemma sn_lap_nxt : forall x, sn_good x -> exists n c',
  csteps tmw n (sn_anc x) = Some c' /\ lift c' = lift (sn_anc (sn_nxt x)) /\ 0 < n.
Proof.
  intros [[j i] [|k]] [Hj Hs]; cbn [sn_anc sn_nxt].
  - apply sn_outer_lap; [exact Hj | lia].
  - apply sn_inner_lap. exact Hj.
Qed.

(** *** Reachability between anchors, in [stepn] space over [lift] *)

Definition Reach (x y : nat * nat * nat) : Prop :=
  exists n, stepn tmw n (lift (sn_anc x)) = Some (lift (sn_anc y)).

Lemma reach_refl : forall x, Reach x x.
Proof. intros x. exists 0. reflexivity. Qed.

Lemma reach_trans : forall x y z, Reach x y -> Reach y z -> Reach x z.
Proof.
  intros x y z (n1 & H1) (n2 & H2). exists (n1 + n2).
  rewrite stepn_add, H1. exact H2.
Qed.

Lemma reach_of_lap : forall x y,
  (exists n c', csteps tmw n (sn_anc x) = Some c' /\ lift c' = lift (sn_anc y) /\ 0 < n) ->
  Reach x y.
Proof.
  intros x y (n & c' & H & Hl & _). exists n. rewrite <- Hl.
  apply csteps_lift. exact H.
Qed.

Lemma reach_inner : forall m j i k, j < P -> Reach (j, i, m + k) (j, i + m, k).
Proof.
  induction m as [|m IH]; intros j i k Hj.
  - rewrite Nat.add_0_r. apply reach_refl.
  - apply reach_trans with (j, S i, m + k).
    + apply reach_of_lap. cbn [sn_anc]. exact (sn_inner_lap j i (m + k) Hj).
    + replace (i + S m) with (S i + m) by lia. apply IH. exact Hj.
Qed.

Lemma reach_zero : forall j i k, j < P -> Reach (j, i, k) (j, i + k, 0).
Proof.
  intros j i k Hj. pose proof (reach_inner k j i 0 Hj) as H.
  rewrite Nat.add_0_r in H. exact H.
Qed.

(** one round: the outer lap, then the inner laps down to [k = 0] *)
Lemma reach_round : forall j s, j < P -> M <= s ->
  Reach (j, s, 0) (fnxt j, f_e (F j) + (s + f_d (F j)), 0).
Proof.
  intros j s Hj Hs.
  apply reach_trans with (fnxt j, f_e (F j), s + f_d (F j)).
  - apply reach_of_lap. cbn [sn_anc]. exact (sn_outer_lap j s Hj Hs).
  - apply reach_zero, fnxt_lt.
Qed.

Fixpoint fiter (m j : nat) : nat :=
  match m with
  | 0 => j
  | S m' => fiter m' (fnxt j)
  end.

Lemma reach_walk : forall m j s, j < P -> M <= s -> exists s',
  s <= s' /\ Reach (j, s, 0) (fiter m j, s', 0).
Proof.
  induction m as [|m IH]; intros j s Hj Hs.
  - exists s. split; [lia | apply reach_refl].
  - destruct (IH (fnxt j) (f_e (F j) + (s + f_d (F j))) (fnxt_lt j) ltac:(lia))
      as (s' & Hle & H).
    exists s'. split; [lia |].
    exact (reach_trans _ _ _ (reach_round j s Hj Hs) H).
Qed.

Lemma fnxt_S : forall j, S j < P -> fnxt j = S j.
Proof.
  intros j H. unfold sn_fnxt.
  apply Nat.ltb_lt in H. rewrite H. reflexivity.
Qed.

Lemma fiter_up : forall m j, j + m < P -> fiter m j = j + m.
Proof.
  induction m as [|m IH]; intros j H; cbn [fiter].
  - lia.
  - rewrite (fnxt_S j ltac:(lia)), (IH (S j) ltac:(lia)). lia.
Qed.

Lemma fiter_wrap : forall m j, j + S m = P -> fiter (S m) j = 0.
Proof.
  induction m as [|m IH]; intros j H; cbn [fiter].
  - unfold sn_fnxt.
    replace (S j <? P) with false by (symmetry; apply Nat.ltb_ge; lia). reflexivity.
  - rewrite (fnxt_S j ltac:(lia)). exact (IH (S j) ltac:(lia)).
Qed.

Lemma fiter_add : forall a b j, fiter (a + b) j = fiter b (fiter a j).
Proof. induction a as [|a IH]; intros b j; cbn [fiter Nat.add]; [reflexivity | apply IH]. Qed.

Lemma fiter_to : forall j j', j < P -> j' < P -> exists m, fiter m j = j'.
Proof.
  intros j j' Hj Hj'.
  destruct (le_lt_dec j j') as [Hle | Hlt].
  - exists (j' - j). rewrite fiter_up by lia. lia.
  - exists (S (P - j - 1) + j'). rewrite fiter_add, (fiter_wrap (P - j - 1) j ltac:(lia)).
    rewrite fiter_up by lia. reflexivity.
Qed.

Lemma reach_to : forall j s j', j < P -> j' < P -> M <= s -> exists s',
  s <= s' /\ Reach (j, s, 0) (j', s', 0).
Proof.
  intros j s j' Hj Hj' Hs.
  destruct (fiter_to j j' Hj Hj') as (m & Hm).
  destruct (reach_walk m j s Hj Hs) as (s' & Hle & H).
  rewrite Hm in H. exists s'. auto.
Qed.

(** the block grows by at least a unit each time family 0 closes a round *)
Lemma reach_big : forall B j s, j < P -> M <= s -> exists s',
  s + B <= s' /\ Reach (j, s, 0) (0, s', 0).
Proof.
  induction B as [|B IH]; intros j s Hj Hs.
  - destruct (reach_to j s 0 Hj ltac:(lia) Hs) as (s' & Hle & H).
    exists s'. split; [lia | exact H].
  - destruct (IH j s Hj Hs) as (s1 & Hle1 & H1).
    pose proof (reach_round 0 s1 ltac:(lia) ltac:(lia)) as H2.
    destruct (reach_to (fnxt 0) (f_e (F 0) + (s1 + f_d (F 0))) 0 (fnxt_lt 0)
                ltac:(lia) ltac:(lia)) as (s3 & Hle3 & H3).
    exists s3. split; [lia |].
    exact (reach_trans _ _ _ H1 (reach_trans _ _ _ H2 H3)).
Qed.

Lemma reach_fam : forall B x j', sn_good x -> j' < P -> exists s',
  B <= s' /\ M <= s' /\ Reach x (j', s', 0).
Proof.
  intros B [[j i] k] j' [Hj Hs] Hj'.
  destruct (reach_big B j (i + k) Hj Hs) as (s1 & Hle1 & H1).
  destruct (reach_to 0 s1 j' ltac:(lia) Hj' ltac:(lia)) as (s2 & Hle2 & H2).
  exists s2. split; [lia | split; [lia |]].
  exact (reach_trans _ _ _ (reach_zero j i k Hj)
           (reach_trans _ _ _ H1 H2)).
Qed.

Definition fprev (j : nat) : nat := if j =? 0 then P - 1 else j - 1.

Lemma fprev_ok : forall j, j < P -> fprev j < P /\ fnxt (fprev j) = j.
Proof.
  intros j Hj. unfold fprev. destruct (j =? 0) eqn:E.
  - apply Nat.eqb_eq in E. subst. split; [lia |].
    unfold sn_fnxt.
    replace (S (P - 1) <? P) with false by (symmetry; apply Nat.ltb_ge; lia).
    reflexivity.
  - apply Nat.eqb_neq in E. split; [lia |].
    rewrite fnxt_S by lia. lia.
Qed.

(** a family's anchors with at least [B] units ahead *)
Lemma reach_ahead : forall B x j, sn_good x -> j < P -> exists i k,
  B <= k /\ Reach x (j, i, k).
Proof.
  intros B x j Hx Hj. destruct (fprev_ok j Hj) as [Hp Hn].
  destruct (reach_fam B x (fprev j) Hx Hp) as (s & HB & HM & H).
  exists (f_e (F (fprev j))), (s + f_d (F (fprev j))). split; [lia |].
  apply (reach_trans _ _ _ H). apply reach_of_lap.
  pose proof (sn_outer_lap (fprev j) s Hp HM) as Ho. rewrite Hn in Ho.
  exact Ho.
Qed.

(** *** Fires *)

Definition FiresFrom (x : nat * nat * nat) (t : Instr) : Prop :=
  exists k e, stepn tmw k (lift (sn_anc x)) = Some e /\ instr_of e = t.

Lemma fires_back : forall x y t, Reach x y -> FiresFrom y t -> FiresFrom x t.
Proof.
  intros x y t (n & H) (k & e & Hk & Ht). exists (n + k), e.
  split; [rewrite stepn_add, H; exact Hk | exact Ht].
Qed.

Lemma fires_of_instr : forall el er ch c0 XL XR n t y,
  srun_instr tmw el er ch c0 = Some t ->
  (el = true -> XL = []) -> (er = true -> XR = []) ->
  sn_anc y = cden XL XR n c0 -> FiresFrom y t.
Proof.
  intros el er ch c0 XL XR n t y H HL HR Hd.
  apply fire_lift_of_csteps with (Cc := fun _ => sn_anc y) (p := xH).
  exact (fire_of_run_instr tmw (fun _ => sn_anc y) el er ch c0 xH n XL XR t H HL HR Hd).
Qed.

Lemma sn_fire_any : forall t, ~ In t (sn_pins w) ->
  forall x, sn_good x -> FiresFrom x t.
Proof.
  intros t Hnin x Hx.
  pose proof Hfires as H. unfold sn_fires_ok in H.
  rewrite forallb_forall in H.
  specialize (H t (all_Instr_complete t)).
  apply orb_prop in H as [H | H].
  { exfalso. apply Hnin, tr_inb_spec, H. }
  apply existsb_exists in H as ([[j o] ch] & _ & Hf).
  unfold sn_fire_ok in Hf. cbv beta iota zeta in Hf.
  apply andb_prop in Hf as [Hj Hf]. apply Nat.ltb_lt in Hj.
  destruct o.
  2: destruct (f_behind (F j)) eqn:Hb.
  all: cbv beta iota in Hf.
  all: match type of Hf with
       | (match ?m with Some _ => _ | None => _ end = true) =>
           destruct m as [t'|] eqn:E; [|discriminate]
       end.
  all: apply instr_eqb_spec in Hf; subst t'.
  - (* an outer-lap fire: at [(j, s, 0)], [s >= M >= ma + mb] *)
    destruct (reach_fam 0 x j Hx Hj) as (s & _ & HM & Hr).
    apply (fires_back _ _ _ Hr).
    destruct (sn_fam_ok j Hj) as (_ & _ & Hm).
    apply (fires_of_instr true true ch (swOB (F j)) [] [] (s - (f_ma (F j) + f_mb (F j))) t
             _ E ltac:(reflexivity) ltac:(reflexivity)).
    rewrite swOB_den. cbn [sn_anc]. f_equal. lia.
  - (* a behind inner-lap fire: at [(j, na + n + nb, S k)] *)
      destruct (reach_ahead (f_na (F j) + f_nb (F j) + 1) x j Hx Hj)
        as (i & k & HB & Hr).
      apply (fires_back _ _ _ Hr).
      apply (fires_back _ (j, i + (f_na (F j) + f_nb (F j)),
                           k - (f_na (F j) + f_nb (F j)))).
      { replace k with ((f_na (F j) + f_nb (F j)) + (k - (f_na (F j) + f_nb (F j))))
          at 1 by lia.
        apply reach_inner. exact Hj. }
      apply (fires_of_instr true false ch (swAb (F j)) []
               (rep (f_uR (F j)) (k - (f_na (F j) + f_nb (F j)) - 1) ++ f_Rpost (F j))
               i t _ E ltac:(reflexivity) ltac:(discriminate)).
      rewrite swAb_den. cbn [sn_anc]. f_equal; lia.
  - (* an ahead inner-lap fire: at [(j, i, na + n + nb)] *)
      destruct (reach_ahead (f_na (F j) + f_nb (F j)) x j Hx Hj)
        as (i & k & HB & Hr).
      apply (fires_back _ _ _ Hr).
      apply (fires_of_instr false true ch (swAa (F j))
               (rep (f_uL (F j)) i ++ f_Lpost (F j)) []
               (k - (f_na (F j) + f_nb (F j))) t _ E
               ltac:(discriminate) ltac:(reflexivity)).
      rewrite swAa_den. cbn [sn_anc]. f_equal. lia.
Qed.

(** ** The enumeration: every lap becomes one [Hlap] *)

Definition snCf (x0 : nat * nat * nat) (p : positive) : cconf :=
  sn_anc (Nat.iter (Nat.pred (Pos.to_nat p)) sn_nxt x0).

Lemma snCf_succ : forall x0 p, snCf x0 (Pos.succ p) =
  sn_anc (sn_nxt (Nat.iter (Nat.pred (Pos.to_nat p)) sn_nxt x0)).
Proof.
  intros x0 p. unfold snCf. rewrite Pos2Nat.inj_succ.
  destruct (Pos2Nat.is_succ p) as (m & Hm). rewrite Hm. reflexivity.
Qed.

Lemma sn_iter_good : forall x0, sn_good x0 -> forall m,
  sn_good (Nat.iter m sn_nxt x0).
Proof.
  intros x0 H0. induction m as [|m IH]; [exact H0 |].
  cbn [Nat.iter nat_rect]. exact (sn_nxt_good _ IH).
Qed.

Theorem sn_glue : forall x0, sn_good x0 ->
  (exists t0, stepn tmw t0 InitES = Some (lift (sn_anc x0))) ->
  NeverQuasiHaltsTr tm.
Proof.
  intros x0 H0 Hboot.
  apply (glue_neverqhtr tm (sn_pins w) (snCf x0) xH).
  - destruct Hboot as (t0 & Ht0). exists t0. exact Ht0.
  - intros p _. rewrite snCf_succ. apply sn_lap_nxt, sn_iter_good. exact H0.
  - intros t Hnin p _.
    apply fire_csteps_of_lift. unfold snCf.
    apply (sn_fire_any t Hnin), sn_iter_good. exact H0.
Qed.

End Sound.

Theorem sweep_nqh_sound : forall tm w, sweep_nqh_check tm w = true ->
  NeverQuasiHaltsTr tm.
Proof.
  intros tm w H. unfold sweep_nqh_check in H.
  apply andb_prop in H as [H Hf].
  apply andb_prop in H as [H Hfs].
  apply andb_prop in H as [H Hb].
  apply andb_prop in H as [H Hg].
  apply andb_prop in H as [H HM].
  apply andb_prop in H as [HP Hj].
  apply Nat.leb_le in HP, Hg, HM. apply Nat.ltb_lt in Hj.
  apply (sn_glue tm w HP Hg Hfs Hf (sn_j0 w, sn_i0 w, sn_k0 w)).
  - split; [exact Hj | exact HM].
  - exists (sn_t0 w). unfold sn_boot_ok in Hb.
    destruct (csteps (tm_wrap_trs tm (sn_pins w)) (sn_t0 w) c0) as [c|] eqn:E;
      [|discriminate].
    rewrite <- lift_c0, (csteps_lift _ _ _ _ E).
    f_equal. exact (ceqb_lift _ _ Hb).
Qed.

(** the hole moves LEFT: certify the mirror *)
Theorem sweep_nqh_sound_mirror : forall tm w,
  sweep_nqh_check (mirror_tm tm) w = true -> NeverQuasiHaltsTr tm.
Proof.
  intros tm w H. apply neverqhtr_mirror. exact (sweep_nqh_sound _ w H).
Qed.
