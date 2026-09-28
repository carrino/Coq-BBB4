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

    A chain needs concrete cells where the machine turns or changes
    state inside a block, so each start may UNROLL units at the block's
    two ends: [na]/[nb] for the inner lap (the last [na + nb - 1] inner
    laps then take concrete [sw_base] chains), [ma]/[mb] for the outer
    lap (every visited anchor has at least [ma + mb] units, [sw_good],
    checked at the boot and kept by both laps).

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
  sw_na    : nat;            (** inner start: units unrolled at the near end *)
  sw_nb    : nat;            (** ... and at the far end *)
  sw_chi   : list lstep;     (** inner lap, from [swA0] *)
  sw_base  : list (list lstep);  (** the last [na + nb - 1] inner laps, concrete *)
  sw_ma    : nat;            (** outer start: units unrolled at the near end *)
  sw_mb    : nat;            (** ... and at the far end *)
  sw_cho   : list lstep;     (** outer lap, from [swB0] *)
  sw_fires : list (bool * list lstep);  (** (outer?, chain prefix) *)
  sw_t0    : nat;            (** boot index, on the original machine *)
  sw_i0    : nat;
  sw_k0    : nat
}.

Definition swC (w : swcert) (i k : nat) : cconf :=
  (sw_q w, (sw_Lpre w ++ rep (sw_uL w) i ++ sw_Lpost w, sw_h w,
            sw_Rpre w ++ rep (sw_uR w) k ++ sw_Rpost w)).

(** the inner lap's start: left tail opaque, [na + k + nb] units ahead,
    [na] of them unrolled into the prefix (so the chain can step onto
    the block) and [nb] into the suffix (so the return sweep can turn on
    it).  Anchors with fewer units ahead take the concrete [sw_base]
    chains from [swBase]. *)
Definition swA0 (w : swcert) : sconf :=
  mkC (sw_q w) (sflat (sw_Lpre w)) (sw_h w)
      (mkS (sw_Rpre w ++ rep (sw_uR w) (sw_na w)) (sw_uR w) 1 0
           (rep (sw_uR w) (sw_nb w) ++ sw_Rpost w)).

Definition swBase (w : swcert) (k : nat) : sconf :=
  mkC (sw_q w) (sflat (sw_Lpre w)) (sw_h w)
      (sflat (sw_Rpre w ++ rep (sw_uR w) (S k) ++ sw_Rpost w)).

(** the outer lap's start: [ma + i + mb] units behind ([ma] and [mb] of
    them unrolled at the two ends), none ahead.  The anchors never have
    fewer than [ma + mb] units in all ([sw_good]), so no concrete outer
    chains are needed. *)
Definition swB0 (w : swcert) : sconf :=
  mkC (sw_q w) (mkS (sw_Lpre w ++ rep (sw_uL w) (sw_ma w)) (sw_uL w) 1 0
                    (rep (sw_uL w) (sw_mb w) ++ sw_Lpost w)) (sw_h w)
      (sflat (sw_Rpre w ++ sw_Rpost w)).

(** ** The checker *)

Definition sside_flat_is (s : sside) (x : list Sym) : bool :=
  syms_eqb (s_pre s) x && syms_eqb (s_u s) [] && syms_eqb (s_post s) [].

(** the inner end's right side denotes [Rpre ++ rep uR (k + c) ++ Rpost]
    ([c = na + nb - 1]): its prefix is [Rpre] and [x] units, its suffix
    (up to trailing blanks) [y] units and [Rpost], [x + b + y = c] *)
Definition sside_end_is (s : sside) (pre u : list Sym) (c : nat)
                        (post : list Sym) : bool :=
  syms_eqb (s_u s) u && Nat.eqb (s_a s) 1 && (s_b s <=? c)
  && existsb (fun x => syms_eqb (s_pre s) (pre ++ rep u x)
                       && lpad_eqb (s_post s) (rep u (c - s_b s - x) ++ post))
             (seq 0 (S (c - s_b s))).

Definition sw_inner_ok (tmw : TM) (w : swcert) : bool :=
  match srun tmw false true (sw_chi w) (swA0 w) with
  | Some (c1, _, cb) =>
      st_eqb (c_st c1) (sw_q w) && sym_eqb (c_h c1) (sw_h w)
      && sside_flat_is (c_l c1) (sw_Lpre w ++ sw_uL w)
      && sside_end_is (c_r c1) (sw_Rpre w) (sw_uR w)
                      (sw_na w + sw_nb w - 1) (sw_Rpost w)
      && (0 <? cb)
  | None => false
  end && (1 <=? sw_na w + sw_nb w).

Definition sw_base1_ok (tmw : TM) (w : swcert) (k : nat) (ch : list lstep) : bool :=
  match srun tmw false true ch (swBase w k) with
  | Some (c1, _, cb) =>
      st_eqb (c_st c1) (sw_q w) && sym_eqb (c_h c1) (sw_h w)
      && sside_flat_is (c_l c1) (sw_Lpre w ++ sw_uL w)
      && syms_eqb (s_u (c_r c1)) [] && syms_eqb (s_post (c_r c1)) []
      && lpad_eqb (s_pre (c_r c1)) (sw_Rpre w ++ rep (sw_uR w) k ++ sw_Rpost w)
      && (0 <? cb)
  | None => false
  end.

Fixpoint sw_base_from (tmw : TM) (w : swcert) (k : nat) (l : list (list lstep)) : bool :=
  match l with
  | [] => true
  | ch :: l' => sw_base1_ok tmw w k ch && sw_base_from tmw w (S k) l'
  end.

Definition sw_base_ok (tmw : TM) (w : swcert) : bool :=
  sw_base_from tmw w 0 (sw_base w) && (sw_na w + sw_nb w <=? S (length (sw_base w))).

Definition sw_outer_ok (tmw : TM) (w : swcert) : bool :=
  match srun tmw true true (sw_cho w) (swB0 w) with
  | Some (c1, _, cb) =>
      st_eqb (c_st c1) (sw_q w) && sym_eqb (c_h c1) (sw_h w)
      && syms_eqb (s_u (c_l c1)) [] && syms_eqb (s_post (c_l c1)) []
      && lpad_eqb (s_pre (c_l c1))
                  (sw_Lpre w ++ rep (sw_uL w) (sw_e w) ++ sw_Lpost w)
      && sside_end_is (c_r c1) (sw_Rpre w) (sw_uR w)
                      (sw_ma w + sw_mb w + sw_d w) (sw_Rpost w)
      && (0 <? cb)
  | None => false
  end && (1 <=? sw_e w + sw_d w)
  && (sw_ma w + sw_mb w <=? sw_i0 w + sw_k0 w).

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
  && sw_inner_ok tmw w && sw_base_ok tmw w && sw_outer_ok tmw w
  && sw_fires_ok tmw w.

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
Hypothesis Hbase : sw_base_ok tmw w = true.
Hypothesis Hout : sw_outer_ok tmw w = true.
Hypothesis Hfires : sw_fires_ok tmw w = true.

(** the anchors ARE the chain starts' denotations *)
Lemma swA0_den : forall i k,
  cden (rep (sw_uL w) i ++ sw_Lpost w) [] k (swA0 w)
  = swC w i (sw_na w + k + sw_nb w).
Proof.
  intros i k. unfold cden, swA0, swC, sden, sflat;
    cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
  replace (1 * k + 0) with k by lia. cbn [rep]. rewrite !app_nil_r.
  rewrite !rep_add, <- !app_assoc. reflexivity.
Qed.

Lemma swBase_den : forall i k,
  cden (rep (sw_uL w) i ++ sw_Lpost w) [] 0 (swBase w k) = swC w i (S k).
Proof.
  intros i k. unfold cden, swBase, swC, sden, sflat;
    cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post rep].
  rewrite !app_nil_r, <- !app_assoc. reflexivity.
Qed.

Lemma swB0_den : forall i,
  cden [] [] i (swB0 w) = swC w (sw_ma w + i + sw_mb w) 0.
Proof.
  intros i. unfold cden, swB0, swC, sden, sflat;
    cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
  replace (1 * i + 0) with i by lia. cbn [rep]. rewrite !app_nil_r.
  rewrite !rep_add, <- !app_assoc. reflexivity.
Qed.

Lemma sw_na_nb : 1 <= sw_na w + sw_nb w.
Proof.
  pose proof Hin as H. unfold sw_inner_ok in H.
  apply andb_prop in H as [_ H]. apply Nat.leb_le in H. exact H.
Qed.

(** the main inner lap: [na + k + nb] units ahead *)
Lemma sw_inner_main : forall i k, exists n c',
  csteps tmw n (swC w i (sw_na w + k + sw_nb w)) = Some c' /\
  lift c' = lift (swC w (S i) (k + (sw_na w + sw_nb w - 1))) /\ 0 < n.
Proof.
  intros i k. pose proof Hin as H. unfold sw_inner_ok in H.
  apply andb_prop in H as [H _].
  destruct (srun tmw false true (sw_chi w) (swA0 w)) as [[[c1 ca] cb]|] eqn:E;
    [|discriminate].
  destruct c1 as [q1 [lp lu la lb lq] h1 [rp ru ra rb rq]].
  unfold sside_flat_is, sside_end_is in H;
    cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post] in H.
  apply andb_prop in H as [H Hcb].
  apply andb_prop in H as [H Hr].
  apply andb_prop in H as [H Hl].
  apply andb_prop in H as [Hq Hh].
  apply andb_prop in Hr as [Hr Hx].
  apply andb_prop in Hr as [Hr Hrb].
  apply andb_prop in Hr as [Hru Hra].
  apply andb_prop in Hl as [Hl Hlq].
  apply andb_prop in Hl as [Hlp Hlu].
  apply existsb_exists in Hx as (x & Hxin & Hx).
  apply in_seq in Hxin.
  apply andb_prop in Hx as [Hrp Hrq].
  apply st_eqb_spec in Hq; apply sym_eqb_spec in Hh.
  apply syms_eqb_eq in Hrp, Hru, Hlp, Hlu, Hlq.
  apply Nat.eqb_eq in Hra. apply Nat.leb_le in Hrb. apply Nat.ltb_lt in Hcb.
  subst.
  set (c := sw_na w + sw_nb w - 1) in *.
  exists (ca * k + cb),
    (cden (rep (sw_uL w) i ++ sw_Lpost w) [] k
          (mkC (sw_q w) (mkS (sw_Lpre w ++ sw_uL w) [] la lb []) (sw_h w)
               (mkS (sw_Rpre w ++ rep (sw_uR w) x) (sw_uR w) 1 rb rq))).
  split; [| split; [| lia]].
  - rewrite <- swA0_den.
    exact (srun_sound tmw false true (sw_chi w) (swA0 w) _ ca cb E
             (rep (sw_uL w) i ++ sw_Lpost w) [] k
             ltac:(discriminate) ltac:(reflexivity)).
  - unfold cden, swC, sden; cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post rep].
    rewrite rep_nil. rewrite !app_nil_r, <- !app_assoc. cbn [app].
    apply lift_lpad; [apply lpad_eqb_refl |].
    replace (k + c) with (x + ((1 * k + rb) + (c - rb - x))) by lia.
    rewrite !rep_add, <- !app_assoc.
    repeat apply lpad_eqb_app. exact Hrq.
Qed.

Lemma sw_base_from_nth : forall l k0, sw_base_from tmw w k0 l = true ->
  forall k ch, nth_error l k = Some ch -> sw_base1_ok tmw w (k0 + k) ch = true.
Proof.
  induction l as [|ch0 l IH]; intros k0 H k ch Hk.
  - destruct k; discriminate.
  - cbn [sw_base_from] in H. apply andb_prop in H as [H0 H].
    destruct k as [|k]; cbn in Hk.
    + injection Hk as <-. rewrite Nat.add_0_r. exact H0.
    + replace (k0 + S k) with (S k0 + k) by lia. exact (IH (S k0) H k ch Hk).
Qed.

(** a concrete inner lap: [S k] units ahead, [k < na + nb - 1] *)
Lemma sw_inner_base : forall i k, S k < sw_na w + sw_nb w -> exists n c',
  csteps tmw n (swC w i (S k)) = Some c' /\
  lift c' = lift (swC w (S i) k) /\ 0 < n.
Proof.
  intros i k Hk. pose proof Hbase as H. unfold sw_base_ok in H.
  apply andb_prop in H as [Hb Hlen]. apply Nat.leb_le in Hlen.
  destruct (nth_error (sw_base w) k) as [ch|] eqn:Ech.
  2: { apply nth_error_None in Ech. lia. }
  pose proof (sw_base_from_nth _ 0 Hb k ch Ech) as H. cbn [Nat.add] in H.
  unfold sw_base1_ok in H.
  destruct (srun tmw false true ch (swBase w k)) as [[[c1 ca] cb]|] eqn:E;
    [|discriminate].
  destruct c1 as [q1 [lp lu la lb lq] h1 [rp ru ra rb rq]].
  unfold sside_flat_is in H; cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post] in H.
  apply andb_prop in H as [H Hcb].
  apply andb_prop in H as [H Hrp].
  apply andb_prop in H as [H Hrq].
  apply andb_prop in H as [H Hru].
  apply andb_prop in H as [H Hl].
  apply andb_prop in H as [Hq Hh].
  apply andb_prop in Hl as [Hl Hlq].
  apply andb_prop in Hl as [Hlp Hlu].
  apply st_eqb_spec in Hq; apply sym_eqb_spec in Hh.
  apply syms_eqb_eq in Hru, Hrq, Hlp, Hlu, Hlq. apply Nat.ltb_lt in Hcb.
  subst.
  exists (ca * 0 + cb),
    (cden (rep (sw_uL w) i ++ sw_Lpost w) [] 0
          (mkC (sw_q w) (mkS (sw_Lpre w ++ sw_uL w) [] la lb []) (sw_h w)
               (mkS rp [] ra rb []))).
  split; [| split; [| lia]].
  - rewrite <- swBase_den.
    exact (srun_sound tmw false true ch (swBase w k) _ ca cb E
             (rep (sw_uL w) i ++ sw_Lpost w) [] 0
             ltac:(discriminate) ltac:(reflexivity)).
  - unfold cden, swC, sden; cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post rep].
    rewrite !rep_nil, !app_nil_r, <- !app_assoc. cbn [app].
    apply lift_lpad; [apply lpad_eqb_refl | exact Hrp].
Qed.

Lemma sw_inner_lap : forall i k, exists n c',
  csteps tmw n (swC w i (S k)) = Some c' /\
  lift c' = lift (swC w (S i) k) /\ 0 < n.
Proof.
  intros i k.
  destruct (lt_dec (S k) (sw_na w + sw_nb w)) as [Hlt | Hge].
  - exact (sw_inner_base i k Hlt).
  - pose proof sw_na_nb.
    destruct (sw_inner_main i (S k - (sw_na w + sw_nb w))) as (n & c' & H1 & H2 & H3).
    replace (sw_na w + (S k - (sw_na w + sw_nb w)) + sw_nb w) with (S k) in H1 by lia.
    replace (S k - (sw_na w + sw_nb w) + (sw_na w + sw_nb w - 1)) with k in H2 by lia.
    exists n, c'. auto.
Qed.

Lemma sw_outer_main : forall i, exists n c',
  csteps tmw n (swC w (sw_ma w + i + sw_mb w) 0) = Some c' /\
  lift c' = lift (swC w (sw_e w) (i + (sw_ma w + sw_mb w + sw_d w))) /\ 0 < n.
Proof.
  intros i. pose proof Hout as H. unfold sw_outer_ok in H.
  apply andb_prop in H as [H _]. apply andb_prop in H as [H _].
  destruct (srun tmw true true (sw_cho w) (swB0 w)) as [[[c1 ca] cb]|] eqn:E;
    [|discriminate].
  destruct c1 as [q1 [lp lu la lb lq] h1 [rp ru ra rb rq]].
  unfold sside_end_is in H; cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post] in H.
  apply andb_prop in H as [H Hcb].
  apply andb_prop in H as [H Hr].
  apply andb_prop in H as [H Hlp].
  apply andb_prop in H as [H Hlq].
  apply andb_prop in H as [H Hlu].
  apply andb_prop in H as [Hq Hh].
  apply andb_prop in Hr as [Hr Hx].
  apply andb_prop in Hr as [Hr Hrb].
  apply andb_prop in Hr as [Hru Hra].
  apply existsb_exists in Hx as (x & Hxin & Hx).
  apply in_seq in Hxin.
  apply andb_prop in Hx as [Hrp Hrq].
  apply st_eqb_spec in Hq; apply sym_eqb_spec in Hh.
  apply syms_eqb_eq in Hrp, Hru, Hlu, Hlq.
  apply Nat.eqb_eq in Hra. apply Nat.leb_le in Hrb. apply Nat.ltb_lt in Hcb.
  subst.
  set (c := sw_ma w + sw_mb w + sw_d w) in *.
  exists (ca * i + cb),
    (cden [] [] i
          (mkC (sw_q w) (mkS lp [] la lb []) (sw_h w)
               (mkS (sw_Rpre w ++ rep (sw_uR w) x) (sw_uR w) 1 rb rq))).
  split; [| split; [| lia]].
  - rewrite <- swB0_den.
    exact (srun_sound tmw true true (sw_cho w) (swB0 w) _ ca cb E [] [] i
             ltac:(reflexivity) ltac:(reflexivity)).
  - unfold cden, swC, sden; cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
    rewrite rep_nil. rewrite !app_nil_r.
    apply lift_lpad; [exact Hlp |].
    replace (i + c) with (x + ((1 * i + rb) + (c - rb - x))) by lia.
    rewrite !rep_add, <- !app_assoc.
    repeat apply lpad_eqb_app. exact Hrq.
Qed.

Lemma sw_outer_lap : forall i, sw_ma w + sw_mb w <= i -> exists n c',
  csteps tmw n (swC w i 0) = Some c' /\
  lift c' = lift (swC w (sw_e w) (i + sw_d w)) /\ 0 < n.
Proof.
  intros i Hi.
  destruct (sw_outer_main (i - (sw_ma w + sw_mb w))) as (n & c' & H1 & H2 & H3).
  replace (sw_ma w + (i - (sw_ma w + sw_mb w)) + sw_mb w) with i in H1 by lia.
  replace (i - (sw_ma w + sw_mb w) + (sw_ma w + sw_mb w + sw_d w))
    with (i + sw_d w) in H2 by lia.
  exists n, c'. auto.
Qed.

Lemma sw_e_d : 1 <= sw_e w + sw_d w.
Proof.
  pose proof Hout as H. unfold sw_outer_ok in H.
  apply andb_prop in H as [H _]. apply andb_prop in H as [_ H].
  apply Nat.leb_le in H. exact H.
Qed.

(** the anchors the run visits: never fewer than [ma + mb] units *)
Definition sw_good (i k : nat) : Prop := sw_ma w + sw_mb w <= i + k.

Lemma sw_good_boot : sw_good (sw_i0 w) (sw_k0 w).
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

Lemma sw_nxt_good : forall ik, sw_good (fst ik) (snd ik) ->
  sw_good (fst (sw_nxt ik)) (snd (sw_nxt ik)).
Proof. intros [i [|k]]; unfold sw_good; cbn; lia. Qed.

Lemma sw_iter_good : forall m, let ik := Nat.iter m sw_nxt (sw_i0 w, sw_k0 w) in
  sw_good (fst ik) (snd ik).
Proof.
  induction m as [|m IH]; [exact sw_good_boot |].
  cbn [Nat.iter nat_rect]. exact (sw_nxt_good _ IH).
Qed.

Lemma sw_lap_nxt : forall ik, sw_good (fst ik) (snd ik) -> exists n c',
  csteps tmw n (swCp ik) = Some c' /\ lift c' = lift (swCp (sw_nxt ik)) /\ 0 < n.
Proof.
  intros [i [|k]] Hg; unfold swCp, sw_good in *; cbn [sw_nxt fst snd] in *.
  - apply sw_outer_lap. lia.
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
  forall i k, FiresFrom (swC w i (sw_na w + k + sw_nb w)) t.
Proof.
  intros ch t H i k.
  apply fire_lift_of_csteps with (Cc := fun _ => swC w i (sw_na w + k + sw_nb w)) (p := xH).
  exact (fire_of_run_instr tmw (fun _ => swC w i (sw_na w + k + sw_nb w)) false true
           ch (swA0 w) xH k (rep (sw_uL w) i ++ sw_Lpost w) [] t H
           ltac:(discriminate) ltac:(reflexivity) (eq_sym (swA0_den i k))).
Qed.

Lemma fire_outer : forall ch t,
  srun_instr tmw true true ch (swB0 w) = Some t ->
  forall i, sw_ma w + sw_mb w <= i -> FiresFrom (swC w i 0) t.
Proof.
  intros ch t H i Hi.
  replace i with (sw_ma w + (i - (sw_ma w + sw_mb w)) + sw_mb w) by lia.
  apply fire_lift_of_csteps
    with (Cc := fun _ => swC w (sw_ma w + (i - (sw_ma w + sw_mb w)) + sw_mb w) 0)
         (p := xH).
  exact (fire_of_run_instr tmw
           (fun _ => swC w (sw_ma w + (i - (sw_ma w + sw_mb w)) + sw_mb w) 0)
           true true ch (swB0 w) xH (i - (sw_ma w + sw_mb w)) [] [] t H
           ltac:(reflexivity) ltac:(reflexivity) (eq_sym (swB0_den _))).
Qed.

(** the block grows by at least a unit per round ([1 <= e + d]) *)
Lemma sw_reach_big : forall m i, sw_ma w + sw_mb w <= i -> exists N n,
  m <= N /\ i <= N /\
  stepn tmw n (lift (swC w i 0)) = Some (lift (swC w N 0)).
Proof.
  induction m as [|m IH]; intros i Hi.
  - exists i, 0. split; [lia | split; [lia | reflexivity]].
  - destruct (IH i Hi) as (N & n1 & HN & HiN & H1).
    destruct (sw_outer_lap N ltac:(lia)) as (n2 & c2 & H2 & Hl2 & _).
    destruct (sw_reach_zero (N + sw_d w) (sw_e w)) as (n3 & H3).
    pose proof sw_e_d.
    exists (sw_e w + (N + sw_d w)), (n1 + (n2 + n3)). split; [lia | split; [lia |]].
    rewrite stepn_add, H1, stepn_add, (lap_stepn _ _ _ _ H2 Hl2). exact H3.
Qed.

(** an inner-lap fire, from any visited anchor: grow until [na + nb]
    units are ahead *)
Lemma fire_inner_any : forall ch t,
  srun_instr tmw false true ch (swA0 w) = Some t ->
  forall i k, sw_good i k -> FiresFrom (swC w i k) t.
Proof.
  intros ch t H i k Hg. unfold sw_good in Hg.
  destruct (sw_reach_zero k i) as (n1 & H1).
  destruct (sw_reach_big (sw_na w + sw_nb w) (i + k) Hg) as (N & n2 & HN & HiN & H2).
  destruct (sw_outer_lap N ltac:(lia)) as (n3 & c3 & H3 & Hl3 & _).
  apply (fires_back _ _ n1 t H1), (fires_back _ _ n2 t H2),
        (fires_back _ _ n3 t (lap_stepn _ _ _ _ H3 Hl3)).
  replace (N + sw_d w) with (sw_na w + (N + sw_d w - (sw_na w + sw_nb w)) + sw_nb w) by lia.
  apply (fire_inner ch t H).
Qed.

(** an outer-lap fire, from any visited anchor: [k] inner laps first *)
Lemma fire_outer_any : forall ch t,
  srun_instr tmw true true ch (swB0 w) = Some t ->
  forall i k, sw_good i k -> FiresFrom (swC w i k) t.
Proof.
  intros ch t H i k Hg.
  destruct (sw_reach_zero k i) as (n & Hn).
  exact (fires_back _ _ n t Hn (fire_outer ch t H (i + k) Hg)).
Qed.

Lemma sw_fire_any : forall t, ~ In t (sw_pins w) ->
  forall i k, sw_good i k -> FiresFrom (swC w i k) t.
Proof.
  intros t Hnin i k Hg.
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
    exact (fire_outer_any ch t E i k Hg).
  - destruct (srun_instr tmw false true ch (swA0 w)) as [t'|] eqn:E; [|discriminate].
    apply instr_eqb_spec in Hf. subst t'.
    exact (fire_inner_any ch t E i k Hg).
Qed.

End Sound.

Theorem sweep_sound : forall tm w, sweep_check tm w = true ->
  NonHalt tm /\ QHBoundTr 32779478 tm /\ QuasiHaltsTr tm.
Proof.
  intros tm w H. unfold sweep_check in H.
  apply andb_prop in H as [H Hf].
  apply andb_prop in H as [H Ho].
  apply andb_prop in H as [H Hbs].
  apply andb_prop in H as [H Hi].
  apply andb_prop in H as [H Hcap].
  apply andb_prop in H as [Hb Hwit].
  apply (lap_qh_stage tm (sw_pins w) (swCf w) xH (sw_t0 w) 32779478).
  - unfold sw_boot_ok in Hb.
    destruct (csteps tm (sw_t0 w) c0) as [c|] eqn:E; [|discriminate].
    rewrite <- lift_c0, (csteps_lift _ _ _ _ E).
    f_equal. exact (ceqb_lift _ _ Hb).
  - intros p _. rewrite swCf_succ. apply (sw_lap_nxt tm w Hi Hbs Ho).
    apply (sw_iter_good tm w Ho).
  - intros t Hnin p _.
    apply fire_csteps_of_lift.
    unfold swCf, swCp.
    apply (sw_fire_any tm w Hi Hbs Ho Hf t Hnin).
    apply (sw_iter_good tm w Ho).
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
