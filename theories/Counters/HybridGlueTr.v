(** * HybridGlueTr: bouncer + counter hybrids, a counter lap whose far side
    is a growing bouncer block, decided by one boolean checker.

    A hybrid (SCOPING_INSTR.md 7.4.DX, 7.4.HY) keeps a binary counter at
    one end of the tape and a bouncer block [w^n] beside it.  Each lap
    increments the counter once, at its low end next to the block, and
    sweeps the block, growing it.  The anchor is two-index:

      [hyC P p n] = [(q, (Lpre ++ E p, h, Rpre ++ rep w n ++ Rpost))]

    with [E] the counter word ([E xH = C], [E (xO r) = A ++ E r],
    [E (xI r) = B ++ E r], the shape of every inferred counter alphabet,
    here generic in [A], [B], [C]).  One lap is two chains through a MID
    configuration

      [hyM P p n] = [(q2, (Mpre ++ E p, h2, rep w n ++ Rpost))]:

    - the COUNTER half [hyC P p (m + n) -> hyM P (Pos.succ p) n] is a
      [LapDecider] chain indexed by the carry length, with the block as
      its OPAQUE right tail ([m] units of it concrete).  As in the
      monotone-counter boards it has an interior branch ([cview p = (j,
      Some r)], the high part [E r] opaque on the left) and an overflow
      branch ([cview p = (S j, None)], the far left known empty), each
      with its first [nu] / [no] carry units unrolled and the shorter
      carries as concrete chains.  The overflow branch carries the carry
      instruction, the piece an irules sweep cycle lacks (7.4.DX);
    - the SWEEP half [hyM P p (na + k + nb) -> hyC P' p (k + c)] is a chain
      indexed by the block length, with the counter as its OPAQUE left
      tail: [SweepGlueTr]'s inner loop over the block.  It may cross the
      block several times (a counter that steps once every few sweeps).

    The anchor shape [P] (state, head symbol, how the block's unit lines
    up with the junction) may cycle with the lap: when the block grows by
    a number of cells the unit does not divide, the junction sees the
    unit at a different offset each lap.  A certificate is a list of
    PHASES, each phase's sweep ending on the next phase's anchor, so the
    lap is [(p, n, i) -> (Pos.succ p, n - nmin_i + c_i, i + 1 mod L)].
    The run visits one anchor per counter value: [hyCf p] is the
    [(p - p0)]-th iterate from the boot, which is the single-index [Hlap]
    of [LapGlueTr.glue_neverqhtr] (DN rows) or
    [QHConveyorTr.lap_qh_stage] (QH rows).

    Per-instruction fires come from chain prefixes of any phase's three
    chains, reached by laps ([hy_reach]): a sweep fire from the next
    anchor of that phase; an interior or overflow fire from a counter
    value with the right carry shape IN that phase, named by the
    certificate as a family ([ones_on j (xO (r0 + L s))], resp.
    [ones_on (k0 + T s) xH]) whose phase the checker computes.

    Everything a board supplies is DATA ([hycert]); [hy_check_nqh] /
    [hy_check_qh] are evaluated by [vm_compute] and the soundness is
    proved once.  Axiom footprint: [functional_extensionality_dep] (via
    [CTape.lift]). *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape ClosureTr Mirror.
From BBB4.Checkers Require Import WrapTr LapDecider TCyclerQHTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
From BBB4.Counters Require Import WTape MonoCounter LapCertGlue LapCertGlueLift
                                  LapGlueTr SweepGlueTr.
From BBB4.CensusTr Require Import TNF_QHTr QHConveyorTr.
Import ListNotations.

(** ** The counter word, generic in its three digit words *)

Fixpoint hyE (A B C : list Sym) (p : positive) : list Sym :=
  match p with
  | xH => C
  | xO r => A ++ hyE A B C r
  | xI r => B ++ hyE A B C r
  end.

Lemma hyE_some : forall A B C p j r, cview p = (j, Some r) ->
  hyE A B C p = rep B j ++ A ++ hyE A B C r /\
  hyE A B C (Pos.succ p) = rep A j ++ B ++ hyE A B C r.
Proof.
  intros A B C. induction p; intros j r H; cbn in H.
  - destruct (cview p) as [j' r'] eqn:E. inversion H; subst j r'.
    destruct (IHp j' r eq_refl) as (H1 & H2).
    cbn [hyE Pos.succ rep]. rewrite H1, H2, <- !app_assoc. split; reflexivity.
  - inversion H; subst j r. split; reflexivity.
  - discriminate.
Qed.

Lemma hyE_none : forall A B C p j, cview p = (S j, None) ->
  hyE A B C p = rep B j ++ C /\
  hyE A B C (Pos.succ p) = rep A (S j) ++ C.
Proof.
  intros A B C. induction p; intros j H; cbn in H.
  - destruct (cview p) as [j' r] eqn:E. inversion H; subst j' r.
    destruct j as [|j].
    + exfalso. destruct (cview_pos p 0 E) as (x & Hx). discriminate.
    + destruct (IHp j eq_refl) as (H1 & H2).
      cbn [hyE Pos.succ]. rewrite H1, H2.
      change (rep B (S j)) with (B ++ rep B j).
      change (rep A (S (S j))) with (A ++ rep A (S j)).
      rewrite <- !app_assoc. split; reflexivity.
  - discriminate.
  - inversion H; subst j. cbn. rewrite app_nil_r. split; reflexivity.
Qed.

(** ** The certificate *)

(** one phase of the lap: the anchor shape, the mid configuration, and the
    three chains.  The sweep of a phase ends on the NEXT phase's anchor. *)
Record hyphase := mkHP {
  hp_q     : St;
  hp_h     : Sym;
  hp_Lpre  : list Sym;
  hp_Rpre  : list Sym;
  hp_w     : list Sym;       (** the block's unit, as this phase reads it *)
  hp_Rpost : list Sym;
  hp_m     : nat;            (** block units the counter half sees *)
  hp_q2    : St;             (** the mid configuration *)
  hp_h2    : Sym;
  hp_Mpre  : list Sym;
  hp_c     : nat;            (** the sweep ends on [k + c] units of the next phase *)
  hp_nu    : nat;            (** interior: carry units unrolled *)
  hp_chi   : list lstep;
  hp_ibase : list (list lstep);  (** the carries [j < nu], concrete *)
  hp_no    : nat;            (** overflow: carry units unrolled *)
  hp_cho   : list lstep;
  hp_obase : list (list lstep);  (** the carries [j < no], concrete *)
  hp_na    : nat;            (** sweep: units unrolled at the near end *)
  hp_nb    : nat;            (** ... and at the far end *)
  hp_chs   : list lstep
}.

(** a fire witness: a chain prefix of one phase's interior (kind 0),
    overflow (kind 1) or sweep (kind 2) chain.  For kinds 0 and 1, [a] and
    [b] name a family of counter values of that phase with the right carry
    shape: [ones_on a (xO (b + L s))] (interior) and [ones_on (a + b s) xH]
    (overflow), [s] arbitrary. *)
Record hyfire := mkHF {
  hf_ph   : nat;
  hf_kind : nat;
  hf_a    : nat;
  hf_b    : nat;
  hf_ch   : list lstep
}.

Record hycert := mkHY {
  hy_pins   : list Instr;    (** never fire after the boot (and the undefined ones) *)
  hy_A      : list Sym;      (** digit 0 *)
  hy_B      : list Sym;      (** digit 1 *)
  hy_C      : list Sym;      (** the top digit, and whatever lies beyond it *)
  hy_phases : list hyphase;  (** the lap cycles through them *)
  hy_fires  : list hyfire;
  hy_t0     : nat;           (** the boot index *)
  hy_p0     : positive;      (** the counter at the boot *)
  hy_i0     : nat;           (** the phase at the boot *)
  hy_n0     : nat            (** the block at the boot *)
}.

Definition hp_dflt : hyphase :=
  mkHP StA S0 [] [] [] [] 0 StA S0 [] 0 0 [] [] 0 [] [] 0 0 [].

Section Defs.

Variable w : hycert.

Definition hyEw : positive -> list Sym := hyE (hy_A w) (hy_B w) (hy_C w).

Definition hyL : nat := length (hy_phases w).
Definition hyph (i : nat) : hyphase := nth i (hy_phases w) hp_dflt.
Definition hynx (i : nat) : nat := S i mod hyL.

Section Phase.

Variable P : hyphase.

Definition hyC (p : positive) (n : nat) : cconf :=
  (hp_q P, (hp_Lpre P ++ hyEw p, hp_h P, hp_Rpre P ++ rep (hp_w P) n ++ hp_Rpost P)).

Definition hyM (p : positive) (n : nat) : cconf :=
  (hp_q2 P, (hp_Mpre P ++ hyEw p, hp_h2 P, rep (hp_w P) n ++ hp_Rpost P)).

Definition hyRw : list Sym := hp_Rpre P ++ rep (hp_w P) (hp_m P).

(** the chain starts *)
Definition hyA0 : sconf :=
  mkC (hp_q P) (mkS (hp_Lpre P ++ rep (hy_B w) (hp_nu P)) (hy_B w) 1 0 (hy_A w))
      (hp_h P) (sflat hyRw).

Definition hyB0 : sconf :=
  mkC (hp_q P) (mkS (hp_Lpre P ++ rep (hy_B w) (hp_no P)) (hy_B w) 1 0 (hy_C w))
      (hp_h P) (sflat hyRw).

Definition hyIB (j : nat) : sconf :=
  mkC (hp_q P) (sflat (hp_Lpre P ++ rep (hy_B w) j ++ hy_A w)) (hp_h P) (sflat hyRw).

Definition hyOB (j : nat) : sconf :=
  mkC (hp_q P) (sflat (hp_Lpre P ++ rep (hy_B w) j ++ hy_C w)) (hp_h P) (sflat hyRw).

Definition hyS0 : sconf :=
  mkC (hp_q2 P) (sflat (hp_Mpre P)) (hp_h2 P)
      (mkS (rep (hp_w P) (hp_na P)) (hp_w P) 1 0 (rep (hp_w P) (hp_nb P) ++ hp_Rpost P)).

Definition hy_nmin : nat := hp_m P + hp_na P + hp_nb P.

(** ** The checker, per phase *)

Definition sside_nil (s : sside) : bool :=
  syms_eqb (s_pre s) [] && syms_eqb (s_u s) [] && syms_eqb (s_post s) [].

Definition hy_eqb (el : bool) (a b : list Sym) : bool :=
  if el then lpad_eqb a b else syms_eqb a b.

(** a counter half ends on the mid, its left side denoting
    [Mpre ++ rep A (j + c) ++ post] *)
Definition hy_cend_ok (el : bool) (c : nat) (post : list Sym) (c1 : sconf) : bool :=
  st_eqb (c_st c1) (hp_q2 P) && sym_eqb (c_h c1) (hp_h2 P) && sside_nil (c_r c1)
  && syms_eqb (s_u (c_l c1)) (hy_A w) && Nat.eqb (s_a (c_l c1)) 1
  && (s_b (c_l c1) <=? c)
  && existsb (fun x => syms_eqb (s_pre (c_l c1)) (hp_Mpre P ++ rep (hy_A w) x)
                       && hy_eqb el (s_post (c_l c1))
                                 (rep (hy_A w) (c - s_b (c_l c1) - x) ++ post))
             (seq 0 (S (c - s_b (c_l c1)))).

Definition hy_cbase_ok (el : bool) (want : list Sym) (c1 : sconf) : bool :=
  st_eqb (c_st c1) (hp_q2 P) && sym_eqb (c_h c1) (hp_h2 P) && sside_nil (c_r c1)
  && syms_eqb (s_u (c_l c1)) [] && syms_eqb (s_post (c_l c1)) []
  && hy_eqb el (s_pre (c_l c1)) want.

Definition hy_run_ok (tmw : TM) (el er : bool) (ch : list lstep) (c : sconf)
                     (ok : sconf -> bool) : bool :=
  match srun tmw el er ch c with
  | Some (c1, _, _) => ok c1
  | None => false
  end.

Fixpoint hy_list_ok (f : nat -> list lstep -> bool) (j : nat)
                    (l : list (list lstep)) : bool :=
  match l with
  | [] => true
  | ch :: l' => f j ch && hy_list_ok f (S j) l'
  end.

Definition hy_counter_ok (tmw : TM) : bool :=
  hy_run_ok tmw false false (hp_chi P) hyA0 (hy_cend_ok false (hp_nu P) (hy_B w))
  && hy_run_ok tmw true false (hp_cho P) hyB0 (hy_cend_ok true (S (hp_no P)) (hy_C w))
  && hy_list_ok (fun j ch => hy_run_ok tmw false false ch (hyIB j)
                   (hy_cbase_ok false (hp_Mpre P ++ rep (hy_A w) j ++ hy_B w)))
                0 (hp_ibase P)
  && (hp_nu P <=? length (hp_ibase P))
  && hy_list_ok (fun j ch => hy_run_ok tmw true false ch (hyOB j)
                   (hy_cbase_ok true (hp_Mpre P ++ rep (hy_A w) (S j) ++ hy_C w)))
                0 (hp_obase P)
  && (hp_no P <=? length (hp_obase P)).

(** the sweep lands on the next phase's anchor, [k + c] units *)
Definition hy_sweep_ok (tmw : TM) (P' : hyphase) : bool :=
  match srun tmw false true (hp_chs P) hyS0 with
  | Some (c1, _, cb) =>
      st_eqb (c_st c1) (hp_q P') && sym_eqb (c_h c1) (hp_h P')
      && sside_flat_is (c_l c1) (hp_Lpre P')
      && sside_end_is (c_r c1) (hp_Rpre P') (hp_w P') (hp_c P) (hp_Rpost P')
      && (0 <? cb)
  | None => false
  end.

End Phase.

(** every phase: its counter half, its sweep onto the next phase, and the
    block never below the next phase's minimum *)
Definition hy_phase_ok (tmw : TM) (i : nat) : bool :=
  hy_counter_ok (hyph i) tmw && hy_sweep_ok (hyph i) tmw (hyph (hynx i))
  && (hy_nmin (hyph (hynx i)) <=? hp_c (hyph i)).

Definition hy_phases_ok (tmw : TM) : bool :=
  (1 <=? hyL) && forallb (hy_phase_ok tmw) (seq 0 hyL).

(** the phase of the anchor at counter value [x] *)
Definition hy_phase_of (x : nat) : nat := (hy_i0 w + (x - Pos.to_nat (hy_p0 w))) mod hyL.

(** interior family: [ones_on j (xO (r0 + L s))] is in phase [i] for every [s] *)
Definition hy_int_fam_ok (i j r0 : nat) : bool :=
  let x := 2 ^ S j * r0 + (2 ^ j - 1) in
  (1 <=? r0) && (Pos.to_nat (hy_p0 w) <=? x) && Nat.eqb (hy_phase_of x) i.

(** overflow family: [ones_on (k0 + T s) xH] is in phase [i] for every [s] *)
Definition hy_ovf_fam_ok (i k0 T : nat) : bool :=
  let a := 2 ^ S k0 in
  (1 <=? T) && (Pos.to_nat (hy_p0 w) <=? a - 1)
  && Nat.eqb ((2 ^ (S k0 + T)) mod hyL) (a mod hyL) && Nat.eqb (hy_phase_of (a - 1)) i.

Definition hy_fire_ok (tmw : TM) (t : Instr) (f : hyfire) : bool :=
  let P := hyph (hf_ph f) in
  (hf_ph f <? hyL) &&
  match hf_kind f with
  | 0 => match srun_instr tmw false false (hf_ch f) (hyA0 P) with
         | Some t' => instr_eqb t' t && (hp_nu P <=? hf_a f)
                      && hy_int_fam_ok (hf_ph f) (hf_a f) (hf_b f)
         | None => false
         end
  | 1 => match srun_instr tmw true false (hf_ch f) (hyB0 P) with
         | Some t' => instr_eqb t' t && (hp_no P <=? hf_a f)
                      && hy_ovf_fam_ok (hf_ph f) (hf_a f) (hf_b f)
         | None => false
         end
  | _ => match srun_instr tmw false true (hf_ch f) (hyS0 P) with
         | Some t' => instr_eqb t' t
         | None => false
         end
  end.

Definition hy_fires_ok (tmw : TM) : bool :=
  forallb (fun t => tr_inb t (hy_pins w) || existsb (hy_fire_ok tmw t) (hy_fires w))
          all_Instr.

Definition hy_core_ok (tmw : TM) : bool :=
  hy_phases_ok tmw && hy_fires_ok tmw
  && (hy_i0 w <? hyL) && (hy_nmin (hyph (hy_i0 w)) <=? hy_n0 w).

Definition hy_boot_ok (tm : TM) : bool :=
  match csteps tm (hy_t0 w) c0 with
  | Some c => ceqb c (hyC (hyph (hy_i0 w)) (hy_p0 w) (hy_n0 w))
  | None => false
  end.

End Defs.

(** the never-quasihalting check: boot and laps on the wrapped machine *)
Definition hy_check_nqh (tm : TM) (w : hycert) : bool :=
  let tmw := tm_wrap_trs tm (hy_pins w) in
  hy_boot_ok w tmw && hy_core_ok w tmw.

(** the quasihalting check: the boot on the original machine, a pinned
    instruction fired in it, and a boot index under [2^24] (the QH
    hybrids' quiet instructions stop near step 8M; the bound is read off
    [Nat.log2] so no unary [2^24] is ever built per row) *)
Definition hy_check_qh (tm : TM) (w : hycert) : bool :=
  let tmw := tm_wrap_trs tm (hy_pins w) in
  hy_boot_ok w tm
  && existsb (fun tg => cfires tm c0 (hy_t0 w) tg) (hy_pins w)
  && (Nat.log2 (hy_t0 w) <? 24)
  && hy_core_ok w tmw.

(** ** Soundness *)

Lemma hy_cap_le : forall n, (Nat.log2 n <? 24) = true -> (n <=? 32779478) = true.
Proof.
  intros n H. apply Nat.ltb_lt in H. apply Nat.leb_le.
  destruct n as [|n]; [lia |].
  apply (Nat.le_trans _ (2 ^ 24)).
  - apply Nat.lt_le_incl. apply Nat.log2_lt_pow2; [lia | exact H].
  - apply Nat.leb_le. vm_compute. reflexivity.
Qed.

Lemma hy_eqb_lpad : forall el a b X, hy_eqb el a b = true -> (el = true -> X = []) ->
  lpad_eqb (a ++ X) (b ++ X) = true.
Proof.
  intros [|] a b X H HX; cbn [hy_eqb] in H.
  - rewrite (HX eq_refl), !app_nil_r. exact H.
  - apply syms_eqb_eq in H. subst b. apply lpad_eqb_refl.
Qed.

Lemma sside_nil_den : forall s X j, sside_nil s = true -> sden X j s = X.
Proof.
  intros [pre u a b post] X j H. unfold sside_nil in H; cbn [s_pre s_u s_post] in H.
  apply andb_prop in H as [H Hp]. apply andb_prop in H as [Hr Hu].
  apply syms_eqb_eq in Hr, Hu, Hp. subst.
  unfold sden; cbn [s_pre s_u s_a s_b s_post]. rewrite rep_nil. reflexivity.
Qed.

Lemma hy_list_ok_nth : forall f l j0, hy_list_ok f j0 l = true ->
  forall k ch, nth_error l k = Some ch -> f (j0 + k) ch = true.
Proof.
  intros f. induction l as [|ch0 l IH]; intros j0 H k ch Hk.
  - destruct k; discriminate.
  - cbn [hy_list_ok] in H. apply andb_prop in H as [H0 H].
    destruct k as [|k]; cbn in Hk.
    + injection Hk as <-. rewrite Nat.add_0_r. exact H0.
    + replace (j0 + S k) with (S j0 + k) by lia. exact (IH (S j0) H k ch Hk).
Qed.

Lemma lap_stepn : forall tm x y n c',
  csteps tm n x = Some c' -> lift c' = lift y ->
  stepn tm n (lift x) = Some (lift y).
Proof. intros tm x y n c' H Hl. rewrite <- Hl. apply csteps_lift. exact H. Qed.

(** ** One phase *)

Section PhaseSound.

Variable tmw : TM.
Variable w : hycert.
Variable P : hyphase.

Hypothesis Hctr : hy_counter_ok w P tmw = true.

(** a counter half's end, denoted *)
Lemma hy_cend_den : forall el c post c1 XL XR j,
  hy_cend_ok w P el c post c1 = true -> (el = true -> XL = []) ->
  lift (cden XL XR j c1)
  = lift (hp_q2 P, (hp_Mpre P ++ rep (hy_A w) (c + j) ++ post ++ XL, hp_h2 P, XR)).
Proof.
  intros el c post [q1 [lp lu la lb lq] h1 r1] XL XR j H HX.
  unfold hy_cend_ok in H; cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post] in H.
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
  replace (c + j) with (x + ((1 * j + lb) + (c - lb - x))) by lia.
  rewrite !rep_add, <- !app_assoc.
  repeat apply lpad_eqb_app.
  pose proof (hy_eqb_lpad el _ _ XL Hpost HX) as Hz. rewrite <- app_assoc in Hz. exact Hz.
Qed.

Lemma hy_cbase_den : forall el want c1 XL XR j,
  hy_cbase_ok P el want c1 = true -> (el = true -> XL = []) ->
  lift (cden XL XR j c1) = lift (hp_q2 P, (want ++ XL, hp_h2 P, XR)).
Proof.
  intros el want [q1 [lp lu la lb lq] h1 r1] XL XR j H HX.
  unfold hy_cbase_ok in H; cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post] in H.
  apply andb_prop in H as [H Hp].
  apply andb_prop in H as [H Hq'].
  apply andb_prop in H as [H Hu].
  apply andb_prop in H as [H Hr].
  apply andb_prop in H as [Hq Hh].
  apply st_eqb_spec in Hq; apply sym_eqb_spec in Hh.
  apply syms_eqb_eq in Hu, Hq'. subst.
  unfold cden; cbn [c_st c_l c_h c_r].
  rewrite (sside_nil_den r1 XR j Hr).
  apply lift_lpad; [| apply lpad_eqb_refl].
  unfold sden; cbn [s_pre s_u s_a s_b s_post]. rewrite rep_nil. cbn [app].
  exact (hy_eqb_lpad el _ _ XL Hp HX).
Qed.

Lemma hy_run_sound : forall el er ch c ok, hy_run_ok tmw el er ch c ok = true ->
  exists c1 ca cb, srun tmw el er ch c = Some (c1, ca, cb) /\ ok c1 = true.
Proof.
  intros el er ch c ok H. unfold hy_run_ok in H.
  destruct (srun tmw el er ch c) as [[[c1 ca] cb]|]; [|discriminate].
  exists c1, ca, cb. split; [reflexivity | exact H].
Qed.

(** the chain starts denote the anchors *)
Lemma hyA0_den : forall p j r n, hyEw w p = rep (hy_B w) (hp_nu P + j) ++ hy_A w ++ hyEw w r ->
  hyC w P p (hp_m P + n) = cden (hyEw w r) (rep (hp_w P) n ++ hp_Rpost P) j (hyA0 w P).
Proof.
  intros p j r n H1.
  unfold hyC, hyA0, hyRw, cden, sden, sflat;
    cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
  rewrite H1, rep_nil. replace (1 * j + 0) with j by lia.
  rewrite !rep_add, <- !app_assoc. reflexivity.
Qed.

Lemma hyB0_den : forall p j n, hyEw w p = rep (hy_B w) (hp_no P + j) ++ hy_C w ->
  hyC w P p (hp_m P + n) = cden [] (rep (hp_w P) n ++ hp_Rpost P) j (hyB0 w P).
Proof.
  intros p j n H1.
  unfold hyC, hyB0, hyRw, cden, sden, sflat;
    cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
  rewrite H1, rep_nil. replace (1 * j + 0) with j by lia.
  rewrite !rep_add, <- !app_assoc, !app_nil_r. reflexivity.
Qed.

(** *** The counter half *)

Lemma hy_int_main : forall p j r n, cview p = (hp_nu P + j, Some r) ->
  exists N c', csteps tmw N (hyC w P p (hp_m P + n)) = Some c' /\
               lift c' = lift (hyM w P (Pos.succ p) n).
Proof.
  intros p j r n Hv.
  pose proof Hctr as H. unfold hy_counter_ok in H.
  do 5 (apply andb_prop in H as [H _]).
  destruct (hy_run_sound _ _ _ _ _ H) as (c1 & ca & cb & Hrun & Hok).
  destruct (hyE_some (hy_A w) (hy_B w) (hy_C w) p _ r Hv) as (H1 & H2).
  exists (ca * j + cb), (cden (hyEw w r) (rep (hp_w P) n ++ hp_Rpost P) j c1).
  split.
  - rewrite (hyA0_den p j r n H1).
    exact (srun_sound tmw false false _ _ _ ca cb Hrun _ _ j
             ltac:(discriminate) ltac:(discriminate)).
  - rewrite (hy_cend_den false _ _ c1 _ _ j Hok ltac:(discriminate)).
    unfold hyM, hyEw. rewrite H2. reflexivity.
Qed.

Lemma hy_ovf_main : forall p j n, cview p = (S (hp_no P + j), None) ->
  exists N c', csteps tmw N (hyC w P p (hp_m P + n)) = Some c' /\
               lift c' = lift (hyM w P (Pos.succ p) n).
Proof.
  intros p j n Hv.
  pose proof Hctr as H. unfold hy_counter_ok in H.
  do 4 (apply andb_prop in H as [H _]). apply andb_prop in H as [_ H].
  destruct (hy_run_sound _ _ _ _ _ H) as (c1 & ca & cb & Hrun & Hok).
  destruct (hyE_none (hy_A w) (hy_B w) (hy_C w) p _ Hv) as (H1 & H2).
  exists (ca * j + cb), (cden [] (rep (hp_w P) n ++ hp_Rpost P) j c1).
  split.
  - rewrite (hyB0_den p j n H1).
    exact (srun_sound tmw true false _ _ _ ca cb Hrun _ _ j
             ltac:(reflexivity) ltac:(discriminate)).
  - rewrite (hy_cend_den true _ _ c1 _ _ j Hok ltac:(reflexivity)).
    unfold hyM, hyEw. rewrite H2, app_nil_r. reflexivity.
Qed.

Lemma hy_int_base : forall p j r n, j < hp_nu P -> cview p = (j, Some r) ->
  exists N c', csteps tmw N (hyC w P p (hp_m P + n)) = Some c' /\
               lift c' = lift (hyM w P (Pos.succ p) n).
Proof.
  intros p j r n Hj Hv.
  pose proof Hctr as H. unfold hy_counter_ok in H.
  do 2 (apply andb_prop in H as [H _]).
  apply andb_prop in H as [H Hlen]. apply andb_prop in H as [_ H].
  apply Nat.leb_le in Hlen.
  destruct (nth_error (hp_ibase P) j) as [ch|] eqn:Ech.
  2: { apply nth_error_None in Ech. lia. }
  pose proof (hy_list_ok_nth _ _ 0 H j ch Ech) as Hj0. cbn [Nat.add] in Hj0.
  destruct (hy_run_sound _ _ _ _ _ Hj0) as (c1 & ca & cb & Hrun & Hok).
  destruct (hyE_some (hy_A w) (hy_B w) (hy_C w) p _ r Hv) as (H1 & H2).
  exists (ca * 0 + cb), (cden (hyEw w r) (rep (hp_w P) n ++ hp_Rpost P) 0 c1).
  split.
  - assert (E : hyC w P p (hp_m P + n)
                = cden (hyEw w r) (rep (hp_w P) n ++ hp_Rpost P) 0 (hyIB w P j)).
    { unfold hyC, hyIB, hyRw, cden, sden, sflat, hyEw;
        cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
      rewrite H1, !rep_nil. rewrite !rep_add, <- !app_assoc. reflexivity. }
    rewrite E. exact (srun_sound tmw false false _ _ _ ca cb Hrun _ _ 0
                        ltac:(discriminate) ltac:(discriminate)).
  - rewrite (hy_cbase_den false _ c1 _ _ 0 Hok ltac:(discriminate)).
    unfold hyM, hyEw. rewrite H2, <- !app_assoc. reflexivity.
Qed.

Lemma hy_ovf_base : forall p j n, j < hp_no P -> cview p = (S j, None) ->
  exists N c', csteps tmw N (hyC w P p (hp_m P + n)) = Some c' /\
               lift c' = lift (hyM w P (Pos.succ p) n).
Proof.
  intros p j n Hj Hv.
  pose proof Hctr as H. unfold hy_counter_ok in H.
  apply andb_prop in H as [H Hlen]. apply andb_prop in H as [_ H].
  apply Nat.leb_le in Hlen.
  destruct (nth_error (hp_obase P) j) as [ch|] eqn:Ech.
  2: { apply nth_error_None in Ech. lia. }
  pose proof (hy_list_ok_nth _ _ 0 H j ch Ech) as Hj0. cbn [Nat.add] in Hj0.
  destruct (hy_run_sound _ _ _ _ _ Hj0) as (c1 & ca & cb & Hrun & Hok).
  destruct (hyE_none (hy_A w) (hy_B w) (hy_C w) p _ Hv) as (H1 & H2).
  exists (ca * 0 + cb), (cden [] (rep (hp_w P) n ++ hp_Rpost P) 0 c1).
  split.
  - assert (E : hyC w P p (hp_m P + n)
                = cden [] (rep (hp_w P) n ++ hp_Rpost P) 0 (hyOB w P j)).
    { unfold hyC, hyOB, hyRw, cden, sden, sflat, hyEw;
        cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
      rewrite H1, !rep_nil. rewrite !rep_add, <- !app_assoc, !app_nil_r. reflexivity. }
    rewrite E. exact (srun_sound tmw true false _ _ _ ca cb Hrun _ _ 0
                        ltac:(reflexivity) ltac:(discriminate)).
  - rewrite (hy_cbase_den true _ c1 _ _ 0 Hok ltac:(reflexivity)).
    unfold hyM, hyEw. rewrite H2, <- !app_assoc, !app_nil_r. reflexivity.
Qed.

Lemma hy_half : forall p n, exists N c',
  csteps tmw N (hyC w P p (hp_m P + n)) = Some c' /\
  lift c' = lift (hyM w P (Pos.succ p) n).
Proof.
  intros p n.
  destruct (cview p) as [j [r|]] eqn:Hv.
  - destruct (lt_dec j (hp_nu P)) as [Hj | Hj].
    + exact (hy_int_base p j r n Hj Hv).
    + replace j with (hp_nu P + (j - hp_nu P)) in Hv by lia.
      exact (hy_int_main p _ r n Hv).
  - destruct (cview_pos p j Hv) as (j' & ->).
    destruct (lt_dec j' (hp_no P)) as [Hj | Hj].
    + exact (hy_ovf_base p j' n Hj Hv).
    + replace j' with (hp_no P + (j' - hp_no P)) in Hv by lia.
      exact (hy_ovf_main p _ n Hv).
Qed.

Lemma hy_to_mid : forall p n, hy_nmin P <= n -> exists N,
  stepn tmw N (lift (hyC w P p n))
  = Some (lift (hyM w P (Pos.succ p) (hp_na P + (n - hy_nmin P) + hp_nb P))).
Proof.
  intros p n Hn. unfold hy_nmin in *.
  destruct (hy_half p (n - hp_m P)) as (N & c' & H1 & Hl).
  exists N. replace (hp_na P + (n - (hp_m P + hp_na P + hp_nb P)) + hp_nb P)
    with (n - hp_m P) by lia.
  replace n with (hp_m P + (n - hp_m P)) at 1 by lia.
  exact (lap_stepn _ _ _ _ _ H1 Hl).
Qed.

End PhaseSound.

Lemma hyS0_den : forall w P p k,
  cden (hyEw w p) [] k (hyS0 P) = hyM w P p (hp_na P + k + hp_nb P).
Proof.
  intros w P p k. unfold cden, hyS0, hyM, sden, sflat;
    cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
  replace (1 * k + 0) with k by lia. rewrite rep_nil, !app_nil_r.
  rewrite !rep_add, <- !app_assoc. reflexivity.
Qed.

(** *** The sweep half, onto the next phase *)

Lemma hy_sweep_main : forall tmw w P P', hy_sweep_ok P tmw P' = true ->
  forall p k, exists N c',
  csteps tmw N (hyM w P p (hp_na P + k + hp_nb P)) = Some c' /\
  lift c' = lift (hyC w P' p (k + hp_c P)) /\ 0 < N.
Proof.
  intros tmw w P P' H p k. unfold hy_sweep_ok in H.
  destruct (srun tmw false true (hp_chs P) (hyS0 P)) as [[[c1 ca] cb]|] eqn:E;
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
  set (c := hp_c P) in *.
  exists (ca * k + cb),
    (cden (hyEw w p) [] k
          (mkC (hp_q P') (mkS (hp_Lpre P') [] la lb []) (hp_h P')
               (mkS (hp_Rpre P' ++ rep (hp_w P') x) (hp_w P') 1 rb rq))).
  split; [| split; [| lia]].
  - rewrite <- hyS0_den.
    exact (srun_sound tmw false true (hp_chs P) (hyS0 P) _ ca cb E
             (hyEw w p) [] k ltac:(discriminate) ltac:(reflexivity)).
  - unfold cden, hyC, sden; cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post rep].
    rewrite rep_nil. rewrite !app_nil_r. cbn [app].
    apply lift_lpad; [apply lpad_eqb_refl |].
    replace (k + c) with (x + ((1 * k + rb) + (c - rb - x))) by lia.
    rewrite !rep_add, <- !app_assoc.
    repeat apply lpad_eqb_app. exact Hrq.
Qed.

(** *** One lap: counter half, then sweep *)

Lemma hy_lap : forall tmw w P P', hy_counter_ok w P tmw = true ->
  hy_sweep_ok P tmw P' = true ->
  forall p n, hy_nmin P <= n -> exists N, 0 < N /\
  stepn tmw N (lift (hyC w P p n))
  = Some (lift (hyC w P' (Pos.succ p) (n - hy_nmin P + hp_c P))).
Proof.
  intros tmw w P P' Hc Hs p n Hn.
  destruct (hy_to_mid tmw w P Hc p n Hn) as (N1 & H1).
  destruct (hy_sweep_main tmw w P P' Hs (Pos.succ p) (n - hy_nmin P))
    as (N2 & c2 & H2 & Hl2 & HN2).
  exists (N1 + N2). split; [lia |].
  rewrite stepn_add, H1, (lap_stepn _ _ _ _ _ H2 Hl2). reflexivity.
Qed.

(** *** Fires, from one phase's anchors *)

Definition FiresFrom (tmw : TM) (c : cconf) (t : Instr) : Prop :=
  exists k e, stepn tmw k (lift c) = Some e /\ instr_of e = t.

Lemma fires_back : forall tmw x y n t,
  stepn tmw n (lift x) = Some (lift y) -> FiresFrom tmw y t -> FiresFrom tmw x t.
Proof.
  intros tmw x y n t H (k & e & Hk & Ht). exists (n + k), e.
  split; [rewrite stepn_add, H; exact Hk | exact Ht].
Qed.

Lemma fire_int : forall tmw w P ch t, srun_instr tmw false false ch (hyA0 w P) = Some t ->
  forall p j r n, cview p = (hp_nu P + j, Some r) ->
  FiresFrom tmw (hyC w P p (hp_m P + n)) t.
Proof.
  intros tmw w P ch t H p j r n Hv.
  destruct (hyE_some (hy_A w) (hy_B w) (hy_C w) p _ r Hv) as (H1 & _).
  apply fire_lift_of_csteps with (Cc := fun _ => hyC w P p (hp_m P + n)) (p := xH).
  exact (fire_of_run_instr tmw (fun _ => hyC w P p (hp_m P + n)) false false
           ch (hyA0 w P) xH j (hyEw w r) (rep (hp_w P) n ++ hp_Rpost P) t H
           ltac:(discriminate) ltac:(discriminate) (hyA0_den w P p j r n H1)).
Qed.

Lemma fire_ovf : forall tmw w P ch t, srun_instr tmw true false ch (hyB0 w P) = Some t ->
  forall p j n, cview p = (S (hp_no P + j), None) ->
  FiresFrom tmw (hyC w P p (hp_m P + n)) t.
Proof.
  intros tmw w P ch t H p j n Hv.
  destruct (hyE_none (hy_A w) (hy_B w) (hy_C w) p _ Hv) as (H1 & _).
  apply fire_lift_of_csteps with (Cc := fun _ => hyC w P p (hp_m P + n)) (p := xH).
  exact (fire_of_run_instr tmw (fun _ => hyC w P p (hp_m P + n)) true false
           ch (hyB0 w P) xH j [] (rep (hp_w P) n ++ hp_Rpost P) t H
           ltac:(reflexivity) ltac:(discriminate) (hyB0_den w P p j n H1)).
Qed.

Lemma fire_sweep : forall tmw w P ch t, srun_instr tmw false true ch (hyS0 P) = Some t ->
  forall p k, FiresFrom tmw (hyM w P p (hp_na P + k + hp_nb P)) t.
Proof.
  intros tmw w P ch t H p k.
  apply fire_lift_of_csteps with (Cc := fun _ => hyM w P p (hp_na P + k + hp_nb P)) (p := xH).
  exact (fire_of_run_instr tmw (fun _ => hyM w P p (hp_na P + k + hp_nb P)) false true
           ch (hyS0 P) xH k (hyEw w p) [] t H
           ltac:(discriminate) ltac:(reflexivity) (eq_sym (hyS0_den w P p k))).
Qed.

(** ** Counter values with a chosen carry shape *)

(** [k] ones below [r] *)
Fixpoint ones_on (k : nat) (r : positive) : positive :=
  match k with
  | 0 => r
  | S k' => xI (ones_on k' r)
  end.

Lemma cview_ones_xO : forall k r, cview (ones_on k (xO r)) = (k, Some r).
Proof.
  induction k as [|k IH]; intros r; [reflexivity |].
  cbn [ones_on cview]. rewrite IH. reflexivity.
Qed.

Lemma cview_ones_xH : forall k, cview (ones_on k xH) = (S k, None).
Proof.
  induction k as [|k IH]; [reflexivity |].
  cbn [ones_on cview]. rewrite IH. reflexivity.
Qed.

Lemma ones_on_nat : forall k r,
  Pos.to_nat (ones_on k r) = 2 ^ k * Pos.to_nat r + (2 ^ k - 1).
Proof.
  induction k as [|k IH]; intros r; cbn [ones_on].
  - cbn. lia.
  - rewrite Pos2Nat.inj_xI, IH. rewrite Nat.pow_succ_r'.
    pose proof (Nat.pow_nonzero 2 k ltac:(discriminate)).
    set (Y := 2 ^ k) in *. nia.
Qed.

(** ** The phases together *)

Section Sound.

Variable tmw : TM.
Variable w : hycert.

Hypothesis Hcore : hy_core_ok w tmw = true.

Lemma hy_core_phases : hy_phases_ok w tmw = true.
Proof.
  pose proof Hcore as H. unfold hy_core_ok in H.
  do 3 (apply andb_prop in H as [H _]). exact H.
Qed.

Lemma hy_core_fires : hy_fires_ok w tmw = true.
Proof.
  pose proof Hcore as H. unfold hy_core_ok in H.
  do 2 (apply andb_prop in H as [H _]). apply andb_prop in H as [_ H]. exact H.
Qed.

Lemma hy_L_pos : 1 <= hyL w.
Proof.
  pose proof hy_core_phases as H. unfold hy_phases_ok in H.
  apply andb_prop in H as [H _]. apply Nat.leb_le in H. exact H.
Qed.

Lemma hy_phase_at : forall i, i < hyL w ->
  hy_counter_ok w (hyph w i) tmw = true
  /\ hy_sweep_ok (hyph w i) tmw (hyph w (hynx w i)) = true
  /\ hy_nmin (hyph w (hynx w i)) <= hp_c (hyph w i).
Proof.
  intros i Hi. pose proof hy_core_phases as H. unfold hy_phases_ok in H.
  apply andb_prop in H as [_ H]. rewrite forallb_forall in H.
  specialize (H i ltac:(apply in_seq; lia)).
  unfold hy_phase_ok in H.
  apply andb_prop in H as [H Hn]. apply andb_prop in H as [Hc Hs].
  apply Nat.leb_le in Hn. auto.
Qed.

(** the anchors the run visits: counter [p], block [n], phase [i] *)
Definition hyS : Type := (positive * nat * nat)%type.

Definition hyA (s : hyS) : cconf :=
  let '(p, n, i) := s in hyC w (hyph w i) p n.

Definition hy_good (s : hyS) : Prop :=
  let '(p, n, i) := s in
  (hy_p0 w <= p)%positive /\ i = hy_phase_of w (Pos.to_nat p)
  /\ hy_nmin (hyph w i) <= n.

Definition hy_nxt (s : hyS) : hyS :=
  let '(p, n, i) := s in (Pos.succ p, n - hy_nmin (hyph w i) + hp_c (hyph w i), hynx w i).

Lemma hy_phase_lt : forall x, hy_phase_of w x < hyL w.
Proof. intros x. unfold hy_phase_of. apply Nat.mod_upper_bound. pose proof hy_L_pos. lia. Qed.

Lemma hy_phase_succ : forall p, (hy_p0 w <= p)%positive ->
  hy_phase_of w (Pos.to_nat (Pos.succ p)) = hynx w (hy_phase_of w (Pos.to_nat p)).
Proof.
  intros p Hp. apply Pos2Nat.inj_le in Hp. pose proof hy_L_pos as HL.
  unfold hy_phase_of, hynx. rewrite Pos2Nat.inj_succ.
  replace (hy_i0 w + (S (Pos.to_nat p) - Pos.to_nat (hy_p0 w)))
    with (1 + (hy_i0 w + (Pos.to_nat p - Pos.to_nat (hy_p0 w)))) by lia.
  symmetry. exact (Nat.Div0.add_mod_idemp_r 1 _ _).
Qed.

Lemma hy_step : forall s, hy_good s -> hy_good (hy_nxt s) /\ exists N, 0 < N /\
  stepn tmw N (lift (hyA s)) = Some (lift (hyA (hy_nxt s))).
Proof.
  intros [[p n] i] (Hp & Hi & Hn). cbn [hy_nxt hyA hy_good].
  destruct (hy_phase_at i ltac:(rewrite Hi; apply hy_phase_lt)) as (Hc & Hs & Hm).
  split.
  - split; [eapply Pos.le_trans; [exact Hp | apply Pos.lt_le_incl, Pos.lt_succ_diag_r] |].
    split; [rewrite Hi; symmetry; exact (hy_phase_succ p Hp) | lia].
  - exact (hy_lap tmw w _ _ Hc Hs p n Hn).
Qed.

(** reaching any larger counter value *)
Lemma hy_reach : forall p' s, hy_good s -> (fst (fst s) <= p')%positive ->
  exists T s', hy_good s' /\ fst (fst s') = p' /\
    stepn tmw T (lift (hyA s)) = Some (lift (hyA s')).
Proof.
  induction p' as [|p' IH] using Pos.peano_ind; intros s Hg Hp.
  - exists 0, s. split; [exact Hg |]. split; [| reflexivity].
    apply Pos.le_antisym; [exact Hp | apply Pos.le_1_l].
  - destruct (Pos.eq_dec (fst (fst s)) (Pos.succ p')) as [He | Hne].
    + exists 0, s. auto.
    + assert (Hlt : (fst (fst s) <= p')%positive).
      { apply Pos.lt_succ_r. apply Pos.le_lteq in Hp as [Hp | Hp]; [exact Hp |].
        contradiction. }
      destruct (IH s Hg Hlt) as (T & s' & Hg' & Hp' & HT).
      destruct (hy_step s' Hg') as (Hg'' & N & _ & HN).
      exists (T + N), (hy_nxt s'). split; [exact Hg'' |].
      split; [destruct s' as [[p1 n1] i1]; cbn in *; subst; reflexivity |].
      rewrite stepn_add, HT. exact HN.
Qed.

(** reaching a counter value [p'] from any visited anchor below it: the
    phase there is [hy_phase_of p'] *)
Lemma hy_reach_at : forall s p', hy_good s -> (fst (fst s) <= p')%positive ->
  exists T n', hy_nmin (hyph w (hy_phase_of w (Pos.to_nat p'))) <= n' /\
    stepn tmw T (lift (hyA s))
    = Some (lift (hyC w (hyph w (hy_phase_of w (Pos.to_nat p'))) p' n')).
Proof.
  intros s p' Hg Hp.
  destruct (hy_reach p' s Hg Hp) as (T & [[p1 n1] i1] & (Hp1 & Hi1 & Hn1) & He & HT).
  cbn in He. subst p1 i1. exists T, n1. auto.
Qed.

Lemma hy_int_phase : forall i j r0 q, hy_int_fam_ok w i j r0 = true ->
  hy_phase_of w (Pos.to_nat (ones_on j (xO (Pos.of_nat (r0 + hyL w * q))))) = i
  /\ (hy_p0 w <= ones_on j (xO (Pos.of_nat (r0 + hyL w * q))))%positive
  /\ q <= Pos.to_nat (ones_on j (xO (Pos.of_nat (r0 + hyL w * q)))).
Proof.
  intros i j r0 q H. unfold hy_int_fam_ok in H.
  apply andb_prop in H as [H Hph]. apply andb_prop in H as [Hr0 Hx].
  apply Nat.leb_le in Hr0, Hx. apply Nat.eqb_eq in Hph.
  pose proof hy_L_pos as HL.
  assert (Hof : Pos.to_nat (Pos.of_nat (r0 + hyL w * q)) = r0 + hyL w * q)
    by (apply Nat2Pos.id; lia).
  rewrite ones_on_nat, Pos2Nat.inj_xO, Hof.
  pose proof (Nat.pow_nonzero 2 j ltac:(discriminate)) as Hz.
  rewrite Nat.pow_succ_r' in Hx, Hph.
  set (Y := 2 ^ j) in *.
  split; [| split].
  - rewrite <- Hph. unfold hy_phase_of.
    replace (hy_i0 w + (Y * (2 * (r0 + hyL w * q)) + (Y - 1) - Pos.to_nat (hy_p0 w)))
      with ((hy_i0 w + (2 * Y * r0 + (Y - 1) - Pos.to_nat (hy_p0 w))) + (2 * Y * q) * hyL w)
      by nia.
    apply Nat.Div0.mod_add.
  - apply Pos2Nat.inj_le. rewrite ones_on_nat, Pos2Nat.inj_xO, Hof. nia.
  - nia.
Qed.

Lemma pow2_mod_period : forall L a T, 0 < L ->
  (2 ^ (a + T)) mod L = (2 ^ a) mod L ->
  forall q, (2 ^ (a + T * q)) mod L = (2 ^ a) mod L.
Proof.
  intros L a T HL H. induction q as [|q IH].
  - rewrite Nat.mul_0_r, Nat.add_0_r. reflexivity.
  - replace (a + T * S q) with ((a + T * q) + T) by lia.
    rewrite Nat.pow_add_r, Nat.Div0.mul_mod, IH, <- Nat.Div0.mul_mod.
    rewrite <- Nat.pow_add_r. exact H.
Qed.

Lemma ones_xH_nat : forall k, Pos.to_nat (ones_on k xH) = 2 ^ S k - 1.
Proof.
  induction k as [|k IH]; [reflexivity |].
  cbn [ones_on]. rewrite Pos2Nat.inj_xI, IH.
  rewrite (Nat.pow_succ_r' 2 (S k)).
  pose proof (Nat.pow_nonzero 2 (S k) ltac:(discriminate)). lia.
Qed.

Lemma hy_ovf_phase : forall i k0 T q, hy_ovf_fam_ok w i k0 T = true ->
  hy_phase_of w (Pos.to_nat (ones_on (k0 + T * q) xH)) = i
  /\ (hy_p0 w <= ones_on (k0 + T * q) xH)%positive
  /\ q <= Pos.to_nat (ones_on (k0 + T * q) xH).
Proof.
  intros i k0 T q H. unfold hy_ovf_fam_ok in H.
  apply andb_prop in H as [H Hph]. apply andb_prop in H as [H Hper].
  apply andb_prop in H as [HT Ha].
  apply Nat.leb_le in HT, Ha. apply Nat.eqb_eq in Hph, Hper.
  pose proof hy_L_pos as HL.
  rewrite ones_xH_nat.
  change (S (k0 + T * q)) with (S k0 + T * q).
  assert (Hge : 2 ^ S k0 <= 2 ^ (S k0 + T * q)) by (apply Nat.pow_le_mono_r; lia).
  assert (Hq : q < 2 ^ (S k0 + T * q)).
  { apply (Nat.lt_le_trans _ (2 ^ q)); [apply Nat.pow_gt_lin_r; lia |].
    apply Nat.pow_le_mono_r; [discriminate | nia]. }
  pose proof (pow2_mod_period (hyL w) (S k0) T ltac:(lia) Hper q) as Hm.
  set (a := 2 ^ S k0) in *. set (Y := 2 ^ (S k0 + T * q)) in *.
  split; [| split].
  - rewrite <- Hph. unfold hy_phase_of.
    pose proof (Nat.div_mod Y (hyL w) ltac:(lia)) as HY.
    pose proof (Nat.div_mod a (hyL w) ltac:(lia)) as Ha'.
    assert (Hd : a / hyL w <= Y / hyL w) by (apply Nat.Div0.div_le_mono; lia).
    replace (hy_i0 w + (Y - 1 - Pos.to_nat (hy_p0 w)))
      with ((hy_i0 w + (a - 1 - Pos.to_nat (hy_p0 w)))
            + (Y / hyL w - a / hyL w) * hyL w) by nia.
    apply Nat.Div0.mod_add.
  - apply Pos2Nat.inj_le. rewrite ones_xH_nat.
    change (S (k0 + T * q)) with (S k0 + T * q). fold Y. lia.
  - lia.
Qed.

Lemma hy_good_ge : forall s, hy_good s -> hy_nmin (hyph w (snd s)) <= snd (fst s).
Proof. intros [[p n] i] (_ & _ & Hn). exact Hn. Qed.

(** a counter value above any given one, in phase [i]: a sweep fire *)
Lemma mod_shift : forall X i L, 0 < L -> i < L ->
  (X + (i + L - X mod L) mod L) mod L = i.
Proof.
  intros X i L HL Hi.
  rewrite Nat.Div0.add_mod_idemp_r, <- Nat.Div0.add_mod_idemp_l.
  pose proof (Nat.mod_upper_bound X L ltac:(lia)).
  replace (X mod L + (i + L - X mod L)) with (i + 1 * L) by lia.
  rewrite Nat.Div0.mod_add. apply Nat.mod_small. exact Hi.
Qed.

Lemma hy_fire_sweep_any : forall i ch t, i < hyL w ->
  srun_instr tmw false true ch (hyS0 (hyph w i)) = Some t ->
  forall s, hy_good s -> FiresFrom tmw (hyA s) t.
Proof.
  intros i ch t Hi H [[p n] i1] Hg.
  pose proof hy_L_pos as HL.
  remember (hy_i0 w + (Pos.to_nat p - Pos.to_nat (hy_p0 w))) as X eqn:EX.
  remember ((i + hyL w - X mod hyL w) mod hyL w) as d eqn:Ed.
  set (p' := Pos.of_nat (Pos.to_nat p + d)).
  assert (Hp' : Pos.to_nat p' = Pos.to_nat p + d) by (apply Nat2Pos.id; lia).
  assert (Hle : (p <= p')%positive) by (apply Pos2Nat.inj_le; lia).
  destruct (hy_reach_at (p, n, i1) p' Hg Hle) as (T & n' & Hn' & HT).
  assert (Hph : hy_phase_of w (Pos.to_nat p') = i).
  { destruct Hg as (Hp & _ & _). apply Pos2Nat.inj_le in Hp.
    unfold hy_phase_of. rewrite Hp'.
    replace (hy_i0 w + (Pos.to_nat p + d - Pos.to_nat (hy_p0 w))) with (X + d) by lia.
    subst d. exact (mod_shift X i (hyL w) ltac:(lia) Hi). }
  rewrite Hph in Hn', HT.
  apply (fires_back tmw _ _ T t HT).
  destruct (hy_to_mid tmw w (hyph w i) (proj1 (hy_phase_at i Hi)) p' n' Hn') as (N & HN).
  apply (fires_back tmw _ _ N t HN). apply (fire_sweep tmw w _ ch t H).
Qed.

Lemma hy_fire_int_any : forall i j r0 ch t, i < hyL w ->
  srun_instr tmw false false ch (hyA0 w (hyph w i)) = Some t ->
  hp_nu (hyph w i) <= j -> hy_int_fam_ok w i j r0 = true ->
  forall s, hy_good s -> FiresFrom tmw (hyA s) t.
Proof.
  intros i j r0 ch t Hi H Hj Hf [[p n] i1] Hg.
  set (p' := ones_on j (xO (Pos.of_nat (r0 + hyL w * Pos.to_nat p)))).
  destruct (hy_int_phase i j r0 (Pos.to_nat p) Hf) as (Hph & _ & Hge).
  fold p' in Hph, Hge.
  assert (Hle : (p <= p')%positive) by (apply Pos2Nat.inj_le; exact Hge).
  destruct (hy_reach_at (p, n, i1) p' Hg Hle) as (T & n' & Hn' & HT).
  rewrite Hph in Hn', HT.
  apply (fires_back tmw _ _ T t HT).
  unfold hy_nmin in Hn'.
  replace n' with (hp_m (hyph w i) + (n' - hp_m (hyph w i))) by lia.
  apply (fire_int tmw w _ ch t H p' (j - hp_nu (hyph w i)) (Pos.of_nat (r0 + hyL w * Pos.to_nat p))).
  replace (hp_nu (hyph w i) + (j - hp_nu (hyph w i))) with j by lia.
  apply cview_ones_xO.
Qed.

Lemma hy_fire_ovf_any : forall i k0 T ch t, i < hyL w ->
  srun_instr tmw true false ch (hyB0 w (hyph w i)) = Some t ->
  hp_no (hyph w i) <= k0 -> hy_ovf_fam_ok w i k0 T = true ->
  forall s, hy_good s -> FiresFrom tmw (hyA s) t.
Proof.
  intros i k0 T ch t Hi H Hk Hf [[p n] i1] Hg.
  set (p' := ones_on (k0 + T * Pos.to_nat p) xH).
  destruct (hy_ovf_phase i k0 T (Pos.to_nat p) Hf) as (Hph & _ & Hge).
  fold p' in Hph, Hge.
  assert (Hle : (p <= p')%positive) by (apply Pos2Nat.inj_le; exact Hge).
  destruct (hy_reach_at (p, n, i1) p' Hg Hle) as (TT & n' & Hn' & HT).
  rewrite Hph in Hn', HT.
  apply (fires_back tmw _ _ TT t HT).
  unfold hy_nmin in Hn'.
  replace n' with (hp_m (hyph w i) + (n' - hp_m (hyph w i))) by lia.
  apply (fire_ovf tmw w _ ch t H p' (k0 + T * Pos.to_nat p - hp_no (hyph w i))).
  replace (S (hp_no (hyph w i) + (k0 + T * Pos.to_nat p - hp_no (hyph w i))))
    with (S (k0 + T * Pos.to_nat p)) by lia.
  apply cview_ones_xH.
Qed.

Lemma hy_fire_any : forall t, ~ In t (hy_pins w) ->
  forall s, hy_good s -> FiresFrom tmw (hyA s) t.
Proof.
  intros t Hnin s Hg.
  pose proof hy_core_fires as H. unfold hy_fires_ok in H.
  rewrite forallb_forall in H.
  specialize (H t (all_Instr_complete t)).
  apply orb_prop in H as [H | H].
  { exfalso. apply Hnin, tr_inb_spec, H. }
  apply existsb_exists in H as ([i k a b ch] & _ & Hf).
  unfold hy_fire_ok in Hf; cbn [hf_ph hf_kind hf_a hf_b hf_ch] in Hf.
  apply andb_prop in Hf as [Hi Hf]. apply Nat.ltb_lt in Hi.
  destruct k as [|[|k]].
  - destruct (srun_instr tmw false false ch (hyA0 w (hyph w i))) as [t'|] eqn:E;
      [|discriminate].
    apply andb_prop in Hf as [Hf Hfam]. apply andb_prop in Hf as [Ht Hj].
    apply instr_eqb_spec in Ht. apply Nat.leb_le in Hj. subst t'.
    exact (hy_fire_int_any i a b ch t Hi E Hj Hfam s Hg).
  - destruct (srun_instr tmw true false ch (hyB0 w (hyph w i))) as [t'|] eqn:E;
      [|discriminate].
    apply andb_prop in Hf as [Hf Hfam]. apply andb_prop in Hf as [Ht Hj].
    apply instr_eqb_spec in Ht. apply Nat.leb_le in Hj. subst t'.
    exact (hy_fire_ovf_any i a b ch t Hi E Hj Hfam s Hg).
  - destruct (srun_instr tmw false true ch (hyS0 (hyph w i))) as [t'|] eqn:E;
      [|discriminate].
    apply instr_eqb_spec in Hf. subst t'.
    exact (hy_fire_sweep_any i ch t Hi E s Hg).
Qed.

(** ** The enumeration: the anchors along the run *)

Definition hy_s0 : hyS := (hy_p0 w, hy_n0 w, hy_i0 w).

Lemma hy_good_s0 : hy_good hy_s0.
Proof.
  pose proof Hcore as H. unfold hy_core_ok in H.
  apply andb_prop in H as [H Hn]. apply andb_prop in H as [_ Hi].
  apply Nat.leb_le in Hn. apply Nat.ltb_lt in Hi.
  cbn [hy_s0 hy_good]. split; [apply Pos.le_refl |]. split; [| exact Hn].
  unfold hy_phase_of. rewrite Nat.sub_diag, Nat.add_0_r. symmetry.
  apply Nat.mod_small. exact Hi.
Qed.

Definition hy_st (k : nat) : hyS := Nat.iter k hy_nxt hy_s0.

Lemma hy_st_good : forall k, hy_good (hy_st k).
Proof.
  induction k as [|k IH]; [exact hy_good_s0 |].
  cbn [hy_st Nat.iter nat_rect]. exact (proj1 (hy_step _ IH)).
Qed.

Definition hyCf (p : positive) : cconf :=
  hyA (hy_st (Pos.to_nat p - Pos.to_nat (hy_p0 w))).

Lemma hy_Hlap : forall p, (hy_p0 w <= p)%positive ->
  exists n c', csteps tmw n (hyCf p) = Some c' /\
               lift c' = lift (hyCf (Pos.succ p)) /\ 0 < n.
Proof.
  intros p Hp.
  destruct (hy_step _ (hy_st_good (Pos.to_nat p - Pos.to_nat (hy_p0 w))))
    as (_ & N & HN & H).
  destruct (stepn_csteps_at tmw N (hyCf p) _ H) as (c' & Hc & Hl).
  exists N, c'. split; [exact Hc |]. split; [| exact HN].
  rewrite Hl. unfold hyCf. f_equal. f_equal.
  apply Pos2Nat.inj_le in Hp. rewrite Pos2Nat.inj_succ.
  replace (S (Pos.to_nat p) - Pos.to_nat (hy_p0 w))
    with (S (Pos.to_nat p - Pos.to_nat (hy_p0 w))) by lia.
  reflexivity.
Qed.

Lemma hy_Hfire : forall t, ~ In t (hy_pins w) -> forall p, (hy_p0 w <= p)%positive ->
  exists k c, csteps tmw k (hyCf p) = Some c /\ cinstr c = t.
Proof.
  intros t Hnin p _. apply fire_csteps_of_lift.
  exact (hy_fire_any t Hnin _ (hy_st_good _)).
Qed.

End Sound.

Lemma hy_boot : forall tm w, hy_boot_ok w tm = true ->
  stepn tm (hy_t0 w) InitES = Some (lift (hyCf w (hy_p0 w))).
Proof.
  intros tm w Hb. unfold hy_boot_ok in Hb.
  destruct (csteps tm (hy_t0 w) c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E).
  f_equal. unfold hyCf. rewrite Nat.sub_diag. cbn [hy_st Nat.iter nat_rect hy_s0 hyA].
  exact (ceqb_lift _ _ Hb).
Qed.

Theorem hy_sound_nqh : forall tm w, hy_check_nqh tm w = true -> NeverQuasiHaltsTr tm.
Proof.
  intros tm w H. unfold hy_check_nqh in H.
  apply andb_prop in H as [Hb Hc].
  apply (glue_neverqhtr tm (hy_pins w) (hyCf w) (hy_p0 w)).
  - exists (hy_t0 w). exact (hy_boot _ w Hb).
  - exact (hy_Hlap _ w Hc).
  - exact (hy_Hfire _ w Hc).
Qed.

Theorem hy_sound_qh : forall tm w, hy_check_qh tm w = true ->
  NonHalt tm /\ QHBoundTr 32779478 tm /\ QuasiHaltsTr tm.
Proof.
  intros tm w H. unfold hy_check_qh in H.
  apply andb_prop in H as [H Hc].
  apply andb_prop in H as [H Hcap].
  apply andb_prop in H as [Hb Hwit].
  apply (lap_qh_stage tm (hy_pins w) (hyCf w) (hy_p0 w) (hy_t0 w) 32779478).
  - exact (hy_boot tm w Hb).
  - exact (hy_Hlap _ w Hc).
  - exact (hy_Hfire _ w Hc).
  - exact Hwit.
  - exact (hy_cap_le _ Hcap).
Qed.

(** the counter sits on the RIGHT: certify the mirror *)
Theorem hy_sound_nqh_mirror : forall tm w, hy_check_nqh (mirror_tm tm) w = true ->
  NeverQuasiHaltsTr tm.
Proof.
  intros tm w H. exact (neverqhtr_mirror tm (hy_sound_nqh _ w H)).
Qed.

Theorem hy_sound_qh_mirror : forall tm w, hy_check_qh (mirror_tm tm) w = true ->
  NonHalt tm /\ QHBoundTr 32779478 tm /\ QuasiHaltsTr tm.
Proof.
  intros tm w H. exact (qh_triple_unmirror 32779478 tm (hy_sound_qh _ w H)).
Qed.
