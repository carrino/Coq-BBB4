(** * Checkers.LadderCheckStepTr: the value-family ladder for a counter that
    adds a STEP [s > 1] per anchor visit (SCOPING_INSTR 7.4.LE3).

    LE2's "mod-3 clock" ([1RB1LD_1RC0RB_1RD0LD_1LA0LD]) is not a second
    counter.  Read at its anchor, the whole counter side is one base-4
    counter that adds 3 per visit: its low digit cycles through the residues
    while the high digits count.  [LadderFam] already carries the step
    ([fm_step]) and [fam_next] is stated on the VALUE, so the family is
    expressible as it stands; what [LadderCheck] lacks is a CLASS SPLIT for a
    step other than 1 ([pos1_class_succ] and [pos1_top_shape] are
    [(Binary, 1)] only).  This file is that split, for a positional base-[b]
    counter whose step divides [b - 1]:

    - with [s | b - 1], [b] is [1] mod [s], so a string's value mod [s] is its
      DIGIT SUM mod [s] ([val_mod]).  The value mod [s] never changes inside a
      width (each visit adds [s]), and a fill whose fill digit is [0] mod [s]
      lands on a residue that depends on the phase alone.  The board carries
      that residue, [cres ph], as data; it is an invariant ([InvS]), checked
      at the boot and at each fill law by [vm_compute];
    - the successor splits on the LOW DIGIT [u] alone.  If [u + s < b] the
      visit rewrites [u] to [u + s] and nothing else (one arm per [u], the
      rest of the counter opaque).  Otherwise it writes [u + s - b] and
      carries one into the rest: [u :: t^n ++ d :: rest -> (u+s-b) :: 0^n ++
      (d+1) :: rest] with [t = b - 1] (one arm per [u], [d] and arm index,
      the [LadderCheck] arm scheme on [n]);
    - the top of a width is [u :: t^n] with [u + s >= b]; the residue pins
      [u] to the phase's [utop ph] (two numbers in one window of [s]
      consecutive values with the same residue are equal), so the fill arm
      leaves from ONE string per phase and width, exactly as at step 1.

    Section 5 of [LadderCheck] (tops are cofinal, in a chosen phase) is
    restated over [InvS]; the measure [b^k - value] still falls at every
    interior visit.  The arms are [LadderNest.ReachL] programs and the fires
    are [LadderCheckNestTr.nfire]s, so a plain kernel chain and a chain of
    chains are both accepted, and both closers of [LadderCheckNestTr] are
    reproduced: [boardS_neverqhtr] (the boot on the machine wrapped at the
    pins) and [boardS_qhtr] (the boot on the original machine, past the
    pinned instructions' last fire).

    Nothing landed is modified.  Axiom footprint: as [LadderCheckNestTr] --
    [functional_extensionality_dep], via [CTape.lift]. *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape ClosureTr.
From BBB4.Counters Require Import WTape LapCertGlueLift.
From BBB4.Checkers Require Import WrapTr LapDecider LadderKernel LadderFam LadderCheck LadderCheckTr LadderNest LadderCheckNestTr TCyclerQHTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
From BBB4.Counters Require Import LapGlueTr.
From BBB4.CensusTr Require Import TNF_QHTr QHConveyorTr.
Import ListNotations.

(** ** 1. Residues: with [s | b - 1] the value mod [s] is the digit sum mod [s] *)

Lemma val_mod : forall b s ds, 0 < s -> (b - 1) mod s = 0 -> 1 <= b ->
  val_pos b ds mod s = dsum ds mod s.
Proof.
  intros b s ds Hs Hbs Hb1.
  apply Nat.mod_divides in Hbs as (q & Hq); [|lia].
  induction ds as [|d t IH]; [reflexivity|].
  cbn [val_pos]. rewrite dsum_cons.
  replace (d + b * val_pos b t) with ((d + val_pos b t) + (q * val_pos b t) * s)
    by nia.
  rewrite Nat.mod_add by lia.
  rewrite <- Nat.add_mod_idemp_r, IH, Nat.add_mod_idemp_r by lia.
  reflexivity.
Qed.

Lemma step_le : forall b s, 1 < b -> 0 < s -> (b - 1) mod s = 0 -> s <= b - 1.
Proof.
  intros b s Hb Hs Hbs.
  apply Nat.mod_divides in Hbs as (q & Hq); [|lia].
  destruct q; nia.
Qed.

(** Two numbers in one window of [s] consecutive values with the same residue
    are the same number. *)
Lemma window_eq : forall s a x y, 0 < s ->
  a <= x -> x < a + s -> a <= y -> y < a + s -> x mod s = y mod s -> x = y.
Proof.
  intros s a x y Hs Hx1 Hx2 Hy1 Hy2 Hm.
  pose proof (Nat.div_mod x s ltac:(lia)) as Ex.
  pose proof (Nat.div_mod y s ltac:(lia)) as Ey.
  assert (Hq : x / s = y / s).
  { destruct (Nat.lt_trichotomy (x / s) (y / s)) as [H|[H|H]]; [|exact H|].
    - assert (s * (x / s) + s <= s * (y / s)) by nia. lia.
    - assert (s * (y / s) + s <= s * (x / s)) by nia. lia. }
  lia.
Qed.

Lemma dsum_top : forall u t n s, t mod s = 0 -> 0 < s ->
  dsum (u :: repeat t n) mod s = u mod s.
Proof.
  intros u t n s Ht Hs.
  apply Nat.mod_divides in Ht as (q & Hq); [|lia].
  rewrite dsum_cons, dsum_repeat.
  replace (u + n * t) with (u + (n * q) * s) by nia.
  apply Nat.mod_add. lia.
Qed.

(** ** 2. The successor of each class, on the VALUE *)

(** The one shape every interior step has: a string of the same width, in
    range, whose value is [s] more.  Then it IS [fam_next], and the step is
    not the top. *)
Lemma next_of_val : forall F ds nd ph,
  1 < fm_b F -> fm_code F = Binary ->
  Forall (fun x => x < fm_b F) nd -> length nd = length ds ->
  fam_value F nd = fam_value F ds + fm_step F ->
  fam_next F ds ph = Some nd /\ fam_is_top F ds = false.
Proof.
  intros F ds nd ph Hb Hcode Hbnd Hlen Hval.
  assert (Hlt : fam_value F nd < Nat.pow (fm_b F) (length ds)).
  { rewrite <- Hlen. unfold fam_value. rewrite Hcode.
    apply val_pos_lt; [lia | exact Hbnd]. }
  assert (Htop : fam_is_top F ds = false).
  { unfold fam_is_top. rewrite (fam_lim_bin F _ Hcode).
    apply Nat.ltb_ge. lia. }
  split; [|exact Htop].
  unfold fam_next. rewrite Htop. unfold fam_of_value.
  rewrite (fam_lim_bin F _ Hcode), (fam_lo_bin F _ Hcode), Hcode.
  cbn [Nat.leb andb]. rewrite <- Hval.
  destruct (Nat.ltb_spec (fam_value F nd) (Nat.pow (fm_b F) (length ds)));
    [|lia].
  f_equal. rewrite <- Hlen. unfold fam_value. rewrite Hcode.
  apply pos_of_val_pos; [lia | exact Hbnd].
Qed.

Section Classes.

Variable F : Fam.
Hypothesis Hb    : 1 < fm_b F.
Hypothesis Hcode : fm_code F = Binary.
Hypothesis Hs0   : 0 < fm_step F.
Hypothesis Hbs   : (fm_b F - 1) mod fm_step F = 0.

(** The low digit takes the whole step. *)
Lemma stepA_succ : forall u R ph,
  u + fm_step F < fm_b F -> Forall (fun x => x < fm_b F) R ->
  fam_next F (u :: R) ph = Some ((u + fm_step F) :: R)
  /\ fam_is_top F (u :: R) = false.
Proof.
  intros u R ph Hu HR. apply next_of_val; try assumption.
  - constructor; [lia | exact HR].
  - reflexivity.
  - unfold fam_value. rewrite Hcode. cbn [val_pos]. lia.
Qed.

(** The low digit wraps and a carry ripples through the top run. *)
Lemma stepB_succ : forall u n d rest ph,
  fm_b F <= u + fm_step F -> u < fm_b F -> d < fm_b F - 1 ->
  Forall (fun x => x < fm_b F) rest ->
  fam_next F (u :: repeat (fm_b F - 1) n ++ d :: rest) ph
    = Some ((u + fm_step F - fm_b F) :: repeat 0 n ++ S d :: rest)
  /\ fam_is_top F (u :: repeat (fm_b F - 1) n ++ d :: rest) = false.
Proof.
  intros u n d rest ph Hu1 Hu2 Hd Hrest.
  pose proof (step_le (fm_b F) (fm_step F) Hb Hs0 Hbs) as Hsb.
  apply next_of_val; try assumption.
  - constructor; [lia|]. apply Forall_app. split.
    + apply Forall_forall. intros x Hx. apply repeat_spec in Hx. lia.
    + constructor; [lia | exact Hrest].
  - cbn [length]. rewrite !app_length, !repeat_length. reflexivity.
  - unfold fam_value. rewrite Hcode. cbn [val_pos].
    rewrite val_pos_class, val_pos_repeat0 by lia. cbn [val_pos].
    pose proof (pow_pos (fm_b F) n ltac:(lia)) as Hp.
    set (P := Nat.pow (fm_b F) n) in *.
    set (V := val_pos (fm_b F) rest).
    set (b := fm_b F) in *.
    assert (E1 : b * (P - 1 + P * (d + b * V)) = b * P * (d + b * V) + b * P - b)
      by (destruct P; [lia | rewrite Nat.sub_succ, Nat.sub_0_r; nia]).
    assert (E2 : b * (P * (S d + b * V)) = b * P * (d + b * V) + b * P) by nia.
    assert (b <= b * P) by nia.
    rewrite E1, E2. lia.
Qed.

(** ...and with nothing to carry into, it is the top of the width. *)
Lemma stepC_top : forall u n,
  fm_b F <= u + fm_step F ->
  fam_is_top F (u :: repeat (fm_b F - 1) n) = true.
Proof.
  intros u n Hu. unfold fam_is_top, fam_value.
  rewrite (fam_lim_bin F _ Hcode), Hcode. cbn [val_pos length].
  rewrite repeat_length, val_pos_repeat_max by lia.
  pose proof (pow_pos (fm_b F) n ltac:(lia)).
  apply Nat.ltb_lt. cbn [Nat.pow]. nia.
Qed.

(** Every nonempty string is in exactly one of the three. *)
Lemma step_split : forall ds, 0 < length ds ->
  (exists u R, ds = u :: R /\ u + fm_step F < fm_b F) \/
  (exists u n d rest, ds = u :: repeat (fm_b F - 1) n ++ d :: rest
                      /\ fm_b F <= u + fm_step F /\ d <> fm_b F - 1) \/
  (exists u n, ds = u :: repeat (fm_b F - 1) n /\ fm_b F <= u + fm_step F).
Proof.
  intros [|u R] Hl; [cbn in Hl; lia|].
  destruct (Nat.lt_ge_cases (u + fm_step F) (fm_b F)) as [H|H].
  - left. exists u, R. split; [reflexivity | exact H].
  - right. destruct (digs_decomp (fm_b F - 1) R) as [HR | (n & d & rest & HR & Hd)].
    + right. exists u, (length R). rewrite HR at 1. split; [reflexivity | exact H].
    + left. exists u, n, d, rest. rewrite HR. split; [reflexivity | split; assumption].
Qed.

(** The residue of a top string is its low digit's. *)
Lemma top_res : forall u n,
  fam_value F (u :: repeat (fm_b F - 1) n) mod fm_step F = u mod fm_step F.
Proof.
  intros u n. unfold fam_value. rewrite Hcode.
  rewrite val_mod by (lia || assumption).
  apply dsum_top; assumption.
Qed.

End Classes.

(** ** 3. The widths are cofinal: [LadderCheck] section 5 over the residue *)

Section IterS.

Variable F : Fam.
Variable NPH : nat.
Variable cres : nat -> nat.        (** the value's residue mod the step, per phase *)
Hypothesis Hb    : 1 < fm_b F.
Hypothesis Hcode : fm_code F = Binary.
Hypothesis Hs0   : 0 < fm_step F.
Hypothesis Hbs   : (fm_b F - 1) mod fm_step F = 0.
Hypothesis Hfpre : forall ph, ph < NPH ->
  Forall (fun d => d < fm_b F) (f_pre (fam_fill F ph)).
Hypothesis Hfsuf : forall ph, ph < NPH ->
  Forall (fun d => d < fm_b F) (f_suf (fam_fill F ph)).
Hypothesis Hfmid : forall ph, ph < NPH -> f_mid (fam_fill F ph) < fm_b F.
Hypothesis Hfs   : forall ph, ph < NPH ->
  length (f_pre (fam_fill F ph)) + length (f_suf (fam_fill F ph))
  <= 1 + f_s (fam_fill F ph).
Hypothesis Hfto  : forall ph, ph < NPH -> f_to (fam_fill F ph) < NPH.
(** the fill digit adds nothing to the residue, and each fill lands on the
    residue of the phase it lands in *)
Hypothesis Hfmids : forall ph, ph < NPH -> f_mid (fam_fill F ph) mod fm_step F = 0.
Hypothesis Hfres : forall ph, ph < NPH ->
  (dsum (f_pre (fam_fill F ph)) + dsum (f_suf (fam_fill F ph))) mod fm_step F
  = cres (f_to (fam_fill F ph)).

Definition InvS (s : CtrSt) : Prop :=
  Inv F NPH s /\ fam_value F (ct_ds s) mod fm_step F = cres (ct_ph s).

Lemma invS_value_lt : forall s,
  InvS s -> fam_value F (ct_ds s) < Nat.pow (fm_b F) (length (ct_ds s)).
Proof.
  intros [[ds p] ph] ((Hbnd & _ & _) & _); simpl.
  unfold fam_value. rewrite Hcode. apply val_pos_lt; [lia | exact Hbnd].
Qed.

Lemma fill_at_topS : forall ds ph, ph < NPH ->
  0 < length ds -> fam_is_top F ds = true ->
  fam_next F ds ph = Some (filled F ph (length ds)).
Proof.
  intros ds ph Hph Hk Htop. unfold fam_next, filled. rewrite Htop, Hcode.
  unfold fill_apply. pose proof (Hfs ph Hph).
  destruct (Nat.leb_spec (length (f_pre (fam_fill F ph))
                          + length (f_suf (fam_fill F ph)))
              (length ds + f_s (fam_fill F ph))); [reflexivity | lia].
Qed.

Lemma filledS_length : forall ph k, ph < NPH -> 0 < k ->
  length (filled F ph k) = k + f_s (fam_fill F ph).
Proof.
  intros ph k Hph Hk. unfold filled. pose proof (Hfs ph Hph).
  rewrite !app_length, repeat_length. lia.
Qed.

Lemma filledS_bnd : forall ph k, ph < NPH ->
  Forall (fun d => d < fm_b F) (filled F ph k).
Proof.
  intros ph k Hph. unfold filled. apply Forall_app.
  split; [apply (Hfpre ph Hph)|].
  apply Forall_app. split; [|apply (Hfsuf ph Hph)].
  apply Forall_forall. intros x Hx. apply repeat_spec in Hx.
  pose proof (Hfmid ph Hph). lia.
Qed.

Lemma filledS_res : forall ph k, ph < NPH ->
  fam_value F (filled F ph k) mod fm_step F = cres (f_to (fam_fill F ph)).
Proof.
  intros ph k Hph. unfold fam_value. rewrite Hcode.
  rewrite val_mod by (lia || assumption).
  unfold filled. rewrite !dsum_app, dsum_repeat.
  pose proof (Hfmids ph Hph) as Hm.
  apply Nat.mod_divides in Hm as (q & Hq); [|lia].
  rewrite <- (Hfres ph Hph). rewrite Hq.
  set (n := _ - _).
  replace (dsum (f_pre (fam_fill F ph)) + (n * (fm_step F * q)
            + dsum (f_suf (fam_fill F ph))))
    with ((dsum (f_pre (fam_fill F ph)) + dsum (f_suf (fam_fill F ph)))
          + (n * q) * fm_step F) by nia.
  apply Nat.mod_add. lia.
Qed.

Lemma fam_succ_totalS : forall s,
  InvS s -> exists s', fam_succ F s = Some s' /\ InvS s'.
Proof.
  intros [[ds p] ph] Hi. destruct Hi as ((Hbnd & Hlen & Hph) & Hres).
  simpl in Hres.
  destruct (fam_is_top F ds) eqn:Htop.
  - eexists. unfold fam_succ.
    rewrite (fill_at_topS ds ph Hph Hlen Htop), Htop.
    split; [reflexivity|]. simpl. repeat split.
    + apply filledS_bnd; exact Hph.
    + rewrite filledS_length by assumption. pose proof (Hfs ph Hph). lia.
    + apply Hfto; exact Hph.
    + apply filledS_res; exact Hph.
  - assert (Hlt : fam_value F ds + fm_step F < Nat.pow (fm_b F) (length ds)).
    { unfold fam_is_top in Htop. rewrite (fam_lim_bin F _ Hcode) in Htop.
      apply Nat.ltb_ge in Htop.
      pose proof (pow_pos (fm_b F) (length ds) ltac:(lia)). lia. }
    destruct (fam_next F ds ph) as [nd|] eqn:Hnd.
    2:{ exfalso. unfold fam_next in Hnd. rewrite Htop in Hnd.
        unfold fam_of_value in Hnd.
        rewrite (fam_lim_bin F _ Hcode), (fam_lo_bin F _ Hcode) in Hnd.
        cbn [Nat.leb andb] in Hnd.
        destruct (Nat.ltb_spec (fam_value F ds + fm_step F)
                    (Nat.pow (fm_b F) (length ds))); [discriminate | lia]. }
    exists (nd, p, ph). unfold fam_succ. rewrite Hnd, Htop.
    split; [reflexivity|].
    destruct (fam_next_interior F ds ph nd Hb Htop Hnd) as (Hval & Hlen').
    assert (Hbnd' : Forall (fun d => d < fm_b F) nd).
    { unfold fam_next in Hnd. rewrite Htop in Hnd. unfold fam_of_value in Hnd.
      destruct ((fam_lo F (length ds) <=? fam_value F ds + fm_step F)
                && (fam_value F ds + fm_step F <? fam_lim F (length ds)));
        [|discriminate].
      rewrite Hcode in Hnd. injection Hnd as <-. apply pos_of_lt; lia. }
    unfold InvS, Inv; cbn [ct_ds ct_ph]. repeat split.
    + exact Hbnd'.
    + rewrite Hlen'. exact Hlen.
    + exact Hph.
    + rewrite Hval, <- Hres.
      replace (fam_value F ds + fm_step F) with (fam_value F ds + 1 * fm_step F)
        by lia.
      apply Nat.mod_add. lia.
Qed.

Lemma fam_iter_totalS : forall N s,
  InvS s -> exists s', fam_iter F s N = Some s' /\ InvS s'.
Proof.
  induction N as [|N IH]; intros s Hi; [exists s; split; [reflexivity|exact Hi]|].
  destruct (fam_succ_totalS s Hi) as (s1 & H1 & Hi1).
  destruct (IH s1 Hi1) as (s' & H' & Hi').
  exists s'. split; [|exact Hi']. simpl. rewrite H1. exact H'.
Qed.

Lemma top_reachedS_aux : forall m s,
  InvS s ->
  Nat.pow (fm_b F) (length (ct_ds s)) - fam_value F (ct_ds s) <= m ->
  exists n s', fam_iter F s n = Some s' /\ fam_is_top F (ct_ds s') = true
               /\ InvS s' /\ ct_ph s' = ct_ph s.
Proof.
  induction m as [|m IH]; intros s Hi Hm.
  - exfalso. pose proof (invS_value_lt s Hi). lia.
  - destruct (fam_is_top F (ct_ds s)) eqn:Htop.
    + exists 0, s.
      split; [reflexivity | split; [exact Htop | split; [exact Hi|reflexivity]]].
    + destruct s as [[ds p] ph]. simpl in Htop.
      destruct (fam_succ_totalS _ Hi) as (s1 & H1 & Hi1).
      unfold fam_succ in H1. rewrite Htop in H1.
      destruct (fam_next F ds ph) as [nd|] eqn:Hnd; [|discriminate].
      injection H1 as <-.
      destruct (fam_next_interior F ds ph nd Hb Htop Hnd) as (Hval & Hlen').
      destruct (IH (nd, p, ph) Hi1) as (n & s' & Hit & Htop' & Hi' & Hph').
      { simpl. simpl in Hm. rewrite Hval, Hlen'. lia. }
      exists (S n), s'.
      split; [|split; [exact Htop' | split; [exact Hi' | exact Hph']]].
      simpl. unfold fam_succ. rewrite Htop, Hnd. exact Hit.
Qed.

Lemma top_reachedS : forall s,
  InvS s ->
  exists n s', fam_iter F s n = Some s' /\ fam_is_top F (ct_ds s') = true
               /\ InvS s' /\ ct_ph s' = ct_ph s.
Proof.
  intros s Hi.
  apply (top_reachedS_aux
           (Nat.pow (fm_b F) (length (ct_ds s)) - fam_value F (ct_ds s)) s Hi).
  lia.
Qed.

Lemma top_afterS : forall k s, InvS s ->
  exists n s', fam_iter F s n = Some s' /\ fam_is_top F (ct_ds s') = true
               /\ InvS s' /\ ct_ph s' = phto F k (ct_ph s).
Proof.
  induction k as [|k IH]; intros s Hi.
  - destruct (top_reachedS s Hi) as (n & s' & Hit & Htop & Hi' & Hph).
    exists n, s'.
    split; [exact Hit | split; [exact Htop | split; [exact Hi' | exact Hph]]].
  - destruct (top_reachedS s Hi) as (n & s1 & Hit & Htop & Hi1 & Hph).
    destruct (fam_succ_totalS s1 Hi1) as (s2 & Hs2 & Hi2).
    assert (Hph2 : ct_ph s2 = f_to (fam_fill F (ct_ph s1))).
    { destruct s1 as [[ds1 p1] ph1]. simpl in Htop |- *.
      unfold fam_succ in Hs2. rewrite Htop in Hs2.
      destruct (fam_next F ds1 ph1) as [nd|]; [|discriminate].
      injection Hs2 as <-. reflexivity. }
    destruct (IH s2 Hi2) as (m & s' & Hit2 & Htop' & Hi' & Hph').
    exists (n + (1 + m)), s'.
    split; [| split; [exact Htop' | split; [exact Hi' |]]].
    + rewrite fam_iter_add, Hit. simpl. rewrite Hs2. exact Hit2.
    + rewrite Hph', Hph2, Hph. reflexivity.
Qed.

Theorem tops_cofinal_atS : forall pv s N,
  (forall ph, ph < NPH -> exists k, phto F k ph = pv) ->
  InvS s ->
  exists n s', N <= n /\ fam_iter F s n = Some s'
               /\ fam_is_top F (ct_ds s') = true /\ InvS s'
               /\ ct_ph s' = pv.
Proof.
  intros pv s N Hcyc Hi.
  destruct (fam_iter_totalS N s Hi) as (sN & HN & HiN).
  assert (HphN : ct_ph sN < NPH)
    by (destruct sN as [[? ?] ?]; destruct HiN as ((_ & _ & H) & _); exact H).
  destruct (Hcyc (ct_ph sN) HphN) as (k & Hk).
  destruct (top_afterS k sN HiN) as (m & s' & Hm & Htop & Hi' & Hph).
  exists (N + m), s'.
  split; [lia | split; [| split; [exact Htop | split; [exact Hi' |]]]].
  - rewrite fam_iter_add, HN. exact Hm.
  - rewrite Hph. exact Hk.
Qed.

End IterS.

(** ** 4. The board *)

Section BoardSTr.

Variable tm0   : TM.
Variable pins  : list Instr.
Local Notation tm := (tm_wrap_trs tm0 pins).

Variable F     : Fam.
Variable NPH   : nat.
Variable cres  : nat -> nat.        (** the residue of each phase *)
Variable utop  : nat -> nat.        (** the low digit of each phase's tops *)
Variable AA    : nat -> LRule.      (** no carry: per low digit *)
Variable AB    : nat -> nat -> nat -> LRule.  (** a carry: low digit, the
                                                  digit it lands on, index *)
Variable N0i sti : nat.
Variable Afill : nat -> nat -> LRule.  (** per arm index (on the top run
                                           [t^(k-1)]) and phase *)
Variable N0f stf : nat.
Variable fm1 fm2 : nat -> nat -> nat.
Variable pv    : nat.
Variable rsv   : list LRule.
Variable vsegs : nat -> Instr -> list nseg.
Variable visI  : nat -> Instr -> list lstep.
Variable ds0   : list nat.
Variable ph0   : nat.

Hypothesis Hb    : 1 < fm_b F.
Hypothesis Hcode : fm_code F = Binary.
Hypothesis Hs0   : 0 < fm_step F.
Hypothesis Hbs   : (fm_b F - 1) mod fm_step F = 0.
Hypothesis Hfpre : forall ph, ph < NPH ->
  Forall (fun d => d < fm_b F) (f_pre (fam_fill F ph)).
Hypothesis Hfsuf : forall ph, ph < NPH ->
  Forall (fun d => d < fm_b F) (f_suf (fam_fill F ph)).
Hypothesis Hfmid : forall ph, ph < NPH -> f_mid (fam_fill F ph) < fm_b F.
Hypothesis Hfs   : forall ph, ph < NPH ->
  length (f_pre (fam_fill F ph)) + length (f_suf (fam_fill F ph))
  <= 1 + f_s (fam_fill F ph).
Hypothesis Hfto  : forall ph, ph < NPH -> f_to (fam_fill F ph) < NPH.
Hypothesis Hfmids : forall ph, ph < NPH -> f_mid (fam_fill F ph) mod fm_step F = 0.
Hypothesis Hfres : forall ph, ph < NPH ->
  (dsum (f_pre (fam_fill F ph)) + dsum (f_suf (fam_fill F ph))) mod fm_step F
  = cres (f_to (fam_fill F ph)).
Hypothesis Hutop : forall ph, ph < NPH ->
  fm_b F <= utop ph + fm_step F /\ utop ph < fm_b F
  /\ utop ph mod fm_step F = cres ph.
Hypothesis Hpv   : pv < NPH.
Hypothesis Hcyc  : forall ph, ph < NPH -> exists k, phto F k ph = pv.
Hypothesis Hfm12 : forall r ph, r < N0f + stf -> ph < NPH ->
  fm1 r ph + fm2 r ph
  + (length (f_pre (fam_fill F ph)) + length (f_suf (fam_fill F ph)))
  = S r + f_s (fam_fill F ph).

Hypothesis Hbnd0 : Forall (fun d => d < fm_b F) ds0.
Hypothesis Hlen0 : 0 < length ds0.
Hypothesis Hph0  : ph0 < NPH.
Hypothesis Hres0 : fam_value F ds0 mod fm_step F = cres ph0.

Hypothesis HAAS : forall u, u + fm_step F < fm_b F ->
  ReachL tm (negb (fm_left F)) (fm_left F) (lr_lhs (AA u)) (lr_rhs (AA u)).
Hypothesis HAAL : forall u, u + fm_step F < fm_b F ->
  lr_lhs (AA u) = cls_conf F (cls_side F [u] 0 0 0 []).
Hypothesis HAAR : forall u, u + fm_step F < fm_b F ->
  lr_rhs (AA u) = cls_conf F (cls_side F [u + fm_step F] 0 0 0 []).

Hypothesis Hsti : 0 < sti.
Hypothesis HABS : forall u d r,
  fm_b F <= u + fm_step F -> u < fm_b F -> d < fm_b F - 1 -> r < N0i + sti ->
  ReachL tm (negb (fm_left F)) (fm_left F) (lr_lhs (AB u d r)) (lr_rhs (AB u d r)).
Hypothesis HABL : forall u d r,
  fm_b F <= u + fm_step F -> u < fm_b F -> d < fm_b F - 1 -> r < N0i + sti ->
  lr_lhs (AB u d r)
    = cls_conf F (cls_side F [u] (fm_b F - 1) r (astride N0i sti r) [d]).
Hypothesis HABR : forall u d r,
  fm_b F <= u + fm_step F -> u < fm_b F -> d < fm_b F - 1 -> r < N0i + sti ->
  lr_rhs (AB u d r)
    = cls_conf F (cls_side F [u + fm_step F - fm_b F] 0 r (astride N0i sti r)
                    [S d]).

Hypothesis Hstf : 0 < stf.
Hypothesis HAfS : forall r ph, r < N0f + stf -> ph < NPH ->
  ReachL tm true true (lr_lhs (Afill r ph)) (lr_rhs (Afill r ph)).
Hypothesis HAfL : forall r ph, r < N0f + stf -> ph < NPH ->
  lr_lhs (Afill r ph)
    = cls_conf F (run_side F (fm_b F - 1) r (astride N0f stf r) 0 ph
                    [utop ph] []).
Hypothesis HAfR : forall r ph, r < N0f + stf -> ph < NPH ->
  lr_rhs (Afill r ph)
    = cls_conf F (run_side F (f_mid (fam_fill F ph)) (fm1 r ph)
                    (astride N0f stf r) (fm2 r ph) (f_to (fam_fill F ph))
                    (f_pre (fam_fill F ph)) (f_suf (fam_fill F ph))).

Hypothesis Hrsv : Forall (RuleSound tm false false) rsv.
Hypothesis Hfire : forall r t, ~ In t pins -> r < N0f + stf ->
  nfire tm true true rsv (vsegs r t) (visI r t) (lr_lhs (Afill r pv)) = Some t.

Local Notation Cf := (CfB F ds0 ph0).
Local Notation INV := (InvS F NPH cres).

Lemma invS0 : INV (ds0, 0, ph0).
Proof. split; [simpl; repeat split; assumption | exact Hres0]. Qed.

(** A top of a member, in phase [ph], is the phase's one top string. *)
Lemma top_shapeS : forall ds p ph, INV (ds, p, ph) ->
  fam_is_top F ds = true ->
  ds = utop ph :: repeat (fm_b F - 1) (length ds - 1).
Proof.
  intros ds p ph ((Hbnd & Hlen & Hph) & Hres) Htop. simpl in Hres.
  destruct (step_split F Hb Hs0 Hbs ds Hlen)
    as [(u & R & -> & Hu) | [(u & n & d & rest & -> & Hu & Hd)
                            | (u & n & -> & Hu)]].
  - inversion Hbnd; subst.
    rewrite (proj2 (stepA_succ F Hb Hcode Hs0 Hbs u R ph Hu ltac:(assumption))) in Htop.
    discriminate.
  - inversion Hbnd as [|? ? Hub Hrb]; subst.
    apply Forall_app in Hrb as [_ Hrest'].
    inversion Hrest' as [|? ? Hdb Hrest]; subst.
    rewrite (proj2 (stepB_succ F Hb Hcode Hs0 Hbs u n d rest ph Hu Hub
                      ltac:(lia) Hrest)) in Htop.
    discriminate.
  - inversion Hbnd as [|? ? Hub _]; subst.
    destruct (Hutop ph Hph) as (Ht1 & Ht2 & Ht3).
    pose proof (step_le (fm_b F) (fm_step F) Hb Hs0 Hbs) as Hsb.
    assert (Hu' : u = utop ph).
    { apply (window_eq (fm_step F) (fm_b F - fm_step F)); try lia.
      rewrite Ht3, <- Hres, (top_res F Hb Hcode Hs0 Hbs u n). reflexivity. }
    subst u. cbn [length]. rewrite repeat_length.
    replace (S n - 1) with n by lia. reflexivity.
Qed.

Lemma cells_topS : forall ph r st m,
  fam_cells F (utop ph :: repeat (fm_b F - 1) (r + st * m)) ph
    = sden [] m (run_side F (fm_b F - 1) r st 0 ph [utop ph] []).
Proof.
  intros ph r st m.
  rewrite <- (fam_cells_run F (fm_b F - 1) r st m 0 ph [utop ph] []).
  f_equal. rewrite Nat.add_0_r, app_nil_r. reflexivity.
Qed.

Lemma cells_filledS : forall k a st m c ph,
  a + st * m + c
    = k + f_s (fam_fill F ph)
      - (length (f_pre (fam_fill F ph)) + length (f_suf (fam_fill F ph))) ->
  fam_cells F (filled F ph k) (f_to (fam_fill F ph))
    = sden [] m
        (run_side F (f_mid (fam_fill F ph)) a st c (f_to (fam_fill F ph))
           (f_pre (fam_fill F ph)) (f_suf (fam_fill F ph))).
Proof.
  intros k a st m c ph Hk.
  transitivity (fam_cells F
    (f_pre (fam_fill F ph)
     ++ repeat (f_mid (fam_fill F ph)) (a + st * m + c)
     ++ f_suf (fam_fill F ph)) (f_to (fam_fill F ph))).
  - f_equal. unfold filled. rewrite Hk. reflexivity.
  - apply fam_cells_run.
Qed.

(** The lap, by the three-way split on the low digit. *)
Lemma board_armS : forall s, INV s ->
  exists s' A el er X n,
    fam_succ F s = Some s'
    /\ ReachL tm el er (lr_lhs A) (lr_rhs A)
    /\ (el = true -> tailL F X = []) /\ (er = true -> tailR F X = [])
    /\ fam_cfg F s  = cden (tailL F X) (tailR F X) n (lr_lhs A)
    /\ fam_cfg F s' = cden (tailL F X) (tailR F X) n (lr_rhs A).
Proof.
  intros [[ds p] ph] Hi. pose proof Hi as Hi0.
  destruct Hi as ((Hbnd & Hlen & Hph) & Hres).
  destruct (step_split F Hb Hs0 Hbs ds Hlen)
    as [(u & R & -> & Hu) | [(u & n & d & rest & -> & Hu & Hd)
                            | (u & n & -> & Hu)]].
  - (* no carry *)
    inversion Hbnd as [|? ? Hub HR]; subst.
    destruct (stepA_succ F Hb Hcode Hs0 Hbs u R ph Hu HR) as (Hnx & Hnt).
    exists ((u + fm_step F) :: R, p, ph), (AA u).
    exists (negb (fm_left F)), (fm_left F), (cls_tail F R ph), 0.
    split; [|split; [|split; [|split; [|split]]]].
    + unfold fam_succ. rewrite Hnx, Hnt. reflexivity.
    + exact (HAAS u Hu).
    + intros He. unfold tailL. destruct (fm_left F); [discriminate|reflexivity].
    + intros He. unfold tailR. rewrite He. reflexivity.
    + rewrite (HAAL u Hu). symmetry. apply cden_cls_conf.
      exact (fam_cells_class F [u] 0 0 0 0 [] R ph).
    + rewrite (HAAR u Hu). symmetry. apply cden_cls_conf.
      exact (fam_cells_class F [u + fm_step F] 0 0 0 0 [] R ph).
  - (* a carry into the first digit below the top *)
    inversion Hbnd as [|? ? Hub Hrb]; subst.
    apply Forall_app in Hrb as [_ Hrest'].
    inversion Hrest' as [|? ? Hdb Hrest]; subst.
    assert (Hdlt : d < fm_b F - 1) by lia.
    destruct (stepB_succ F Hb Hcode Hs0 Hbs u n d rest ph Hu Hub Hdlt Hrest)
      as (Hnx & Hnt).
    remember (aoff N0i sti n) as r eqn:Er.
    assert (Hrlt : r < N0i + sti) by (subst r; apply arm_index_lt; assumption).
    assert (Hn : r + astride N0i sti r * acnt N0i sti n = n)
      by (subst r; apply arm_index; assumption).
    exists ((u + fm_step F - fm_b F) :: repeat 0 n ++ S d :: rest, p, ph), (AB u d r).
    exists (negb (fm_left F)), (fm_left F), (cls_tail F rest ph).
    exists (acnt N0i sti n).
    split; [|split; [|split; [|split; [|split]]]].
    + unfold fam_succ. rewrite Hnx, Hnt. reflexivity.
    + exact (HABS u d r Hu Hub Hdlt Hrlt).
    + intros He. unfold tailL. destruct (fm_left F); [discriminate|reflexivity].
    + intros He. unfold tailR. rewrite He. reflexivity.
    + rewrite (HABL u d r Hu Hub Hdlt Hrlt). symmetry. apply cden_cls_conf.
      rewrite <- Hn at 1.
      exact (fam_cells_class F [u] (fm_b F - 1) r (astride N0i sti r)
               (acnt N0i sti n) [d] rest ph).
    + rewrite (HABR u d r Hu Hub Hdlt Hrlt). symmetry. apply cden_cls_conf.
      rewrite <- Hn at 1.
      exact (fam_cells_class F [u + fm_step F - fm_b F] 0 r (astride N0i sti r)
               (acnt N0i sti n) [S d] rest ph).
  - (* the top: the fill arm of this phase *)
    assert (Hist : fam_is_top F (u :: repeat (fm_b F - 1) n) = true)
      by exact (stepC_top F Hb Hcode Hs0 Hbs u n Hu).
    pose proof (top_shapeS _ p ph Hi0 Hist) as Hsh.
    cbn [length] in Hsh. rewrite repeat_length in Hsh.
    replace (S n - 1) with n in Hsh by lia.
    injection Hsh as Hu'. subst u.
    remember (aoff N0f stf n) as r eqn:Er.
    assert (Hrlt : r < N0f + stf) by (subst r; apply arm_index_lt; assumption).
    assert (Hk : r + astride N0f stf r * acnt N0f stf n = n)
      by (subst r; apply arm_index; assumption).
    exists (filled F ph (S n), p, f_to (fam_fill F ph)), (Afill r ph).
    exists true, true, [], (acnt N0f stf n).
    split; [|split; [|split; [|split; [|split]]]].
    + unfold fam_succ.
      rewrite (fill_at_topS F NPH Hb Hcode Hs0 Hbs Hfs _ ph Hph Hlen Hist), Hist.
      cbn [length]. rewrite repeat_length. reflexivity.
    + exact (HAfS r ph Hrlt Hph).
    + intros _; apply tailL_nil.
    + intros _; apply tailR_nil.
    + rewrite (HAfL r ph Hrlt Hph). symmetry.
      apply cden_cls_conf. rewrite <- Hk at 1. apply cells_topS.
    + rewrite (HAfR r ph Hrlt Hph). symmetry.
      apply cden_cls_conf. apply cells_filledS.
      pose proof (Hfm12 r ph Hrlt Hph). lia.
Qed.

Lemma lapS : forall n, exists m c,
  0 < m /\ csteps tm m (Cf n) = Some c /\ lift c = lift (Cf (S n)).
Proof.
  intros n.
  destruct (fam_iter_totalS F NPH cres Hb Hcode Hs0 Hbs Hfpre Hfsuf Hfmid Hfs Hfto
              Hfmids Hfres n (ds0, 0, ph0) invS0) as (s & Hit & Hi).
  destruct (board_armS s Hi)
    as (s' & A & el & er & X & k & Hsucc & HA & HL & HR & Hl & Hr).
  destruct (HA _ _ k HL HR) as (m & c & Hm & Hc & Hlc).
  exists m, c. split; [exact Hm|]. split.
  - unfold CfB. rewrite Hit, Hl. exact Hc.
  - rewrite Hlc, <- Hr. unfold CfB.
    replace (S n) with (n + 1) by lia.
    rewrite fam_iter_add, Hit. simpl. rewrite Hsucc. reflexivity.
Qed.

Lemma fireS : forall t N, ~ In t pins ->
  exists n k c, N <= n /\ csteps tm k (Cf n) = Some c /\ cinstr c = t.
Proof.
  intros t N Hnp.
  destruct (tops_cofinal_atS F NPH cres Hb Hcode Hs0 Hbs Hfpre Hfsuf Hfmid Hfs
              Hfto Hfmids Hfres pv (ds0, 0, ph0) N Hcyc invS0)
    as (n & s' & HN & Hit & Htop & Hi' & Hph).
  exists n.
  destruct s' as [[ds' p'] ph']. simpl in Htop. simpl in Hph. subst ph'.
  pose proof (top_shapeS ds' p' pv Hi' Htop) as Hsh.
  set (n' := length ds' - 1) in Hsh.
  remember (aoff N0f stf n') as r eqn:Er.
  assert (Hrlt : r < N0f + stf) by (subst r; apply arm_index_lt; assumption).
  assert (Hk : r + astride N0f stf r * acnt N0f stf n' = n')
    by (subst r; apply arm_index; assumption).
  assert (Hden : Cf n
                 = cden [] [] (acnt N0f stf n') (lr_lhs (Afill r pv))).
  { unfold CfB. rewrite Hit, (HAfL r pv Hrlt Hpv).
    rewrite <- (cden_cls_conf F
                  (run_side F (fm_b F - 1) r (astride N0f stf r) 0 pv [utop pv] [])
                  [] (acnt N0f stf n') ds' p' pv).
    - unfold tailL, tailR; destruct (fm_left F); reflexivity.
    - rewrite Hsh at 1. rewrite <- Hk at 1. apply cells_topS. }
  destruct (nfire_sound tm true true rsv (vsegs r t) (visI r t)
              (lr_lhs (Afill r pv)) t Hrsv (Hfire r t Hnp Hrlt)
              [] [] (acnt N0f stf n')
              (fun _ => eq_refl) (fun _ => eq_refl)) as (k & c & Hc & Ht).
  exists k, c. rewrite Hden. split; [exact HN | split; [exact Hc | exact Ht]].
Qed.

(** *** Never-quasihalting rows: the boot on the wrapped machine, up to [lift] *)
Theorem boardS_neverqhtr : forall t0,
  stepn tm t0 InitES = Some (lift (fam_cfg F (ds0, 0, ph0))) ->
  NeverQuasiHaltsTr tm0.
Proof.
  intros t0 Hboot.
  apply (glue_neverqhtrN tm0 pins Cf).
  - exists t0. unfold CfB; simpl. exact Hboot.
  - intros n. destruct (lapS n) as (m & c & Hm & Hrun & Hl).
    exists m, c. split; [exact Hrun | split; [exact Hl | exact Hm]].
  - intros t Hnp N. exact (fireS t N Hnp).
Qed.

(** *** Quasihalting rows: the boot on the ORIGINAL machine, up to [lift] *)

Lemma reachS : forall d n,
  exists T, stepn tm T (lift (Cf n)) = Some (lift (Cf (n + d))).
Proof.
  induction d; intros n.
  - exists 0. rewrite Nat.add_0_r. reflexivity.
  - destruct (IHd n) as (T & HT).
    destruct (lapS (n + d)) as (m & c & _ & Hm & Hl).
    exists (T + m). rewrite stepn_add, HT.
    replace (n + S d) with (S (n + d)) by lia.
    rewrite <- Hl. apply csteps_lift. exact Hm.
Qed.

Lemma fire_everyS : forall t, ~ In t pins -> forall n,
  exists k c, csteps tm k (Cf n) = Some c /\ cinstr c = t.
Proof.
  intros t Hnp n.
  destruct (fireS t n Hnp) as (m & k & c & Hm & Hk & Hc).
  destruct (reachS (m - n) n) as (T & HT).
  replace (n + (m - n)) with m in HT by lia.
  assert (Hs : stepn tm (T + k) (lift (Cf n)) = Some (lift c)).
  { rewrite stepn_add, HT. apply csteps_lift. exact Hk. }
  destruct (stepn_csteps_at tm (T + k) (Cf n) (lift c) Hs) as (c' & Hc' & Hl').
  exists (T + k), c'. split; [exact Hc'|].
  rewrite <- cinstr_lift, Hl', cinstr_lift. exact Hc.
Qed.

Theorem boardS_qhtr : forall t0 B,
  stepn tm0 t0 InitES = Some (lift (fam_cfg F (ds0, 0, ph0))) ->
  existsb (fun tg => cfires tm0 CTape.c0 t0 tg) pins = true ->
  (t0 <=? B) = true ->
  NonHalt tm0 /\ QHBoundTr B tm0 /\ QuasiHaltsTr tm0.
Proof.
  intros t0 B Hboot Hwit Hle.
  apply (lap_qh_stage tm0 pins (fun p => Cf (Nat.pred (Pos.to_nat p)))
           1%positive t0 B).
  - simpl. unfold CfB; simpl. exact Hboot.
  - intros p _.
    destruct (lapS (Nat.pred (Pos.to_nat p))) as (m & c & Hm & Hrun & Hl).
    exists m, c. split; [exact Hrun | split; [|exact Hm]].
    rewrite Hl, Pos2Nat.inj_succ.
    replace (S (Nat.pred (Pos.to_nat p))) with (Pos.to_nat p)
      by (pose proof (Pos2Nat.is_pos p); lia).
    reflexivity.
  - intros t Hnp p _. exact (fire_everyS t Hnp (Nat.pred (Pos.to_nat p))).
  - exact Hwit.
  - exact Hle.
Qed.

End BoardSTr.
