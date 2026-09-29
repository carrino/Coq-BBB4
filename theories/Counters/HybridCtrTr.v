(** * HybridCtrTr: bouncer + counter hybrids whose counter is any
    positional-style numeration: base [b], one word per digit, and a TOP
    that steps through a table of words before the counter widens.

    [HybridGlueTr] (SCOPING_INSTR.md 7.4.HY) glues a binary counter
    [E p] ([E xH = C], [E (xO r) = A ++ E r], [E (xI r) = B ++ E r]) to a
    growing bouncer block.  Its residue (7.4.HY, 7.4.HY2) is mostly the
    same lap with a counter [E] cannot write:

    - base 3 and base 4 counters (a 3- or 4-cell word per digit; the
      base-4 ones are CE2's two-bits-per-digit counters);
    - a top that is not one digit word: the digit under the MSB written
      differently until the next overflow, a long terminator, a counter
      with a terminator and no top digit at all, or a top that steps
      through a few words before an overflow;
    - the lift-tolerant fills of CE2 (the overflow stops a blank short),
      which the chains here state up to trailing blanks.

    The counter is a pair [(low, tv)]: [low] its low digits, LSB first,
    each [< b], and [tv] the top value, [lo <= tv < hi].  Its word is

      [hcE (low, tv) = concat (map D low) ++ T tv]

    with [D] ([b] words) and [T] ([hi - lo] words) certificate data, and
    the increment has three shapes, each ONE generic carry chain indexed by
    the carry length [j]:

    - interior, per digit [d < b - 1]:
        [D(b-1)^j ++ D d ++ X  ->  D 0^j ++ D (d+1) ++ X]   ([X] opaque);
    - top step, per [tv] with [tv + 1 < hi]:
        [D(b-1)^j ++ T tv  ->  D 0^j ++ T (tv + 1)]         (far end known);
    - overflow, [tv = hi - 1]:
        [D(b-1)^j ++ T tv  ->  D 0^(j+1) ++ T lo]           (far end known).

    [hi = b * lo] is a positional counter ([lo = b^(t-1)]: a top window of
    [t] digits); [lo = 0, hi = 1] a counter with a terminator and no top
    digit; other ranges are counters whose top steps through [hi - lo]
    words before it widens.  With [b = 2], [lo = 1], [hi = 2], [D = [A; B]]
    and [T = [C]] this is exactly [HybridGlueTr]'s interior and overflow.

    Everything else -- the two-index anchor [hcC c n], the mid, the sweep
    half over the block with the counter opaque, the phase list for a
    block whose unit rotates at the junction, and the fire families -- is
    [HybridGlueTr]'s, restated over [(low, tv)].  Fire families are named
    by RANK (the number of increments from [([], lo)]): an interior fire
    at digit [d] after [j] carries is reached at the ranks
    [(hi - lo) G (j+1) + (b^j - 1) + b^j d + b^(j+1) (H0 + L s)], a
    top/overflow fire at [ytop e (j0 + T s) - 1]; the checker computes
    their phase.

    Axiom footprint: [functional_extensionality_dep] (via [CTape.lift]). *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape ClosureTr Mirror.
From BBB4.Checkers Require Import WrapTr LapDecider TCyclerQHTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
From BBB4.Counters Require Import WTape MonoCounter LapCertGlue LapCertGlueLift
                                  LapGlueTr SweepGlueTr HybridGlueTr.
From BBB4.CensusTr Require Import TNF_QHTr QHConveyorTr.
Import ListNotations.

(** ** The numeration

    A counter is [(low, tv)]: low digits LSB first, each [< b], and a top
    value [lo <= tv < hi].  The successor adds one to the low digits; when
    they are all [b - 1] it clears them and steps the top value, and when
    the top value is [hi - 1] it clears them, adds one more digit and
    restarts the top at [lo].  Positional counters are [hi = b * lo];
    [lo = 0, hi = 1] is a counter with no top digit, only a terminator (the
    bijective numeration: an overflow widens [D(b-1)^k] to [D 0^(k+1)]).

    The value is the RANK, the number of successors from [([], lo)]:

      [cval (low, tv) = (hi - lo) * G |low| + vl low + b^|low| * (tv - lo)]

    with [G k = 1 + b + ... + b^(k-1)] the number of counters shorter than
    [k] digits per top value. *)

Section Num.

Variable b lo hi : nat.

Fixpoint vl (ds : list nat) : nat :=
  match ds with
  | [] => 0
  | d :: r => d + b * vl r
  end.

Definition G (k : nat) : nat := vl (repeat 1 k).

Definition cval (c : list nat * nat) : nat :=
  (hi - lo) * G (length (fst c)) + vl (fst c) + b ^ length (fst c) * (snd c - lo).

Definition canon (c : list nat * nat) : Prop :=
  Forall (fun d => d < b) (fst c) /\ lo <= snd c /\ snd c < hi.

Fixpoint dinc (ds : list nat) : option (list nat) :=
  match ds with
  | [] => None
  | d :: r => if S d <? b then Some (S d :: r) else option_map (cons 0) (dinc r)
  end.

Definition csucc (c : list nat * nat) : list nat * nat :=
  match dinc (fst c) with
  | Some l => (l, snd c)
  | None => if S (snd c) <? hi then (repeat 0 (length (fst c)), S (snd c))
            else (repeat 0 (S (length (fst c))), lo)
  end.

Hypothesis Hb : 2 <= b.
Hypothesis Hlh : lo < hi.

Lemma vl_app : forall a c, vl (a ++ c) = vl a + b ^ length a * vl c.
Proof.
  induction a as [|x a IH]; intros c; cbn [app vl length].
  - cbn. lia.
  - rewrite IH, Nat.pow_succ_r'. nia.
Qed.

Lemma vl_max : forall j, vl (repeat (b - 1) j) = b ^ j - 1.
Proof.
  induction j as [|j IH]; [reflexivity |].
  cbn [repeat vl]. rewrite IH, Nat.pow_succ_r'.
  pose proof (Nat.pow_nonzero b j ltac:(lia)). nia.
Qed.

Lemma vl_zero : forall j, vl (repeat 0 j) = 0.
Proof. induction j as [|j IH]; [reflexivity |]. cbn [repeat vl]. rewrite IH. lia. Qed.

Lemma vl_lt : forall ds, Forall (fun d => d < b) ds -> vl ds < b ^ length ds.
Proof.
  induction ds as [|d r IH]; intros H; cbn [vl length]; [cbn; lia |].
  inversion H as [|? ? Hd Hr]; subst. specialize (IH Hr).
  rewrite Nat.pow_succ_r'. nia.
Qed.

Lemma G_S : forall k, G (S k) = G k + b ^ k.
Proof.
  unfold G. induction k as [|k IH]; [cbn; lia |].
  change (vl (repeat 1 (S (S k)))) with (1 + b * vl (repeat 1 (S k))).
  change (vl (repeat 1 (S k))) with (1 + b * vl (repeat 1 k)) at 2.
  rewrite IH, Nat.pow_succ_r'. nia.
Qed.

Lemma G_add : forall a c, G (a + c) = G a + b ^ a * G c.
Proof.
  unfold G. induction a as [|a IH]; intros c; [cbn; lia |].
  change (vl (repeat 1 (S a + c))) with (1 + b * vl (repeat 1 (a + c))).
  change (vl (repeat 1 (S a))) with (1 + b * vl (repeat 1 a)).
  rewrite IH, Nat.pow_succ_r'. nia.
Qed.

Lemma G_mono : forall k1 k2, k1 < k2 -> G (S k1) <= G k2.
Proof.
  intros k1 k2 H. replace k2 with (S k1 + (k2 - S k1)) by lia.
  rewrite G_add. lia.
Qed.

Lemma dinc_int : forall j d r, S d < b ->
  dinc (repeat (b - 1) j ++ d :: r) = Some (repeat 0 j ++ S d :: r).
Proof.
  induction j as [|j IH]; intros d r Hd; cbn [repeat app dinc].
  - replace (S d <? b) with true by (symmetry; apply Nat.ltb_lt; exact Hd). reflexivity.
  - replace (S (b - 1) <? b) with false by (symmetry; apply Nat.ltb_ge; lia).
    rewrite (IH d r Hd). reflexivity.
Qed.

Lemma dinc_max : forall j, dinc (repeat (b - 1) j) = None.
Proof.
  induction j as [|j IH]; [reflexivity |]. cbn [repeat dinc].
  replace (S (b - 1) <? b) with false by (symmetry; apply Nat.ltb_ge; lia).
  rewrite IH. reflexivity.
Qed.

(** the low digits either hold a digit below [b - 1] above a run of
    [b - 1]s (an interior carry) or are all [b - 1] (the carry reaches the
    top) *)
Lemma low_shape : forall ds, Forall (fun d => d < b) ds ->
  (exists j d r, ds = repeat (b - 1) j ++ d :: r /\ S d < b)
  \/ ds = repeat (b - 1) (length ds).
Proof.
  induction ds as [|x r IH]; intros H; [right; reflexivity |].
  inversion H as [|? ? Hx Hr]; subst.
  destruct (Nat.lt_ge_cases (S x) b) as [Hs | Hs].
  - left. exists 0, x, r. split; [reflexivity | exact Hs].
  - assert (Ex : x = b - 1) by lia. subst x.
    destruct (IH Hr) as [(j & d & r' & -> & Hd) | Hm].
    + left. exists (S j), d, r'. split; [reflexivity | exact Hd].
    + right. cbn [length repeat]. f_equal. exact Hm.
Qed.

Lemma csucc_int : forall j d r tv, S d < b ->
  csucc (repeat (b - 1) j ++ d :: r, tv) = (repeat 0 j ++ S d :: r, tv).
Proof. intros j d r tv Hd. unfold csucc; cbn [fst snd]. rewrite dinc_int by exact Hd. reflexivity. Qed.

Lemma csucc_top : forall j tv, S tv < hi ->
  csucc (repeat (b - 1) j, tv) = (repeat 0 j, S tv).
Proof.
  intros j tv Ht. unfold csucc; cbn [fst snd]. rewrite dinc_max, repeat_length.
  replace (S tv <? hi) with true by (symmetry; apply Nat.ltb_lt; exact Ht). reflexivity.
Qed.

Lemma csucc_ovf : forall j tv, hi <= S tv ->
  csucc (repeat (b - 1) j, tv) = (repeat 0 (S j), lo).
Proof.
  intros j tv Ht. unfold csucc; cbn [fst snd]. rewrite dinc_max, repeat_length.
  replace (S tv <? hi) with false by (symmetry; apply Nat.ltb_ge; exact Ht). reflexivity.
Qed.

Lemma forall_repeat : forall x j, x < b -> Forall (fun d => d < b) (repeat x j).
Proof. intros x j Hx. induction j; constructor; auto. Qed.

Lemma cval_int : forall j d r tv,
  cval (repeat (b - 1) j ++ d :: r, tv)
  = (hi - lo) * G (S j) + (b ^ j - 1) + b ^ j * d + b ^ S j * cval (r, tv).
Proof.
  intros j d r tv. unfold cval; cbn [fst snd].
  rewrite vl_app, vl_max, app_length, repeat_length. cbn [vl length].
  replace (j + S (length r)) with (S j + length r) by lia.
  rewrite G_add, Nat.pow_add_r, !Nat.pow_succ_r'.
  pose proof (Nat.pow_nonzero b j ltac:(lia)). nia.
Qed.

Lemma cval_zint : forall j d r tv,
  cval (repeat 0 j ++ d :: r, tv) = (hi - lo) * G (S j) + b ^ j * d + b ^ S j * cval (r, tv).
Proof.
  intros j d r tv. unfold cval; cbn [fst snd].
  rewrite vl_app, vl_zero, app_length, repeat_length. cbn [vl length].
  replace (j + S (length r)) with (S j + length r) by lia.
  rewrite G_add, Nat.pow_add_r, !Nat.pow_succ_r'. nia.
Qed.

Lemma cval_max : forall j tv,
  cval (repeat (b - 1) j, tv) = (hi - lo) * G j + (b ^ j - 1) + b ^ j * (tv - lo).
Proof. intros j tv. unfold cval; cbn [fst snd]. rewrite vl_max, repeat_length. reflexivity. Qed.

Lemma cval_zero : forall j tv, cval (repeat 0 j, tv) = (hi - lo) * G j + b ^ j * (tv - lo).
Proof. intros j tv. unfold cval; cbn [fst snd]. rewrite vl_zero, repeat_length. lia. Qed.

Lemma canon_succ : forall c, canon c -> canon (csucc c) /\ cval (csucc c) = S (cval c).
Proof.
  intros [low tv] (Hf & Hl & Hh); cbn [fst snd] in *.
  destruct (low_shape low Hf) as [(j & d & r & -> & Hd) | Hm].
  - rewrite csucc_int by exact Hd. split.
    + split; [| cbn; lia]. cbn [fst].
      apply Forall_app in Hf as [_ Hr]. inversion Hr as [|? ? _ Hr']; subst.
      apply Forall_app; split; [apply forall_repeat; lia | constructor; auto].
    + rewrite cval_int, cval_zint. pose proof (Nat.pow_nonzero b j ltac:(lia)). nia.
  - rewrite Hm. set (j := length low).
    pose proof (Nat.pow_nonzero b j ltac:(lia)).
    destruct (Nat.lt_ge_cases (S tv) hi) as [Ht | Ht].
    + rewrite csucc_top by exact Ht. split.
      * split; [apply forall_repeat; lia | cbn; lia].
      * rewrite cval_max, cval_zero.
        replace (S tv - lo) with (S (tv - lo)) by lia. nia.
    + rewrite csucc_ovf by exact Ht. split.
      * split; [apply forall_repeat; lia | cbn; lia].
      * rewrite cval_max, cval_zero, G_S, Nat.sub_diag, Nat.mul_0_r, Nat.add_0_r.
        replace (tv - lo) with (hi - lo - 1) by lia. nia.
Qed.

Lemma cval_bounds : forall c, canon c ->
  (hi - lo) * G (length (fst c)) <= cval c /\ cval c < (hi - lo) * G (S (length (fst c))).
Proof.
  intros [low tv] (Hf & Hl & Hh); cbn [fst snd] in *. unfold cval; cbn [fst snd].
  pose proof (vl_lt low Hf). rewrite G_S. nia.
Qed.

Lemma vl_inj : forall l1 l2, Forall (fun d => d < b) l1 -> Forall (fun d => d < b) l2 ->
  length l1 = length l2 -> vl l1 = vl l2 -> l1 = l2.
Proof.
  induction l1 as [|x1 r1 IH]; intros l2 H1 H2 Hlen Hv; destruct l2 as [|x2 r2];
    try discriminate; [reflexivity |].
  inversion H1 as [|? ? Hx1 Hr1]; inversion H2 as [|? ? Hx2 Hr2]; subst.
  cbn [vl length] in *.
  assert (Ex : x1 = x2).
  { apply (f_equal (fun v => v mod b)) in Hv.
    rewrite !(Nat.mul_comm b), !Nat.Div0.mod_add in Hv.
    rewrite !Nat.mod_small in Hv by lia. exact Hv. }
  subst x2. f_equal. apply IH; [exact Hr1 | exact Hr2 | lia | nia].
Qed.

Lemma canon_inj : forall c1 c2, canon c1 -> canon c2 -> cval c1 = cval c2 -> c1 = c2.
Proof.
  intros [l1 t1] [l2 t2] H1 H2 Hv.
  pose proof (cval_bounds _ H1) as (B1 & B1'); pose proof (cval_bounds _ H2) as (B2 & B2').
  cbn [fst snd] in *.
  assert (Hlen : length l1 = length l2).
  { destruct (Nat.lt_trichotomy (length l1) (length l2)) as [Hlt | [He | Hlt]]; [| exact He |].
    - pose proof (G_mono _ _ Hlt). nia.
    - pose proof (G_mono _ _ Hlt). nia. }
  destruct H1 as (F1 & L1 & _); destruct H2 as (F2 & L2 & _); cbn [fst snd] in *.
  unfold cval in Hv; cbn [fst snd] in Hv. rewrite Hlen in Hv.
  pose proof (vl_lt l1 F1) as V1; pose proof (vl_lt l2 F2) as V2. rewrite Hlen in V1.
  set (K := b ^ length l2) in *.
  assert (Et : t1 - lo = t2 - lo).
  { assert (Hv' : vl l1 + K * (t1 - lo) = vl l2 + K * (t2 - lo)) by lia.
    apply (f_equal (fun v => v / K)) in Hv'.
    rewrite !(Nat.mul_comm K), !Nat.div_add in Hv' by lia.
    rewrite !Nat.div_small in Hv' by lia. exact Hv'. }
  assert (t1 = t2) by lia. subst t2.
  f_equal. apply vl_inj; [exact F1 | exact F2 | exact Hlen | nia].
Qed.

Lemma canon_exists : forall v, exists c, canon c /\ cval c = v.
Proof.
  induction v as [|v IH].
  - exists ([], lo). split.
    + split; [exact (Forall_nil _) | cbn [snd]; lia].
    + unfold cval; cbn [fst snd vl length]. unfold G; cbn. lia.
  - destruct IH as (c & Hc & Hcv). destruct (canon_succ c Hc) as (Hc' & Hv').
    exists (csucc c). split; [exact Hc' | lia].
Qed.

End Num.

(** the top family's ranks [(hi - lo) G j + b^j (e + 1) - 1], plus one,
    follow [y (j + 1) = (hi - lo) + b * y j]: mod [L] they are a function of
    the previous one, so equal at [j0] and [j0 + T] means equal all along *)
Definition ytop (b lo hi e j : nat) : nat := (hi - lo) * G b j + b ^ j * (e + 1).

Lemma ytop_S : forall b lo hi e j, ytop b lo hi e (S j) = (hi - lo) + b * ytop b lo hi e j.
Proof.
  intros b lo hi e j. unfold ytop.
  change (G b (S j)) with (1 + b * G b j). rewrite Nat.pow_succ_r'. nia.
Qed.


(** [ytop] mod [L], by the recurrence (no large power is built) *)
Fixpoint ytop_mod (b d L y0 j : nat) : nat :=
  match j with
  | 0 => y0 mod L
  | S j' => (d + b * ytop_mod b d L y0 j') mod L
  end.

Lemma ytop_mod_spec : forall b lo hi L e j, 0 < L ->
  ytop_mod b (hi - lo) L (e + 1) j = (ytop b lo hi e j) mod L.
Proof.
  intros b lo hi L e j HL. induction j as [|j IH].
  - cbn [ytop_mod]. unfold ytop, G. cbn. rewrite Nat.mul_0_r, !Nat.add_0_r. reflexivity.
  - cbn [ytop_mod]. rewrite IH, ytop_S.
    set (x := ytop b lo hi e j).
    rewrite (Nat.Div0.add_mod (hi - lo) (b * (x mod L))), (Nat.Div0.add_mod (hi - lo) (b * x)),
            (Nat.Div0.mul_mod_idemp_r b x). reflexivity.
Qed.

Lemma ytop_period : forall b lo hi L e a T, 0 < L ->
  (ytop b lo hi e (a + T)) mod L = (ytop b lo hi e a) mod L ->
  forall s, (ytop b lo hi e (a + T * s)) mod L = (ytop b lo hi e a) mod L.
Proof.
  intros b lo hi L e a T HL H.
  assert (Hsh : forall x y n, (ytop b lo hi e x) mod L = (ytop b lo hi e y) mod L ->
            (ytop b lo hi e (x + n)) mod L = (ytop b lo hi e (y + n)) mod L).
  { intros x y n Hxy. induction n as [|n IHn]; [rewrite !Nat.add_0_r; exact Hxy |].
    rewrite !Nat.add_succ_r, !ytop_S.
    rewrite (Nat.Div0.add_mod _ (b * ytop b lo hi e (x + n))),
            (Nat.Div0.add_mod _ (b * ytop b lo hi e (y + n))),
            (Nat.Div0.mul_mod b (ytop b lo hi e (x + n))),
            (Nat.Div0.mul_mod b (ytop b lo hi e (y + n))), IHn.
    reflexivity. }
  induction s as [|s IH]; [rewrite Nat.mul_0_r, Nat.add_0_r; reflexivity |].
  replace (a + T * S s) with ((a + T) + T * s) by lia.
  rewrite (Hsh (a + T) a (T * s) H). exact IH.
Qed.

(** ** The certificate *)

(** one carry shape: [nu] carry units unrolled in the chain [ch], and the
    shorter carries [j < nu] as concrete chains *)
Record hcase := mkHK {
  hk_nu   : nat;
  hk_ch   : list lstep;
  hk_base : list (list lstep)
}.

Definition hk_dflt : hcase := mkHK 0 [] [].

(** one phase of the lap, as in [HybridGlueTr.hyphase]; the counter half is
    one carry case per digit below [b - 1] ([hc_int]) and one per top value
    ([hc_top], the last one the overflow) *)
Record hcphase := mkHC {
  hc_q     : St;
  hc_h     : Sym;
  hc_Lpre  : list Sym;
  hc_Rpre  : list Sym;
  hc_w     : list Sym;
  hc_Rpost : list Sym;
  hc_m     : nat;
  hc_q2    : St;
  hc_h2    : Sym;
  hc_Mpre  : list Sym;
  hc_c     : nat;
  hc_int   : list hcase;
  hc_top   : list hcase;
  hc_na    : nat;
  hc_nb    : nat;
  hc_chs   : list lstep
}.

(** a fire witness: a chain prefix of one phase's interior case [k]
    (kind 0; family [(b^a - 1) + b^a k + b^(a+1) (bb + L s)]), top case [k]
    (kind 1; family [b^(a + bb s) (lo + k + 1) - 1]) or sweep (kind 2) *)
Record hcfire := mkHCF {
  hcf_ph   : nat;
  hcf_kind : nat;
  hcf_k    : nat;
  hcf_a    : nat;
  hcf_b    : nat;
  hcf_ch   : list lstep
}.

Record hccert := mkHCC {
  hcc_pins   : list Instr;
  hcc_b      : nat;             (** the base *)
  hcc_lo     : nat;             (** the top value ranges over [lo <= tv < hi] *)
  hcc_hi     : nat;
  hcc_D      : list (list Sym); (** the digit words *)
  hcc_T      : list (list Sym); (** the top words, [T tv] at index [tv - lo] *)
  hcc_phases : list hcphase;
  hcc_fires  : list hcfire;
  hcc_t0     : nat;
  hcc_low0   : list nat;        (** the counter at the boot *)
  hcc_tv0    : nat;
  hcc_i0     : nat;
  hcc_n0     : nat
}.

Definition hc_dflt : hcphase :=
  mkHC StA S0 [] [] [] [] 0 StA S0 [] 0 [] [] 0 0 [].

Section Defs.

Variable w : hccert.

Definition hcb : nat := hcc_b w.
Definition hclo : nat := hcc_lo w.
Definition hchi : nat := hcc_hi w.
Definition hcD (d : nat) : list Sym := nth d (hcc_D w) [].
Definition hcT (tv : nat) : list Sym := nth (tv - hclo) (hcc_T w) [].
Definition hcDm : list Sym := hcD (hcb - 1).
Definition hcD0 : list Sym := hcD 0.

Definition hcE (c : list nat * nat) : list Sym := concat (map hcD (fst c)) ++ hcT (snd c).

Definition hcL : nat := length (hcc_phases w).
Definition hcph (i : nat) : hcphase := nth i (hcc_phases w) hc_dflt.
Definition hcnx (i : nat) : nat := S i mod hcL.
Definition hcv0 : nat := cval hcb hclo hchi (hcc_low0 w, hcc_tv0 w).
Definition hc_phase_of (x : nat) : nat := (hcc_i0 w + (x - hcv0)) mod hcL.

Section Phase.

Variable P : hcphase.

Definition hcC (c : list nat * nat) (n : nat) : cconf :=
  (hc_q P, (hc_Lpre P ++ hcE c, hc_h P, hc_Rpre P ++ rep (hc_w P) n ++ hc_Rpost P)).

Definition hcM (c : list nat * nat) (n : nat) : cconf :=
  (hc_q2 P, (hc_Mpre P ++ hcE c, hc_h2 P, rep (hc_w P) n ++ hc_Rpost P)).

Definition hcRw : list Sym := hc_Rpre P ++ rep (hc_w P) (hc_m P).

(** a carry case starts on [Lpre ++ Dm^(nu + j) ++ Ps] *)
Definition hcK0 (K : hcase) (Ps : list Sym) : sconf :=
  mkC (hc_q P) (mkS (hc_Lpre P ++ rep hcDm (hk_nu K)) hcDm 1 0 Ps) (hc_h P) (sflat hcRw).

Definition hcKB (Ps : list Sym) (j : nat) : sconf :=
  mkC (hc_q P) (sflat (hc_Lpre P ++ rep hcDm j ++ Ps)) (hc_h P) (sflat hcRw).

Definition hcS0 : sconf :=
  mkC (hc_q2 P) (sflat (hc_Mpre P)) (hc_h2 P)
      (mkS (rep (hc_w P) (hc_na P)) (hc_w P) 1 0 (rep (hc_w P) (hc_nb P) ++ hc_Rpost P)).

Definition hc_nmin : nat := hc_m P + hc_na P + hc_nb P.

(** a carry case ends on the mid, its left side denoting
    [Mpre ++ D0^(c + j) ++ post] *)
Definition hc_cend_ok (el : bool) (c : nat) (post : list Sym) (c1 : sconf) : bool :=
  st_eqb (c_st c1) (hc_q2 P) && sym_eqb (c_h c1) (hc_h2 P) && sside_nil (c_r c1)
  && syms_eqb (s_u (c_l c1)) hcD0 && Nat.eqb (s_a (c_l c1)) 1
  && (s_b (c_l c1) <=? c)
  && existsb (fun x => syms_eqb (s_pre (c_l c1)) (hc_Mpre P ++ rep hcD0 x)
                       && hy_eqb el (s_post (c_l c1))
                                 (rep hcD0 (c - s_b (c_l c1) - x) ++ post))
             (seq 0 (S (c - s_b (c_l c1)))).

Definition hc_cbase_ok (el : bool) (want : list Sym) (c1 : sconf) : bool :=
  st_eqb (c_st c1) (hc_q2 P) && sym_eqb (c_h c1) (hc_h2 P) && sside_nil (c_r c1)
  && syms_eqb (s_u (c_l c1)) [] && syms_eqb (s_post (c_l c1)) []
  && hy_eqb el (s_pre (c_l c1)) want.

(** one carry case: [Dm^j ++ Ps -> D0^(j + off) ++ Pe] *)
Definition hc_case_ok (tmw : TM) (el : bool) (off : nat) (Ps Pe : list Sym)
                      (K : hcase) : bool :=
  hy_run_ok tmw el false (hk_ch K) (hcK0 K Ps) (hc_cend_ok el (hk_nu K + off) Pe)
  && hy_list_ok (fun j ch => hy_run_ok tmw el false ch (hcKB Ps j)
                   (hc_cbase_ok el (hc_Mpre P ++ rep hcD0 (j + off) ++ Pe)))
                0 (hk_base K)
  && (hk_nu K <=? length (hk_base K)).

Definition hc_int_ok (tmw : TM) (d : nat) : bool :=
  hc_case_ok tmw false 0 (hcD d) (hcD (S d)) (nth d (hc_int P) hk_dflt).

Definition hc_top_ok (tmw : TM) (e : nat) : bool :=
  if S (hclo + e) <? hchi
  then hc_case_ok tmw true 0 (hcT (hclo + e)) (hcT (S (hclo + e))) (nth e (hc_top P) hk_dflt)
  else hc_case_ok tmw true 1 (hcT (hclo + e)) (hcT hclo) (nth e (hc_top P) hk_dflt).

Definition hc_counter_ok (tmw : TM) : bool :=
  forallb (hc_int_ok tmw) (seq 0 (hcb - 1))
  && forallb (hc_top_ok tmw) (seq 0 (hchi - hclo)).

(** the sweep lands on the next phase's anchor, [k + c] units *)
Definition hc_sweep_ok (tmw : TM) (P' : hcphase) : bool :=
  match srun tmw false true (hc_chs P) hcS0 with
  | Some (c1, _, cb) =>
      st_eqb (c_st c1) (hc_q P') && sym_eqb (c_h c1) (hc_h P')
      && sside_flat_is (c_l c1) (hc_Lpre P')
      && sside_end_is (c_r c1) (hc_Rpre P') (hc_w P') (hc_c P) (hc_Rpost P')
      && (0 <? cb)
  | None => false
  end.

End Phase.

Definition hc_phase_ok (tmw : TM) (i : nat) : bool :=
  hc_counter_ok (hcph i) tmw && hc_sweep_ok (hcph i) tmw (hcph (hcnx i))
  && (hc_nmin (hcph (hcnx i)) <=? hc_c (hcph i)).

Definition hc_phases_ok (tmw : TM) : bool :=
  (1 <=? hcL) && forallb (hc_phase_ok tmw) (seq 0 hcL).

(** interior family at digit [d]: the ranks
    [(hi - lo) G (j+1) + (b^j - 1) + b^j d + b^(j+1) (H0 + L s)], all in
    phase [i] *)
Definition hc_int_fam_ok (i d j H0 : nat) : bool :=
  let x := (hchi - hclo) * G hcb (S j) + (hcb ^ j - 1) + hcb ^ j * d + hcb ^ S j * H0 in
  (S d <? hcb) && (hcv0 <=? x) && Nat.eqb (hc_phase_of x) i.

(** top family at [tv = lo + e]: the ranks [ytop e (j0 + T s) - 1] *)
Definition hc_top_fam_ok (i e j0 T : nat) : bool :=
  let x := ytop hcb hclo hchi e j0 - 1 in
  (e <? hchi - hclo) && (1 <=? T)
  && Nat.eqb (ytop_mod hcb (hchi - hclo) hcL (e + 1) (j0 + T))
             (ytop_mod hcb (hchi - hclo) hcL (e + 1) j0)
  && (hcv0 <=? x) && Nat.eqb (hc_phase_of x) i.

Definition hc_fire_ok (tmw : TM) (t : Instr) (f : hcfire) : bool :=
  let P := hcph (hcf_ph f) in
  (hcf_ph f <? hcL) &&
  match hcf_kind f with
  | 0 => let K := nth (hcf_k f) (hc_int P) hk_dflt in
         match srun_instr tmw false false (hcf_ch f) (hcK0 P K (hcD (hcf_k f))) with
         | Some t' => instr_eqb t' t && (hk_nu K <=? hcf_a f)
                      && hc_int_fam_ok (hcf_ph f) (hcf_k f) (hcf_a f) (hcf_b f)
         | None => false
         end
  | 1 => let K := nth (hcf_k f) (hc_top P) hk_dflt in
         match srun_instr tmw true false (hcf_ch f) (hcK0 P K (hcT (hclo + hcf_k f))) with
         | Some t' => instr_eqb t' t && (hk_nu K <=? hcf_a f)
                      && hc_top_fam_ok (hcf_ph f) (hcf_k f) (hcf_a f) (hcf_b f)
         | None => false
         end
  | _ => match srun_instr tmw false true (hcf_ch f) (hcS0 P) with
         | Some t' => instr_eqb t' t
         | None => false
         end
  end.

Definition hc_fires_ok (tmw : TM) : bool :=
  forallb (fun t => tr_inb t (hcc_pins w) || existsb (hc_fire_ok tmw t) (hcc_fires w))
          all_Instr.

Definition hc_canon0 : bool :=
  forallb (fun d => d <? hcb) (hcc_low0 w)
  && (hclo <=? hcc_tv0 w) && (hcc_tv0 w <? hchi).

Definition hc_core_ok (tmw : TM) : bool :=
  (2 <=? hcb) && (hclo <? hchi) && hc_canon0
  && hc_phases_ok tmw && hc_fires_ok tmw
  && (hcc_i0 w <? hcL) && (hc_nmin (hcph (hcc_i0 w)) <=? hcc_n0 w).

Definition hc_boot_ok (tm : TM) : bool :=
  match csteps tm (hcc_t0 w) c0 with
  | Some c => ceqb c (hcC (hcph (hcc_i0 w)) (hcc_low0 w, hcc_tv0 w) (hcc_n0 w))
  | None => false
  end.

End Defs.

Definition hc_check_nqh (tm : TM) (w : hccert) : bool :=
  let tmw := tm_wrap_trs tm (hcc_pins w) in
  hc_boot_ok w tmw && hc_core_ok w tmw.

Definition hc_check_qh (tm : TM) (w : hccert) : bool :=
  let tmw := tm_wrap_trs tm (hcc_pins w) in
  hc_boot_ok w tm
  && existsb (fun tg => cfires tm c0 (hcc_t0 w) tg) (hcc_pins w)
  && (Nat.log2 (hcc_t0 w) <? 24)
  && hc_core_ok w tmw.

(** ** Soundness *)

Lemma concat_map_repeat : forall (f : nat -> list Sym) x j,
  concat (map f (repeat x j)) = rep (f x) j.
Proof. intros f x j. induction j as [|j IH]; [reflexivity |]. cbn. rewrite IH. reflexivity. Qed.

Lemma hcE_int : forall w j d r tv,
  hcE w (repeat (hcb w - 1) j ++ d :: r, tv) = rep (hcDm w) j ++ hcD w d ++ hcE w (r, tv).
Proof.
  intros w j d r tv. unfold hcE; cbn [fst snd].
  rewrite map_app, concat_app, concat_map_repeat. cbn [map concat].
  rewrite <- !app_assoc. reflexivity.
Qed.

Lemma hcE_zint : forall w j d r tv,
  hcE w (repeat 0 j ++ d :: r, tv) = rep (hcD0 w) j ++ hcD w d ++ hcE w (r, tv).
Proof.
  intros w j d r tv. unfold hcE; cbn [fst snd].
  rewrite map_app, concat_app, concat_map_repeat. cbn [map concat].
  rewrite <- !app_assoc. reflexivity.
Qed.

Lemma hcE_max : forall w j tv, hcE w (repeat (hcb w - 1) j, tv) = rep (hcDm w) j ++ hcT w tv.
Proof. intros w j tv. unfold hcE; cbn [fst snd]. rewrite concat_map_repeat. reflexivity. Qed.

Lemma hcE_zero : forall w j tv, hcE w (repeat 0 j, tv) = rep (hcD0 w) j ++ hcT w tv.
Proof. intros w j tv. unfold hcE; cbn [fst snd]. rewrite concat_map_repeat. reflexivity. Qed.

Section PhaseSound.

Variable tmw : TM.
Variable w : hccert.
Variable P : hcphase.

Lemma hc_cend_den : forall el c post c1 XL XR j,
  hc_cend_ok w P el c post c1 = true -> (el = true -> XL = []) ->
  lift (cden XL XR j c1)
  = lift (hc_q2 P, (hc_Mpre P ++ rep (hcD0 w) (c + j) ++ post ++ XL, hc_h2 P, XR)).
Proof.
  intros el c post [q1 [lp lu la lb lq] h1 r1] XL XR j H HX.
  unfold hc_cend_ok in H; cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post] in H.
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

Lemma hc_cbase_den : forall el want c1 XL XR j,
  hc_cbase_ok P el want c1 = true -> (el = true -> XL = []) ->
  lift (cden XL XR j c1) = lift (hc_q2 P, (want ++ XL, hc_h2 P, XR)).
Proof.
  intros el want [q1 [lp lu la lb lq] h1 r1] XL XR j H HX.
  unfold hc_cbase_ok in H; cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post] in H.
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

(** the configuration a carry case starts on *)
Definition hcKc (Ps XL : list Sym) (j n : nat) : cconf :=
  (hc_q P, (hc_Lpre P ++ rep (hcDm w) j ++ Ps ++ XL, hc_h P,
            hc_Rpre P ++ rep (hc_w P) (hc_m P + n) ++ hc_Rpost P)).

Lemma hcK0_den : forall K Ps XL j n,
  cden XL (rep (hc_w P) n ++ hc_Rpost P) j (hcK0 w P K Ps) = hcKc Ps XL (hk_nu K + j) n.
Proof.
  intros K Ps XL j n. unfold cden, hcK0, hcKc, hcRw, sden, sflat;
    cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
  rewrite rep_nil. replace (1 * j + 0) with j by lia.
  rewrite !rep_add, <- !app_assoc. reflexivity.
Qed.

Lemma hcKB_den : forall Ps XL j n,
  cden XL (rep (hc_w P) n ++ hc_Rpost P) 0 (hcKB w P Ps j) = hcKc Ps XL j n.
Proof.
  intros Ps XL j n. unfold cden, hcKB, hcKc, hcRw, sden, sflat;
    cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
  rewrite !rep_nil. cbn [app]. rewrite !rep_add, <- !app_assoc. reflexivity.
Qed.

Lemma hc_case_sound : forall el off Ps Pe K, hc_case_ok w P tmw el off Ps Pe K = true ->
  forall j XL n, (el = true -> XL = []) ->
  exists N c', csteps tmw N (hcKc Ps XL j n) = Some c' /\
    lift c' = lift (hc_q2 P, (hc_Mpre P ++ rep (hcD0 w) (j + off) ++ Pe ++ XL, hc_h2 P,
                              rep (hc_w P) n ++ hc_Rpost P)).
Proof.
  intros el off Ps Pe K H j XL n HX. unfold hc_case_ok in H.
  apply andb_prop in H as [H Hlen]. apply andb_prop in H as [Hm Hl].
  apply Nat.leb_le in Hlen.
  destruct (lt_dec j (hk_nu K)) as [Hj | Hj].
  - destruct (nth_error (hk_base K) j) as [ch|] eqn:Ech.
    2: { apply nth_error_None in Ech. lia. }
    pose proof (hy_list_ok_nth _ _ 0 Hl j ch Ech) as Hj0. cbn [Nat.add] in Hj0.
    destruct (hy_run_sound _ _ _ _ _ _ Hj0) as (c1 & ca & cb & Hrun & Hok).
    exists (ca * 0 + cb), (cden XL (rep (hc_w P) n ++ hc_Rpost P) 0 c1). split.
    + rewrite <- hcKB_den.
      exact (srun_sound tmw el false _ _ _ ca cb Hrun _ _ 0 HX ltac:(discriminate)).
    + rewrite (hc_cbase_den el _ c1 _ _ 0 Hok HX), <- !app_assoc. reflexivity.
  - destruct (hy_run_sound _ _ _ _ _ _ Hm) as (c1 & ca & cb & Hrun & Hok).
    exists (ca * (j - hk_nu K) + cb),
      (cden XL (rep (hc_w P) n ++ hc_Rpost P) (j - hk_nu K) c1). split.
    + replace (hcKc Ps XL j n) with (hcKc Ps XL (hk_nu K + (j - hk_nu K)) n)
        by (f_equal; lia).
      rewrite <- hcK0_den.
      exact (srun_sound tmw el false _ _ _ ca cb Hrun _ _ _ HX ltac:(discriminate)).
    + rewrite (hc_cend_den el _ _ c1 _ _ _ Hok HX).
      replace (hk_nu K + off + (j - hk_nu K)) with (j + off) by lia. reflexivity.
Qed.

Hypothesis Hctr : hc_counter_ok w P tmw = true.
Hypothesis Hb : 2 <= hcb w.
Hypothesis Hlh : hclo w < hchi w.

Lemma hc_half : forall c n, canon (hcb w) (hclo w) (hchi w) c -> exists N c',
  csteps tmw N (hcC w P c (hc_m P + n)) = Some c' /\
  lift c' = lift (hcM w P (csucc (hcb w) (hclo w) (hchi w) c) n).
Proof.
  intros [low tv] n (Hf & Hl & Hh); cbn [fst snd] in *.
  unfold hc_counter_ok in Hctr. apply andb_prop in Hctr as [Hi Ht].
  rewrite forallb_forall in Hi, Ht.
  destruct (low_shape (hcb w) (hclo w) (hchi w) Hb Hlh low Hf) as [(j & d & r & -> & Hd) | Hm].
  - rewrite csucc_int by (lia || exact Hd).
    specialize (Hi d ltac:(apply in_seq; lia)). unfold hc_int_ok in Hi.
    destruct (hc_case_sound _ _ _ _ _ Hi j (hcE w (r, tv)) n ltac:(discriminate))
      as (N & c' & H1 & H2).
    exists N, c'. split.
    + unfold hcC. rewrite hcE_int. exact H1.
    + rewrite H2. unfold hcM. rewrite hcE_zint, Nat.add_0_r. reflexivity.
  - rewrite Hm. set (j := length low).
    specialize (Ht (tv - hclo w) ltac:(apply in_seq; nia)). unfold hc_top_ok in Ht.
    replace (hclo w + (tv - hclo w)) with tv in Ht by lia.
    destruct (Nat.lt_ge_cases (S tv) (hchi w)) as [Hs | Hs].
    + replace (S tv <? hchi w) with true in Ht by (symmetry; apply Nat.ltb_lt; lia).
      rewrite csucc_top by (lia || exact Hs).
      destruct (hc_case_sound _ _ _ _ _ Ht j [] n ltac:(reflexivity))
        as (N & c' & H1 & H2).
      exists N, c'. split.
      * unfold hcC. rewrite hcE_max. unfold hcKc in H1. rewrite app_nil_r in H1. exact H1.
      * rewrite H2. unfold hcM. rewrite hcE_zero, Nat.add_0_r, app_nil_r. reflexivity.
    + replace (S tv <? hchi w) with false in Ht by (symmetry; apply Nat.ltb_ge; lia).
      rewrite csucc_ovf by (lia || exact Hs).
      destruct (hc_case_sound _ _ _ _ _ Ht j [] n ltac:(reflexivity))
        as (N & c' & H1 & H2).
      exists N, c'. split.
      * unfold hcC. rewrite hcE_max. unfold hcKc in H1. rewrite app_nil_r in H1. exact H1.
      * rewrite H2. unfold hcM. rewrite hcE_zero, Nat.add_1_r, app_nil_r. reflexivity.
Qed.

Lemma hc_to_mid : forall c n, canon (hcb w) (hclo w) (hchi w) c -> hc_nmin P <= n -> exists N,
  stepn tmw N (lift (hcC w P c n))
  = Some (lift (hcM w P (csucc (hcb w) (hclo w) (hchi w) c) (hc_na P + (n - hc_nmin P) + hc_nb P))).
Proof.
  intros c n Hc Hn. unfold hc_nmin in *.
  destruct (hc_half c (n - hc_m P) Hc) as (N & c' & H1 & Hl).
  exists N. replace (hc_na P + (n - (hc_m P + hc_na P + hc_nb P)) + hc_nb P)
    with (n - hc_m P) by lia.
  replace n with (hc_m P + (n - hc_m P)) at 1 by lia.
  exact (lap_stepn _ _ _ _ _ H1 Hl).
Qed.

End PhaseSound.

Lemma hcS0_den : forall w P c k,
  cden (hcE w c) [] k (hcS0 P) = hcM w P c (hc_na P + k + hc_nb P).
Proof.
  intros w P c k. unfold cden, hcS0, hcM, sden, sflat;
    cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
  replace (1 * k + 0) with k by lia. rewrite rep_nil, !app_nil_r.
  rewrite !rep_add, <- !app_assoc. reflexivity.
Qed.

Lemma hc_sweep_main : forall tmw w P P', hc_sweep_ok P tmw P' = true ->
  forall c k, exists N c',
  csteps tmw N (hcM w P c (hc_na P + k + hc_nb P)) = Some c' /\
  lift c' = lift (hcC w P' c (k + hc_c P)) /\ 0 < N.
Proof.
  intros tmw w P P' H c k. unfold hc_sweep_ok in H.
  destruct (srun tmw false true (hc_chs P) (hcS0 P)) as [[[c1 ca] cb]|] eqn:E;
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
  set (cc := hc_c P) in *.
  exists (ca * k + cb),
    (cden (hcE w c) [] k
          (mkC (hc_q P') (mkS (hc_Lpre P') [] la lb []) (hc_h P')
               (mkS (hc_Rpre P' ++ rep (hc_w P') x) (hc_w P') 1 rb rq))).
  split; [| split; [| lia]].
  - rewrite <- hcS0_den.
    exact (srun_sound tmw false true (hc_chs P) (hcS0 P) _ ca cb E
             (hcE w c) [] k ltac:(discriminate) ltac:(reflexivity)).
  - unfold cden, hcC, sden; cbn [c_st c_l c_h c_r s_pre s_u s_a s_b s_post rep].
    rewrite rep_nil. rewrite !app_nil_r. cbn [app].
    apply lift_lpad; [apply lpad_eqb_refl |].
    replace (k + cc) with (x + ((1 * k + rb) + (cc - rb - x))) by lia.
    rewrite !rep_add, <- !app_assoc.
    repeat apply lpad_eqb_app. exact Hrq.
Qed.

Lemma hc_lap : forall tmw w P P', hc_counter_ok w P tmw = true ->
  hc_sweep_ok P tmw P' = true -> 2 <= hcb w -> hclo w < hchi w ->
  forall c n, canon (hcb w) (hclo w) (hchi w) c -> hc_nmin P <= n -> exists N, 0 < N /\
  stepn tmw N (lift (hcC w P c n))
  = Some (lift (hcC w P' (csucc (hcb w) (hclo w) (hchi w) c) (n - hc_nmin P + hc_c P))).
Proof.
  intros tmw w P P' Hc Hs Hb Hlh c n Hcn Hn.
  destruct (hc_to_mid tmw w P Hc Hb Hlh c n Hcn Hn) as (N1 & H1).
  destruct (hc_sweep_main tmw w P P' Hs (csucc (hcb w) (hclo w) (hchi w) c) (n - hc_nmin P))
    as (N2 & c2 & H2 & Hl2 & HN2).
  exists (N1 + N2). split; [lia |].
  rewrite stepn_add, H1, (lap_stepn _ _ _ _ _ H2 Hl2). reflexivity.
Qed.

(** *** Fires *)

Lemma fire_case : forall tmw w P el K Ps ch t,
  srun_instr tmw el false ch (hcK0 w P K Ps) = Some t ->
  forall j XL n, (el = true -> XL = []) ->
  FiresFrom tmw (hcKc w P Ps XL (hk_nu K + j) n) t.
Proof.
  intros tmw w P el K Ps ch t H j XL n HX.
  apply fire_lift_of_csteps with (Cc := fun _ => hcKc w P Ps XL (hk_nu K + j) n) (p := xH).
  exact (fire_of_run_instr tmw (fun _ => hcKc w P Ps XL (hk_nu K + j) n) el false
           ch (hcK0 w P K Ps) xH j XL (rep (hc_w P) n ++ hc_Rpost P) t H
           HX ltac:(discriminate) (eq_sym (hcK0_den w P K Ps XL j n))).
Qed.

Lemma hc_fire_sweep : forall tmw w P ch t, srun_instr tmw false true ch (hcS0 P) = Some t ->
  forall c k, FiresFrom tmw (hcM w P c (hc_na P + k + hc_nb P)) t.
Proof.
  intros tmw w P ch t H c k.
  apply fire_lift_of_csteps with (Cc := fun _ => hcM w P c (hc_na P + k + hc_nb P)) (p := xH).
  exact (fire_of_run_instr tmw (fun _ => hcM w P c (hc_na P + k + hc_nb P)) false true
           ch (hcS0 P) xH k (hcE w c) [] t H
           ltac:(discriminate) ltac:(reflexivity) (eq_sym (hcS0_den w P c k))).
Qed.

(** ** Modular arithmetic for the families *)

Lemma mod_cancel_r : forall L u v k, 0 < L ->
  (u + k) mod L = (v + k) mod L -> u mod L = v mod L.
Proof.
  intros L u v k HL H.
  assert (E : forall x, x mod L = ((x + k) mod L + (L - k mod L)) mod L).
  { intros x. rewrite Nat.Div0.add_mod_idemp_l.
    pose proof (Nat.div_mod k L ltac:(lia)) as Hk.
    pose proof (Nat.mod_upper_bound k L ltac:(lia)).
    replace (x + k + (L - k mod L)) with (x + (k / L + 1) * L) by nia.
    rewrite Nat.Div0.mod_add. reflexivity. }
  rewrite (E u), (E v), H. reflexivity.
Qed.

Lemma powb_mod_period : forall b L a T, 0 < L ->
  (b ^ (a + T)) mod L = (b ^ a) mod L ->
  forall q, (b ^ (a + T * q)) mod L = (b ^ a) mod L.
Proof.
  intros b L a T HL H. induction q as [|q IH].
  - rewrite Nat.mul_0_r, Nat.add_0_r. reflexivity.
  - replace (a + T * S q) with ((a + T * q) + T) by lia.
    rewrite Nat.pow_add_r, Nat.Div0.mul_mod, IH, <- Nat.Div0.mul_mod.
    rewrite <- Nat.pow_add_r. exact H.
Qed.

Section Sound.

Variable tmw : TM.
Variable w : hccert.

Hypothesis Hcore : hc_core_ok w tmw = true.

Local Notation b := (hcb w).
Local Notation lo := (hclo w).
Local Notation hi := (hchi w).

Lemma hc_core_parts : 2 <= b /\ lo < hi /\ hc_canon0 w = true /\ hc_phases_ok w tmw = true
  /\ hc_fires_ok w tmw = true /\ hcc_i0 w < hcL w /\ hc_nmin (hcph w (hcc_i0 w)) <= hcc_n0 w.
Proof.
  pose proof Hcore as H. unfold hc_core_ok in H.
  apply andb_prop in H as [H Hn]. apply andb_prop in H as [H Hi].
  apply andb_prop in H as [H Hf]. apply andb_prop in H as [H Hp].
  apply andb_prop in H as [H Hc]. apply andb_prop in H as [Hb Hl].
  apply Nat.leb_le in Hb, Hn. apply Nat.ltb_lt in Hi, Hl. tauto.
Qed.

Lemma hc_b2 : 2 <= b. Proof. apply hc_core_parts. Qed.
Lemma hc_lh : lo < hi. Proof. apply hc_core_parts. Qed.

Lemma hc_L_pos : 1 <= hcL w.
Proof.
  destruct hc_core_parts as (_ & _ & _ & H & _). unfold hc_phases_ok in H.
  apply andb_prop in H as [H _]. apply Nat.leb_le in H. exact H.
Qed.

Lemma hc_phase_at : forall i, i < hcL w ->
  hc_counter_ok w (hcph w i) tmw = true
  /\ hc_sweep_ok (hcph w i) tmw (hcph w (hcnx w i)) = true
  /\ hc_nmin (hcph w (hcnx w i)) <= hc_c (hcph w i).
Proof.
  intros i Hi. destruct hc_core_parts as (_ & _ & _ & H & _). unfold hc_phases_ok in H.
  apply andb_prop in H as [_ H]. rewrite forallb_forall in H.
  specialize (H i ltac:(apply in_seq; lia)).
  unfold hc_phase_ok in H.
  apply andb_prop in H as [H Hn]. apply andb_prop in H as [Hc Hs].
  apply Nat.leb_le in Hn. auto.
Qed.

Definition hcS : Type := ((list nat * nat) * nat * nat)%type.

Definition hcA (s : hcS) : cconf :=
  let '(c, n, i) := s in hcC w (hcph w i) c n.

Definition hc_good (s : hcS) : Prop :=
  let '(c, n, i) := s in
  canon b lo hi c /\ hcv0 w <= cval b lo hi c /\ i = hc_phase_of w (cval b lo hi c)
  /\ hc_nmin (hcph w i) <= n.

Definition hc_nxt (s : hcS) : hcS :=
  let '(c, n, i) := s in
  (csucc b lo hi c, n - hc_nmin (hcph w i) + hc_c (hcph w i), hcnx w i).

Lemma hc_phase_lt : forall x, hc_phase_of w x < hcL w.
Proof. intros x. unfold hc_phase_of. apply Nat.mod_upper_bound. pose proof hc_L_pos. lia. Qed.

Lemma hc_phase_succ : forall x, hcv0 w <= x ->
  hc_phase_of w (S x) = hcnx w (hc_phase_of w x).
Proof.
  intros x Hx. pose proof hc_L_pos as HL.
  unfold hc_phase_of, hcnx.
  replace (hcc_i0 w + (S x - hcv0 w)) with (1 + (hcc_i0 w + (x - hcv0 w))) by lia.
  symmetry. exact (Nat.Div0.add_mod_idemp_r 1 _ _).
Qed.

(** two values congruent mod [L] (both past the boot) are in one phase *)
Lemma hc_phase_cong : forall x y, hcv0 w <= x -> hcv0 w <= y ->
  x mod hcL w = y mod hcL w -> hc_phase_of w x = hc_phase_of w y.
Proof.
  intros x y Hx Hy H. pose proof hc_L_pos as HL. unfold hc_phase_of.
  apply (mod_cancel_r (hcL w) _ _ (hcv0 w)); [lia |].
  replace (hcc_i0 w + (x - hcv0 w) + hcv0 w) with (hcc_i0 w + x) by lia.
  replace (hcc_i0 w + (y - hcv0 w) + hcv0 w) with (hcc_i0 w + y) by lia.
  rewrite (Nat.Div0.add_mod (hcc_i0 w) x), (Nat.Div0.add_mod (hcc_i0 w) y), H.
  reflexivity.
Qed.

Lemma hc_step : forall s, hc_good s -> hc_good (hc_nxt s) /\ exists N, 0 < N /\
  stepn tmw N (lift (hcA s)) = Some (lift (hcA (hc_nxt s))).
Proof.
  intros [[c n] i] (Hc & Hv & Hi & Hn). cbn [hc_nxt hcA hc_good].
  destruct (hc_phase_at i ltac:(rewrite Hi; apply hc_phase_lt)) as (Hk & Hs & Hm).
  destruct (canon_succ b lo hi hc_b2 hc_lh c Hc) as (Hc' & Hv').
  split.
  - split; [exact Hc' |]. rewrite Hv'. split; [lia |].
    split; [rewrite Hi; symmetry; exact (hc_phase_succ _ Hv) | lia].
  - exact (hc_lap tmw w _ _ Hk Hs hc_b2 hc_lh c n Hc Hn).
Qed.

Lemma hc_reach : forall D s, hc_good s ->
  exists T s', hc_good s' /\ cval b lo hi (fst (fst s')) = cval b lo hi (fst (fst s)) + D /\
    stepn tmw T (lift (hcA s)) = Some (lift (hcA s')).
Proof.
  induction D as [|D IH]; intros s Hg.
  - exists 0, s. split; [exact Hg |]. split; [lia | reflexivity].
  - destruct (IH s Hg) as (T & s' & Hg' & Hv & HT).
    destruct (hc_step s' Hg') as (Hg'' & N & _ & HN).
    exists (T + N), (hc_nxt s'). split; [exact Hg'' |]. split.
    + destruct s' as [[c1 n1] i1]. cbn [hc_nxt fst] in *.
      destruct Hg' as (Hc1 & _).
      rewrite (proj2 (canon_succ b lo hi hc_b2 hc_lh c1 Hc1)). lia.
    + rewrite stepn_add, HT. exact HN.
Qed.

(** any canonical counter at or above a visited anchor's is visited, in the
    phase its value names *)
Lemma hc_reach_at : forall s c', hc_good s -> canon b lo hi c' ->
  cval b lo hi (fst (fst s)) <= cval b lo hi c' ->
  exists T n', hc_nmin (hcph w (hc_phase_of w (cval b lo hi c'))) <= n' /\
    stepn tmw T (lift (hcA s))
    = Some (lift (hcC w (hcph w (hc_phase_of w (cval b lo hi c'))) c' n')).
Proof.
  intros s c' Hg Hc' Hle.
  destruct (hc_reach (cval b lo hi c' - cval b lo hi (fst (fst s))) s Hg)
    as (T & [[c1 n1] i1] & (Hc1 & Hv1 & Hi1 & Hn1) & He & HT).
  cbn [fst] in He.
  assert (Ec : c1 = c').
  { apply (canon_inj b lo hi hc_b2 hc_lh _ _ Hc1 Hc'). lia. }
  subst c1 i1. exists T, n1. auto.
Qed.

Lemma hc_fire_sweep_any : forall i ch t, i < hcL w ->
  srun_instr tmw false true ch (hcS0 (hcph w i)) = Some t ->
  forall s, hc_good s -> FiresFrom tmw (hcA s) t.
Proof.
  intros i ch t Hi H s Hg.
  pose proof hc_L_pos as HL.
  set (x0 := cval b lo hi (fst (fst s))).
  remember (hcc_i0 w + (x0 - hcv0 w)) as X eqn:EX.
  remember ((i + hcL w - X mod hcL w) mod hcL w) as d eqn:Ed.
  destruct (canon_exists b lo hi hc_b2 hc_lh (x0 + d))
    as (c' & Hc' & Hv').
  destruct (hc_reach_at s c' Hg Hc' ltac:(lia)) as (T & n' & Hn' & HT).
  assert (Hph : hc_phase_of w (cval b lo hi c') = i).
  { destruct s as [[c n] i1]. destruct Hg as (_ & Hv & _). cbn [fst] in x0.
    unfold hc_phase_of. rewrite Hv'.
    replace (hcc_i0 w + (x0 + d - hcv0 w)) with (X + d) by (subst x0; lia).
    subst d. exact (mod_shift X i (hcL w) ltac:(lia) Hi). }
  rewrite Hph in Hn', HT.
  apply (fires_back tmw _ _ T t HT).
  destruct (hc_to_mid tmw w (hcph w i) (proj1 (hc_phase_at i Hi)) hc_b2 hc_lh c' n' Hc' Hn')
    as (N & HN).
  apply (fires_back tmw _ _ N t HN). apply (hc_fire_sweep tmw w _ ch t H).
Qed.

Lemma hc_fire_int_any : forall i d j H0 ch t, i < hcL w ->
  srun_instr tmw false false ch (hcK0 w (hcph w i) (nth d (hc_int (hcph w i)) hk_dflt) (hcD w d))
    = Some t ->
  hk_nu (nth d (hc_int (hcph w i)) hk_dflt) <= j -> hc_int_fam_ok w i d j H0 = true ->
  forall s, hc_good s -> FiresFrom tmw (hcA s) t.
Proof.
  intros i d j H0 ch t Hi H Hj Hf s Hg.
  pose proof hc_L_pos as HL. pose proof hc_b2 as Hb2.
  unfold hc_int_fam_ok in Hf.
  apply andb_prop in Hf as [Hf Hph]. apply andb_prop in Hf as [Hd Hx].
  apply Nat.ltb_lt in Hd. apply Nat.leb_le in Hx. apply Nat.eqb_eq in Hph.
  set (x0 := cval b lo hi (fst (fst s))).
  destruct (canon_exists b lo hi hc_b2 hc_lh (H0 + hcL w * x0)) as ([r tv] & Hr & Hrv).
  set (c' := (repeat (b - 1) j ++ d :: r, tv)).
  assert (Hc' : canon b lo hi c').
  { destruct Hr as (Hrf & Hrl & Hrh). split; [| exact (conj Hrl Hrh)].
    cbn [fst]. apply Forall_app. split; [apply forall_repeat; lia | constructor; [lia | exact Hrf]]. }
  assert (Hcv : cval b lo hi c'
                = ((hi - lo) * G b (S j) + (b ^ j - 1) + b ^ j * d + b ^ S j * H0)
                  + (b ^ S j * x0) * hcL w).
  { unfold c'. rewrite (cval_int _ _ _ hc_b2 hc_lh), Hrv. nia. }
  pose proof (Nat.pow_nonzero b (S j) ltac:(lia)) as Hpz.
  assert (Hge : x0 <= cval b lo hi c') by (rewrite Hcv; nia).
  destruct (hc_reach_at s c' Hg Hc' Hge) as (T & n' & Hn' & HT).
  assert (Hp : hc_phase_of w (cval b lo hi c') = i).
  { rewrite <- Hph. apply hc_phase_cong; [lia | exact Hx |].
    rewrite Hcv. apply Nat.Div0.mod_add. }
  rewrite Hp in Hn', HT.
  apply (fires_back tmw _ _ T t HT).
  unfold hc_nmin in Hn'.
  set (K := nth d (hc_int (hcph w i)) hk_dflt) in *.
  assert (E : hcC w (hcph w i) c' n'
              = hcKc w (hcph w i) (hcD w d) (hcE w (r, tv)) (hk_nu K + (j - hk_nu K))
                     (n' - hc_m (hcph w i))).
  { unfold hcC, hcKc, c'. rewrite hcE_int.
    replace (hk_nu K + (j - hk_nu K)) with j by lia.
    replace (hc_m (hcph w i) + (n' - hc_m (hcph w i))) with n' by lia. reflexivity. }
  rewrite E. exact (fire_case tmw w _ false K _ ch t H _ _ _ ltac:(discriminate)).
Qed.

Lemma hc_fire_top_any : forall i e j0 TT ch t, i < hcL w ->
  srun_instr tmw true false ch
    (hcK0 w (hcph w i) (nth e (hc_top (hcph w i)) hk_dflt) (hcT w (lo + e))) = Some t ->
  hk_nu (nth e (hc_top (hcph w i)) hk_dflt) <= j0 -> hc_top_fam_ok w i e j0 TT = true ->
  forall s, hc_good s -> FiresFrom tmw (hcA s) t.
Proof.
  intros i e j0 TT ch t Hi H Hj Hf s Hg.
  pose proof hc_L_pos as HL. pose proof hc_b2 as Hb2. pose proof hc_lh as Hlh.
  unfold hc_top_fam_ok in Hf.
  apply andb_prop in Hf as [Hf Hph]. apply andb_prop in Hf as [Hf Hx].
  apply andb_prop in Hf as [Hf Hper]. apply andb_prop in Hf as [He HT].
  apply Nat.ltb_lt in He. apply Nat.leb_le in HT, Hx. apply Nat.eqb_eq in Hph, Hper.
  rewrite !ytop_mod_spec in Hper by lia.
  set (x0 := cval b lo hi (fst (fst s))).
  set (j := j0 + TT * x0).
  set (c' := (repeat (b - 1) j, lo + e)).
  assert (Hc' : canon b lo hi c').
  { unfold canon, c'; cbn [fst snd]. split; [apply forall_repeat; lia | lia]. }
  assert (Hcv : forall k, cval b lo hi (repeat (b - 1) k, lo + e) = ytop b lo hi e k - 1).
  { intros k. rewrite (cval_max _ _ _ hc_b2 hc_lh). unfold ytop.
    pose proof (Nat.pow_nonzero b k ltac:(lia)).
    replace (lo + e - lo) with e by lia. nia. }
  assert (Hmono : forall k n, ytop b lo hi e k <= ytop b lo hi e (k + n)).
  { intros k n. induction n as [|n IHn]; [rewrite Nat.add_0_r; lia |].
    rewrite Nat.add_succ_r, ytop_S. nia. }
  assert (Hpj : x0 < b ^ j).
  { apply (Nat.lt_le_trans _ (b ^ x0)); [apply Nat.pow_gt_lin_r; lia |].
    apply Nat.pow_le_mono_r; [lia | nia]. }
  assert (Hge : x0 <= cval b lo hi c').
  { unfold c'. rewrite Hcv. unfold ytop. nia. }
  destruct (hc_reach_at s c' Hg Hc' Hge) as (T & n' & Hn' & HT').
  assert (Hp : hc_phase_of w (cval b lo hi c') = i).
  { rewrite <- Hph. unfold c'. rewrite Hcv.
    pose proof (Hmono j0 (TT * x0)) as Hm0. fold j in Hm0.
    apply hc_phase_cong; [lia | exact Hx |].
    pose proof (ytop_period b lo hi (hcL w) e j0 TT ltac:(lia) Hper x0) as Hm.
    fold j in Hm.
    set (Z := ytop b lo hi e j) in *. set (Z0 := ytop b lo hi e j0) in *.
    assert (HZ1 : 1 <= Z0) by (unfold Z0, ytop; pose proof (Nat.pow_nonzero b j0 ltac:(lia)); nia).
    pose proof (Nat.div_mod Z (hcL w) ltac:(lia)) as HZd.
    pose proof (Nat.div_mod Z0 (hcL w) ltac:(lia)) as HZ0d.
    assert (Hd : Z0 / hcL w <= Z / hcL w) by (apply Nat.Div0.div_le_mono; lia).
    replace (Z - 1) with ((Z0 - 1) + (Z / hcL w - Z0 / hcL w) * hcL w) by nia.
    apply Nat.Div0.mod_add. }
  rewrite Hp in Hn', HT'.
  apply (fires_back tmw _ _ T t HT').
  unfold hc_nmin in Hn'.
  set (K := nth e (hc_top (hcph w i)) hk_dflt) in *.
  assert (E : hcC w (hcph w i) c' n'
              = hcKc w (hcph w i) (hcT w (lo + e)) [] (hk_nu K + (j - hk_nu K))
                     (n' - hc_m (hcph w i))).
  { unfold hcC, hcKc, c'. rewrite hcE_max, app_nil_r.
    replace (hk_nu K + (j - hk_nu K)) with j by lia.
    replace (hc_m (hcph w i) + (n' - hc_m (hcph w i))) with n' by lia. reflexivity. }
  rewrite E. exact (fire_case tmw w _ true K _ ch t H _ _ _ ltac:(reflexivity)).
Qed.

Lemma hc_fire_any : forall t, ~ In t (hcc_pins w) ->
  forall s, hc_good s -> FiresFrom tmw (hcA s) t.
Proof.
  intros t Hnin s Hg.
  destruct hc_core_parts as (_ & _ & _ & _ & H & _). unfold hc_fires_ok in H.
  rewrite forallb_forall in H.
  specialize (H t (all_Instr_complete t)).
  apply orb_prop in H as [H | H].
  { exfalso. apply Hnin, tr_inb_spec, H. }
  apply existsb_exists in H as ([i k d a bb ch] & _ & Hf).
  unfold hc_fire_ok in Hf; cbn [hcf_ph hcf_kind hcf_k hcf_a hcf_b hcf_ch] in Hf.
  apply andb_prop in Hf as [Hi Hf]. apply Nat.ltb_lt in Hi.
  destruct k as [|[|k]].
  - match type of Hf with context [srun_instr ?a ?b ?c ?d ?e] =>
      destruct (srun_instr a b c d e) as [t'|] eqn:E; [|discriminate] end.
    apply andb_prop in Hf as [Hf Hfam]. apply andb_prop in Hf as [Ht Hj].
    apply instr_eqb_spec in Ht. apply Nat.leb_le in Hj. subst t'.
    exact (hc_fire_int_any i d a bb ch t Hi E Hj Hfam s Hg).
  - match type of Hf with context [srun_instr ?a ?b ?c ?d ?e] =>
      destruct (srun_instr a b c d e) as [t'|] eqn:E; [|discriminate] end.
    apply andb_prop in Hf as [Hf Hfam]. apply andb_prop in Hf as [Ht Hj].
    apply instr_eqb_spec in Ht. apply Nat.leb_le in Hj. subst t'.
    exact (hc_fire_top_any i d a bb ch t Hi E Hj Hfam s Hg).
  - destruct (srun_instr tmw false true ch (hcS0 (hcph w i))) as [t'|] eqn:E;
      [|discriminate].
    apply instr_eqb_spec in Hf. subst t'.
    exact (hc_fire_sweep_any i ch t Hi E s Hg).
Qed.

(** ** The enumeration: the anchors along the run *)

Definition hc_s0 : hcS := ((hcc_low0 w, hcc_tv0 w), hcc_n0 w, hcc_i0 w).

Lemma hc_good_s0 : hc_good hc_s0.
Proof.
  destruct hc_core_parts as (_ & _ & Hc & _ & _ & Hi & Hn).
  unfold hc_canon0 in Hc.
  apply andb_prop in Hc as [Hc Hh]. apply andb_prop in Hc as [Hf Hl].
  rewrite forallb_forall in Hf. apply Nat.leb_le in Hl. apply Nat.ltb_lt in Hh.
  cbn [hc_s0 hc_good]. split; [| split; [unfold hcv0; lia | split; [| exact Hn]]].
  - split; [| cbn [snd]; auto]. cbn [fst].
    apply Forall_forall. intros x Hx. apply Nat.ltb_lt, Hf, Hx.
  - unfold hc_phase_of, hcv0. rewrite Nat.sub_diag, Nat.add_0_r. symmetry.
    apply Nat.mod_small. exact Hi.
Qed.

Definition hc_st (k : nat) : hcS := Nat.iter k hc_nxt hc_s0.

Lemma hc_st_good : forall k, hc_good (hc_st k).
Proof.
  induction k as [|k IH]; [exact hc_good_s0 |].
  cbn [hc_st Nat.iter nat_rect]. exact (proj1 (hc_step _ IH)).
Qed.

Definition hcCf (p : positive) : cconf := hcA (hc_st (Pos.to_nat p - 1)).

Lemma hc_Hlap : forall p, (1 <= p)%positive ->
  exists n c', csteps tmw n (hcCf p) = Some c' /\
               lift c' = lift (hcCf (Pos.succ p)) /\ 0 < n.
Proof.
  intros p _.
  destruct (hc_step _ (hc_st_good (Pos.to_nat p - 1))) as (_ & N & HN & H).
  destruct (stepn_csteps_at tmw N (hcCf p) _ H) as (c' & Hc & Hl).
  exists N, c'. split; [exact Hc |]. split; [| exact HN].
  rewrite Hl. unfold hcCf. f_equal. f_equal.
  rewrite Pos2Nat.inj_succ. pose proof (Pos2Nat.is_pos p).
  replace (S (Pos.to_nat p) - 1) with (S (Pos.to_nat p - 1)) by lia.
  reflexivity.
Qed.

Lemma hc_Hfire : forall t, ~ In t (hcc_pins w) -> forall p, (1 <= p)%positive ->
  exists k c, csteps tmw k (hcCf p) = Some c /\ cinstr c = t.
Proof.
  intros t Hnin p _. apply fire_csteps_of_lift.
  exact (hc_fire_any t Hnin _ (hc_st_good _)).
Qed.

End Sound.

Lemma hc_boot : forall tm w, hc_boot_ok w tm = true ->
  stepn tm (hcc_t0 w) InitES = Some (lift (hcCf w xH)).
Proof.
  intros tm w Hb. unfold hc_boot_ok in Hb.
  destruct (csteps tm (hcc_t0 w) c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E).
  f_equal. unfold hcCf. cbn [Pos.to_nat Pos.iter_op Nat.sub].
  cbn [hc_st Nat.iter nat_rect hc_s0 hcA].
  exact (ceqb_lift _ _ Hb).
Qed.

Theorem hc_sound_nqh : forall tm w, hc_check_nqh tm w = true -> NeverQuasiHaltsTr tm.
Proof.
  intros tm w H. unfold hc_check_nqh in H.
  apply andb_prop in H as [Hb Hc].
  apply (glue_neverqhtr tm (hcc_pins w) (hcCf w) xH).
  - exists (hcc_t0 w). exact (hc_boot _ w Hb).
  - exact (hc_Hlap _ w Hc).
  - exact (hc_Hfire _ w Hc).
Qed.

Theorem hc_sound_qh : forall tm w, hc_check_qh tm w = true ->
  NonHalt tm /\ QHBoundTr 32779478 tm /\ QuasiHaltsTr tm.
Proof.
  intros tm w H. unfold hc_check_qh in H.
  apply andb_prop in H as [H Hc].
  apply andb_prop in H as [H Hcap].
  apply andb_prop in H as [Hb Hwit].
  apply (lap_qh_stage tm (hcc_pins w) (hcCf w) xH (hcc_t0 w) 32779478).
  - exact (hc_boot tm w Hb).
  - exact (hc_Hlap _ w Hc).
  - exact (hc_Hfire _ w Hc).
  - exact Hwit.
  - exact (hy_cap_le _ Hcap).
Qed.

(** the counter sits on the RIGHT: certify the mirror *)
Theorem hc_sound_nqh_mirror : forall tm w, hc_check_nqh (mirror_tm tm) w = true ->
  NeverQuasiHaltsTr tm.
Proof.
  intros tm w H. exact (neverqhtr_mirror tm (hc_sound_nqh _ w H)).
Qed.

Theorem hc_sound_qh_mirror : forall tm w, hc_check_qh (mirror_tm tm) w = true ->
  NonHalt tm /\ QHBoundTr 32779478 tm /\ QuasiHaltsTr tm.
Proof.
  intros tm w H. exact (qh_triple_unmirror 32779478 tm (hc_sound_qh _ w H)).
Qed.
