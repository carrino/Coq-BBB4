(** * Checkers.LadderCheckTankPhTr: a binary counter that widens into a
    TANK, with a cycle of PHASES between the refills (SCOPING_INSTR 7.4.LE9).

    [LadderCheckTankTr] (LE7) states a counter followed by a tank word run
    that the counter eats as it widens, and ONE refill: an empty tank at the
    top rewrites the whole tape as [z ++ T^(k + a)].  Six of LE7's residue
    rows are the same counter, but between two refills the machine passes
    through a short cycle of phases, each with its own suffix at the far
    end.  Read at the right anchor, [1RB0LC_0LA1RC_1RD1LA_1RB0RD] is
    [(1011 | 1111)^k (0111)^m suf_p] with phases [suf = [], [1], [1;1]]:

      (x, m, p)          -> (x + 1, m, p)                 x not all-top
      (top^k, m + 1, p)  -> (0^k 1, m, p)                 the widening eats a tank word
      (top^k, 0, p)      -> (fill_p k, p + 1 mod P)       the FILL of phase p

    and a fill either keeps the width ([kz p]: [x = 0^k ++ z_p],
    [m = a_p]) or refills the tank ([x = z_p], [m = k + a_p]).  Cells
    [pre ++ flat_map dig x ++ T^m ++ suf_p].  [1RB0LD_1RC0RC_0LA0RA_1RA1LA]
    is the second shape: [(1110 | 1111)^k (1101)^m] with phases
    [suf = [1;1]] (tank), [[1;1;1]] (fill to [0^k 1]: one digit wider) and
    [[]] (fill to an empty counter and a full tank).

    Liveness: within a phase [(m, x)] rises lexicographically until the top
    of an empty tank, so every phase's fill recurs, and the phases cycle;
    each instruction is read off the fill arms of ONE phase.

    Nothing landed is modified.  Axiom footprint: [functional_extensionality_dep],
    via [CTape.lift]. *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape ClosureTr.
From BBB4.Counters Require Import WTape LapCertGlueLift.
From BBB4.Checkers Require Import WrapTr LapDecider LadderKernel LadderFam LadderCheck LadderCheckTr LadderNest LadderCheckNestTr TCyclerQHTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
From BBB4.Counters Require Import LapGlueTr.
From BBB4.CensusTr Require Import TNF_QHTr QHConveyorTr.
From BBB4.Checkers Require Import LadderCheckTankTr.
Import ListNotations.

(** ** 1. The counter *)

Section TankPh.

Variable F : Fam.
Variable T : list Sym.
Variable P : nat.                    (** the number of phases *)
Variable suf : nat -> list Sym.      (** the far-end suffix of each phase *)
Variable kz : nat -> bool.           (** the fill keeps the width (true) or refills the tank *)
Variable z : nat -> list nat.        (** the fill's fixed digits *)
Variable a : nat -> nat.             (** the fill's tank offset *)

Local Notation b := (fm_b F).

Definition nxtP (p : nat) : nat := if S p =? P then 0 else S p.

Definition PSt : Type := (list nat * nat * nat)%type.

Definition pfill (k p : nat) : PSt :=
  if kz p
  then (repeat 0 k ++ z p, a p, nxtP p)
  else (z p, k + a p, nxtP p).

Definition psucc (s : PSt) : PSt :=
  let '(x, m, p) := s in
  if alltopK F x
  then match m with
       | O => pfill (length x) p
       | S m' => (incK F x, m', p)
       end
  else (incK F x, m, p).

Fixpoint piter (s : PSt) (n : nat) : PSt :=
  match n with
  | O => s
  | S n' => piter (psucc s) n'
  end.

Lemma piter_add : forall n1 n2 s, piter s (n1 + n2) = piter (piter s n1) n2.
Proof. induction n1 as [|n1 IH]; intros n2 s; [reflexivity | apply IH]. Qed.

Definition pcells (x : list nat) (m p : nat) : list Sym :=
  fm_pre F ++ flat_map (dig F) x ++ rep T m ++ suf p.

Definition pcfg (s : PSt) : cconf :=
  let '(x, m, p) := s in
  if fm_left F
  then (fm_st F, (pcells x m p, fm_hs F, fm_other F))
  else (fm_st F, (fm_other F, fm_hs F, pcells x m p)).

Lemma pcfg_cls : forall sd X n x m p,
  pcells x m p = sden X n sd ->
  cden (tailL F X) (tailR F X) n (cls_conf F sd) = pcfg (x, m, p).
Proof.
  intros sd X n x m p H.
  unfold cden, cls_conf, pcfg, tailL, tailR.
  destruct (fm_left F); simpl; rewrite sden_flat, app_nil_r, <- H; reflexivity.
Qed.

Hypothesis Hb : 1 < b.
Hypothesis HP : 0 < P.
Hypothesis Hz : forall p, p < P -> Forall (fun d => d < b) (z p).

Lemma nxtP_lt : forall p, p < P -> nxtP p < P.
Proof. intros p Hp. unfold nxtP. destruct (Nat.eqb_spec (S p) P); lia. Qed.

(** *** Fills recur, and the phases cycle *)

Definition PInv (s : PSt) : Prop :=
  let '(x, m, p) := s in Forall (fun d => d < b) x /\ (x <> [] \/ 0 < m) /\ p < P.

Lemma Forall_repeat0 : forall k, Forall (fun d => d < b) (repeat 0 k).
Proof. induction k as [|k IH]; constructor; [lia | exact IH]. Qed.

Lemma pfill_inv : forall k p, 0 < k -> p < P -> PInv (pfill k p).
Proof.
  intros k p Hk Hp. unfold pfill, PInv.
  destruct (kz p) eqn:Ekz.
  - split; [apply Forall_app; split; [apply Forall_repeat0 | apply Hz, Hp]|].
    split; [|apply nxtP_lt, Hp].
    left. destruct k; [lia|]. discriminate.
  - split; [apply Hz, Hp|]. split; [right; lia | apply nxtP_lt, Hp].
Qed.

Lemma psucc_inv : forall s, PInv s -> PInv (psucc s).
Proof.
  intros [[x m] p] (Hx & Hne & Hp). cbn [psucc].
  destruct (alltopK F x) eqn:Et; [destruct m as [|m]|].
  - destruct Hne as [Hne|Hne]; [|lia].
    apply pfill_inv; [destruct x; [congruence | cbn; lia] | exact Hp].
  - split; [apply inc_bndK; assumption|]. split; [left; apply inc_neK | exact Hp].
  - split; [apply inc_bndK; assumption|]. split; [left; apply inc_neK | exact Hp].
Qed.

Lemma piter_inv : forall n s, PInv s -> PInv (piter s n).
Proof. induction n as [|n IH]; intros s Hs; [exact Hs|]. apply IH, psucc_inv, Hs. Qed.

(** the top of the empty tank: [x] all-top, [m = 0] *)
Definition ptop (s : PSt) : Prop :=
  let '(x, m, p) := s in alltopK F x = true /\ m = 0.

Definition pph (s : PSt) : nat := let '(_, _, p) := s in p.

(** within a phase the top of the empty tank is reached, and the phase
    does not change on the way *)
Lemma fill_reached : forall m v x p, PInv (x, m, p) ->
  Nat.pow b (length x) - val_pos b x <= v ->
  exists n, ptop (piter (x, m, p) n) /\ PInv (piter (x, m, p) n)
            /\ pph (piter (x, m, p) n) = p.
Proof.
  induction m as [|m IHm]; intros v; induction v as [|v IHv]; intros x p Hs Hv.
  - exfalso. pose proof (val_pos_lt b x Hb (proj1 Hs)). lia.
  - destruct (alltopK F x) eqn:E.
    + exists 0. split; [split; [exact E | reflexivity]|]. split; [exact Hs | reflexivity].
    + destruct Hs as (Hx & Hne & Hp).
      assert (Hi : PInv (incK F x, 0, p))
        by (split; [apply inc_bndK; assumption | split; [left; apply inc_neK | exact Hp]]).
      destruct (IHv (incK F x) p Hi) as (n & Hn).
      * rewrite (inc_lenK F x E), (inc_valK F Hb x Hx E). lia.
      * exists (S n). cbn [piter psucc]. rewrite E. exact Hn.
  - exfalso. pose proof (val_pos_lt b x Hb (proj1 Hs)). lia.
  - destruct Hs as (Hx & Hne & Hp). destruct (alltopK F x) eqn:E.
    + (* the widening: one tank word fewer *)
      assert (Hi : PInv (incK F x, m, p))
        by (split; [apply inc_bndK; assumption | split; [left; apply inc_neK | exact Hp]]).
      destruct (IHm (Nat.pow b (length (incK F x)) - val_pos b (incK F x)) (incK F x) p Hi (le_n _))
        as (n & Hn).
      exists (S n). cbn [piter psucc]. rewrite E. exact Hn.
    + assert (Hi : PInv (incK F x, S m, p))
        by (split; [apply inc_bndK; assumption | split; [left; apply inc_neK | exact Hp]]).
      destruct (IHv (incK F x) p Hi) as (n & Hn).
      * rewrite (inc_lenK F x E), (inc_valK F Hb x Hx E). lia.
      * exists (S n). cbn [piter psucc]. rewrite E. exact Hn.
Qed.

Lemma fill_reached_s : forall s, PInv s ->
  exists n, ptop (piter s n) /\ PInv (piter s n) /\ pph (piter s n) = pph s.
Proof.
  intros [[x m] p] Hs.
  exact (fill_reached m (Nat.pow b (length x) - val_pos b x) x p Hs (le_n _)).
Qed.

Lemma psucc_top_ph : forall s, ptop s -> pph (psucc s) = nxtP (pph s).
Proof.
  intros [[x m] p] [Et Em]. subst m. cbn [psucc pph]. rewrite Et.
  unfold pfill. destruct (kz p); reflexivity.
Qed.

Fixpoint nxt_iter (d p : nat) : nat :=
  match d with O => p | S d' => nxt_iter d' (nxtP p) end.

(** after [d] fills the phase has advanced [d] times *)
Lemma fill_phase : forall d s, PInv s ->
  exists n, ptop (piter s n) /\ PInv (piter s n) /\ pph (piter s n) = nxt_iter d (pph s).
Proof.
  induction d as [|d IH]; intros s Hs.
  - exact (fill_reached_s s Hs).
  - destruct (fill_reached_s s Hs) as (n1 & Ht1 & Hi1 & Hp1).
    pose proof (psucc_inv _ Hi1) as Hi2.
    destruct (IH (psucc (piter s n1)) Hi2) as (n2 & Ht2 & Hi3 & Hp2).
    exists (n1 + S n2). rewrite piter_add. cbn [piter].
    split; [exact Ht2|]. split; [exact Hi3|].
    rewrite Hp2, (psucc_top_ph _ Ht1), Hp1. reflexivity.
Qed.

Lemma nxt_iter_mod : forall d p, p < P -> nxt_iter d p = (p + d) mod P.
Proof.
  induction d as [|d IH]; intros p Hp.
  - rewrite Nat.add_0_r, Nat.mod_small by exact Hp. reflexivity.
  - cbn [nxt_iter]. rewrite IH by (apply nxtP_lt, Hp).
    unfold nxtP. destruct (Nat.eqb_spec (S p) P) as [E|E].
    + rewrite <- E. replace (p + S d) with (d + 1 * S p) by lia.
      rewrite Nat.Div0.mod_add by lia. reflexivity.
    + replace (p + S d) with (S p + d) by lia. reflexivity.
Qed.

(** the fill of any one phase recurs past every bound *)
Theorem fill_cofinal : forall s N pt, PInv s -> pt < P ->
  exists n, N <= n /\ ptop (piter s n) /\ PInv (piter s n) /\ pph (piter s n) = pt.
Proof.
  intros s N pt Hs Hpt.
  pose proof (piter_inv N s Hs) as HsN.
  set (p := pph (piter s N)).
  assert (Hp : p < P) by (unfold p; destruct (piter s N) as [[x m] q]; exact (proj2 (proj2 HsN))).
  destruct (fill_phase (pt + P - p) (piter s N) HsN) as (n & Ht & Hi & Hph).
  exists (N + n). rewrite piter_add. split; [lia|]. split; [exact Ht|]. split; [exact Hi|].
  rewrite Hph. fold p. rewrite nxt_iter_mod by exact Hp.
  replace (p + (pt + P - p)) with (pt + 1 * P) by lia.
  rewrite Nat.Div0.mod_add, Nat.mod_small by lia. reflexivity.
Qed.

(** *** The cells of each class *)

Lemma pcells_int : forall t r st n d rest m p,
  pcells (repeat t (r + st * n) ++ d :: rest) m p
    = sden (flat_map (dig F) rest ++ rep T m ++ suf p) n
        (blk (fm_pre F ++ rep (dig F t) r) (dig F t) st (dig F d)).
Proof.
  intros t r st n d rest m p. unfold pcells.
  rewrite blk_den, flat_map_app, flat_map_repeat_nil.
  cbn [flat_map]. rewrite rep_add, !app_assoc. reflexivity.
Qed.

Lemma pcells_wid : forall t r st n m p,
  pcells (repeat t (r + st * n)) (S m) p
    = sden (rep T m ++ suf p) n (blk (fm_pre F ++ rep (dig F t) r) (dig F t) st T).
Proof.
  intros t r st n m p. unfold pcells.
  rewrite blk_den, flat_map_repeat_nil, rep_add. cbn [rep].
  rewrite !app_assoc. reflexivity.
Qed.

Lemma pcells_widened : forall r st n m p,
  pcells (repeat 0 (r + st * n) ++ [1]) m p
    = sden (rep T m ++ suf p) n
        (blk (fm_pre F ++ rep (dig F 0) r) (dig F 0) st (dig F 1)).
Proof.
  intros r st n m p. unfold pcells.
  rewrite blk_den, flat_map_app, flat_map_repeat_nil, rep_add.
  cbn [flat_map]. rewrite app_nil_r, !app_assoc. reflexivity.
Qed.

Lemma pcells_top : forall t r st n p,
  pcells (repeat t (r + st * n)) 0 p
    = sden [] n (blk (fm_pre F ++ rep (dig F t) r) (dig F t) st (suf p)).
Proof.
  intros t r st n p. unfold pcells.
  rewrite blk_den, flat_map_repeat_nil, rep_add. cbn [rep].
  rewrite !app_assoc, !app_nil_r. reflexivity.
Qed.

Lemma pcells_kept : forall r st n zz aa p,
  pcells (repeat 0 (r + st * n) ++ zz) aa p
    = sden [] n (blk (fm_pre F ++ rep (dig F 0) r) (dig F 0) st
                     (flat_map (dig F) zz ++ rep T aa ++ suf p)).
Proof.
  intros r st n zz aa p. unfold pcells.
  rewrite blk_den, flat_map_app, flat_map_repeat_nil, rep_add, !app_nil_r, !app_assoc.
  reflexivity.
Qed.

Lemma pcells_refilled : forall zz f1 st n f2 p,
  pcells zz (f1 + st * n + f2) p
    = sden [] n (blk (fm_pre F ++ flat_map (dig F) zz ++ rep T f1) T st (rep T f2 ++ suf p)).
Proof.
  intros zz f1 st n f2 p. unfold pcells.
  rewrite blk_den, !rep_add, !app_nil_r, !app_assoc. reflexivity.
Qed.

End TankPh.

(** ** 2. The board *)

Section BoardP.

Variable tm0   : TM.
Variable pins  : list Instr.
Local Notation tm := (tm_wrap_trs tm0 pins).

Variable F     : Fam.
Variable T     : list Sym.
Variable P     : nat.
Variable suf   : nat -> list Sym.
Variable kz    : nat -> bool.
Variable z     : nat -> list nat.
Variable a     : nat -> nat.
Variable AI    : nat -> nat -> LRule.   (** interior: digit, index *)
Variable N0i sti : nat.
Variable AW    : nat -> LRule.          (** widening: index (the width) *)
Variable N0w stw : nat.
Variable AR    : nat -> nat -> LRule.   (** fill: phase, index (the width) *)
Variable N0r str : nat -> nat.
Variable fm1 fm2 : nat -> nat -> nat.
Variable rsv   : list LRule.
Variable vph   : Instr -> nat.          (** the phase whose fill arms fire an instruction *)
Variable vsegs : nat -> Instr -> list nseg.
Variable visI  : nat -> Instr -> list lstep.
Variable x0    : list nat.
Variable m0 p0 : nat.

Local Notation b := (fm_b F).

Hypothesis Hb    : 1 < b.
Hypothesis HP    : 0 < P.
Hypothesis Hz    : forall p, p < P -> Forall (fun d => d < b) (z p).
Hypothesis Hinv0 : PInv F P (x0, m0, p0).

Hypothesis Hsti : 0 < sti.
Hypothesis HAIS : forall d r, d < b - 1 -> r < N0i + sti ->
  ReachL tm (negb (fm_left F)) (fm_left F) (lr_lhs (AI d r)) (lr_rhs (AI d r)).
Hypothesis HAIL : forall d r, d < b - 1 -> r < N0i + sti ->
  lr_lhs (AI d r) = cls_conf F (blk (fm_pre F ++ rep (dig F (b - 1)) r) (dig F (b - 1))
                                  (astride N0i sti r) (dig F d)).
Hypothesis HAIR : forall d r, d < b - 1 -> r < N0i + sti ->
  lr_rhs (AI d r) = cls_conf F (blk (fm_pre F ++ rep (dig F 0) r) (dig F 0)
                                  (astride N0i sti r) (dig F (S d))).

(** the widening, from every width including the empty counter *)
Hypothesis Hstw : 0 < stw.
Hypothesis HAWS : forall r, r < N0w + stw ->
  ReachL tm (negb (fm_left F)) (fm_left F) (lr_lhs (AW r)) (lr_rhs (AW r)).
Hypothesis HAWL : forall r, r < N0w + stw ->
  lr_lhs (AW r) = cls_conf F (blk (fm_pre F ++ rep (dig F (b - 1)) r)
                                (dig F (b - 1)) (astride N0w stw r) T).
Hypothesis HAWR : forall r, r < N0w + stw ->
  lr_rhs (AW r) = cls_conf F (blk (fm_pre F ++ rep (dig F 0) r)
                                (dig F 0) (astride N0w stw r) (dig F 1)).

(** the fills, one family per phase *)
Hypothesis Hstr : forall p, p < P -> 0 < str p.
Hypothesis HN0r : forall p, p < P -> 0 < N0r p.
Hypothesis HARS : forall p r, p < P -> 0 < r -> r < N0r p + str p ->
  ReachL tm true true (lr_lhs (AR p r)) (lr_rhs (AR p r)).
Hypothesis HARL : forall p r, p < P -> 0 < r -> r < N0r p + str p ->
  lr_lhs (AR p r) = cls_conf F (blk (fm_pre F ++ rep (dig F (b - 1)) r) (dig F (b - 1))
                                  (astride (N0r p) (str p) r) (suf p)).
Hypothesis HARR : forall p r, p < P -> 0 < r -> r < N0r p + str p ->
  lr_rhs (AR p r) =
    if kz p
    then cls_conf F (blk (fm_pre F ++ rep (dig F 0) r) (dig F 0) (astride (N0r p) (str p) r)
                         (flat_map (dig F) (z p) ++ rep T (a p) ++ suf (nxtP P p)))
    else cls_conf F (blk (fm_pre F ++ flat_map (dig F) (z p) ++ rep T (fm1 p r)) T
                         (astride (N0r p) (str p) r) (rep T (fm2 p r) ++ suf (nxtP P p))).
Hypothesis Hfm : forall p r, p < P -> 0 < r -> r < N0r p + str p -> kz p = false ->
  fm1 p r + fm2 p r = r + a p.

Hypothesis Hrsv : Forall (RuleSound tm false false) rsv.
(** each instruction is witnessed from every fill arm of one phase *)
Hypothesis Hvph : forall t, ~ In t pins -> vph t < P.
Hypothesis Hfire : forall t, ~ In t pins -> forall r, 0 < r -> r < N0r (vph t) + str (vph t) ->
  nfire tm true true rsv (vsegs r t) (visI r t) (lr_lhs (AR (vph t) r)) = Some t.

Local Notation Cf := (fun n => pcfg F T suf (piter F P kz z a (x0, m0, p0) n)).

Lemma board_armP : forall s, PInv F P s ->
  exists A el er X n,
    ReachL tm el er (lr_lhs A) (lr_rhs A)
    /\ (el = true -> tailL F X = []) /\ (er = true -> tailR F X = [])
    /\ pcfg F T suf s = cden (tailL F X) (tailR F X) n (lr_lhs A)
    /\ pcfg F T suf (psucc F P kz z a s) = cden (tailL F X) (tailR F X) n (lr_rhs A).
Proof.
  intros [[x m] p] (Hx & Hne & Hp).
  destruct (digs_decomp (b - 1) x) as [Htop | (n & d & rest & Hxe & Hd)].
  - set (j := length x) in Htop.
    assert (Ht : alltopK F x = true) by (rewrite Htop; apply alltop_repeatK).
    destruct m as [|m].
    + (* the fill *)
      assert (Hj : 0 < j) by (destruct Hne as [Hne|Hne]; [unfold j; destruct x; [congruence | cbn; lia] | lia]).
      pose proof (Hstr p Hp) as Hst. pose proof (HN0r p Hp) as HN0.
      remember (aoff (N0r p) (str p) j) as r eqn:Er.
      assert (Hr0 : 0 < r) by (subst r; apply arm_index_pos; assumption).
      assert (Hrlt : r < N0r p + str p) by (subst r; apply arm_index_lt; assumption).
      assert (Hk : r + astride (N0r p) (str p) r * acnt (N0r p) (str p) j = j)
        by (subst r; apply arm_index; assumption).
      exists (AR p r), true, true, [], (acnt (N0r p) (str p) j).
      split; [|split; [|split; [|split]]].
      * exact (HARS p r Hp Hr0 Hrlt).
      * intros _; apply tailL_nil.
      * intros _; apply tailR_nil.
      * rewrite (HARL p r Hp Hr0 Hrlt). symmetry. apply pcfg_cls.
        rewrite Htop, <- Hk at 1. apply pcells_top.
      * rewrite (HARR p r Hp Hr0 Hrlt). symmetry. cbn [psucc]. rewrite Ht.
        fold j. unfold pfill. destruct (kz p) eqn:Ekz.
        -- apply pcfg_cls. rewrite <- Hk at 1. apply pcells_kept.
        -- apply pcfg_cls. pose proof (Hfm p r Hp Hr0 Hrlt Ekz).
           rewrite <- (pcells_refilled F T suf (z p) (fm1 p r) (astride (N0r p) (str p) r)
                         (acnt (N0r p) (str p) j) (fm2 p r)).
           f_equal. lia.
    + (* the widening *)
      remember (aoff N0w stw j) as r eqn:Er.
      assert (Hrlt : r < N0w + stw) by (subst r; apply arm_index_lt; assumption).
      assert (Hk : r + astride N0w stw r * acnt N0w stw j = j)
        by (subst r; apply arm_index; assumption).
      exists (AW r), (negb (fm_left F)), (fm_left F), (rep T m ++ suf p), (acnt N0w stw j).
      split; [|split; [|split; [|split]]].
      * exact (HAWS r Hrlt).
      * intros He. unfold tailL. destruct (fm_left F); [discriminate|reflexivity].
      * intros He. unfold tailR. rewrite He. reflexivity.
      * rewrite (HAWL r Hrlt). symmetry. apply pcfg_cls.
        rewrite Htop, <- Hk at 1. apply pcells_wid.
      * rewrite (HAWR r Hrlt). symmetry. cbn [psucc]. rewrite Ht.
        apply pcfg_cls. rewrite Htop, (inc_topK F). fold j.
        replace (repeat 0 j ++ [1])
          with (repeat 0 (r + astride N0w stw r * acnt N0w stw j) ++ [1]) by (rewrite Hk; reflexivity).
        apply pcells_widened.
  - (* the interior *)
    rewrite Hxe in Hx.
    apply Forall_app in Hx as [_ Hrest'].
    inversion Hrest' as [|? ? Hdb Hrest].
    assert (Hdlt : d < b - 1) by lia.
    remember (aoff N0i sti n) as r eqn:Er.
    assert (Hrlt : r < N0i + sti) by (subst r; apply arm_index_lt; assumption).
    assert (Hn : r + astride N0i sti r * acnt N0i sti n = n)
      by (subst r; apply arm_index; assumption).
    exists (AI d r), (negb (fm_left F)), (fm_left F),
           (flat_map (dig F) rest ++ rep T m ++ suf p), (acnt N0i sti n).
    split; [|split; [|split; [|split]]].
    + exact (HAIS d r Hdlt Hrlt).
    + intros He. unfold tailL. destruct (fm_left F); [discriminate|reflexivity].
    + intros He. unfold tailR. rewrite He. reflexivity.
    + rewrite (HAIL d r Hdlt Hrlt). symmetry. apply pcfg_cls.
      rewrite Hxe, <- Hn at 1. apply pcells_int.
    + rewrite (HAIR d r Hdlt Hrlt). symmetry. cbn [psucc].
      rewrite Hxe, (alltop_classK F n d rest Hd), (inc_classK F n d rest Hdlt).
      apply pcfg_cls. rewrite <- Hn at 1. apply pcells_int.
Qed.

Lemma lapP : forall n, exists m c',
  0 < m /\ csteps tm m (Cf n) = Some c' /\ lift c' = lift (Cf (S n)).
Proof.
  intros n.
  assert (Hi : PInv F P (piter F P kz z a (x0, m0, p0) n)) by (eapply piter_inv; eauto).
  destruct (board_armP _ Hi) as (A & el & er & X & k & HA & HL & HR & Hl & Hr).
  destruct (HA _ _ k HL HR) as (m & c' & Hm & Hc' & Hlc).
  exists m, c'. split; [exact Hm|]. split.
  - cbn beta. rewrite Hl. exact Hc'.
  - rewrite Hlc, <- Hr. cbn beta.
    replace (S n) with (n + 1) by lia. rewrite piter_add. reflexivity.
Qed.

Lemma fireP : forall t N, ~ In t pins ->
  exists n k c', N <= n /\ csteps tm k (Cf n) = Some c' /\ cinstr c' = t.
Proof.
  intros t N Hnp.
  set (pt := vph t).
  assert (Hpt : pt < P) by (apply Hvph, Hnp).
  assert (Hc : exists n, N <= n /\ ptop F (piter F P kz z a (x0, m0, p0) n)
                /\ PInv F P (piter F P kz z a (x0, m0, p0) n)
                /\ pph (piter F P kz z a (x0, m0, p0) n) = pt)
    by (eapply fill_cofinal; eauto).
  destruct Hc as (n & HN & Htp & Hi & Hph).
  exists n.
  destruct (piter F P kz z a (x0, m0, p0) n) as [[x m] p] eqn:Eit.
  destruct Htp as [Htop Hm]. cbn [pph] in Hph. subst m p.
  destruct Hi as (_ & Hne & _).
  destruct (digs_decomp (b - 1) x) as [Hx | (n' & d & rest & Hxe & Hd)].
  2:{ exfalso. rewrite Hxe, (alltop_classK F n' d rest Hd) in Htop. discriminate. }
  set (j := length x) in Hx.
  assert (Hj : 0 < j) by (destruct Hne as [Hne|Hne]; [unfold j; destruct x; [congruence | cbn; lia] | lia]).
  pose proof (Hstr pt Hpt) as Hst. pose proof (HN0r pt Hpt) as HN0.
  remember (aoff (N0r pt) (str pt) j) as r eqn:Er.
  assert (Hr0 : 0 < r) by (subst r; apply arm_index_pos; assumption).
  assert (Hrlt : r < N0r pt + str pt) by (subst r; apply arm_index_lt; assumption).
  assert (Hk : r + astride (N0r pt) (str pt) r * acnt (N0r pt) (str pt) j = j)
    by (subst r; apply arm_index; assumption).
  assert (Hden : pcfg F T suf (x, 0, pt) = cden [] [] (acnt (N0r pt) (str pt) j) (lr_lhs (AR pt r))).
  { rewrite (HARL pt r Hpt Hr0 Hrlt).
    rewrite <- (pcfg_cls F T suf (blk (fm_pre F ++ rep (dig F (b - 1)) r) (dig F (b - 1))
                                (astride (N0r pt) (str pt) r) (suf pt)) [] (acnt (N0r pt) (str pt) j) x 0 pt).
    - unfold tailL, tailR; destruct (fm_left F); reflexivity.
    - rewrite Hx, <- Hk at 1. apply pcells_top. }
  destruct (nfire_sound tm true true rsv (vsegs r t) (visI r t)
              (lr_lhs (AR pt r)) t Hrsv (Hfire t Hnp r Hr0 Hrlt)
              [] [] (acnt (N0r pt) (str pt) j)
              (fun _ => eq_refl) (fun _ => eq_refl)) as (k & c' & Hc' & Ht).
  exists k, c'. cbn beta. rewrite ?Eit, Hden.
  split; [exact HN | split; [exact Hc' | exact Ht]].
Qed.

Theorem boardP_neverqhtr : forall t0,
  stepn tm t0 InitES = Some (lift (pcfg F T suf (x0, m0, p0))) ->
  NeverQuasiHaltsTr tm0.
Proof.
  intros t0 Hboot.
  apply (glue_neverqhtrN tm0 pins Cf).
  - exists t0. exact Hboot.
  - intros n. destruct (lapP n) as (m & c' & Hm & Hrun & Hl).
    exists m, c'. split; [exact Hrun | split; [exact Hl | exact Hm]].
  - intros t Hnp N. exact (fireP t N Hnp).
Qed.

Lemma reachP : forall d n,
  exists Tm, stepn tm Tm (lift (Cf n)) = Some (lift (Cf (n + d))).
Proof.
  induction d; intros n.
  - exists 0. rewrite Nat.add_0_r. reflexivity.
  - destruct (IHd n) as (Tm & HT).
    destruct (lapP (n + d)) as (m & c' & _ & Hm & Hl).
    exists (Tm + m). rewrite stepn_add, HT.
    replace (n + S d) with (S (n + d)) by lia.
    rewrite <- Hl. apply csteps_lift. exact Hm.
Qed.

Lemma fire_everyP : forall t, ~ In t pins -> forall n,
  exists k c', csteps tm k (Cf n) = Some c' /\ cinstr c' = t.
Proof.
  intros t Hnp n.
  destruct (fireP t n Hnp) as (m & k & c' & Hm & Hk & Hc').
  destruct (reachP (m - n) n) as (Tm & HT).
  replace (n + (m - n)) with m in HT by lia.
  assert (Hs : stepn tm (Tm + k) (lift (Cf n)) = Some (lift c')).
  { rewrite stepn_add, HT. apply csteps_lift. exact Hk. }
  destruct (stepn_csteps_at tm (Tm + k) (Cf n) (lift c') Hs) as (c'' & Hc'' & Hl').
  exists (Tm + k), c''. split; [exact Hc''|].
  rewrite <- cinstr_lift, Hl', cinstr_lift. exact Hc'.
Qed.

Theorem boardP_qhtr : forall t0 B,
  stepn tm0 t0 InitES = Some (lift (pcfg F T suf (x0, m0, p0))) ->
  existsb (fun tg => cfires tm0 CTape.c0 t0 tg) pins = true ->
  (t0 <=? B) = true ->
  NonHalt tm0 /\ QHBoundTr B tm0 /\ QuasiHaltsTr tm0.
Proof.
  intros t0 B Hboot Hwit Hle.
  apply (lap_qh_stage tm0 pins (fun p => Cf (Nat.pred (Pos.to_nat p)))
           1%positive t0 B).
  - exact Hboot.
  - intros p _.
    destruct (lapP (Nat.pred (Pos.to_nat p))) as (m & c' & Hm & Hrun & Hl).
    exists m, c'. split; [exact Hrun | split; [|exact Hm]].
    rewrite Hl, Pos2Nat.inj_succ.
    replace (S (Nat.pred (Pos.to_nat p))) with (Pos.to_nat p)
      by (pose proof (Pos2Nat.is_pos p); lia).
    reflexivity.
  - intros t Hnp p _. exact (fire_everyP t Hnp (Nat.pred (Pos.to_nat p))).
  - exact Hwit.
  - exact Hle.
Qed.

End BoardP.
