(** * Checkers.LadderFam: the value family, with its SUCCESSOR as data.

    LADDER_PLAN.md 4f closed Stage B's last open question by making the
    successor a PARAMETER of the family rather than a fixed law.  This file
    is that parameter, and nothing else: a [Fam] record carrying

    - the digit alphabet and the near-head prefix (4d);
    - the FILL LAW, one per phase: the top string of width [k] goes to
      [pre ++ mid^n ++ suf] at width [k + s], landing in phase [f_to] (4e/4f);
    - the terminator of each PHASE, the phase being part of the counter's
      state exactly like the width (4f);
    - the CODE the digit string is read in -- positional or reflected --
      and the value STEP per anchor visit (4g),

    and a successor [fam_succ] COMPUTED from them.  Four times running the
    missing constructor turned out to be a hard-coded assumption about the
    counter's own arithmetic (the carry, the anchor, the base, the
    terminator); the discipline here is that none of those is written into a
    definition.  The next constructor -- 4f's residue names it, a terminator
    run template [word^m] -- is a change to this record, not to the kernel
    that consumes it.

    Nothing in this file is trusted: every field is re-checked downstream by
    [LadderCheck], and a wrong field makes the checker return [false] rather
    than a wrong theorem. *)

From Coq Require Import Arith Lia Bool List.
From BBB4 Require Import BBB4_Statement CTape.
Import ListNotations.

(** ** The reflected (Gray) code

    The general base-[b] reflected code: decoding is a running sum down the
    digit string, encoding the difference to the next digit up.  At [b = 2]
    both collapse to the XOR chain.  Digit strings are LSB-first, so
    [gdec]'s value at index [i] is the sum of digits [i..] modulo [b]. *)

Fixpoint gdec (b : nat) (ds : list nat) : list nat :=
  match ds with
  | [] => []
  | d :: t => let r := gdec b t in ((d + hd 0 r) mod b) :: r
  end.

Fixpoint genc (b : nat) (ns : list nat) : list nat :=
  match ns with
  | [] => []
  | n :: t => ((n mod b + (b - (hd 0 t) mod b)) mod b) :: genc b t
  end.

Lemma gdec_length : forall b ds, length (gdec b ds) = length ds.
Proof. induction ds; simpl; auto. Qed.

Lemma genc_length : forall b ns, length (genc b ns) = length ns.
Proof. induction ns; simpl; auto. Qed.

(** ** Positional values *)

Fixpoint val_pos (b : nat) (ds : list nat) : nat :=
  match ds with
  | [] => 0
  | d :: t => d + b * val_pos b t
  end.

Fixpoint pos_of (b k : nat) (v : nat) : list nat :=
  match k with
  | O => []
  | S k' => (v mod b) :: pos_of b k' (v / b)
  end.

Lemma pos_of_length : forall b k v, length (pos_of b k v) = k.
Proof. induction k; intro v; simpl; auto. Qed.

(** ** The fill law

    [E(p, b^p - 1) -> E(p + s, pre ++ mid^n ++ suf)], landing in phase
    [f_to].  A one-phase family fills back into itself ([f_to = 0]), which
    is what every row closed before 4f does; a multi-phase counter laps once
    per terminator, so its phase-0 fill lands in phase 1 without widening at
    all and only the last phase's fill moves the width. *)

Record Fill : Set := mkFill {
  f_s   : nat;          (** widens by *)
  f_pre : list nat;     (** target prefix digits *)
  f_mid : nat;          (** the fill digit *)
  f_suf : list nat;     (** target suffix digits *)
  f_to  : nat           (** the phase the fill lands in *)
}.

(** The odometer carry, kept only as the DEFAULT for a family whose law was
    never fitted -- it is one law among fourteen, not the law. *)
Definition carry_fill : Fill := mkFill 1 [] 0 [1] 0.

Definition fill_apply (f : Fill) (k : nat) : option (list nat) :=
  let w := k + f_s f in
  let m := length (f_pre f) + length (f_suf f) in
  if m <=? w
  then Some (f_pre f ++ repeat (f_mid f) (w - m) ++ f_suf f)
  else None.

Lemma fill_apply_length : forall f k t,
  fill_apply f k = Some t -> length t = k + f_s f.
Proof.
  intros f k t H. unfold fill_apply in H.
  destruct (Nat.leb_spec (length (f_pre f) + length (f_suf f)) (k + f_s f));
    [|discriminate].
  injection H as <-.
  rewrite !app_length, repeat_length. lia.
Qed.

(** ** The FIBONACCI numeration

    LADDER_PLAN.md 4p measured five core rows whose counter is not positional
    at all: the digit at index [i] carries weight [1, 1, 2, 3, 5, 8, ...].
    The weights are DETERMINED by the position, so they are computed here
    rather than carried as a field -- no [mkFam] call and no board data
    changes, which is the whole reason this is a [Code] constructor.

    The numeration is REDUNDANT ([fibw 0 = fibw 1 = 1], so [1;0;0] and
    [0;1;0] both have value 1), and which representative the counter stands
    on is a MEMBERSHIP predicate, not an arithmetic fact.  That predicate
    lives in [LadderCheck] (section 3c) with the class laws it discriminates;
    what is here is the arithmetic it is a predicate over: the weights, the
    weighted fold, and the DECODER that inverts it. *)

Fixpoint fibw (i : nat) : nat :=
  match i with
  | O => 1
  | S n => match n with
           | O => 1
           | S j => fibw n + fibw j
           end
  end.

Lemma fibw_SS : forall j, fibw (S (S j)) = fibw (S j) + fibw j.
Proof. reflexivity. Qed.

Lemma fibw_pos2 : forall i, 0 < fibw i /\ 0 < fibw (S i).
Proof.
  induction i as [|i IH]; [cbn; lia|].
  destruct IH as [H1 H2]. split; [exact H2 | rewrite fibw_SS; lia].
Qed.

Lemma fibw_pos : forall i, 0 < fibw i.
Proof. intros i. apply (fibw_pos2 i). Qed.

Lemma fibw_mono : forall i, fibw i <= fibw (S i).
Proof.
  destruct i as [|i]; [cbn; lia|].
  rewrite fibw_SS. pose proof (fibw_pos i). lia.
Qed.

(** The largest value a width can spell: the sum of the weights it covers.
    This is what [b^k - 1] was, and it is NOT a power of anything --
    [fibsum] telescopes into the NEXT weight, which is the one identity the
    whole numeration rests on. *)
Fixpoint fibsum (k : nat) : nat :=
  match k with
  | O => 0
  | S k' => fibsum k' + fibw k'
  end.

Lemma fibsum_S : forall k, S (fibsum k) = fibw (S k).
Proof.
  induction k as [|k IH]; [reflexivity|].
  cbn [fibsum]. rewrite fibw_SS, <- IH. lia.
Qed.

Lemma fibsum_mono : forall k, fibsum k <= fibsum (S k).
Proof. intros k. cbn [fibsum]. lia. Qed.

(** The weighted fold, LSB-first, from weight index [j] up. *)
Fixpoint fibvl (j : nat) (ds : list nat) : nat :=
  match ds with
  | [] => 0
  | d :: t => d * fibw j + fibvl (S j) t
  end.

Definition fibval (ds : list nat) : nat := fibvl 0 ds.

Lemma fibvl_app : forall a j b,
  fibvl j (a ++ b) = fibvl j a + fibvl (j + length a) b.
Proof.
  induction a as [|x a IH]; intros j b; cbn [app fibvl length].
  - rewrite Nat.add_0_r. reflexivity.
  - rewrite IH. replace (S j + length a) with (j + S (length a)) by lia. lia.
Qed.

(** The one instance the induction on the WIDTH uses: the top digit sits at
    weight index [length a], and everything below it is untouched. *)
Lemma fibval_snoc : forall a d,
  fibval (a ++ [d]) = fibval a + d * fibw (length a).
Proof.
  intros a d. unfold fibval. rewrite fibvl_app. cbn [fibvl].
  rewrite Nat.add_0_l, Nat.add_0_r. reflexivity.
Qed.

Lemma fibval_app : forall a b,
  fibval (a ++ b) = fibval a + fibvl (length a) b.
Proof. intros a b. unfold fibval. rewrite fibvl_app. reflexivity. Qed.

(** *** The decoder, and the two-state reading that makes it one

    Read MSB-first, a member is accepted by a TWO-STATE automaton: from [E]
    a [0] stays in [E] and a [1] goes to [O]; from [O] the next digit must be
    a [1], which returns to [E]; both states accept at the end (the leading
    run of [1]s -- the one that reaches index 0 -- is the one run allowed to
    be odd).  [o] is that state.

    What makes the decode DETERMINISTIC is that each state's reachable values
    are an INTERVAL and the two the top digit selects between are disjoint:
    from [E] at width [k] the values are [0 .. fibsum k], split by the top
    digit at exactly [fibw k] -- because [fibsum (k-1) + 1 = fibw k], which
    is [fibsum_S].  From [O] the top digit is forced. *)
Definition fiblo (o : bool) (k : nat) : nat :=
  if o then match k with O => 0 | S k' => fibw k' end else 0.

(** State [O]'s floor at width [k], plus the top digit's own weight, is at
    least the weight the decode tests against.  This is the whole reason the
    [1] branch is FORCED when the value is at or above [fibw k] -- and with
    it the round trip needs no case split on [k]. *)
Lemma fiblo_fibw : forall k, fibw (S k) <= fiblo true k + fibw k.
Proof.
  destruct k as [|k]; cbn [fiblo]; [cbn [fibw]; lia|].
  rewrite fibw_SS. lia.
Qed.

Fixpoint fibdec (k : nat) (o : bool) (v : nat) : list nat :=
  match k with
  | O => []
  | S k' => if o || (fibw (S k') <=? v)
            then fibdec k' (negb o) (v - fibw k') ++ [1]
            else fibdec k' false v ++ [0]
  end.

Lemma fibdec_length : forall k o v, length (fibdec k o v) = k.
Proof.
  induction k as [|k IH]; intros o v; [reflexivity|].
  cbn [fibdec]. destruct (o || _);
    rewrite app_length, IH; cbn [length]; lia.
Qed.

Lemma fibdec_bnd : forall k o v, Forall (fun d => d < 2) (fibdec k o v).
Proof.
  induction k as [|k IH]; intros o v; [constructor|].
  cbn [fibdec]. destruct (o || _); apply Forall_app; split;
    solve [apply IH | repeat constructor; lia].
Qed.

(** The decode is a right inverse of the fold on the whole of each state's
    interval.  This is the half that does not need membership at all -- only
    the RANGE -- and it is what [fam_value_of_value] becomes at [Fib]. *)
Lemma fibdec_val : forall k o v,
  fiblo o k <= v -> v <= fibsum k -> fibval (fibdec k o v) = v.
Proof.
  induction k as [|k IH]; intros o v Hlo Hhi.
  - cbn [fibsum] in Hhi. cbn [fibdec]. unfold fibval. cbn [fibvl]. lia.
  - pose proof (fibsum_S k) as Hss.
    pose proof (fibw_mono k) as Hmo.
    cbn [fibsum] in Hhi. cbn [fibdec].
    destruct (o || (fibw (S k) <=? v)) eqn:Eb.
    + (* the top digit is 1: subtract its weight and read on *)
      assert (Hge : fibw k <= v).
      { destruct o; [cbn [fiblo] in Hlo; exact Hlo|].
        cbn [orb] in Eb. apply Nat.leb_le in Eb. lia. }
      assert (Hlo' : fiblo (negb o) k <= v - fibw k).
      { destruct o; cbn [negb fiblo]; [lia|].
        destruct k as [|k']; [lia|].
        cbn [orb] in Eb. apply Nat.leb_le in Eb.
        rewrite fibw_SS in Eb. lia. }
      rewrite fibval_snoc, fibdec_length,
              (IH (negb o) (v - fibw k) Hlo' ltac:(lia)).
      lia.
    + (* the top digit is 0: the value is below the next weight, hence
         inside the narrower width *)
      apply orb_false_elim in Eb as [Eo Et].
      apply Nat.leb_gt in Et. subst o.
      rewrite fibval_snoc, fibdec_length,
              (IH false v ltac:(cbn [fiblo]; lia) ltac:(lia)).
      lia.
Qed.

(** ** The LAZY representative of the same numeration

    LADDER_PLAN.md 4v/4w measured six more core rows against [fibw] and found
    every number of the numeration already right and one thing wrong: the
    CANONICAL FORM.  [fibw] is redundant ([fibw 0 = fibw 1]), so a value does
    not determine a string, and [fibdec] picks the GREEDY representative --
    "every maximal run of [1]s has even length except the one that reaches
    index 0".  Those six rows stand on the other end of the redundancy, the
    LAZY (maximal) one:

      LSB-first, [d0 = 1], NO TWO ZEROS ADJACENT, and the top digit [1].

    Two routes measured it independently: 4v reads it off 23,614 values per
    row (the machine's string equals [fibdec] on 651 of them and satisfies
    the predicate above on all 23,614), and 4w counts membership at every
    anchor (324 of 4,000 against [fibokb], 4,000 of 4,000 against "no 00",
    with 4r's five boarded rows the exact complement).

    Nothing about the arithmetic moves -- not [fibw], not [fibsum], not
    [fam_lim].  What is here is the second DECODER, and its two-state reading
    is [fibdec]'s with the transitions swapped: from a [1] the next digit
    down is free, from a [0] it is forced to be [1].  (In [fibdec] a [1]
    forces a [1].)  Read MSB-first, [o] is "this digit is forced to be [1]".

    What makes the decode deterministic is again that each state's reachable
    values are an INTERVAL, and here the two intervals are

      [o = true]  (the top digit is 1)   [fibw k    .. fibsum k]
      [o = false] (the top digit is free) [fibwp k  .. fibsum k]

    with the top digit splitting the free state at exactly [fibw k] -- the
    same [fibsum_S] that makes [fibdec] deterministic, used at the other
    branch.  The FLOOR is what is new: unlike every earlier code, a width
    does not spell every value below its ceiling, so [fam_of_value] needs a
    lower guard as well ([fam_lo]). *)

(** The weight one place DOWN, with [0] at the bottom.  [fibwp k + fibw k =
    fibw (S k)] is [fibw_SS] made total, and it is the only identity the lazy
    decode needs beyond [fibsum_S]. *)
Definition fibwp (k : nat) : nat := match k with O => 0 | S k' => fibw k' end.

Lemma fibwp_fibw : forall k, fibwp k + fibw k = fibw (S k).
Proof. destruct k as [|k]; cbn [fibwp]; [reflexivity | rewrite fibw_SS; lia]. Qed.

Lemma fibwp_le : forall k, fibwp k <= fibw k.
Proof.
  destruct k as [|k]; cbn [fibwp]; [lia | apply fibw_mono].
Qed.

Definition lazlo (o : bool) (k : nat) : nat := if o then fibw k else fibwp k.

Fixpoint fiblaz (k : nat) (o : bool) (v : nat) : list nat :=
  match k with
  | O => []
  | S k' => if o || (fibw (S k') <=? v)
            then fiblaz k' false (v - fibw k') ++ [1]
            else fiblaz k' true v ++ [0]
  end.

Lemma fiblaz_length : forall k o v, length (fiblaz k o v) = k.
Proof.
  induction k as [|k IH]; intros o v; [reflexivity|].
  cbn [fiblaz]. destruct (o || _);
    rewrite app_length, IH; cbn [length]; lia.
Qed.

Lemma fiblaz_bnd : forall k o v, Forall (fun d => d < 2) (fiblaz k o v).
Proof.
  induction k as [|k IH]; intros o v; [constructor|].
  cbn [fiblaz]. destruct (o || _); apply Forall_app; split;
    solve [apply IH | repeat constructor; lia].
Qed.

(** The decode is a right inverse of the fold on the whole of each state's
    interval -- the half that needs the RANGE and not membership. *)
Lemma fiblaz_val : forall k o v,
  lazlo o k <= v -> v <= fibsum k -> fibval (fiblaz k o v) = v.
Proof.
  induction k as [|k IH]; intros o v Hlo Hhi.
  - cbn [fibsum] in Hhi. cbn [fiblaz]. unfold fibval. cbn [fibvl].
    destruct o; cbn [lazlo fibw fibwp] in Hlo; lia.
  - pose proof (fibsum_S k) as Hss.
    pose proof (fibwp_fibw k) as Hwp.
    cbn [fibsum] in Hhi. cbn [fiblaz].
    destruct (o || (fibw (S k) <=? v)) eqn:Eb.
    + (* the top digit is 1: forced, or chosen because the value is high *)
      assert (Hge : fibw (S k) <= v).
      { destruct o; [cbn [lazlo] in Hlo; exact Hlo|].
        cbn [orb] in Eb. apply Nat.leb_le in Eb. exact Eb. }
      rewrite fibval_snoc, fiblaz_length,
              (IH false (v - fibw k) ltac:(cbn [lazlo]; lia) ltac:(lia)).
      lia.
    + (* the top digit is 0: the value is below the next weight, and the
         digit below it is then FORCED to be 1 *)
      apply orb_false_elim in Eb as [Eo Et].
      apply Nat.leb_gt in Et. subst o.
      cbn [lazlo fibwp] in Hlo.
      rewrite fibval_snoc, fiblaz_length,
              (IH true v ltac:(cbn [lazlo]; lia) ltac:(lia)).
      lia.
Qed.

(** ** Word runs

    The lazy increment sends a run of [1]s to an ALTERNATING run, so the
    repeated unit of a class is a digit WORD rather than a digit.  [wrep] is
    that run; it is [rep]'s shape one level up, and [flat_map] carries it to
    [rep] because [rep] already takes a word. *)

Fixpoint wrep (u : list nat) (n : nat) : list nat :=
  match n with
  | O => []
  | S m => u ++ wrep u m
  end.

Lemma wrep_add : forall u j k, wrep u (j + k) = wrep u j ++ wrep u k.
Proof.
  induction j as [|j IH]; intros k; simpl; [reflexivity|].
  rewrite IH, app_assoc. reflexivity.
Qed.

Lemma wrep_snoc : forall u n, wrep u (S n) = wrep u n ++ u.
Proof.
  intros u n. replace (S n) with (n + 1) by lia.
  rewrite wrep_add. cbn [wrep]. rewrite app_nil_r. reflexivity.
Qed.

Lemma wrep_length : forall u n, length (wrep u n) = n * length u.
Proof.
  induction n as [|n IH]; simpl; [reflexivity|].
  rewrite app_length, IH. lia.
Qed.

Lemma wrep_single : forall d n, wrep [d] n = repeat d n.
Proof. induction n as [|n IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma wrep_bnd : forall b u n,
  Forall (fun d => d < b) u -> Forall (fun d => d < b) (wrep u n).
Proof.
  intros b u n H. induction n as [|n IH]; simpl; [constructor|].
  apply Forall_app. split; assumption.
Qed.

(** The two run values the lazy classes need.  [wrep [1;0] n] is the
    alternating run the increment leaves behind, and both identities are the
    same telescoping [fibw_SS] read at the two parities. *)
Lemma wrep10_val0 : forall n, fibval (wrep [1;0] n) = fibwp (2 * n).
Proof.
  induction n as [|n IH]; [reflexivity|].
  rewrite wrep_snoc, fibval_app, wrep_length, IH.
  cbn [length fibvl fibw].
  replace (n * 2) with (2 * n) by lia.
  replace (2 * S n) with (S (S (2 * n))) by lia.
  cbn [fibwp]. destruct (2 * n) as [|m] eqn:E; cbn [fibwp].
  - cbn [fibw]. lia.
  - rewrite fibw_SS. cbn [fibwp]. lia.
Qed.

Lemma wrep10_val1 : forall n, S (fibvl 1 (wrep [1;0] n)) = fibw (2 * n).
Proof.
  induction n as [|n IH]; [reflexivity|].
  rewrite wrep_snoc, fibvl_app, wrep_length.
  cbn [length fibvl].
  replace (1 + n * 2) with (S (2 * n)) by lia.
  replace (2 * S n) with (S (S (2 * n))) by lia.
  rewrite fibw_SS. lia.
Qed.

(** The FILL at the lazy representative: the top of a width is [1^k] and its
    successor is the SMALLEST string of width [k + 1], which is the
    alternating one.  Its two parities are the two [Fill] laws 4v measured,
    and stating it as a function of the width is what keeps the family
    ONE-PHASE: [Fill]'s [f_mid] is a digit, so a [Fill] record cannot spell
    an alternating run at all, and a phase per parity would be the only other
    way to select between them. *)
Definition lazfill (k : nat) : list nat :=
  if Nat.even k
  then wrep [1;0] (Nat.div2 k) ++ [1]
  else 1 :: wrep [1;0] (Nat.div2 k) ++ [1].

Lemma lazfill_length : forall k, length (lazfill k) = S k.
Proof.
  intros k. unfold lazfill.
  pose proof (Nat.div2_odd k) as Hd.
  destruct (Nat.even k) eqn:E.
  - rewrite app_length, wrep_length. cbn [length].
    apply (f_equal negb) in E. rewrite Nat.negb_even in E. cbn [negb] in E.
    rewrite E in Hd. cbn [Nat.b2n] in Hd. lia.
  - cbn [length]. rewrite app_length, wrep_length. cbn [length].
    apply (f_equal negb) in E. rewrite Nat.negb_even in E. cbn [negb] in E.
    rewrite E in Hd. cbn [Nat.b2n] in Hd. lia.
Qed.

Lemma lazfill_bnd : forall k, Forall (fun d => d < 2) (lazfill k).
Proof.
  intros k. unfold lazfill.
  assert (Hw : Forall (fun d => d < 2) (wrep [1;0] (Nat.div2 k)))
    by (apply wrep_bnd; repeat constructor; lia).
  destruct (Nat.even k);
    [apply Forall_app; split; [exact Hw | repeat constructor; lia]
    |constructor; [lia | apply Forall_app; split;
                        [exact Hw | repeat constructor; lia]]].
Qed.

(** ** The code and the family *)

Inductive Code : Set := Binary | Gray | Fib | FibL.

Record Fam : Set := mkFam {
  fm_b     : nat;              (** base *)
  fm_digs  : list (list Sym);  (** digit words, index = digit value *)
  fm_pre   : list Sym;         (** near-head prefix cells *)
  fm_tails : list (list Sym);  (** the terminator of each phase *)
  fm_code  : Code;             (** positional or reflected *)
  fm_step  : nat;              (** value step per anchor visit *)
  fm_fills : list Fill;        (** one fill law per phase *)
  fm_st    : St;               (** the anchor *)
  fm_hs    : Sym;
  fm_left  : bool;             (** is the counter the LEFT side? *)
  fm_other : list Sym          (** the far side *)
}.

Definition fam_value (F : Fam) (ds : list nat) : nat :=
  match fm_code F with
  | Binary => val_pos (fm_b F) ds
  | Gray => val_pos (fm_b F) (gdec (fm_b F) ds)
  | Fib | FibL => fibval ds
  end.

(** The width's CEILING: one past the largest value it can spell.  For a
    positional or reflected code that is [b^k]; for [Fib] it is
    [S (fibsum k)], which is not a power of anything.  It is the ONE thing a
    weighted numeration changes about the interface, and naming it here is
    what keeps [fam_is_top], [fam_of_value] and the liveness measure one
    definition each rather than one per code. *)
Definition fam_lim (F : Fam) (k : nat) : nat :=
  match fm_code F with
  | Fib | FibL => S (fibsum k)
  | _ => Nat.pow (fm_b F) k
  end.

(** The width's FLOOR.  Every code but [FibL] spells every value below its
    ceiling, so the floor is [0] and [fam_of_value]'s guard is the ceiling
    alone; the lazy representative of width [k] spells exactly
    [fibw k .. fibsum k], and without the lower guard [fam_of_value] would
    return a string whose value is not the one asked for. *)
Definition fam_lo (F : Fam) (k : nat) : nat :=
  match fm_code F with
  | FibL => fibw k
  | _ => 0
  end.

Lemma fam_lo_bin : forall F k, fm_code F = Binary -> fam_lo F k = 0.
Proof. intros F k H. unfold fam_lo. rewrite H. reflexivity. Qed.

Lemma fam_lo_gray : forall F k, fm_code F = Gray -> fam_lo F k = 0.
Proof. intros F k H. unfold fam_lo. rewrite H. reflexivity. Qed.

Lemma fam_lo_fib : forall F k, fm_code F = Fib -> fam_lo F k = 0.
Proof. intros F k H. unfold fam_lo. rewrite H. reflexivity. Qed.

Lemma fam_lo_fibl : forall F k, fm_code F = FibL -> fam_lo F k = fibw k.
Proof. intros F k H. unfold fam_lo. rewrite H. reflexivity. Qed.

Lemma fam_lim_bin : forall F k,
  fm_code F = Binary -> fam_lim F k = Nat.pow (fm_b F) k.
Proof. intros F k H. unfold fam_lim. rewrite H. reflexivity. Qed.

Lemma fam_lim_gray : forall F k,
  fm_code F = Gray -> fam_lim F k = Nat.pow (fm_b F) k.
Proof. intros F k H. unfold fam_lim. rewrite H. reflexivity. Qed.

Lemma fam_lim_fib : forall F k,
  fm_code F = Fib -> fam_lim F k = S (fibsum k).
Proof. intros F k H. unfold fam_lim. rewrite H. reflexivity. Qed.

Lemma fam_lim_fibl : forall F k,
  fm_code F = FibL -> fam_lim F k = S (fibsum k).
Proof. intros F k H. unfold fam_lim. rewrite H. reflexivity. Qed.

Definition fam_of_value (F : Fam) (v k : nat) : option (list nat) :=
  if (fam_lo F k <=? v) && (v <? fam_lim F k) then
    let ns := pos_of (fm_b F) k v in
    Some (match fm_code F with
          | Binary => ns
          | Gray => genc (fm_b F) ns
          | Fib => fibdec k false v
          | FibL => fiblaz k true v
          end)
  else None.

Lemma fam_of_value_length : forall F v k ds,
  fam_of_value F v k = Some ds -> length ds = k.
Proof.
  intros F v k ds H. unfold fam_of_value in H.
  destruct ((fam_lo F k <=? v) && (v <? fam_lim F k)); [|discriminate].
  destruct (fm_code F); injection H as <-;
    [apply pos_of_length | rewrite genc_length; apply pos_of_length
     | apply fibdec_length | apply fiblaz_length].
Qed.

(** The width-[k] string the fill leaves from.  For [Binary] with step 1
    this is the all-max string, which is what the law used to test for
    directly; for a reflected code it is not the all-max string at all,
    which is why the test below is on the VALUE. *)
Definition fam_top (F : Fam) (k : nat) : option (list nat) :=
  fam_of_value F (fam_lim F k - 1) k.

Definition fam_is_top (F : Fam) (ds : list nat) : bool :=
  fam_lim F (length ds) - 1 <? fam_value F ds + fm_step F.

Definition fam_fill (F : Fam) (ph : nat) : Fill :=
  nth ph (fm_fills F) carry_fill.

(** The successor inside a width, and the phase's FILL LAW at the top.
    Stated on the VALUE rather than as a digit-wise carry ripple, so it is
    right for any code the family reads in and any step it advances by. *)
Definition fam_next (F : Fam) (ds : list nat) (ph : nat) : option (list nat) :=
  if fam_is_top F ds
  then match fm_code F with
       | FibL => Some (lazfill (length ds))
       | _ => fill_apply (fam_fill F ph) (length ds)
       end
  else fam_of_value F (fam_value F ds + fm_step F) (length ds).

Lemma fam_next_fill : forall F ds ph,
  fm_code F <> FibL -> fam_is_top F ds = true ->
  fam_next F ds ph = fill_apply (fam_fill F ph) (length ds).
Proof.
  intros F ds ph Hc Htop. unfold fam_next. rewrite Htop.
  destruct (fm_code F); congruence.
Qed.

(** The counter's state: the digit string, the outer parameter, the PHASE.
    The interior arms never touch the last two -- that is the whole
    discipline -- and the fill is the only arm that crosses either. *)
Definition CtrSt : Set := (list nat * nat * nat)%type.

Definition fam_succ (F : Fam) (s : CtrSt) : option CtrSt :=
  let '(ds, p, ph) := s in
  match fam_next F ds ph with
  | None => None
  | Some nd =>
      if fam_is_top F ds
      then Some (nd, p, f_to (fam_fill F ph))
      else Some (nd, p, ph)
  end.

(** ** Denotation

    Cells are NOT stripped of trailing blanks here: a lap's SOURCE has to be
    matched exactly by an arm, and its target is compared up to [lift]
    ([CTape.lift] ignores trailing blanks), which is the same contract
    [LapDecider.lap_of_run] already uses for the overflow lap. *)

Definition fam_cells (F : Fam) (ds : list nat) (ph : nat) : list Sym :=
  fm_pre F ++ flat_map (fun d => nth d (fm_digs F) []) ds
          ++ nth ph (fm_tails F) [].

Definition fam_cfg (F : Fam) (s : CtrSt) : cconf :=
  let '(ds, _, ph) := s in
  if fm_left F
  then (fm_st F, (fam_cells F ds ph, fm_hs F, fm_other F))
  else (fm_st F, (fm_other F, fm_hs F, fam_cells F ds ph)).

(** ** Iterating the successor

    The anchor family the closer consumes: [fam_iter F s0 k] is the counter's
    state at its [k]-th anchor visit. *)

Fixpoint fam_iter (F : Fam) (s : CtrSt) (k : nat) : option CtrSt :=
  match k with
  | O => Some s
  | S k' => match fam_succ F s with
            | None => None
            | Some s' => fam_iter F s' k'
            end
  end.

Lemma fam_iter_add : forall F k1 k2 s,
  fam_iter F s (k1 + k2) =
  match fam_iter F s k1 with
  | None => None
  | Some s1 => fam_iter F s1 k2
  end.
Proof.
  induction k1 as [|k1 IH]; intros k2 s; simpl; [reflexivity|].
  destruct (fam_succ F s) as [s'|]; [apply IH | reflexivity].
Qed.

(** ** The width grows without bound

    The one arithmetic fact liveness needs.  Within a width the value
    strictly increases by [fm_step], and it is bounded by [b^k - 1]; so the
    top of a width is reached after finitely many visits, and the fill fires
    there.  This is what makes "the arms taken infinitely often" a
    THEOREM about the fill arm rather than an assertion of the certificate. *)

Definition fam_wf (F : Fam) (s : CtrSt) : Prop :=
  let '(ds, _, _) := s in fam_value F ds < fam_lim F (length ds).

(** The codec round-trip, for both codes.  [genc] and [gdec] are inverse
    because [gdec]'s entry [i] is the suffix sum of [genc]'s entries from
    [i] up, and the sum telescopes. *)

Lemma val_pos_pos_of : forall b k v,
  1 < b -> v < Nat.pow b k -> val_pos b (pos_of b k v) = v.
Proof.
  induction k as [|k IH]; intros v Hb Hv; simpl in *.
  - lia.
  - rewrite IH; [| exact Hb |].
    + pose proof (Nat.div_mod v b ltac:(lia)). lia.
    + apply Nat.div_lt_upper_bound; lia.
Qed.

(** The one modular identity the codec needs: encoding subtracts the next
    digit up, decoding adds it back, and the two cancel whichever way the
    difference wrapped. *)
Lemma modb_add_sub : forall b n m,
  1 < b -> n < b -> m < b -> ((n + (b - m)) mod b + m) mod b = n.
Proof.
  intros b n m Hb Hn Hm.
  destruct (Nat.le_gt_cases m n) as [H|H].
  - assert (E : (n + (b - m)) mod b = n - m).
    { replace (n + (b - m)) with ((n - m) + 1 * b) by lia.
      rewrite Nat.mod_add by lia. apply Nat.mod_small; lia. }
    rewrite E. replace (n - m + m) with n by lia. apply Nat.mod_small; lia.
  - assert (E : (n + (b - m)) mod b = n + (b - m))
      by (apply Nat.mod_small; lia).
    rewrite E. replace (n + (b - m) + m) with (n + 1 * b) by lia.
    rewrite Nat.mod_add by lia. apply Nat.mod_small; lia.
Qed.

Lemma gdec_genc : forall b ns,
  1 < b -> Forall (fun n => n < b) ns -> gdec b (genc b ns) = ns.
Proof.
  induction ns as [|n t IH]; intros Hb HF; simpl; [reflexivity|].
  inversion HF as [|? ? Hn Ht]; subst.
  rewrite IH by assumption.
  f_equal.
  rewrite (Nat.mod_small n) by lia.
  rewrite <- (Nat.add_mod_idemp_r _ (hd 0 t)) by lia.
  apply modb_add_sub; [lia | lia | apply Nat.mod_upper_bound; lia].
Qed.

Lemma pos_of_lt : forall b k v, 1 < b -> Forall (fun n => n < b) (pos_of b k v).
Proof.
  induction k as [|k IH]; intros v Hb; simpl; constructor.
  - apply Nat.mod_upper_bound; lia.
  - apply IH; exact Hb.
Qed.

Lemma fam_value_of_value : forall F v k ds,
  1 < fm_b F -> fam_of_value F v k = Some ds -> fam_value F ds = v.
Proof.
  intros F v k ds Hb H. unfold fam_of_value in H.
  destruct ((fam_lo F k <=? v) && (v <? fam_lim F k)) eqn:Eg; [|discriminate].
  apply andb_true_iff in Eg as [Elo Ehi].
  apply Nat.leb_le in Elo. apply Nat.ltb_lt in Ehi.
  unfold fam_lo in Elo. unfold fam_lim in Ehi. unfold fam_value.
  destruct (fm_code F); injection H as <-.
  - apply val_pos_pos_of; assumption.
  - rewrite gdec_genc by (assumption || apply pos_of_lt; assumption).
    apply val_pos_pos_of; assumption.
  - apply fibdec_val; [cbn [fiblo]; lia | lia].
  - apply fiblaz_val; [cbn [lazlo]; lia | lia].
Qed.

(** An interior step advances the value by exactly [fm_step] and keeps the
    width.  This is the half of the successor that never touches the outer
    parameter or the phase. *)
Lemma fam_next_interior : forall F ds ph nd,
  1 < fm_b F ->
  fam_is_top F ds = false ->
  fam_next F ds ph = Some nd ->
  fam_value F nd = fam_value F ds + fm_step F /\ length nd = length ds.
Proof.
  intros F ds ph nd Hb Htop H.
  unfold fam_next in H. rewrite Htop in H.
  split; [eapply fam_value_of_value; eassumption
         |eapply fam_of_value_length; eassumption].
Qed.

(** A family member's value is below the width's ceiling: the invariant
    that makes "the top of a width is reached" a terminating count. *)
Lemma fam_next_wf : forall F ds ph nd,
  1 < fm_b F ->
  fam_is_top F ds = false ->
  fam_next F ds ph = Some nd ->
  fam_value F nd < fam_lim F (length nd).
Proof.
  intros F ds ph nd Hb Htop H.
  unfold fam_next in H. rewrite Htop in H.
  rewrite (fam_of_value_length _ _ _ _ H).
  rewrite (fam_value_of_value _ _ _ _ Hb H).
  unfold fam_of_value in H.
  destruct ((fam_lo F (length ds) <=? fam_value F ds + fm_step F)
            && (fam_value F ds + fm_step F <? fam_lim F (length ds))) eqn:Eg;
    [|discriminate].
  apply andb_true_iff in Eg as [_ Ehi]. apply Nat.ltb_lt in Ehi. exact Ehi.
Qed.
