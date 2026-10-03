(** * LP_1RB1LD_1RC0RB_1LA1RC_1LA0LA (SCOPING_INSTR 7.4.LE11)

    A two-level binary mirror counter.  At [B [0]] (the junction) the
    right side is a binary counter [y] (LSB nearest, 2-cell digits [10] /
    [11], then a [11] marker), the left side is [xc u ++ 1 :: xc v]: a
    binary counter [u] (digits [00] / [10]) and, past a single separator
    cell, a second digit string [v] read one cell out of step.  One
    macro step (the C sweep right, the A/D walk left, the B sweep back)
    increments [y] and then:

    - [u] has a 0 digit: [u] is incremented;
    - [u] is all 1s, [v = []]: [u] widens to [0^(|u|+1)] (the era);
    - [u] is all 1s, [v = 1 :: v1]: [u] and the separator are absorbed
      into the right, [y := 1^|u| 0 ++ y+1], the junction moves left;
    - [u] is all 1s, [v = 0 :: v1]: [u := 0^(|u|+1)], [v := v1].

    When [y] is all 1s (and then [v = []]), the walk overflows into the
    left one cell out of step: the right resets to [0^w] or [0^(w+1)] and
    [u] (less its low digit) becomes the new [v].  So each era counts
    until [y] is full, and the next pass re-encodes the left digits as
    right digits.  The orbit stays in the cases above by a numeric
    invariant ([Inv]: in an era the left count [val u + 2^|u|] is at most
    [val y]; in a pass the right deficit [2^|y| - 1 - val y] is at least
    the left deficit [2^l - val (u ++ 1 :: v)]).

    Hand-stated, kernel-checked.  Axiom footprint: [functional_extensionality_dep]. *)
From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Counters Require Import WTape NestCountTr LoopRunTr LoopMirrorTr.
From BBB4.Checkers Require Import WrapTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
Import ListNotations.

Definition tm_1RB1LD_1RC0RB_1LA1RC_1LA0LA : TM := fun q s => match q, s with
  | StA, S0 => Some (mkTrans S1 DR StB) | StA, S1 => Some (mkTrans S1 DL StD)
  | StB, S0 => Some (mkTrans S1 DR StC) | StB, S1 => Some (mkTrans S0 DR StB)
  | StC, S0 => Some (mkTrans S1 DL StA) | StC, S1 => Some (mkTrans S1 DR StC)
  | StD, S0 => Some (mkTrans S1 DL StA) | StD, S1 => Some (mkTrans S0 DL StA)
  end.
Local Notation tm := (tm_wrap_trs tm_1RB1LD_1RC0RB_1LA1RC_1LA0LA []).

(** ** The abstract state and its step *)

Definition xc (u : list bool) : list Sym := bcells [S0; S0] [S1; S0] u.
Definition yc (y : list bool) : list Sym := bcells [S1; S0] [S1; S1] y.

Definition ast : Type := (list bool * list bool * list bool)%type.

Definition enc (s : ast) : cconf :=
  let '(u, v, y) := s in (StB, (xc u ++ S1 :: xc v, S0, yc y ++ [S1; S1])).

Definition allt (l : list bool) : bool := forallb (fun b => b) l.

Definition astep (s : ast) : ast :=
  let '(u, v, y) := s in
  if allt y then
    match u with
    | [] => ([], [], repeat false (S (length y)))
    | true :: u1 => ([], u1 ++ [true], repeat false (S (length y)))
    | false :: u1 => ([false], u1 ++ [true], repeat false (length y))
    end
  else if allt u then
    match v with
    | [] => (repeat false (S (length u)), [], binc y)
    | true :: v1 => ([], v1, repeat true (length u) ++ false :: binc y)
    | false :: v1 => (repeat false (S (length u)), v1, binc y)
    end
  else (binc u, v, binc y).

(** ** List facts *)

Lemma allt_repeat : forall k, allt (repeat true k) = true.
Proof. induction k as [|k IH]; [reflexivity|]. exact IH. Qed.

Lemma allt_int : forall k r, allt (repeat true k ++ false :: r) = false.
Proof. induction k as [|k IH]; intros r; [reflexivity|]. apply IH. Qed.

Lemma allt_dec : forall l, (allt l = true /\ l = repeat true (length l)) \/
  (allt l = false /\ exists k r, l = repeat true k ++ false :: r).
Proof.
  intros l. destruct (ttdecomp l) as [(k & r & ->) | (k & ->)].
  - right. split; [apply allt_int | exists k, r; reflexivity].
  - left. split; [apply allt_repeat | rewrite repeat_length; reflexivity].
Qed.

Lemma xc_ff : forall k r, xc (repeat false k ++ r) = rep [S0; S0] k ++ xc r.
Proof. intros. apply bcells_ff. Qed.
Lemma xc_tt : forall k r, xc (repeat true k ++ r) = rep [S1; S0] k ++ xc r.
Proof. intros. apply bcells_tt. Qed.
Lemma yc_ff : forall k r, yc (repeat false k ++ r) = rep [S1; S0] k ++ yc r.
Proof. intros. apply bcells_ff. Qed.
Lemma yc_tt : forall k r, yc (repeat true k ++ r) = rep [S1; S1] k ++ yc r.
Proof. intros. apply bcells_tt. Qed.
Lemma xc_t : forall r, xc (true :: r) = S1 :: S0 :: xc r.
Proof. reflexivity. Qed.
Lemma xc_f : forall r, xc (false :: r) = S0 :: S0 :: xc r.
Proof. reflexivity. Qed.
Lemma xc_nil : xc [] = [].
Proof. reflexivity. Qed.
Lemma xc_all : forall k, xc (repeat true k) = rep [S1; S0] k.
Proof. intros. apply bcells_alltrue. Qed.
Lemma xc_none : forall k, xc (repeat false k) = rep [S0; S0] k.
Proof. intros. apply bcells_allfalse. Qed.
Lemma xc_app : forall a b, xc (a ++ b) = xc a ++ xc b.
Proof. intros. apply flat_map_app. Qed.

(** ** Machine pieces *)

Lemma csweep : forall n L R, Reach0 tm (cR StC L (rep [S1] n ++ R)) (cR StC (rep [S1] n ++ L) R).
Proof. apply sweepR. intros L R. rr 1. r0. Qed.

Lemma bsweep : forall n L R, Reach0 tm (cR StB L (rep [S1] n ++ R)) (cR StB (rep [S0] n ++ L) R).
Proof. apply sweepR. intros L R. rr 1. r0. Qed.

Lemma adwalk : forall n L R, Reach0 tm (cL StA (rep [S1; S1] n ++ L) R) (cL StA L (rep [S0; S1] n ++ R)).
Proof. apply sweepL. intros L R. rr 2. r0. Qed.

Lemma adwalkx : forall n L R, Reach0 tm (cL StA (rep [S1; S0] n ++ L) R) (cL StA L (rep [S1; S1] n ++ R)).
Proof. apply sweepL. intros L R. rr 2. r0. Qed.

Ltac tocR := match goal with |- Reach0 _ (?q, (?L, chd ?X, ctl ?X)) _ => change (q, (L, chd X, ctl X)) with (cR q L X) end.
Ltac tocL := match goal with |- Reach0 _ (?q, (ctl ?X, chd ?X, ?R)) _ => change (q, (ctl X, chd X, R)) with (cL q X R) end.

Lemma pairs1 : forall (a : Sym) k l, a :: rep [a] (k + k) ++ a :: l = rep [a; a] (S k) ++ l.
Proof.
  intros a k l. rewrite rep1_snoc, rep_pair. replace (S k + S k) with (S (S (k + k))) by lia. reflexivity.
Qed.

(** the right carry, up to the C turn *)
Lemma armR_c : forall k r L M,
  Reach1 tm (StB, (L, S0, yc (repeat true k ++ false :: r) ++ M))
            (cR StC (rep [S1] (S (k + k)) ++ S1 :: L) (S0 :: yc r ++ M)).
Proof.
  intros k r L M. rewrite yc_tt, rep_pair. cbn [yc bcells flat_map]. fold (yc r).
  rr 1. rewrite <- !app_assoc. cbn [app]. rewrite rep1_snoc, rep1_fold. tocR.
  rt (csweep (S (k + k)) (S1 :: L) (S0 :: yc r ++ M)). r0.
Qed.

(** the right carry: [y] incremented, A on the left's first cell *)
Lemma armR : forall k r L M,
  Reach1 tm (StB, (L, S0, yc (repeat true k ++ false :: r) ++ M))
            (cL StA L (S0 :: yc (repeat false k ++ true :: r) ++ M)).
Proof.
  intros k r L M. eapply reach10; [apply armR_c|].
  rr 1. change (StA, (rep [S1] (k + k) ++ S1 :: L, S1, S1 :: yc r ++ M))
    with (cL StA (S1 :: rep [S1] (k + k) ++ S1 :: L) (S1 :: yc r ++ M)).
  rewrite pairs1. rt (adwalk (S k) L (S1 :: yc r ++ M)).
  cbn [rep app]. rewrite (rep_shift S1 S0 k), yc_ff. unfold yc at 2. cbn [bcells flat_map]. fold (yc r).
  rewrite <- app_assoc. r0.
Qed.

Lemma yc_all : forall w, yc (repeat true w) ++ [S1; S1] = rep [S1] (S w + S w).
Proof.
  intros w. unfold yc. rewrite bcells_alltrue. rewrite rep_comm, <- rep_pair. reflexivity.
Qed.

(** the overflow: [y] all 1s, the walk enters the left as D *)
Lemma armO : forall w L,
  Reach1 tm (StB, (L, S0, yc (repeat true w) ++ [S1; S1]))
            (cL StD L (S1 :: rep [S0; S1] (S w) ++ [S1])).
Proof.
  intros w L. rewrite yc_all.
  rr 1. change (StC, (S1 :: L, S1, rep [S1] (w + S w))) with (cR StC (S1 :: L) (rep [S1] (S w + S w))).
  pose proof (csweep (S w + S w) (S1 :: L) []) as H. rewrite app_nil_r in H. rt H.
  rr 1. change (StA, (rep [S1] (w + S w) ++ S1 :: L, S1, [S1]))
    with (cL StA (rep [S1] (S w + S w) ++ S1 :: L) [S1]).
  rewrite <- rep_pair. rt (adwalk (S w) (S1 :: L) [S1]). rr 1. r0.
Qed.

(** the left walks after a right carry (A on the left's first cell) *)
Lemma walk_a : forall k r v Y,
  Reach0 tm (cL StA (xc (repeat true k ++ false :: r) ++ S1 :: xc v) (S0 :: Y))
            (StB, (xc (repeat false k ++ true :: r) ++ S1 :: xc v, S0, Y)).
Proof.
  intros k r v Y. rewrite xc_tt, xc_ff. cbn [xc bcells flat_map]. fold (xc r).
  rewrite <- !app_assoc. cbn [app].
  rt (adwalkx k (S0 :: S0 :: xc r ++ S1 :: xc v) (S0 :: Y)).
  rr 1. rewrite rep_pair. tocR. rt (bsweep (k + k) (S1 :: S0 :: xc r ++ S1 :: xc v) (S0 :: Y)).
  rewrite <- rep_pair. r0.
Qed.

Lemma walk_c : forall k v1 Y,
  Reach0 tm (cL StA (xc (repeat true k) ++ S1 :: xc (true :: v1)) (S0 :: Y))
            (StB, (S1 :: xc v1, S0, rep [S1; S1] k ++ S1 :: S0 :: Y)).
Proof.
  intros k v1 Y. rewrite xc_all, ?xc_t, ?xc_f.
  rt (adwalkx k (S1 :: S1 :: S0 :: xc v1) (S0 :: Y)).
  rr 3. rewrite rep_pair, rep1_snoc, <- rep_pair. r0.
Qed.

Lemma walk_d : forall k v1 Y,
  Reach0 tm (cL StA (xc (repeat true k) ++ S1 :: xc (false :: v1)) (S0 :: Y))
            (StB, (xc (repeat false (S k)) ++ S1 :: xc v1, S0, Y)).
Proof.
  intros k v1 Y. rewrite xc_all, ?xc_t, ?xc_f.
  rt (adwalkx k (S1 :: S0 :: S0 :: xc v1) (S0 :: Y)).
  rr 3. change (StB, (S1 :: xc v1, S1, S1 :: rep [S1; S1] k ++ S0 :: Y))
    with (cR StB (S1 :: xc v1) (rep [S1; S1] (S k) ++ S0 :: Y)).
  rewrite rep_pair. rt (bsweep (S k + S k) (S1 :: xc v1) (S0 :: Y)).
  rewrite xc_none, rep_pair. r0.
Qed.

Lemma walk_b : forall k Y,
  Reach0 tm (cL StA (xc (repeat true k) ++ [S1]) (S0 :: Y))
            (StB, (xc (repeat false (S k)) ++ [S1], S0, Y)).
Proof.
  intros k Y. rewrite xc_all.
  rt (adwalkx k [S1] (S0 :: Y)).
  rr 3. change (StB, ([S1], S1, S1 :: rep [S1; S1] k ++ S0 :: Y))
    with (cR StB [S1] (rep [S1; S1] (S k) ++ S0 :: Y)).
  rewrite rep_pair. rt (bsweep (S k + S k) [S1] (S0 :: Y)).
  rewrite xc_none, rep_pair. r0.
Qed.

(** after the overflow: the walk enters the left one cell out of step *)
Definition RO (w : nat) : list Sym := S1 :: rep [S0; S1] (S w) ++ [S1].

Lemma RO_yc : forall w, RO w = yc (repeat false (S w)) ++ [S1; S1].
Proof. intros w. unfold RO, yc. rewrite bcells_allfalse, rep_shift. reflexivity. Qed.

Lemma RO_yc' : forall w, rep [S0; S1] w ++ [S1] = S0 :: yc (repeat false w) ++ [S1; S1] \/ True.
Proof. right. exact I. Qed.

Lemma ovf_e : forall u1 w,
  Reach0 tm (cL StD (xc (true :: u1) ++ [S1]) (RO w)) (StB, (S1 :: xc u1 ++ [S1], S0, RO w)).
Proof. intros u1 w. rewrite xc_t. rr 2. r0. Qed.

Lemma ovf_f : forall u1 w,
  Reach0 tm (cL StD (xc (false :: u1) ++ [S1]) (RO w))
            (StB, (S0 :: S0 :: S1 :: xc u1 ++ [S1], S0, yc (repeat false w) ++ [S1; S1])).
Proof.
  intros u1 w. rewrite xc_f. unfold RO. rr 4. unfold yc. rewrite bcells_allfalse.
  rewrite rep_shift. r0.
Qed.

Lemma ovf_g : forall w, Reach0 tm (cL StD [S1] (RO w)) (StB, ([S1], S0, RO w)).
Proof. intros w. rr 2. r0. Qed.

(** ** One macro step *)

Lemma padx : forall q L h R, lift (q, (L ++ [S1; S0], h, R)) = lift (q, (L ++ [S1], h, R)).
Proof.
  intros. replace (L ++ [S1; S0]) with ((L ++ [S1]) ++ rep [S0] 1) by (rewrite <- app_assoc; reflexivity).
  apply lift_padL.
Qed.

Lemma macro : forall u v y, (allt y = true -> v = []) ->
  Reach1 tm (enc (u, v, y)) (enc (astep (u, v, y))).
Proof.
  intros u v y Hv. destruct (allt_dec y) as [[Hy Ey] | [Hy (k & r & Ey)]].
  - rewrite (Hv Hy). cbn [astep]. rewrite Hy. unfold enc at 1. rewrite Ey, ?repeat_length.
    eapply reach10; [apply armO|]. fold (RO (length y)).
    destruct u as [|[|] u1].
    + rewrite xc_nil. cbn [app]. rt (ovf_g (length y)). unfold enc. rewrite RO_yc. r0.
    + rt (ovf_e u1 (length y)). unfold enc. rewrite RO_yc, xc_nil, xc_app, xc_t, xc_nil.
      cbn [app]. apply reach0_lift. symmetry. exact (padx _ (S1 :: xc u1) _ _).
    + rt (ovf_f u1 (length y)). unfold enc. rewrite xc_f, xc_nil, xc_app, xc_t, xc_nil.
      cbn [app]. apply reach0_lift. symmetry. exact (padx _ (S0 :: S0 :: S1 :: xc u1) _ _).
  - cbn [astep]. rewrite Hy. unfold enc at 1. rewrite Ey.
    eapply reach10; [apply armR|]. rewrite <- binc_int, <- Ey.
    destruct (allt_dec u) as [[Hu Eu] | [Hu (j & r' & Eu)]]; rewrite Hu.
    + rewrite Eu at 1. destruct v as [|[|] v1].
      * rewrite xc_nil. rt (walk_b (length u) (yc (binc y) ++ [S1; S1])). unfold enc. rewrite xc_nil. r0.
      * rt (walk_c (length u) v1 (yc (binc y) ++ [S1; S1])). unfold enc.
        rewrite xc_nil, yc_tt. cbn [app]. unfold yc at 2. cbn [bcells flat_map]. fold (yc (binc y)).
        rewrite <- app_assoc. r0.
      * rt (walk_d (length u) v1 (yc (binc y) ++ [S1; S1])). unfold enc. r0.
    + rewrite Eu. rt (walk_a j r' v (yc (binc y) ++ [S1; S1])). rewrite <- binc_int. unfold enc. r0.
Qed.

(** ** The invariant *)

Fixpoint val (l : list bool) : nat :=
  match l with [] => 0 | b :: r => (if b then 1 else 0) + 2 * val r end.

Lemma val_lt : forall l, val l < 2 ^ length l.
Proof. induction l as [|[|] l IH]; cbn [val length]; rewrite ?Nat.pow_succ_r', ?Nat.pow_0_r; lia. Qed.

Lemma val_binc : forall l, val (binc l) = S (val l).
Proof. induction l as [|[|] l IH]; cbn [binc val]; lia. Qed.

Lemma len_binc : forall l, allt l = false -> length (binc l) = length l.
Proof.
  induction l as [|[|] l IH]; intros H; [discriminate | | reflexivity].
  cbn [binc length]. rewrite IH; [reflexivity | exact H].
Qed.

Lemma binc_nonnil : forall l, binc l <> [].
Proof. intros [|[|] l]; discriminate. Qed.

Lemma val_app : forall a b, val (a ++ b) = val a + 2 ^ length a * val b.
Proof.
  induction a as [|x a IH]; intros b; cbn [val app length]; [rewrite Nat.pow_0_r; lia|].
  rewrite IH, Nat.pow_succ_r'. destruct x; lia.
Qed.

Lemma val_rt : forall k, val (repeat true k) + 1 = 2 ^ k.
Proof. induction k as [|k IH]; cbn [val repeat]; rewrite ?Nat.pow_succ_r', ?Nat.pow_0_r; lia. Qed.

Lemma val_rf : forall k, val (repeat false k) = 0.
Proof. induction k as [|k IH]; cbn [val repeat]; lia. Qed.

Lemma allt_full : forall l, allt l = true -> val l + 1 = 2 ^ length l.
Proof.
  intros l H. destruct (allt_dec l) as [[_ E] | [H' _]]; [| congruence].
  rewrite E, repeat_length. apply val_rt.
Qed.

Lemma allt_short : forall l, allt l = false -> val l + 2 <= 2 ^ length l.
Proof. intros l H. pose proof (val_lt (binc l)). rewrite val_binc, len_binc in H0 by exact H. lia. Qed.

Lemma pow_pos : forall n, 1 <= 2 ^ n.
Proof. intros n. pose proof (Nat.pow_nonzero 2 n ltac:(lia)). lia. Qed.

Definition Inv (s : ast) : Prop :=
  let '(u, v, y) := s in
  (v = [] /\ val u + 2 ^ length u <= val y /\ (u = [] -> allt y = false)) \/
  (v <> [] /\ last v false = true /\
   2 ^ (length u + S (length v)) + val y + 1 <= 2 ^ length y + val (u ++ true :: v)).

Lemma Inv_side : forall u v y, Inv (u, v, y) -> allt y = true -> v = [].
Proof.
  intros u v y [(Hv & _) | (_ & _ & H)] Hy; [exact Hv|].
  pose proof (allt_full y Hy). pose proof (val_lt (u ++ true :: v)).
  rewrite app_length in H1. cbn [length] in H1. lia.
Qed.

Lemma val_snoc_t : forall l, val (l ++ [true]) = val l + 2 ^ length l.
Proof. intros l. rewrite val_app. cbn [val]. lia. Qed.

Lemma val_rt_app : forall k l, val (repeat true k ++ l) + 1 = 2 ^ k + 2 ^ k * val l.
Proof. intros k l. rewrite val_app, repeat_length. pose proof (val_rt k). lia. Qed.

Lemma Inv_step : forall s, Inv s -> Inv (astep s).
Proof.
  intros [[u v] y] HI. pose proof (Inv_side u v y HI) as Hs.
  destruct (allt_dec y) as [[Hy Ey] | [Hy _]].
  - specialize (Hs Hy). subst v. cbn [astep]. rewrite Hy.
    destruct HI as [(_ & H1 & H2) | (H & _)]; [| congruence].
    pose proof (allt_full y Hy) as Hf.
    destruct u as [|[|] u1].
    + exfalso. specialize (H2 eq_refl). congruence.
    + right. split; [destruct u1; discriminate|]. split; [apply last_last|].
      cbn [app]. rewrite app_length, repeat_length, val_rf. cbn [val length] in *.
      rewrite val_snoc_t. rewrite Nat.pow_succ_r' in H1.
      replace (0 + S (length u1 + 1)) with (S (S (length u1))) by lia.
      rewrite !Nat.pow_succ_r'. lia.
    + right. split; [destruct u1; discriminate|]. split; [apply last_last|].
      cbn [app]. rewrite app_length, repeat_length, val_rf. cbn [val length] in *.
      rewrite val_snoc_t. rewrite Nat.pow_succ_r' in H1.
      assert (Hlt : S (length u1) < length y).
      { apply (Nat.pow_lt_mono_r_iff 2); [lia|]. rewrite Nat.pow_succ_r'. lia. }
      assert (Hle : 2 ^ S (S (length u1)) <= 2 ^ length y) by (apply Nat.pow_le_mono_r; lia).
      replace (1 + S (length u1 + 1)) with (S (S (S (length u1)))) by lia.
      rewrite !Nat.pow_succ_r' in *. lia.
  - cbn [astep]. rewrite Hy. pose proof (allt_short y Hy) as Hys.
    pose proof (len_binc y Hy) as Hlb. pose proof (val_binc y) as Hvb.
    destruct (allt_dec u) as [[Hu Eu] | [Hu _]]; rewrite Hu.
    + pose proof (allt_full u Hu) as Hf. destruct v as [|[|] v1].
      * left. split; [reflexivity|]. split; [|discriminate].
        rewrite val_rf, repeat_length, Nat.pow_succ_r'.
        destruct HI as [(_ & H1 & _) | (H & _)]; [lia | congruence].
      * destruct HI as [(H & _) | (_ & Hl & H)]; [discriminate|].
        pose proof (val_rt_app (length u) (false :: binc y)) as Hy'.
        cbn [val] in Hy'. pose proof (pow_pos (length u)).
        destruct v1 as [|b v1'].
        -- left. split; [reflexivity|]. split; [cbn [val length]; rewrite Nat.pow_0_r; rewrite Hvb in Hy'; nia|].
           intros _. apply allt_int.
        -- right. split; [discriminate|]. split; [exact Hl|].
           rewrite Eu in H at 2.
           pose proof (val_rt_app (length u) (true :: true :: b :: v1')) as Hx.
           cbn [app]. rewrite app_length, repeat_length. cbn [length val] in *.
           pose proof (val_lt (b :: v1')) as Hb. cbn [length val] in Hb.
           rewrite Hlb, Hvb in *. rewrite Nat.pow_add_r in *. rewrite !Nat.pow_succ_r' in *. rewrite Nat.pow_0_r in *.
           remember ((if b then 1 else 0) + 2 * val v1') as bb.
           remember (2 ^ length u) as K. remember (2 ^ length v1') as P. remember (2 ^ length y) as Y.
           remember (val (repeat true (length u) ++ true :: true :: b :: v1')) as V2.
           remember (val (repeat true (length u) ++ false :: binc y)) as V1.
           destruct (Nat.le_exists_sub (bb + 1) (2 * P) ltac:(lia)) as (E & HE & _).
           replace (K * (2 * (2 * (2 * P)))) with (4 * (K * (E + (bb + 1)))) in H
             by (rewrite <- HE; ring).
           assert (H2 : 4 * (K * E) + val y + 2 <= Y) by lia.
           assert (H3 : K * (2 * (4 * (K * E) + val y + 2)) <= K * (2 * Y))
             by (apply Nat.mul_le_mono_l; lia).
           assert (H4 : E <= K * (K * E)) by nia.
           replace (2 * (2 * P)) with (2 * (E + (bb + 1))) by lia.
           replace (2 ^ (length u + S (length y))) with (K * (2 * Y))
             by (subst K Y; rewrite Nat.pow_add_r, Nat.pow_succ_r'; reflexivity).
           lia.
      * destruct HI as [(H & _) | (_ & Hl & H)]; [discriminate|].
        destruct v1 as [|b v1']; [discriminate|].
        right. split; [discriminate|]. split; [exact Hl|].
        rewrite Eu in H at 2.
        pose proof (val_rt_app (length u) (true :: false :: b :: v1')) as Hx.
        rewrite val_app, repeat_length, val_rf. cbn [length val] in *.
        rewrite Nat.pow_add_r in *. rewrite !Nat.pow_succ_r' in *. rewrite Hlb, Hvb. nia.
    + destruct v as [|b v1].
      * left. split; [reflexivity|].
        destruct HI as [(_ & H1 & _) | (H & _)]; [| congruence].
        split; [rewrite val_binc, len_binc by exact Hu; lia|].
        intros H. exfalso. exact (binc_nonnil u H).
      * destruct HI as [(H & _) | (_ & Hl & H)]; [discriminate|].
        right. split; [discriminate|]. split; [exact Hl|].
        rewrite val_app, !val_binc, len_binc, Hlb by exact Hu. rewrite val_app in H. lia.
Qed.

(** ** The orbit *)

Lemma iter_inv : forall n s, Inv s -> Inv (Nat.iter n astep s).
Proof.
  induction n as [|n IH]; intros s H; [exact H|].
  cbn [Nat.iter nat_rect]. apply Inv_step. apply IH, H.
Qed.

Lemma macro_inv : forall s, Inv s -> Reach1 tm (enc s) (enc (astep s)).
Proof. intros [[u v] y] H. apply macro. apply (Inv_side u v y H). Qed.

Lemma iter_reach : forall n s, Inv s -> Reach0 tm (enc s) (enc (Nat.iter n astep s)).
Proof.
  induction n as [|n IH]; intros s H; [apply reach0_refl|].
  rewrite Nat.iter_succ_r. eapply reach0_trans; [apply reach1_0, macro_inv, H|].
  apply IH, Inv_step, H.
Qed.

(** a macro step in which every instruction fires *)
Definition good (s : ast) : Prop :=
  let '(u, v, y) := s in allt y = false /\
  ((exists j r, u = true :: repeat true j ++ false :: r) \/
   (allt u = true /\ (v = [] \/ exists v1, v = false :: v1))).

Lemma to_walk : forall u v y, allt y = false ->
  Reach0 tm (enc (u, v, y)) (cL StA (xc u ++ S1 :: xc v) (S0 :: yc (binc y) ++ [S1; S1])).
Proof.
  intros u v y Hy. destruct (allt_dec y) as [[H _] | [_ (k & r & ->)]]; [congruence|].
  rewrite binc_int. apply reach1_0, armR.
Qed.

Lemma fires_right : forall u v y t, allt y = false ->
  t = (StC, S0) \/ t = (StA, S1) \/ t = (StD, S1) -> Fires tm (enc (u, v, y)) t.
Proof.
  intros u v y t Hy Ht. destruct (allt_dec y) as [[H _] | [_ (k & r & ->)]]; [congruence|].
  unfold enc. eapply fire_back; [apply reach1_0, armR_c|].
  destruct Ht as [-> | [-> | ->]]; [fire_find | fire_find | destruct k; fire_find].
Qed.

Lemma fires_c1 : forall u v y, Fires tm (enc (u, v, y)) (StC, S1).
Proof.
  intros u v y. unfold enc. eapply fire_back; [rr 1; apply reach0_refl|].
  destruct y as [|[|] y]; cbn; apply fires_here; reflexivity.
Qed.

Lemma walk_fires : forall u v Y t, 
  ((exists j r, u = true :: repeat true j ++ false :: r) \/
   (allt u = true /\ (v = [] \/ exists v1, v = false :: v1))) ->
  t = (StA, S0) \/ t = (StD, S0) \/ t = (StB, S1) ->
  Fires tm (cL StA (xc u ++ S1 :: xc v) (S0 :: Y)) t.
Proof.
  intros u v Y t Hg Ht. destruct Hg as [(j & r & ->) | (Hu & Hv)].
  - rewrite xc_t, xc_tt, xc_f. cbn [app]. rewrite <- ?app_assoc. cbn [app].
    destruct Ht as [-> | [-> | ->]]; [| fire_find |].
    all: change (S1 :: S0 :: rep [S1; S0] j ++ S0 :: S0 :: xc r ++ S1 :: xc v)
           with (rep [S1; S0] (S j) ++ S0 :: S0 :: xc r ++ S1 :: xc v).
    all: eapply fire_back; [apply adwalkx|]; fire_find.
  - destruct (allt_dec u) as [[_ Eu] | [Hu' _]]; [|congruence].
    rewrite Eu, xc_all. destruct Hv as [-> | (v1 & ->)]; rewrite ?xc_nil, ?xc_f;
    (eapply fire_back; [apply adwalkx|]); destruct Ht as [-> | [-> | ->]]; fire_find.
Qed.

Lemma good_fires : forall s, good s -> forall t, Fires tm (enc s) t.
Proof.
  intros [[u v] y] (Hy & Hg) [q a].
  destruct q, a;
  first [ apply fires_here; reflexivity
        | apply fires_c1
        | apply fires_right; [exact Hy | tauto]
        | eapply fire_back; [apply (to_walk u v y Hy)|]; apply walk_fires; [exact Hg | tauto] ].
Qed.

Lemma allt_f : forall l, allt (false :: l) = false.
Proof. reflexivity. Qed.

Lemma F_ones : forall v u y, Inv (u, v, y) -> allt u = true -> allt y = false ->
  exists n, good (Nat.iter n astep (u, v, y)).
Proof.
  induction v as [|[|] v1 IH]; intros u y HI Hu Hy.
  - exists 0. cbn. split; [exact Hy|]. right. split; [exact Hu | left; reflexivity].
  - destruct (IH [] (repeat true (length u) ++ false :: binc y)) as (n & Hn).
    + pose proof (Inv_step _ HI) as H. cbn [astep] in H. rewrite Hy, Hu in H. exact H.
    + reflexivity.
    + apply allt_int.
    + exists (S n). rewrite Nat.iter_succ_r. cbn [astep]. rewrite Hy, Hu. exact Hn.
  - exists 0. cbn. split; [exact Hy|]. right. split; [exact Hu | right; exists v1; reflexivity].
Qed.

Lemma Inv_len : forall u y, Inv (u, [], y) -> length u < length y.
Proof.
  intros u y [(_ & H & _) | (H & _)]; [|congruence].
  pose proof (val_lt y). apply (Nat.pow_lt_mono_r_iff 2); lia.
Qed.

Lemma reach_good : forall s, Inv s -> exists n, good (Nat.iter n astep s).
Proof.
  intros [[u v] y] HI.
  destruct (allt_dec y) as [[Hy Ey] | [Hy _]].
  - pose proof (Inv_side u v y HI Hy) as ->.
    pose proof (Inv_len u y HI) as Hl.
    destruct u as [|[|] u1].
    + exfalso. destruct HI as [(_ & _ & H) | (H & _)]; [|congruence].
      specialize (H eq_refl). congruence.
    + destruct (F_ones (u1 ++ [true]) [] (repeat false (S (length y)))) as (n & Hn).
      * pose proof (Inv_step _ HI) as H. cbn [astep] in H. rewrite Hy in H. exact H.
      * reflexivity.
      * reflexivity.
      * exists (S n). rewrite Nat.iter_succ_r. cbn [astep]. rewrite Hy. exact Hn.
    + cbn [length] in Hl. destruct (length y) as [|[|w]] eqn:Ew; [lia | lia |].
      destruct (F_ones (u1 ++ [true]) [true] (binc (repeat false (length y)))) as (n & Hn).
      * pose proof (Inv_step _ (Inv_step _ HI)) as H. cbn [astep] in H. rewrite Hy in H.
        rewrite Ew in H |- *. cbn [allt forallb repeat binc andb] in H |- *. exact H.
      * reflexivity.
      * rewrite Ew. reflexivity.
      * exists (S (S n)). rewrite !Nat.iter_succ_r. cbn [astep]. rewrite Hy.
        rewrite Ew in Hn |- *. exact Hn.
  - destruct (allt_dec u) as [[Hu _] | [Hu (j & r & Eu)]];
      [apply F_ones; assumption|].
    destruct j as [|j].
    + cbn in Eu. subst u.
      assert (HI1 := Inv_step _ HI). cbn [astep] in HI1. rewrite Hy in HI1. cbn [allt forallb andb binc] in HI1.
      destruct (allt_dec (binc y)) as [[Hy1 _] | [Hy1 _]].
      * pose proof (Inv_side _ _ _ HI1 Hy1) as ->.
        destruct (F_ones (r ++ [true]) [] (repeat false (S (length (binc y))))) as (n & Hn).
        -- pose proof (Inv_step _ HI1) as H. cbn [astep] in H. rewrite Hy1 in H. exact H.
        -- reflexivity.
        -- reflexivity.
        -- exists (S (S n)). rewrite !Nat.iter_succ_r. cbn [astep]. rewrite Hy. cbn [allt forallb andb binc].
           cbn [astep]. rewrite Hy1. exact Hn.
      * destruct (allt_dec r) as [[Hr _] | [Hr (i & r' & Er)]].
        -- destruct (F_ones v (true :: r) (binc y) HI1 Hr Hy1) as (n & Hn).
           exists (S n). rewrite Nat.iter_succ_r. cbn [astep]. rewrite Hy. exact Hn.
        -- exists 1. cbn [Nat.iter nat_rect astep]. rewrite Hy. cbn [allt forallb andb binc].
           split; [exact Hy1|]. left. exists i, r'. rewrite Er. reflexivity.
    + exists 0. cbn [Nat.iter nat_rect]. split; [exact Hy|]. left. exists j, r. exact Eu.
Qed.

(** ** The board: from the era start at step 1,045 *)

Definition s0 : ast := ([], [], [false; true; false; true; false; false; true; true; false; false; false; false]).

Lemma Inv_s0 : Inv s0.
Proof. left. split; [reflexivity|]. split; [cbn; lia | intros _; reflexivity]. Qed.

Definition Cf (i : nat) : cconf := enc (Nat.iter i astep s0).

Lemma lap : forall i, Reach1 tm (Cf i) (Cf (S i)).
Proof. intros i. unfold Cf. cbn [Nat.iter nat_rect]. apply macro_inv, iter_inv, Inv_s0. Qed.

Lemma fires : forall t, ~ In t [] -> forall i, Fires tm (Cf i) t.
Proof.
  intros t _ i. unfold Cf. pose proof (iter_inv i s0 Inv_s0) as HI.
  destruct (reach_good _ HI) as (n & Hn).
  eapply fire_back; [apply (iter_reach n _ HI)|]. apply good_fires, Hn.
Qed.

Theorem nqhtr_1RB1LD_1RC0RB_1LA1RC_1LA0LA : NeverQuasiHaltsTr tm_1RB1LD_1RC0RB_1LA1RC_1LA0LA.
Proof.
  apply (boardS_neverqhtr _ [] Cf lap fires 1045).
  apply boot_ok. vm_compute. reflexivity.
Qed.
