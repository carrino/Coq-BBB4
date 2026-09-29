(** * Checkers.LadderNest: arms whose step count is a SUM -- a chain of chains.

    [LadderKernel.LRule] states a rule's step count as affine in the carry
    index ([lr_ca * j + lr_cb]), so a carry whose cost is QUADRATIC in its
    length has no arm (SCOPING_INSTR 7.4.CE2, "the quadratic-cost carry").
    Measured on those rows, the carry is a loop of ROUNDS: each round is an
    ordinary kernel rule whose cost is affine in its OWN index [i] (the run
    it sweeps), and the number of rounds is affine in the arm's index [j].
    The total is a sum of an affine function, which no [LRule] can state, but
    none of the closers needs the count: a lap only has to take SOME
    positive number of steps.

    So this file adds, on top of the unchanged kernel:

    - [ReachP]: from [c] to [c'] in some positive number of steps, against
      any tails the flags permit.  It is what [board_arm]'s generic property
      needs, and [reach_of_sound] is the embedding of [RuleSound].
    - two ITERATION lemmas, over a sound inner rule [Ir] with a LINK that
      makes its right-hand side at [i] its left-hand side at [i +- 1]:
      [iter_up] (the index grows; each round consumes a word from each
      tail) and [iter_down] (the index shrinks; each round pushes a word onto
      each tail).  Both are by induction on the number of rounds, which is
      how the count's sum never has to be written down.
    - a SEGMENT language: an arm is replayed as kernel chains ([NCh], the
      [LadderKernel.rrun] steps) and iteration segments ([NUp], [NDn]) whose
      round count is [al * j + be].  An iteration segment is checked
      SYNTACTICALLY, through three side operations ([sidx]: a side at an
      affine index, [srep]: a repeated word, [sapp]: concatenation when at
      most one side is [j]-dependent) and a canonical form ([ccanon]); the
      certificate supplies the words and the offsets and [vm_compute] checks
      them.  [nrun_sound] is the one theorem.

    Nothing about any machine or numeration is here.  Axiom footprint: none
    beyond what [LadderKernel] and [LapDecider] already use. *)

From Coq Require Import Arith Lia Bool List.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape.
From BBB4.Checkers Require Import LapDecider LadderKernel.
Import ListNotations.

(** ** Reachability, with and without a positive count *)

Definition ReachP (tm : TM) (el er : bool) (c c' : sconf) : Prop :=
  forall XL XR j, (el = true -> XL = []) -> (er = true -> XR = []) ->
  exists m, 0 < m /\ csteps tm m (cden XL XR j c) = Some (cden XL XR j c').

Lemma reach_of_sound : forall tm el er r,
  RuleSound tm el er r -> 0 < lr_cb r ->
  ReachP tm el er (lr_lhs r) (lr_rhs r).
Proof.
  intros tm el er r Hs Hc XL XR j HL HR.
  exists (lr_ca r * j + lr_cb r). split; [lia | exact (Hs XL XR j HL HR)].
Qed.

(** ** Side algebra *)

Lemma sden_tail : forall X j s, sden X j s = sden [] j s ++ X.
Proof. intros X j s. unfold sden. rewrite !app_nil_r, !app_assoc. reflexivity. Qed.

(** A side DEPENDS on [j] when it has a non-empty unit repeated [a*j] times
    with [a <> 0]; otherwise it is one concrete word. *)
Definition sdep (s : sside) : bool :=
  match s_u s with [] => false | _ => negb (s_a s =? 0) end.

Definition sflatl (s : sside) : list Sym := s_pre s ++ rep (s_u s) (s_b s) ++ s_post s.

Lemma sden_nodep : forall X j s, sdep s = false -> sden X j s = sflatl s ++ X.
Proof.
  intros X j [p u a b q] H. unfold sdep in H; simpl in H.
  unfold sden, sflatl; simpl. rewrite <- !app_assoc.
  destruct u as [|x u].
  - rewrite !rep_nil. reflexivity.
  - apply negb_false_iff, Nat.eqb_eq in H. subst a. reflexivity.
Qed.

Definition scanon (s : sside) : sside :=
  if sdep s then s else mkS (sflatl s) [] 0 0 [].

Lemma sden_canon : forall X j s, sden X j (scanon s) = sden X j s.
Proof.
  intros X j s. unfold scanon. destruct (sdep s) eqn:E; [reflexivity|].
  rewrite (sden_nodep X j s E). unfold sden; simpl. reflexivity.
Qed.

Definition ccanon (c : sconf) : sconf :=
  mkC (c_st c) (scanon (c_l c)) (c_h c) (scanon (c_r c)).

Lemma cden_canon : forall XL XR j c, cden XL XR j (ccanon c) = cden XL XR j c.
Proof. intros. unfold cden, ccanon; simpl. rewrite !sden_canon. reflexivity. Qed.

(** Equality of denotations, decided on canonical forms. *)
Definition ceqc (a b : sconf) : bool := sconf_eqb (ccanon a) (ccanon b).

Lemma ceqc_den : forall a b, ceqc a b = true ->
  forall XL XR j, cden XL XR j a = cden XL XR j b.
Proof.
  intros a b H XL XR j. apply sconf_eqb_eq in H.
  rewrite <- (cden_canon XL XR j a), <- (cden_canon XL XR j b), H. reflexivity.
Qed.

(** Concatenation of two sides, when at most one of them depends on [j]. *)
Definition sapp (s1 s2 : sside) : option sside :=
  if sdep s1 then
    if sdep s2 then None
    else Some (mkS (s_pre s1) (s_u s1) (s_a s1) (s_b s1) (s_post s1 ++ sflatl s2))
  else Some (mkS (sflatl s1 ++ s_pre s2) (s_u s2) (s_a s2) (s_b s2) (s_post s2)).

Lemma sapp_sound : forall s1 s2 s, sapp s1 s2 = Some s ->
  forall X j, sden X j s = sden (sden X j s2) j s1.
Proof.
  intros s1 s2 s H X j. unfold sapp in H.
  destruct (sdep s1) eqn:E1.
  - destruct (sdep s2) eqn:E2; [discriminate|].
    injection H as <-. rewrite (sden_nodep X j s2 E2).
    unfold sden; simpl. rewrite <- !app_assoc. reflexivity.
  - injection H as <-. rewrite (sden_nodep _ j s1 E1).
    unfold sden; simpl. rewrite <- !app_assoc. reflexivity.
Qed.

(** A side read at the affine index [i0 + (al*j + be)], as a side in [j]. *)
Definition sidx (s : sside) (i0 al be : nat) : sside :=
  mkS (s_pre s) (s_u s) (s_a s * al) (s_a s * (i0 + be) + s_b s) (s_post s).

Lemma sidx_den : forall X j s i0 al be,
  sden X j (sidx s i0 al be) = sden X (i0 + (al * j + be)) s.
Proof.
  intros X j [p u a b q] i0 al be. unfold sden, sidx; simpl.
  replace (a * al * j + (a * (i0 + be) + b)) with (a * (i0 + (al * j + be)) + b)
    by ring.
  reflexivity.
Qed.

(** A word repeated [al*j + be] times. *)
Definition srep (w : list Sym) (al be : nat) : sside := mkS [] w al be [].

Lemma srep_den : forall X j w al be, sden X j (srep w al be) = rep w (al * j + be) ++ X.
Proof. intros. reflexivity. Qed.

(** ** A normal form for sides, and the end of an arm up to [lift]

    A chain lands on the arm's right-hand side DENOTATIONALLY, but the
    spelling can differ: [0 ++ rep [0] (2j+2)] against [0000 ++ rep [00] j],
    or blanks the machine wrote beside an empty tail.  [snf] folds the
    constant copies into the prefix and the multiplier into the unit, then
    unrotates while the prefix ends like the unit, which is how
    [lapcert.sden_parts] reads a side; two sides with one normal form denote
    the same list.  On a side whose tail is known empty, trailing blanks are
    invisible to [lift] and [side_eqv] ignores them. *)

Fixpoint unrot (fuel : nat) (P U R : list Sym) : list Sym * list Sym * list Sym :=
  match fuel with
  | 0 => (P, U, R)
  | S f =>
      match P, U with
      | [], _ | _, [] => (P, U, R)
      | _, _ =>
          let x := last P S0 in
          if sym_eqb x (last U S0)
          then unrot f (removelast P) (x :: removelast U) (x :: R)
          else (P, U, R)
      end
  end.

Lemma unrot_den : forall fuel P U R P' U' R',
  unrot fuel P U R = (P', U', R') ->
  forall j X, P ++ rep U j ++ R ++ X = P' ++ rep U' j ++ R' ++ X.
Proof.
  induction fuel as [|f IH]; intros P U R P' U' R' H j X; simpl in H.
  - injection H as <- <- <-. reflexivity.
  - destruct P as [|p P0]; [injection H as <- <- <-; reflexivity|].
    destruct U as [|u U0]; [injection H as <- <- <-; reflexivity|].
    destruct (sym_eqb (last (p :: P0) S0) (last (u :: U0) S0)) eqn:E;
      [|injection H as <- <- <-; reflexivity].
    rewrite <- (IH _ _ _ _ _ _ H j X).
    apply sym_eqb_spec in E.
    set (x := last (p :: P0) S0) in *.
    assert (HP : p :: P0 = removelast (p :: P0) ++ [x])
      by (apply app_removelast_last; discriminate).
    assert (HU : u :: U0 = removelast (u :: U0) ++ [x])
      by (rewrite E; apply app_removelast_last; discriminate).
    rewrite HP at 1. rewrite HU at 1.
    rewrite <- app_assoc. cbn [app]. f_equal.
    rewrite app_comm_cons, rep_rot, <- app_assoc. reflexivity.
Qed.

Lemma rep_mul : forall (u : list Sym) a j, rep (rep u a) j = rep u (a * j).
Proof.
  intros u a j; induction j as [|j IH]; simpl.
  - rewrite Nat.mul_0_r. reflexivity.
  - rewrite IH, <- rep_add. f_equal. lia.
Qed.

Definition snf (s : sside) : list Sym * list Sym * list Sym :=
  let P := s_pre s ++ rep (s_u s) (s_b s) in
  unrot (length P) P (rep (s_u s) (s_a s)) (s_post s).

Lemma snf_den : forall s P U R, snf s = (P, U, R) ->
  forall X j, sden X j s = P ++ rep U j ++ R ++ X.
Proof.
  intros s P U R H X j. unfold snf in H.
  rewrite <- (unrot_den _ _ _ _ _ _ _ H j X).
  unfold sden. rewrite rep_mul, Nat.add_comm, rep_add, <- !app_assoc.
  reflexivity.
Qed.

(** Trailing blanks. *)
Fixpoint drop0 (m : list Sym) : list Sym :=
  match m with S0 :: t => drop0 t | _ => m end.

Definition rstrip0 (l : list Sym) : list Sym := rev (drop0 (rev l)).

Lemma drop0_spec : forall m, exists k, m = repeat S0 k ++ drop0 m.
Proof.
  induction m as [|x m IH]; [exists 0; reflexivity|].
  destruct x.
  - destruct IH as (k & Hk). exists (S k). simpl. f_equal. exact Hk.
  - exists 0. reflexivity.
Qed.

Lemma rev_repeat_S0 : forall k, rev (repeat S0 k) = repeat S0 k.
Proof.
  induction k as [|k IH]; [reflexivity|].
  simpl. rewrite IH. clear IH. induction k; [reflexivity | simpl; f_equal; assumption].
Qed.

Lemma rstrip0_blanks : forall l, exists k, l = rstrip0 l ++ repeat S0 k.
Proof.
  intros l. destruct (drop0_spec (rev l)) as (k & Hk). exists k.
  unfold rstrip0. rewrite <- (rev_involutive l) at 1. rewrite Hk at 1.
  rewrite rev_app_distr, rev_repeat_S0. reflexivity.
Qed.

Lemma lift_side_blanks : forall k r, lift_side (r ++ repeat S0 k) = lift_side r.
Proof.
  induction k; intros r; simpl.
  - rewrite app_nil_r. reflexivity.
  - replace (r ++ S0 :: repeat S0 k) with ((r ++ [S0]) ++ repeat S0 k)
      by (rewrite <- app_assoc; reflexivity).
    rewrite IHk. apply lift_side_app_blank.
Qed.

Lemma lift_side_rstrip0 : forall l, lift_side l = lift_side (rstrip0 l).
Proof.
  intros l. destruct (rstrip0_blanks l) as (k & Hk).
  rewrite Hk at 1. apply lift_side_blanks.
Qed.

Lemma lift_side_app_rstrip : forall A R,
  lift_side (A ++ R) = lift_side (A ++ rstrip0 R).
Proof.
  intros A R. destruct (rstrip0_blanks R) as (k & Hk).
  rewrite Hk at 1. rewrite app_assoc. apply lift_side_blanks.
Qed.

(** Two sides that denote the same list against every tail ([op = true]), or
    the same half-tape against the empty tail ([op = false]). *)
Definition side_eqv (op : bool) (s1 s2 : sside) : bool :=
  let '(P1, U1, R1) := snf s1 in
  let '(P2, U2, R2) := snf s2 in
  if op then
    match U1, U2 with
    | [], [] => syms_eqb (P1 ++ R1) (P2 ++ R2)
    | _, _ => syms_eqb P1 P2 && syms_eqb U1 U2 && syms_eqb R1 R2
    end
  else match U1, U2 with
       | [], [] => syms_eqb (rstrip0 (P1 ++ R1)) (rstrip0 (P2 ++ R2))
       | _, _ => syms_eqb P1 P2 && syms_eqb U1 U2
                 && syms_eqb (rstrip0 R1) (rstrip0 R2)
       end.

Lemma side_eqv_open : forall s1 s2, side_eqv true s1 s2 = true ->
  forall X j, sden X j s1 = sden X j s2.
Proof.
  intros s1 s2 H X j. unfold side_eqv in H.
  destruct (snf s1) as [[P1 U1] R1] eqn:E1.
  destruct (snf s2) as [[P2 U2] R2] eqn:E2.
  rewrite (snf_den _ _ _ _ E1), (snf_den _ _ _ _ E2).
  destruct U1 as [|u1 U1'], U2 as [|u2 U2'].
  - apply syms_eqb_eq in H. rewrite !rep_nil. simpl.
    rewrite !app_assoc, H. reflexivity.
  - repeat (apply andb_prop in H as [H ?]).
    apply syms_eqb_eq in H0. discriminate.
  - repeat (apply andb_prop in H as [H ?]).
    apply syms_eqb_eq in H0. discriminate.
  - repeat (apply andb_prop in H as [H ?]).
    repeat match goal with
           | [ H1 : syms_eqb _ _ = true |- _ ] => apply syms_eqb_eq in H1
           end.
    subst. rewrite H1. reflexivity.
Qed.

Lemma side_eqv_closed : forall s1 s2, side_eqv false s1 s2 = true ->
  forall j, lift_side (sden [] j s1) = lift_side (sden [] j s2).
Proof.
  intros s1 s2 H j. unfold side_eqv in H.
  destruct (snf s1) as [[P1 U1] R1] eqn:E1.
  destruct (snf s2) as [[P2 U2] R2] eqn:E2.
  rewrite (snf_den _ _ _ _ E1), (snf_den _ _ _ _ E2), !app_nil_r.
  destruct U1 as [|u1 U1'], U2 as [|u2 U2'].
  - apply syms_eqb_eq in H. rewrite !rep_nil. simpl.
    rewrite lift_side_rstrip0, H, <- lift_side_rstrip0. reflexivity.
  - repeat (apply andb_prop in H as [H ?]).
    apply syms_eqb_eq in H0. discriminate.
  - repeat (apply andb_prop in H as [H ?]).
    apply syms_eqb_eq in H0. discriminate.
  - repeat (apply andb_prop in H as [H ?]).
    repeat match goal with
           | [ H1 : syms_eqb _ _ = true |- _ ] => apply syms_eqb_eq in H1
           end.
    subst. rewrite !app_assoc, (lift_side_app_rstrip _ R1),
      (lift_side_app_rstrip _ R2), H0, H1. reflexivity.
Qed.

(** Configurations equal against every tail, and equal up to [lift] against
    the tails the flags permit. *)
Definition cexact (a b : sconf) : bool :=
  st_eqb (c_st a) (c_st b) && sym_eqb (c_h a) (c_h b)
  && side_eqv true (c_l a) (c_l b) && side_eqv true (c_r a) (c_r b).

Lemma cexact_den : forall a b, cexact a b = true ->
  forall XL XR j, cden XL XR j a = cden XL XR j b.
Proof.
  intros a b H XL XR j. unfold cexact in H.
  repeat (apply andb_prop in H as [H ?]).
  apply st_eqb_spec in H. apply sym_eqb_spec in H2.
  unfold cden. rewrite H, H2, (side_eqv_open _ _ H1), (side_eqv_open _ _ H0).
  reflexivity.
Qed.

(** ** The link: an inner rule's right-hand side is its left-hand side one
    index over, with words moved to or from the tails *)

Definition spush (s : sside) (w : list Sym) : sside :=
  mkS (s_pre s) (s_u s) (s_a s) (s_b s) (s_post s ++ w).

Lemma sden_push : forall X j s w, sden (w ++ X) j s = sden X j (spush s w).
Proof. intros. unfold sden, spush; simpl. rewrite <- !app_assoc. reflexivity. Qed.

Definition sshift (s : sside) : sside :=
  mkS (s_pre s) (s_u s) (s_a s) (s_b s + s_a s) (s_post s).

Lemma sden_shift : forall X j s, sden X (S j) s = sden X j (sshift s).
Proof.
  intros X j [p u a b q]. unfold sden, sshift; simpl.
  replace (a * S j + b) with (a * j + (b + a)) by ring. reflexivity.
Qed.

Definition cpush (c : sconf) (wl wr : list Sym) : sconf :=
  mkC (c_st c) (spush (c_l c) wl) (c_h c) (spush (c_r c) wr).

Definition cshift (c : sconf) : sconf :=
  mkC (c_st c) (sshift (c_l c)) (c_h c) (sshift (c_r c)).

Lemma cden_push : forall XL XR j c wl wr,
  cden (wl ++ XL) (wr ++ XR) j c = cden XL XR j (cpush c wl wr).
Proof. intros. unfold cden, cpush; simpl. rewrite !sden_push. reflexivity. Qed.

Lemma cden_shift : forall XL XR j c, cden XL XR (S j) c = cden XL XR j (cshift c).
Proof. intros. unfold cden, cshift; simpl. rewrite !sden_shift. reflexivity. Qed.

(** UP: [rhs] at [i] with [AL]/[AR] still on the tails is [lhs] at [S i]. *)
Definition link_up (Ir : LRule) (AL AR : list Sym) : bool :=
  cexact (cpush (lr_rhs Ir) AL AR) (cshift (lr_lhs Ir)).

(** DOWN: [rhs] at [S i] is [lhs] at [i] with [BL]/[BR] pushed on the tails. *)
Definition link_down (Ir : LRule) (BL BR : list Sym) : bool :=
  cexact (cshift (lr_rhs Ir)) (cpush (lr_lhs Ir) BL BR).

(** ** The two iterations *)

Section Iter.

Variable tm : TM.
Variable Ir  : LRule.
Hypothesis HI : RuleSound tm false false Ir.

Lemma inner_step : forall XL XR i,
  csteps tm (lr_ca Ir * i + lr_cb Ir) (cden XL XR i (lr_lhs Ir))
    = Some (cden XL XR i (lr_rhs Ir)).
Proof. intros. apply HI; discriminate. Qed.

Lemma iter_up : forall AL AR, link_up Ir AL AR = true ->
  forall n i XL XR, exists m,
    csteps tm m (cden (rep AL n ++ XL) (rep AR n ++ XR) i (lr_lhs Ir))
      = Some (cden XL XR (i + n) (lr_lhs Ir)).
Proof.
  intros AL AR Hl n; induction n as [|n IH]; intros i XL XR.
  - exists 0. rewrite Nat.add_0_r. reflexivity.
  - destruct (IH (S i) XL XR) as (m & Hm).
    exists (lr_ca Ir * i + lr_cb Ir + m).
    rewrite csteps_add. cbn [rep]. rewrite <- !app_assoc.
    rewrite inner_step, cden_push, (cexact_den _ _ Hl), <- cden_shift.
    replace (i + S n) with (S i + n) by lia. exact Hm.
Qed.

Lemma iter_down : forall BL BR, link_down Ir BL BR = true ->
  forall n i XL XR, exists m,
    csteps tm m (cden XL XR (i + n) (lr_lhs Ir))
      = Some (cden (rep BL n ++ XL) (rep BR n ++ XR) i (lr_lhs Ir)).
Proof.
  intros BL BR Hl n; induction n as [|n IH]; intros i XL XR.
  - exists 0. rewrite Nat.add_0_r. reflexivity.
  - destruct (IH i (BL ++ XL) (BR ++ XR)) as (m & Hm).
    exists (lr_ca Ir * (i + S n) + lr_cb Ir + m).
    rewrite csteps_add, inner_step.
    replace (i + S n) with (S (i + n)) by lia.
    rewrite cden_shift, (cexact_den _ _ Hl), <- cden_push.
    rewrite Hm. cbn [rep]. rewrite !app_assoc, !rep_shift. reflexivity.
Qed.

End Iter.

(** ** A configuration at an affine index, followed by fixed rests *)

(** [c] at index [i0 + (al*j + be)], each side followed by its rest. *)
Definition at_idx (c : sconf) (i0 al be : nat) (rl rr : sside) : option sconf :=
  match sapp (sidx (c_l c) i0 al be) rl, sapp (sidx (c_r c) i0 al be) rr with
  | Some l, Some r => Some (mkC (c_st c) l (c_h c) r)
  | _, _ => None
  end.

Lemma at_idx_den : forall c i0 al be rl rr c', at_idx c i0 al be rl rr = Some c' ->
  forall XL XR j, cden XL XR j c'
    = cden (sden XL j rl) (sden XR j rr) (i0 + (al * j + be)) c.
Proof.
  intros c i0 al be rl rr c' H XL XR j. unfold at_idx in H.
  destruct (sapp (sidx (c_l c) i0 al be) rl) as [l|] eqn:El; [|discriminate].
  destruct (sapp (sidx (c_r c) i0 al be) rr) as [r|] eqn:Er; [|discriminate].
  injection H as <-. unfold cden; simpl.
  rewrite (sapp_sound _ _ _ El), (sapp_sound _ _ _ Er), !sidx_den. reflexivity.
Qed.

(** [c] at index [i0], each side followed by a word repeated [al*j + be]
    times and then its rest. *)
Definition at_push (c : sconf) (i0 : nat) (AL AR : list Sym) (al be : nat)
    (rl rr : sside) : option sconf :=
  match sapp (srep AL al be) rl, sapp (srep AR al be) rr with
  | Some tl, Some tr => at_idx c i0 0 0 tl tr
  | _, _ => None
  end.

Lemma at_push_den : forall c i0 AL AR al be rl rr c',
  at_push c i0 AL AR al be rl rr = Some c' ->
  forall XL XR j, cden XL XR j c'
    = cden (rep AL (al * j + be) ++ sden XL j rl)
           (rep AR (al * j + be) ++ sden XR j rr) i0 c.
Proof.
  intros c i0 AL AR al be rl rr c' H XL XR j. unfold at_push in H.
  destruct (sapp (srep AL al be) rl) as [tl|] eqn:El; [|discriminate].
  destruct (sapp (srep AR al be) rr) as [tr|] eqn:Er; [|discriminate].
  rewrite (at_idx_den _ _ _ _ _ _ _ H XL XR j).
  rewrite (sapp_sound _ _ _ El), (sapp_sound _ _ _ Er), !srep_den.
  replace (i0 + (0 * j + 0)) with i0 by lia. reflexivity.
Qed.

(** ** Segments *)

Inductive nseg : Set :=
| NCh (l : list rstep)                  (** a kernel chain *)
| NUp (k : nat) (AL AR : list Sym) (i0 al be : nat) (rl rr : sside) (fin : bool)
    (** [al*j+be] rounds of inner rule [k], index [i0] upwards, consuming
        [AL]/[AR]; with [fin], one more round to the rule's right-hand side *)
| NDn (k : nat) (BL BR : list Sym) (i0 al be : nat) (rl rr : sside) (fin : bool).
    (** [al*j+be] rounds of inner rule [k], index down to [i0], pushing
        [BL]/[BR]; with [fin], one more round at [i0] *)

Definition pick (fin : bool) (Ir : LRule) : sconf :=
  if fin then lr_rhs Ir else lr_lhs Ir.

Fixpoint nrun (tm : TM) (el er : bool) (rs : list LRule) (l : list nseg)
    (c : sconf) : option (sconf * bool) :=
  match l with
  | [] => Some (c, false)
  | NCh ch :: l' =>
      match rrun tm el er rs ch c with
      | Some (c1, _, cb) =>
          match nrun tm el er rs l' c1 with
          | Some (c2, p) => Some (c2, negb (cb =? 0) || p)
          | None => None
          end
      | None => None
      end
  | NUp k AL AR i0 al be rl rr fin :: l' =>
      match nth_error rs k with
      | Some Ir =>
          if link_up Ir AL AR then
            match at_push (lr_lhs Ir) i0 AL AR al be rl rr,
                  at_idx (pick fin Ir) i0 al be rl rr with
            | Some m0, Some m1 => if cexact c m0 then nrun tm el er rs l' m1 else None
            | _, _ => None
            end
          else None
      | None => None
      end
  | NDn k BL BR i0 al be rl rr fin :: l' =>
      match nth_error rs k with
      | Some Ir =>
          if link_down Ir BL BR then
            match at_idx (lr_lhs Ir) i0 al be rl rr,
                  at_push (pick fin Ir) i0 BL BR al be rl rr with
            | Some m0, Some m1 => if cexact c m0 then nrun tm el er rs l' m1 else None
            | _, _ => None
            end
          else None
      | None => None
      end
  end.

(** The optional last round of a segment. *)
Lemma fin_step : forall tm Ir fin, RuleSound tm false false Ir ->
  forall XL XR i, exists m,
    csteps tm m (cden XL XR i (lr_lhs Ir)) = Some (cden XL XR i (pick fin Ir)).
Proof.
  intros tm Ir fin HI XL XR i. destruct fin; simpl.
  - exists (lr_ca Ir * i + lr_cb Ir). apply (inner_step tm Ir HI).
  - exists 0. reflexivity.
Qed.

Theorem nrun_sound : forall tm el er rs l c c' p,
  Forall (RuleSound tm false false) rs ->
  nrun tm el er rs l c = Some (c', p) ->
  forall XL XR j, (el = true -> XL = []) -> (er = true -> XR = []) ->
  exists m, (p = true -> 0 < m)
            /\ csteps tm m (cden XL XR j c) = Some (cden XL XR j c').
Proof.
  intros tm el er rs l; induction l as [|sg l IH];
    intros c c' p HF H XL XR j HL HR; cbn in H.
  - injection H as <- <-. exists 0. split; [discriminate | reflexivity].
  - assert (Hrule : forall k Ir, nth_error rs k = Some Ir -> RuleSound tm false false Ir).
    { intros k Ir Hk. rewrite Forall_forall in HF. apply HF.
      eapply nth_error_In; exact Hk. }
    destruct sg as [ch | k AL AR i0 al be rl rr fin | k BL BR i0 al be rl rr fin].
    + destruct (rrun tm el er rs ch c) as [[[c1 ca] cb]|] eqn:E1; [|discriminate].
      destruct (nrun tm el er rs l c1) as [[c2 p2]|] eqn:E2; [|discriminate].
      injection H as <- <-.
      destruct (IH c1 c2 p2 HF E2 XL XR j HL HR) as (m2 & Hp2 & Hm2).
      exists (ca * j + cb + m2). split.
      * intros Hp. apply orb_true_iff in Hp as [Hp|Hp].
        -- apply negb_true_iff, Nat.eqb_neq in Hp. lia.
        -- specialize (Hp2 Hp). lia.
      * rewrite csteps_add, (rrun_sound tm el er rs ch c c1 ca cb HF E1 XL XR j HL HR).
        exact Hm2.
    + destruct (nth_error rs k) as [Ir|] eqn:Ek; [|discriminate].
      destruct (link_up Ir AL AR) eqn:El; [|discriminate].
      destruct (at_push (lr_lhs Ir) i0 AL AR al be rl rr) as [m0|] eqn:E0;
        [|discriminate].
      destruct (at_idx (pick fin Ir) i0 al be rl rr) as [m1|] eqn:E1; [|discriminate].
      destruct (cexact c m0) eqn:Ec; [|discriminate].
      destruct (IH m1 c' p HF H XL XR j HL HR) as (m2 & Hp2 & Hm2).
      pose proof (Hrule k Ir Ek) as HI.
      destruct (iter_up tm Ir HI AL AR El (al * j + be) i0
                  (sden XL j rl) (sden XR j rr)) as (mi & Hmi).
      destruct (fin_step tm Ir fin HI (sden XL j rl) (sden XR j rr)
                  (i0 + (al * j + be))) as (mf & Hmf).
      exists (mi + (mf + m2)). split; [intros Hp; specialize (Hp2 Hp); lia|].
      rewrite (cexact_den _ _ Ec), (at_push_den _ _ _ _ _ _ _ _ _ E0).
      rewrite csteps_add, Hmi, csteps_add, Hmf.
      rewrite <- (at_idx_den _ _ _ _ _ _ _ E1). exact Hm2.
    + destruct (nth_error rs k) as [Ir|] eqn:Ek; [|discriminate].
      destruct (link_down Ir BL BR) eqn:El; [|discriminate].
      destruct (at_idx (lr_lhs Ir) i0 al be rl rr) as [m0|] eqn:E0; [|discriminate].
      destruct (at_push (pick fin Ir) i0 BL BR al be rl rr) as [m1|] eqn:E1;
        [|discriminate].
      destruct (cexact c m0) eqn:Ec; [|discriminate].
      destruct (IH m1 c' p HF H XL XR j HL HR) as (m2 & Hp2 & Hm2).
      pose proof (Hrule k Ir Ek) as HI.
      destruct (iter_down tm Ir HI BL BR El (al * j + be) i0
                  (sden XL j rl) (sden XR j rr)) as (mi & Hmi).
      destruct (fin_step tm Ir fin HI (rep BL (al * j + be) ++ sden XL j rl)
                  (rep BR (al * j + be) ++ sden XR j rr) i0) as (mf & Hmf).
      exists (mi + (mf + m2)). split; [intros Hp; specialize (Hp2 Hp); lia|].
      rewrite (cexact_den _ _ Ec), (at_idx_den _ _ _ _ _ _ _ E0).
      rewrite csteps_add, Hmi, csteps_add, Hmf.
      rewrite <- (at_push_den _ _ _ _ _ _ _ _ _ E1). exact Hm2.
Qed.

Definition ceqL (el er : bool) (a b : sconf) : bool :=
  st_eqb (c_st a) (c_st b) && sym_eqb (c_h a) (c_h b)
  && side_eqv (negb el) (c_l a) (c_l b) && side_eqv (negb er) (c_r a) (c_r b).

Lemma side_eqv_lift : forall el s1 s2 X j, side_eqv (negb el) s1 s2 = true ->
  (el = true -> X = []) -> lift_side (sden X j s1) = lift_side (sden X j s2).
Proof.
  intros el s1 s2 X j H HX. destruct el; simpl in H.
  - rewrite (HX eq_refl). exact (side_eqv_closed _ _ H j).
  - rewrite (side_eqv_open _ _ H). reflexivity.
Qed.

Lemma ceqL_lift : forall el er a b, ceqL el er a b = true ->
  forall XL XR j, (el = true -> XL = []) -> (er = true -> XR = []) ->
  lift (cden XL XR j a) = lift (cden XL XR j b).
Proof.
  intros el er a b H XL XR j HL HR. unfold ceqL in H.
  repeat (apply andb_prop in H as [H ?]).
  apply st_eqb_spec in H. apply sym_eqb_spec in H2.
  unfold lift, cden, lift_tape; simpl.
  rewrite H, H2, (side_eqv_lift _ _ _ _ _ H1 HL), (side_eqv_lift _ _ _ _ _ H0 HR).
  reflexivity.
Qed.

(** ** Nested arms

    What an arm of the nested boards carries: a positive run to a
    configuration that lifts to the right-hand side's. *)

Definition ReachL (tm : TM) (el er : bool) (c c' : sconf) : Prop :=
  forall XL XR j, (el = true -> XL = []) -> (er = true -> XR = []) ->
  exists m c'', 0 < m /\ csteps tm m (cden XL XR j c) = Some c''
                /\ lift c'' = lift (cden XL XR j c').

Lemma reachL_of_sound : forall tm el er r,
  RuleSound tm el er r -> 0 < lr_cb r ->
  ReachL tm el er (lr_lhs r) (lr_rhs r).
Proof.
  intros tm el er r Hs Hc XL XR j HL HR.
  exists (lr_ca r * j + lr_cb r), (cden XL XR j (lr_rhs r)).
  split; [lia | split; [exact (Hs XL XR j HL HR) | reflexivity]].
Qed.

Definition check_narm (tm : TM) (el er : bool) (rs : list LRule) (a : LRule)
    (l : list nseg) : bool :=
  match nrun tm el er rs l (lr_lhs a) with
  | Some (c, true) => ceqL el er c (lr_rhs a)
  | _ => false
  end.

Theorem narm_reach : forall tm el er rs a l,
  Forall (RuleSound tm false false) rs ->
  check_narm tm el er rs a l = true ->
  ReachL tm el er (lr_lhs a) (lr_rhs a).
Proof.
  intros tm el er rs a l HF H XL XR j HL HR. unfold check_narm in H.
  destruct (nrun tm el er rs l (lr_lhs a)) as [[c p]|] eqn:E; [|discriminate].
  destruct p; [|discriminate].
  destruct (nrun_sound tm el er rs l _ _ _ HF E XL XR j HL HR) as (m & Hp & Hm).
  exists m, (cden XL XR j c). split; [exact (Hp eq_refl)|]. split; [exact Hm|].
  exact (ceqL_lift _ _ _ _ H XL XR j HL HR).
Qed.
