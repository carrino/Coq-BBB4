(** * Comb3_0RB1LC_1LC1RD_1LA0LC_0RD1RB: a three-cell-comb bouncer counter.

    bbchallenge 0RB1LC_1LC1RD_1LA0LC_0RD1RB, the second
    [KCOPY2_EARLY_ONLY] row of the undecided core
    (tools/counter_encodings.tsv; tools/closeout/core_rows.txt).

    Same species as [Comb2_0RB1LC_1LC0RD_1RD0LC_1LA1RB.v] -- head at
    the right edge on a blank in state B, everything to its left -- but
    the comb unit is three cells and the counter's digits are [00] and
    [01]:

      anchor v :  (101)^v  <v in binary, low digit first,
                            digit 0 = 00, digit 1 = 01>   [B:0]

    so again the counter's value is written twice, once in unary as the
    comb's length and once in binary beyond it.  One lap is THREE
    passes, each of the same shape -- a [B 0] turn, state C crossing the
    comb leftward three steps per unit, a gadget at the far end, then
    the head walking back right and rebuilding the comb three steps per
    unit:

      pass 1 (6v + 4*carry(v) + 5 steps) runs the carry: [C 0]/[A 1]
             eat the counter's low digit-1s two steps each (past the
             top digit the cells are blank, which is the same rule, so
             overflow needs no separate case) and leave a run of ones;
      pass 2 (6v + 4*carry(v) + 9 steps) blanks that run again and
             lays the carry's zero digits down;
      pass 3 (6v + 7 steps) sets the digit the carry stopped at and
             closes the comb one unit longer.

    Since [v] grows forever and every anchor visits all four states,
    the machine never quasihalts.

    Lap length [18v + 8*carry(v) + 21], checked differentially against
    the raw simulator for [v = 1..300].

    One [lift] step is needed at the end: at [v] a power of two the
    counter's top digit is fresh, and the pass-3 gadget leaves one
    trailing blank cell beyond the new working area, so the reached
    configuration equals the next anchor only after that blank is
    stripped ([tail_lift]). *)

From Coq Require Import Arith Lia Bool List PArith FunctionalExtensionality.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape LapGlue BCtrCounter.
Import ListNotations.

Definition mk (w : Sym) (d : Dir) (n : St) : option Trans :=
  Some (mkTrans w d n).

(** 0RB1LC_1LC1RD_1LA0LC_0RD1RB *)
Definition tm_c3 : TM := fun q s =>
  match q, s with
  | StA, S0 => mk S0 DR StB | StA, S1 => mk S1 DL StC
  | StB, S0 => mk S1 DL StC | StB, S1 => mk S1 DR StD
  | StC, S0 => mk S1 DL StA | StC, S1 => mk S0 DL StC
  | StD, S0 => mk S0 DR StD | StD, S1 => mk S1 DR StB
  end.

(** ** The counter word: digit 0 = [00], digit 1 = [01] *)

Fixpoint encp (w : list bool) : list Sym :=
  match w with
  | [] => []
  | b :: t => S0 :: (if b then S1 else S0) :: encp t
  end.

(** What is left once the carry has eaten the low digit-1s. *)
Fixpoint crest0 (w : list bool) : list bool :=
  match w with
  | true :: t => crest0 t
  | _ => w
  end.

Lemma encp_incr : forall w,
  encp (incr w) = repeat S0 (2 * carry w) ++ S0 :: S1 :: encp (crest w).
Proof.
  induction w as [|b t IH]; [reflexivity|].
  destruct b; [|reflexivity].
  change (encp (incr (true :: t))) with (S0 :: S0 :: encp (incr t)).
  change (carry (true :: t)) with (S (carry t)).
  change (crest (true :: t)) with (crest t).
  rewrite IH.
  replace (2 * S (carry t)) with (2 + 2 * carry t) by lia.
  reflexivity.
Qed.

Lemma chd_encp : forall w, chd (encp w) = S0.
Proof. destruct w; reflexivity. Qed.

Lemma crest0_cases : forall w,
  (crest0 w = [] /\ crest w = []) \/ crest0 w = false :: crest w.
Proof.
  induction w as [|b t IH]; [left; split; reflexivity|].
  destruct b; [exact IH | right; reflexivity].
Qed.

Lemma chd_ctl_crest0 : forall w, chd (ctl (encp (crest0 w))) = S0.
Proof.
  intros w. destruct (crest0_cases w) as [[H0 _] | H]; rewrite H0 || rewrite H;
    reflexivity.
Qed.

Lemma ctl2_crest0 : forall w, ctl (ctl (encp (crest0 w))) = encp (crest w).
Proof.
  intros w. destruct (crest0_cases w) as [[H0 H1] | H].
  - rewrite H0, H1. reflexivity.
  - rewrite H. reflexivity.
Qed.

(** A missing top digit is a trailing blank, and blanks are invisible
    to [lift]. *)
Lemma lift_side_app_blank_l : forall l, lift_side (l ++ [S0]) = lift_side l.
Proof. exact WTape.lift_side_app_blank. Qed.

Lemma lift_left : forall q l l' h r,
  lift_side l = lift_side l' -> lift (q, (l, h, r)) = lift (q, (l', h, r)).
Proof. intros q l l' h r H. unfold lift; simpl. rewrite H. reflexivity. Qed.

(** ** Comb algebra *)

Lemma comb3 : forall j X,
  rep [S1; S0; S1] (S j) ++ X = S1 :: S0 :: S1 :: (rep [S1; S0; S1] j ++ X).
Proof. intros. cbn [rep]. rewrite <- app_assoc. reflexivity. Qed.

Lemma comb_snoc : forall i Z,
  rep [S1; S0; S1] i ++ S1 :: S0 :: S1 :: Z = rep [S1; S0; S1] (S i) ++ Z.
Proof.
  intros i Z. change (S1 :: S0 :: S1 :: Z) with ([S1; S0; S1] ++ Z).
  rewrite app_assoc, rep_shift. cbn [rep]. reflexivity.
Qed.

Lemma rep110 : forall i X,
  rep [S1; S1; S0] (S i) ++ X = S1 :: S1 :: S0 :: (rep [S1; S1; S0] i ++ X).
Proof. intros. cbn [rep]. rewrite <- app_assoc. reflexivity. Qed.

Lemma rep110_shift : forall i R,
  rep [S1; S1; S0] i ++ S1 :: S1 :: S0 :: R
  = S1 :: S1 :: S0 :: (rep [S1; S1; S0] i ++ R).
Proof.
  intros i R. change (S1 :: S1 :: S0 :: R) with ([S1; S1; S0] ++ R).
  rewrite app_assoc, rep_shift, <- app_assoc. reflexivity.
Qed.

(** ** The unit runs (each checked by [reflexivity]) *)

(** [B 0] turns the head around. *)
Lemma GB0 : forall L R,
  csteps tm_c3 1 (StB, (L, S0, R)) = Some (StC, (ctl L, chd L, S1 :: R)).
Proof. reflexivity. Qed.

(** One comb unit, crossed leftward. *)
Lemma GU : forall L R,
  csteps tm_c3 3 (StC, (S0 :: S1 :: L, S1, R))
  = Some (StC, (ctl L, chd L, S1 :: S1 :: S0 :: R)).
Proof. reflexivity. Qed.

(** One digit-1 of the counter, eaten by the carry. *)
Lemma GC : forall E R,
  csteps tm_c3 2 (StC, (S1 :: E, S0, R))
  = Some (StC, (ctl E, chd E, S1 :: S1 :: R)).
Proof. reflexivity. Qed.

(** The carry stops: [C 0]/[A 0] hand the head back to B. *)
Lemma GE : forall E R, chd E = S0 ->
  csteps tm_c3 2 (StC, (E, S0, R)) = Some (StB, (S0 :: ctl E, S1, R)).
Proof.
  intros E R H. destruct E as [|x E']; [reflexivity|].
  cbn [chd] in H. subst x. reflexivity.
Qed.

(** [B 1]/[D 1] cross two ones. *)
Lemma GD : forall L R,
  csteps tm_c3 2 (StB, (L, S1, S1 :: R))
  = Some (StB, (S1 :: S1 :: L, chd R, ctl R)).
Proof. reflexivity. Qed.

(** [B 1]/[D 0]/[D 1] rebuild one comb unit. *)
Lemma GW : forall L R,
  csteps tm_c3 3 (StB, (L, S1, S0 :: S1 :: R))
  = Some (StB, (S1 :: S0 :: S1 :: L, chd R, ctl R)).
Proof. reflexivity. Qed.

(** [C 1] blanks one cell and steps left (also off the tape end). *)
Lemma GCl : forall L R,
  csteps tm_c3 1 (StC, (L, S1, R)) = Some (StC, (ctl L, chd L, S0 :: R)).
Proof. reflexivity. Qed.

Lemma GB1 : forall L R,
  csteps tm_c3 1 (StB, (L, S1, R)) = Some (StD, (S1 :: L, chd R, ctl R)).
Proof. reflexivity. Qed.

Lemma GD0 : forall L R,
  csteps tm_c3 1 (StD, (L, S0, R)) = Some (StD, (S0 :: L, chd R, ctl R)).
Proof. reflexivity. Qed.

Lemma GD1 : forall L R,
  csteps tm_c3 1 (StD, (L, S1, R)) = Some (StB, (S1 :: L, chd R, ctl R)).
Proof. reflexivity. Qed.

(** Pass 3's gadget: the digit the carry stopped at is set.  The cell
    below the head is the digit's low cell, hence [S0]. *)
Lemma GS : forall X R,
  csteps tm_c3 5 (StC, (S0 :: X, S0, S0 :: S1 :: S1 :: S0 :: R))
  = Some (StB, (S1 :: S0 :: S1 :: S0 :: X, S1, S0 :: R)).
Proof. reflexivity. Qed.

(** ** Transported phases *)

Lemma ccross : forall i L R,
  csteps tm_c3 (3 * i) (StC, (S0 :: S1 :: (rep [S1; S0; S1] i ++ L), S1, R))
  = Some (StC, (S0 :: S1 :: L, S1, rep [S1; S1; S0] i ++ R)).
Proof.
  induction i as [|i IH]; intros L R; [reflexivity|].
  replace (3 * S i) with (3 + 3 * i) by lia.
  rewrite comb3, csteps_add, GU. cbn [chd ctl].
  rewrite IH, rep110_shift, rep110. reflexivity.
Qed.

Lemma csweep : forall w R,
  csteps tm_c3 (2 * carry w) (StC, (ctl (encp w), S0, R))
  = Some (StC, (ctl (encp (crest0 w)), S0, repeat S1 (2 * carry w) ++ R)).
Proof.
  induction w as [|b t IH]; intros R; [reflexivity|].
  destruct b; [|reflexivity].
  change (carry (true :: t)) with (S (carry t)).
  change (crest0 (true :: t)) with (crest0 t).
  change (ctl (encp (true :: t))) with (S1 :: encp t).
  replace (2 * S (carry t)) with (S (S (2 * carry t))) by lia.
  cbn [repeat app].
  replace (S (S (2 * carry t))) with (2 + 2 * carry t) by lia.
  rewrite csteps_add, GC, chd_encp, IH.
  rewrite !rep_snoc. reflexivity.
Qed.

Lemma gdn : forall i L R,
  csteps tm_c3 (2 * i) (StB, (L, S1, repeat S1 (2 * i) ++ R))
  = Some (StB, (repeat S1 (2 * i) ++ L, S1, R)).
Proof.
  induction i as [|i IH]; intros L R; [reflexivity|].
  replace (2 * S i) with (S (S (2 * i))) by lia.
  cbn [repeat app].
  replace (S (S (2 * i))) with (2 + 2 * i) by lia.
  rewrite csteps_add, GD. cbn [chd ctl].
  rewrite IH, !rep_snoc. reflexivity.
Qed.

Lemma clrn : forall i L R,
  csteps tm_c3 i (StC, (repeat S1 i ++ L, S1, R))
  = Some (StC, (L, S1, repeat S0 i ++ R)).
Proof.
  induction i as [|i IH]; intros L R; [reflexivity|].
  cbn [repeat app].
  replace (S i) with (1 + i) by lia.
  rewrite csteps_add, GCl. cbn [chd ctl].
  rewrite IH, rep_snoc. reflexivity.
Qed.

Lemma dzn : forall i L R,
  csteps tm_c3 i (StD, (L, S0, repeat S0 i ++ R))
  = Some (StD, (repeat S0 i ++ L, S0, R)).
Proof.
  induction i as [|i IH]; intros L R; [reflexivity|].
  cbn [repeat app].
  replace (S i) with (1 + i) by lia.
  rewrite csteps_add, GD0. cbn [chd ctl].
  rewrite IH, rep_snoc. reflexivity.
Qed.

Lemma gwn : forall i M,
  csteps tm_c3 (3 * S i) (StB, (M, S1, S0 :: rep [S1; S1; S0] i ++ [S1]))
  = Some (StB, (rep [S1; S0; S1] (S i) ++ M, S0, [])).
Proof.
  induction i as [|i IH]; intros M.
  - replace (3 * 1) with 3 by lia. cbn [rep app]. rewrite GW. reflexivity.
  - replace (3 * S (S i)) with (3 + 3 * S i) by lia.
    rewrite rep110, csteps_add, GW. cbn [chd ctl].
    rewrite IH, comb_snoc. reflexivity.
Qed.

(** The head of every pass: [B 0], then [v] comb units crossed. *)
Lemma start3 : forall j Y,
  csteps tm_c3 (1 + 3 * S j) (StB, (rep [S1; S0; S1] (S j) ++ Y, S0, []))
  = Some (StC, (ctl Y, chd Y, rep [S1; S1; S0] (S j) ++ [S1])).
Proof.
  intros j Y.
  replace (1 + 3 * S j) with (1 + (3 * j + 3)) by lia.
  rewrite comb3, csteps_add, GB0. cbn [chd ctl].
  rewrite csteps_add, ccross, GU, rep110. reflexivity.
Qed.

(** ** The three passes *)

Definition anchor (w : list bool) : cconf :=
  (StB, (rep [S1; S0; S1] (cval w) ++ encp w, S0, [])).

Definition mid1 (j : nat) (w : list bool) : cconf :=
  (StB, (rep [S1; S0; S1] (S j)
         ++ repeat S1 (2 * carry w + 2) ++ S0 :: encp (crest w), S0, [])).

Definition mid2 (j : nat) (w : list bool) : cconf :=
  (StB, (rep [S1; S0; S1] (S j)
         ++ S1 :: repeat S0 (2 * carry w + 2)
            ++ S1 :: S0 :: ctl (encp (crest w)), S0, [])).

Definition fin (j : nat) (w : list bool) : cconf :=
  (StB, (rep [S1; S0; S1] (S (S j))
         ++ repeat S0 (2 * carry w)
            ++ S0 :: S1 :: S0 :: ctl (encp (crest w)), S0, [])).

(** Pass 1: the carry. *)
Lemma pass1 : forall j w, cval w = S j ->
  csteps tm_c3 (6 * S j + 4 * carry w + 5) (anchor w) = Some (mid1 j w).
Proof.
  intros j w Hj. unfold anchor, mid1. rewrite Hj.
  replace (6 * S j + 4 * carry w + 5)
     with ((1 + 3 * S j) + (2 * carry w + (2 + (2 * carry w + (2 + 3 * S j)))))
     by lia.
  rewrite csteps_add, start3, chd_encp.
  rewrite csteps_add, csweep.
  rewrite csteps_add, (GE _ _ (chd_ctl_crest0 w)), ctl2_crest0.
  rewrite csteps_add, gdn.
  rewrite csteps_add, rep110, GD. cbn [chd ctl].
  rewrite gwn.
  replace (2 * carry w + 2) with (S (S (2 * carry w))) by lia.
  cbn [repeat app]. reflexivity.
Qed.

(** Pass 2: the run of ones is blanked and the carry's zeros laid down. *)
Lemma pass2 : forall j w, cval w = S j ->
  csteps tm_c3 (6 * S j + 4 * carry w + 9) (mid1 j w) = Some (mid2 j w).
Proof.
  intros j w Hj. unfold mid1, mid2.
  replace (6 * S j + 4 * carry w + 9)
     with ((1 + 3 * S j) + ((2 * carry w + 1)
           + (1 + (2 + (1 + ((2 * carry w + 1) + (1 + (1 + 3 * S j))))))))
     by lia.
  replace (2 * carry w + 2) with (S (2 * carry w + 1)) by lia.
  cbn [repeat app].
  rewrite csteps_add, start3. cbn [chd ctl].
  rewrite csteps_add, clrn.
  rewrite csteps_add, GCl. cbn [chd ctl].
  rewrite csteps_add, (GE _ _ (chd_encp (crest w))).
  rewrite csteps_add, GB1. cbn [chd ctl].
  rewrite csteps_add, dzn.
  rewrite csteps_add, rep110, GD0. cbn [chd ctl].
  rewrite csteps_add, GD1. cbn [chd ctl].
  rewrite gwn.
  replace (S (2 * carry w + 1)) with (1 + (2 * carry w + 1)) by lia.
  cbn [repeat app]. reflexivity.
Qed.

(** Pass 3: the digit is set and the comb closes one unit longer. *)
Lemma pass3 : forall j w, cval w = S j ->
  csteps tm_c3 (6 * S j + 7) (mid2 j w) = Some (fin j w).
Proof.
  intros j w Hj. unfold mid2, fin.
  replace (6 * S j + 7) with ((1 + 3 * S j) + (1 + (5 + 3 * S j))) by lia.
  replace (2 * carry w + 2) with (S (2 * carry w + 1)) by lia.
  cbn [repeat app].
  rewrite csteps_add, start3. cbn [chd ctl].
  rewrite csteps_add, GCl. cbn [chd ctl].
  replace (2 * carry w + 1) with (S (2 * carry w)) by lia.
  cbn [repeat app].
  rewrite csteps_add, rep110, GS, gwn.
  rewrite <- (comb_snoc (S j)), <- rep_snoc. reflexivity.
Qed.

(** ** The lap *)

(** The one place a blank has to be stripped: at an overflow the
    counter's new top digit has no cells on the tape yet, so the
    reached configuration carries one trailing blank the anchor does
    not spell. *)
Lemma tail_lift : forall i n u,
  lift (StB, (rep [S1; S0; S1] i ++ repeat S0 n
              ++ S0 :: S1 :: S0 :: ctl (encp u), S0, []))
  = lift (StB, (rep [S1; S0; S1] i ++ repeat S0 n
                ++ S0 :: S1 :: encp u, S0, [])).
Proof.
  intros i n u. destruct u as [|b u']; [|reflexivity].
  cbn [encp ctl]. apply lift_left.
  change (S0 :: S1 :: S0 :: @nil Sym) with ([S0; S1] ++ [S0]).
  rewrite (app_assoc (repeat S0 n)), (app_assoc (rep [S1; S0; S1] i)).
  rewrite lift_side_app_blank_l. reflexivity.
Qed.

Lemma lap_lift : forall j w, cval w = S j ->
  lift (fin j w) = lift (anchor (incr w)).
Proof.
  intros j w Hj. unfold fin, anchor.
  rewrite cval_incr, Hj, encp_incr.
  apply tail_lift.
Qed.

Lemma lap : forall j w, cval w = S j ->
  csteps tm_c3 (18 * cval w + 8 * carry w + 21) (anchor w) = Some (fin j w).
Proof.
  intros j w Hj.
  replace (18 * cval w + 8 * carry w + 21)
     with ((6 * S j + 4 * carry w + 5)
           + ((6 * S j + 4 * carry w + 9) + (6 * S j + 7))) by lia.
  rewrite csteps_add, (pass1 j w Hj), csteps_add, (pass2 j w Hj).
  apply (pass3 j w Hj).
Qed.

(** ** Bootstrap, visits, and the theorem *)

Definition Cc (p : positive) : cconf := anchor (bits p).

Lemma cval_bits_pos : forall p, exists j, cval (bits p) = S j.
Proof.
  induction p as [p IH|p IH|]; simpl.
  - eauto.
  - destruct IH as [j Hj]. rewrite Hj. exists (j + S j). lia.
  - exists 0. reflexivity.
Qed.

Lemma boot_c3 : exists t0, stepn tm_c3 t0 InitES = Some (lift (Cc 1)).
Proof.
  exists 22.
  assert (H : match csteps tm_c3 22 c0 with
              | Some c => ceqb c (Cc 1)
              | None => false
              end = true) by (vm_compute; reflexivity).
  destruct (csteps tm_c3 22 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E).
  f_equal. apply ceqb_lift. exact H.
Qed.

(** [B], [C] and [A] are visited in the anchor's first four steps;
    [D] first appears when pass 1 hands the head back to B on a one,
    which is [1 + 3v + 2*carry(v) + 2] steps in. *)
Lemma vis_c3 : forall j w q, cval w = S j ->
  exists k c, csteps tm_c3 k (anchor w) = Some c /\ fst c = q.
Proof.
  intros j w q Hj. unfold anchor. rewrite Hj. destruct q.
  - (* A: three steps in, [C 0] hands the head to A *)
    rewrite comb3. exists 3. eexists. split; reflexivity.
  - (* B: the anchor itself *)
    exists 0. eexists. split; reflexivity.
  - (* C: one step in *)
    exists 1. eexists. split; reflexivity.
  - (* D: pass 1 hands the head back to B on a one, and [B 1] is D's
       only entry *)
    exists ((1 + 3 * S j) + (2 * carry w + (2 + 1))). eexists. split.
    + rewrite csteps_add, start3, chd_encp.
      rewrite csteps_add, csweep.
      rewrite csteps_add, (GE _ _ (chd_ctl_crest0 w)), ctl2_crest0.
      rewrite GB1. reflexivity.
    + reflexivity.
Qed.

(** 0RB1LC_1LC1RD_1LA0LC_0RD1RB never quasihalts. *)
Theorem nqh_0RB1LC_1LC1RD_1LA0LC_0RD1RB : NeverQuasiHaltsSt tm_c3.
Proof.
  apply (glue_neverqh tm_c3 Cc 1).
  - exact boot_c3.
  - intros p _. unfold Cc. rewrite bits_succ.
    destruct (cval_bits_pos p) as [j Hj].
    exists (18 * cval (bits p) + 8 * carry (bits p) + 21), (fin j (bits p)).
    split; [apply (lap j _ Hj) | split].
    + rewrite <- bits_succ. unfold Cc.
      rewrite bits_succ. apply (lap_lift j _ Hj).
    + lia.
  - intros p q _. unfold Cc.
    destruct (cval_bits_pos p) as [j Hj].
    apply (vis_c3 j _ q Hj).
Qed.

Theorem tm_c3_nonhalt : NonHalt tm_c3.
Proof. apply never_qh_nonhalt, nqh_0RB1LC_1LC1RD_1LA0LC_0RD1RB. Qed.
