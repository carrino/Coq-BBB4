(** * Comb2_0RB1LC_1LC0RD_1RD0LC_1LA1RB: a comb bouncer counter.

    bbchallenge 0RB1LC_1LC0RD_1RD0LC_1LA1RB, one of the two
    [KCOPY2_EARLY_ONLY] rows of the undecided core
    (tools/counter_encodings.tsv; tools/closeout/core_rows.txt).

    The head sits at the RIGHT edge of the written tape on a blank, in
    state B, and everything is to its left, nearest cell first:

      anchor0 v :  (10)^v  0   <v in binary, low digit first,
                                 digit 0 = 00, digit 1 = 11>   [B:0]
      anchor1 v :  (10)^v  11  <same counter>                  [B:0]

    So the counter's value is written TWICE -- in unary as the comb's
    length and in binary beyond it -- and one lap of the machine is two
    half-laps:

      anchor0 v -> anchor1 v      (6v + 3 steps)
      anchor1 v -> anchor0 (v+1)  (6v + 8*carry(v) + 13 steps)

    Both halves have the same skeleton.  A single [B 0] turns the head
    around; state C then crosses the comb leftward, four steps per
    unit, converting each [01] pair into a pair of ones deposited on
    the right; a short gadget at the far end does the arithmetic (the
    first half just rebuilds the low marker, the second runs the binary
    increment: [C 1] blanks the counter's low digit-1s -- the run past
    the top digit is blank already, so overflow is the same rule -- and
    a five-step gadget sets the first digit-0); then the head walks
    back right, first over the blanked carry cells (three steps each),
    then over the run of ones, which the [B 1]/[D 1] alternation
    rewrites as a comb one unit longer.

    Since [v] grows forever and every anchor visits all four states in
    its first five steps, the machine never quasihalts.

    Lap length [12v + 8*carry(v) + 16], checked differentially against
    the raw simulator for [v = 1..300]. *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape LapGlue BCtrCounter.
Import ListNotations.

Definition mk (w : Sym) (d : Dir) (n : St) : option Trans :=
  Some (mkTrans w d n).

(** 0RB1LC_1LC0RD_1RD0LC_1LA1RB *)
Definition tm_c2 : TM := fun q s =>
  match q, s with
  | StA, S0 => mk S0 DR StB | StA, S1 => mk S1 DL StC
  | StB, S0 => mk S1 DL StC | StB, S1 => mk S0 DR StD
  | StC, S0 => mk S1 DR StD | StC, S1 => mk S0 DL StC
  | StD, S0 => mk S1 DL StA | StD, S1 => mk S1 DR StB
  end.

(** ** The counter word, two cells per digit

    [cval], [carry], [crest], [incr], [bits] are [BCtrCounter]'s; only
    the tape encoding differs. *)

Fixpoint enc2 (w : list bool) : list Sym :=
  match w with
  | [] => []
  | b :: t => (if b then S1 else S0) :: (if b then S1 else S0) :: enc2 t
  end.

(** What is left once the increment has eaten the low digit-1s: [[]]
    at an overflow, [false :: crest w] otherwise. *)
Fixpoint crest0 (w : list bool) : list bool :=
  match w with
  | true :: t => crest0 t
  | _ => w
  end.

Lemma enc2_incr : forall w,
  enc2 (incr w) = repeat S0 (2 * carry w) ++ S1 :: S1 :: enc2 (crest w).
Proof.
  induction w as [|b t IH]; [reflexivity|].
  destruct b; [|reflexivity].
  change (enc2 (incr (true :: t))) with (S0 :: S0 :: enc2 (incr t)).
  change (carry (true :: t)) with (S (carry t)).
  change (crest (true :: t)) with (crest t).
  rewrite IH.
  replace (2 * S (carry t)) with (2 + 2 * carry t) by lia.
  reflexivity.
Qed.

Lemma chd_crest0 : forall w, chd (enc2 (crest0 w)) = S0.
Proof.
  induction w as [|b t IH]; [reflexivity|].
  destruct b; [exact IH | reflexivity].
Qed.

Lemma ctl2_crest0 : forall w, ctl (ctl (enc2 (crest0 w))) = enc2 (crest w).
Proof.
  induction w as [|b t IH]; [reflexivity|].
  destruct b; [exact IH | reflexivity].
Qed.

(** The sweep stops either off the top of the counter or on a genuine
    digit-0 -- and in the second case the two cells it stops on are
    that digit's, so both are [S0]. *)
Lemma crest0_cases : forall w,
  (crest0 w = [] /\ crest w = []) \/ crest0 w = false :: crest w.
Proof.
  induction w as [|b t IH]; [left; split; reflexivity|].
  destruct b; [exact IH | right; reflexivity].
Qed.

(** ** Comb algebra *)

Lemma rot10 : forall j X, S0 :: (rep [S1; S0] j ++ X) = rep [S0; S1] j ++ S0 :: X.
Proof.
  induction j as [|j IH]; intros X; [reflexivity|].
  cbn [rep]. rewrite <- !app_assoc. cbn [app]. rewrite IH. reflexivity.
Qed.

Lemma comb_hd : forall j X,
  rep [S1; S0] (S j) ++ X = S1 :: (rep [S0; S1] j ++ S0 :: X).
Proof.
  intros j X. cbn [rep]. rewrite <- app_assoc. cbn [app].
  rewrite rot10. reflexivity.
Qed.

(** ** The unit runs (windowed, each checked by [reflexivity]) *)

(** V1: [B 0] turns the head around. *)
Lemma V1 : forall L R,
  csteps tm_c2 1 (StB, (L, S0, R)) = Some (StC, (ctl L, chd L, S1 :: R)).
Proof. reflexivity. Qed.

(** V2: [C 1] blanks one cell and steps left (also off the tape end). *)
Lemma V2 : forall L R,
  csteps tm_c2 1 (StC, (L, S1, R)) = Some (StC, (ctl L, chd L, S0 :: R)).
Proof. reflexivity. Qed.

(** V3: one comb unit, crossed leftward. *)
Lemma V3 : wsteps true true tm_c2 4 (StC, ([S0; S1], S1, []))
           = Some (StC, ([], S1, [S1; S1])).
Proof. reflexivity. Qed.

(** V4: the first half-lap's turn -- the low marker becomes [11]. *)
Lemma V4 : wsteps true true tm_c2 6 (StC, ([S0; S0], S1, []))
           = Some (StB, ([S1; S1], S1, [])).
Proof. reflexivity. Qed.

(** V5: the increment sets the first digit-0 (interior). *)
Lemma V5 : wsteps true true tm_c2 5 (StC, ([S0], S0, [S0]))
           = Some (StB, ([S1; S1], S1, [])).
Proof. reflexivity. Qed.

(** V6: the same at an OVERFLOW -- the digit-0 is past the top digit,
    so the cells are blank rather than present. *)
Lemma V6 : wsteps false true tm_c2 5 (StC, ([], S0, [S0]))
           = Some (StB, ([S1; S1], S1, [])).
Proof. reflexivity. Qed.

(** V7: the head walks right over one blanked carry cell. *)
Lemma V7 : wsteps true true tm_c2 3 (StB, ([], S1, [S0]))
           = Some (StB, ([S0], S1, [])).
Proof. reflexivity. Qed.

(** V8: [B 1]/[D 1] rewrite two ones as one comb unit. *)
Lemma V8 : forall L R,
  csteps tm_c2 2 (StB, (L, S1, S1 :: R))
  = Some (StB, (S1 :: S0 :: L, chd R, ctl R)).
Proof. reflexivity. Qed.

(** ** Transported phases *)

Lemma cross : forall j L R,
  csteps tm_c2 (4 * j) (StC, (rep [S0; S1] j ++ L, S1, R))
  = Some (StC, (L, S1, repeat S1 (2 * j) ++ R)).
Proof.
  intros j L R.
  pose proof (cycL tm_c2 4 StC S1 [S0; S1] [] [S1; S1] V3 j L R) as H.
  cbn [app] in H. rewrite H, rep_dbl.
  replace (rep [S1] (2 * j)) with (repeat S1 (2 * j)); [reflexivity|].
  generalize (2 * j) as n; intro n.
  induction n as [|n IH]; [reflexivity | cbn [rep repeat]; rewrite IH; reflexivity].
Qed.

Lemma turn0 : forall E R,
  csteps tm_c2 6 (StC, (S0 :: S0 :: E, S1, R))
  = Some (StB, (S1 :: S1 :: E, S1, R)).
Proof.
  intros E R.
  exact (wsteps_frame _ _ _ _ _ _ _ _ _ _ E R V4).
Qed.

(** The carry sweep: [C 1] blanks the low digit-1s, two cells each. *)
Lemma sweep : forall w R,
  csteps tm_c2 (2 * carry w) (StC, (enc2 w, S1, R))
  = Some (StC, (enc2 (crest0 w), S1, repeat S0 (2 * carry w) ++ R)).
Proof.
  induction w as [|b t IH]; intros R; [reflexivity|].
  destruct b; [|reflexivity].
  change (carry (true :: t)) with (S (carry t)).
  change (crest0 (true :: t)) with (crest0 t).
  change (enc2 (true :: t)) with (S1 :: S1 :: enc2 t).
  replace (2 * S (carry t)) with (1 + (1 + 2 * carry t)) by lia.
  rewrite csteps_add, V2. cbn [chd ctl].
  rewrite csteps_add, V2. cbn [chd ctl].
  rewrite IH. cbn [repeat]. rewrite !rep_snoc. reflexivity.
Qed.

(** The set gadget, uniform over interior and overflow. *)
Lemma setdig : forall w R,
  csteps tm_c2 5 (StC, (ctl (enc2 (crest0 w)), S0, S0 :: R))
  = Some (StB, (S1 :: S1 :: enc2 (crest w), S1, R)).
Proof.
  intros w R.
  destruct (crest0_cases w) as [[H0 H1] | H].
  - (* overflow: the digit-0 is past the top digit, so blank *)
    rewrite H0, H1. cbn [enc2 ctl].
    pose proof (wsteps_frame_l _ _ _ _ _ _ _ _ _ _ R V6) as Hf.
    cbn [app] in Hf. exact Hf.
  - (* interior: both cells of the digit are present and [S0] *)
    rewrite H. cbn [enc2 ctl].
    pose proof (wsteps_frame _ _ _ _ _ _ _ _ _ _ (enc2 (crest w)) R V5) as Hf.
    cbn [app] in Hf. exact Hf.
Qed.

Lemma zwalk : forall j L R,
  csteps tm_c2 (3 * j) (StB, (L, S1, repeat S0 j ++ R))
  = Some (StB, (repeat S0 j ++ L, S1, R)).
Proof.
  induction j as [|j IH]; intros L R; [reflexivity|].
  replace (3 * S j) with (3 + 3 * j) by lia.
  change (repeat S0 (S j) ++ R) with (S0 :: (repeat S0 j ++ R)).
  rewrite csteps_add.
  pose proof (wsteps_frame _ _ _ _ _ _ _ _ _ _ L (repeat S0 j ++ R) V7) as Hf.
  cbn [app] in Hf. rewrite Hf, IH, rep_snoc. reflexivity.
Qed.

Lemma reb_step : forall j M,
  rep [S1; S0] (S j) ++ S1 :: S0 :: M = rep [S1; S0] (S (S j)) ++ M.
Proof.
  intros j M. change (S1 :: S0 :: M) with ([S1; S0] ++ M).
  rewrite app_assoc, rep_shift. cbn [rep]. reflexivity.
Qed.

(** The rebuild: a run of [2j+2] ones becomes [j+1] comb units. *)
Lemma reb : forall j M,
  csteps tm_c2 (2 * j + 2) (StB, (M, S1, repeat S1 (2 * j + 1)))
  = Some (StB, (rep [S1; S0] (S j) ++ M, S0, [])).
Proof.
  induction j as [|j IH]; intros M.
  - replace (2 * 0 + 2) with 2 by lia.
    replace (2 * 0 + 1) with 1 by lia.
    cbn [repeat]. rewrite V8. reflexivity.
  - replace (2 * S j + 2) with (2 + (2 * j + 2)) by lia.
    replace (2 * S j + 1) with (S (S (2 * j + 1))) by lia.
    cbn [repeat]. rewrite csteps_add, V8. cbn [chd ctl].
    rewrite IH, reb_step. reflexivity.
Qed.

(** ** The two half-laps *)

(** [B 0] turns the head around and state C crosses [j] comb units. *)
Lemma start : forall j Y,
  csteps tm_c2 (1 + 4 * j) (StB, (rep [S1; S0] (S j) ++ Y, S0, []))
  = Some (StC, (S0 :: Y, S1, repeat S1 (2 * j) ++ [S1])).
Proof.
  intros j Y. rewrite comb_hd, csteps_add, V1. cbn [chd ctl]. apply cross.
Qed.

(** One more comb unit, crossed on its own. *)
Lemma cross1 : forall L R,
  csteps tm_c2 4 (StC, (S0 :: S1 :: L, S1, R))
  = Some (StC, (L, S1, S1 :: S1 :: R)).
Proof.
  intros L R.
  pose proof (wsteps_frame _ _ _ _ _ _ _ _ _ _ L R V3) as Hf.
  cbn [app] in Hf. exact Hf.
Qed.

Definition anchor0 (w : list bool) : cconf :=
  (StB, (rep [S1; S0] (cval w) ++ S0 :: enc2 w, S0, [])).

Definition anchor1 (w : list bool) : cconf :=
  (StB, (rep [S1; S0] (cval w) ++ S1 :: S1 :: enc2 w, S0, [])).

(** First half-lap: the low marker [0] becomes [11], the comb is
    rebuilt at the same length. *)
Lemma lap0 : forall j w, cval w = S j ->
  csteps tm_c2 (6 * cval w + 3) (anchor0 w) = Some (anchor1 w).
Proof.
  intros j w Hj. unfold anchor0, anchor1. rewrite Hj.
  replace (6 * S j + 3) with ((1 + 4 * j) + (6 + (2 * j + 2))) by lia.
  rewrite csteps_add, start, csteps_add, turn0.
  replace (repeat S1 (2 * j) ++ [S1]) with (repeat S1 (2 * j + 1))
    by (rewrite repeat_app; reflexivity).
  rewrite reb. reflexivity.
Qed.

(** Second half-lap: the binary increment, and the comb grows by one. *)
Lemma lap1 : forall j w, cval w = S j ->
  csteps tm_c2 (6 * cval w + 8 * carry w + 13) (anchor1 w)
  = Some (anchor0 (incr w)).
Proof.
  intros j w Hj. unfold anchor0, anchor1. rewrite Hj, cval_incr, Hj.
  assert (Hones : S1 :: S1 :: (repeat S1 (2 * j) ++ [S1])
                = repeat S1 (2 * S j) ++ [S1]).
  { replace (2 * S j) with (S (S (2 * j))) by lia. reflexivity. }
  assert (Hzeros : repeat S0 (2 * carry w) ++ S0 :: (repeat S1 (2 * S j) ++ [S1])
                 = repeat S0 (2 * carry w + 1) ++ repeat S1 (2 * S j + 1)).
  { rewrite rep_snoc.
    replace (2 * carry w + 1) with (S (2 * carry w)) by lia.
    cbn [repeat]. rewrite repeat_app. reflexivity. }
  replace (6 * S j + 8 * carry w + 13)
     with ((1 + 4 * j) + (4 + ((1 + (2 * carry w + 1))
           + (5 + (3 * (2 * carry w + 1) + (2 * S j + 2)))))) by lia.
  rewrite csteps_add, start, csteps_add, cross1, Hones.
  rewrite csteps_add, csteps_add, V2. cbn [chd ctl].
  rewrite csteps_add, sweep, V2, chd_crest0.
  rewrite csteps_add, setdig, csteps_add, Hzeros, zwalk, reb.
  do 2 f_equal. rewrite enc2_incr.
  replace (2 * carry w + 1) with (S (2 * carry w)) by lia.
  reflexivity.
Qed.

Lemma lap : forall j w, cval w = S j ->
  csteps tm_c2 (12 * cval w + 8 * carry w + 16) (anchor0 w)
  = Some (anchor0 (incr w)).
Proof.
  intros j w Hj.
  replace (12 * cval w + 8 * carry w + 16)
     with ((6 * cval w + 3) + (6 * cval w + 8 * carry w + 13)) by lia.
  rewrite csteps_add, (lap0 j w Hj). apply (lap1 j w Hj).
Qed.

(** ** Bootstrap, visits, and the theorem *)

Definition Cc (p : positive) : cconf := anchor0 (bits p).

Lemma cval_bits_pos : forall p, exists j, cval (bits p) = S j.
Proof.
  induction p as [p IH|p IH|]; simpl.
  - eauto.
  - destruct IH as [j Hj]. rewrite Hj. exists (j + S j). lia.
  - exists 0. reflexivity.
Qed.

Lemma boot_c2 : exists t0, stepn tm_c2 t0 InitES = Some (lift (Cc 1)).
Proof.
  exists 17.
  assert (H : match csteps tm_c2 17 c0 with
              | Some c => ceqb c (Cc 1)
              | None => false
              end = true) by (vm_compute; reflexivity).
  destruct (csteps tm_c2 17 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E).
  f_equal. apply ceqb_lift. exact H.
Qed.

(** Each anchor visits all four states in its first five steps:
    [B], [C], [C], [D], [A]. *)
Lemma vis_c2 : forall q Z,
  exists k c, csteps tm_c2 k (StB, (S1 :: S0 :: Z, S0, [])) = Some c /\ fst c = q.
Proof.
  intros q Z. destruct q.
  - exists 4. eexists. split; reflexivity.
  - exists 0. eexists. split; reflexivity.
  - exists 1. eexists. split; reflexivity.
  - exists 3. eexists. split; reflexivity.
Qed.

(** 0RB1LC_1LC0RD_1RD0LC_1LA1RB never quasihalts. *)
Theorem nqh_0RB1LC_1LC0RD_1RD0LC_1LA1RB : NeverQuasiHaltsSt tm_c2.
Proof.
  apply (glue_neverqh tm_c2 Cc 1).
  - exact boot_c2.
  - intros p _. unfold Cc. rewrite bits_succ.
    destruct (cval_bits_pos p) as [j Hj].
    exists (12 * cval (bits p) + 8 * carry (bits p) + 16), (anchor0 (incr (bits p))).
    split; [apply (lap j _ Hj) | split; [reflexivity | lia]].
  - intros p q _. unfold Cc, anchor0.
    destruct (cval_bits_pos p) as [j Hj]. rewrite Hj.
    replace (rep [S1; S0] (S j) ++ S0 :: enc2 (bits p))
       with (S1 :: S0 :: (rep [S1; S0] j ++ S0 :: enc2 (bits p)))
       by (rewrite comb_hd, <- rot10; reflexivity).
    apply vis_c2.
Qed.

Theorem tm_c2_nonhalt : NonHalt tm_c2.
Proof. apply never_qh_nonhalt, nqh_0RB1LC_1LC0RD_1RD0LC_1LA1RB. Qed.
