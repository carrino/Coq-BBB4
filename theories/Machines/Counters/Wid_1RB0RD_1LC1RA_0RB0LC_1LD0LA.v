(** * Wid_1RB0RD_1LC1RA_0RB0LC_1LD0LA: a counter that WIDENS into its own
      padding.

    bbchallenge 1RB0RD_1LC1RA_0RB0LC_1LD0LA, one of the undecided core
    rows (tools/closeout/core_rows.txt).  tools/closeout/residue_map.tsv
    reads its alphabet correctly -- [Alph_00_10_1], two cells per digit --
    and then refuses it with `no boot chain`, which is the right refusal
    for the wrong reason: the row has no single anchor family at all.

    The head sits at the LEFT edge of the written tape on a blank, in
    state [C], and everything is to its right:

      anchor (w, m) :  [C:0] <w, low digit first, 0 = 00, 1 = 10> 1^(2m+2)

    so the tape carries a counter word [w] and a PADDING of ones, and

      t=16    [0] 1111            w = [],      m = 1
      t=98    [0] 11111111        w = [],      m = 3
      t=106   [0] 00 111111       w = [0],     m = 2
      t=108   [0] 10 111111       w = [1],     m = 2
      t=120   [0] 0000 1111       w = [0;0],   m = 1
      t=130   [0] 1010 1111       w = [1;1],   m = 1
      t=146   [0] 000000 11       w = [0;0;0], m = 0

    -- the counter counts up, and when it OVERFLOWS it does not carry
    into fresh tape: it eats two cells of its own padding and starts
    again one digit wider.  Reading the tape as a single number, the
    padding IS the top bit, so what the machine actually enumerates is
    every binary word in order of (width, value), i.e. the plain integers
    with the leading 1 stripped.  That is why a search for ONE anchor
    family indexed by ONE counter finds nothing.

    Three rules, and each is one lap:

      count     (w = 1^c ++ 0::t)   -->  0^c ++ 1::t,  m           4c+2  steps
      widen     (w = 1^c, m = S m') -->  0^(c+1),      m'          4c+8  steps
      restart   (w = 1^c, m = 0)    -->  [],           S c         6c+11 steps

    [count] and [widen] share a skeleton -- [C] steps in, [B]/[A] walk
    right over the set digits two cells at a time, and a [C] sweep walks
    home blanking what they wrote -- and differ only in what happens at
    the far end.  [restart] is the odd one: past the last padding cell
    the head falls off the written tape and [D] walks all the way home in
    a four-step cycle, two cells per turn, which is the [4c] in its cost.

    The anchor family is the orbit of the abstract state [(w, m)] under
    [nxt], iterated by [stt]; [LapGlue] indexes that by [Pos.to_nat], so
    each lap is ONE rule and no rule has to know about the others.

    [StA] and [StD] are visited only at an overflow, so the visit
    obligation for them is discharged by running forward to the next one
    -- a well-founded descent on [togo], the number of laps a word still
    has before it is solid ones.

    Every rule was checked differentially against the raw simulator
    (exact [cconf], exact totals) for [c = 0..7] over six tails and four
    paddings before the Coq was written. *)

From Coq Require Import Arith Lia Bool List PArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape LapGlue LinCarry.
Import ListNotations.

Definition mk (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).

(** 1RB0RD_1LC1RA_0RB0LC_1LD0LA *)
Definition tm_wd : TM := fun q s =>
  match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S0 DR StD
  | StB, S0 => mk S1 DL StC | StB, S1 => mk S1 DR StA
  | StC, S0 => mk S0 DR StB | StC, S1 => mk S0 DL StC
  | StD, S0 => mk S1 DL StD | StD, S1 => mk S0 DL StA
  end.

Lemma hA0 : forall l r,
  cstep tm_wd (StA, (l, S0, r)) = Some (StB, (S1 :: l, chd r, ctl r)).
Proof. reflexivity. Qed.
Lemma hA1 : forall l r,
  cstep tm_wd (StA, (l, S1, r)) = Some (StD, (S0 :: l, chd r, ctl r)).
Proof. reflexivity. Qed.
Lemma hB0 : forall l r,
  cstep tm_wd (StB, (l, S0, r)) = Some (StC, (ctl l, chd l, S1 :: r)).
Proof. reflexivity. Qed.
Lemma hB1 : forall l r,
  cstep tm_wd (StB, (l, S1, r)) = Some (StA, (S1 :: l, chd r, ctl r)).
Proof. reflexivity. Qed.
Lemma hC0 : forall l r,
  cstep tm_wd (StC, (l, S0, r)) = Some (StB, (S0 :: l, chd r, ctl r)).
Proof. reflexivity. Qed.
Lemma hC1 : forall l r,
  cstep tm_wd (StC, (l, S1, r)) = Some (StC, (ctl l, chd l, S0 :: r)).
Proof. reflexivity. Qed.
Lemma hD0 : forall l r,
  cstep tm_wd (StD, (l, S0, r)) = Some (StD, (ctl l, chd l, S1 :: r)).
Proof. reflexivity. Qed.
Lemma hD1 : forall l r,
  cstep tm_wd (StD, (l, S1, r)) = Some (StA, (ctl l, chd l, S0 :: r)).
Proof. reflexivity. Qed.

Lemma stepM : forall a b c c',
  csteps tm_wd a c = Some c' -> csteps tm_wd (a + b) c = csteps tm_wd b c'.
Proof. intros a b c c' H. rewrite csteps_add, H. reflexivity. Qed.

Local Ltac go H := erewrite (stepR tm_wd _ _ _ (H _ _)); cbn [chd ctl].
Local Ltac gorun H := erewrite (stepM _ _ _ _ H).

(** ** The tape word *)

Definition dig (b : bool) : list Sym := if b then [S1; S0] else [S0; S0].

Fixpoint enc (w : list bool) : list Sym :=
  match w with [] => [] | b :: t => dig b ++ enc t end.

Lemma enc_app : forall v w, enc (v ++ w) = enc v ++ enc w.
Proof.
  induction v as [|b v IH]; intro w; [reflexivity|].
  cbn [enc app]. rewrite IH, app_assoc. reflexivity.
Qed.

Lemma enc_false : forall c, enc (repeat false c) = rep [S0] (2 * c).
Proof.
  induction c as [|c IH]; [reflexivity|].
  cbn [repeat enc dig app]. rewrite IH.
  replace (2 * S c) with (S (S (2 * c))) by lia. reflexivity.
Qed.

Lemma rep2_cons : forall k, rep [S1; S1] (S k) = S1 :: S1 :: rep [S1; S1] k.
Proof. reflexivity. Qed.

Definition Anc (w : list bool) (m : nat) : cconf :=
  (StC, ([], S0, enc w ++ rep [S1; S1] (S m))).

(** ** The two sweeps

    [passR] walks right over the set digits, writing a pair of ones per
    digit; [sweepL] walks home over exactly those ones, blanking them. *)

Lemma passR : forall c L Z,
  csteps tm_wd (2 * c)
    (StB, (L, chd (enc (repeat true c) ++ Z), ctl (enc (repeat true c) ++ Z)))
  = Some (StB, (rep [S1] (2 * c) ++ L, chd Z, ctl Z)).
Proof.
  induction c as [|c IH]; intros L Z; [reflexivity|].
  cbn [repeat enc dig app]. cbn [chd ctl].
  replace (2 * S c) with (S (S (2 * c))) by lia.
  go hB1. go hA0. rewrite IH, !rep1_snoc. reflexivity.
Qed.

Lemma sweepL : forall k L h R,
  csteps tm_wd (S k) (StC, (rep [S1] k ++ h :: L, S1, R))
    = Some (StC, (L, h, rep [S0] (S k) ++ R)).
Proof.
  induction k as [|k IH]; intros L h R.
  - cbn [rep app]. go hC1. reflexivity.
  - rewrite rep1_cons. cbn [app]. go hC1. rewrite IH, rep1_snoc. reflexivity.
Qed.

(** ** Rule 1: count *)

Lemma rule_count : forall c t m,
  csteps tm_wd (4 * c + 2) (Anc (repeat true c ++ false :: t) m)
    = Some (Anc (repeat false c ++ true :: t) m).
Proof.
  intros c t m. unfold Anc.
  rewrite !enc_app. cbn [enc dig app]. rewrite <- !app_assoc. cbn [app].
  destruct c as [|c].
  - replace (4 * 0 + 2) with 2 by lia.
    cbn [repeat enc app rep chd ctl].
    go hC0. go hB0. reflexivity.
  - replace (4 * S c + 2) with (1 + (2 * S c + (1 + S (2 * c + 1)))) by lia.
    go hC0.
    gorun (passR (S c) [S0] (S0 :: S0 :: (enc t ++ rep [S1; S1] (S m)))).
    cbn [chd ctl].
    replace (2 * S c) with (S (2 * c + 1)) by lia.
    rewrite rep1_cons. cbn [app]. go hB0.
    rewrite (sweepL (2 * c + 1) [] S0 (S1 :: S0 :: (enc t ++ rep [S1; S1] (S m)))).
    rewrite enc_false. replace (2 * S c) with (S (2 * c + 1)) by lia.
    reflexivity.
Qed.

(** ** Rule 2: widen *)

Lemma rule_widen : forall c m,
  csteps tm_wd (4 * c + 8) (Anc (repeat true c) (S m))
    = Some (Anc (repeat false (S c)) m).
Proof.
  intros c m. unfold Anc.
  replace (4 * c + 8)
     with (1 + (2 * c + (1 + (1 + (1 + (1 + (1 + S (2 * c + 1)))))))) by lia.
  rewrite (rep2_cons (S m)).
  go hC0.
  gorun (passR c [S0] (S1 :: S1 :: rep [S1; S1] (S m))). cbn [chd ctl].
  go hB1. rewrite (rep2_cons m). go hA1. go hD1. go hA0. go hB0.
  replace (S1 :: rep [S1] (2 * c) ++ [S0]) with (rep [S1] (2 * c + 1) ++ [S0])
    by (replace (2 * c + 1) with (S (2 * c)) by lia; reflexivity).
  rewrite (sweepL (2 * c + 1) [] S0 (S1 :: S1 :: rep [S1; S1] m)).
  rewrite enc_false. replace (2 * S c) with (S (2 * c + 1)) by lia.
  reflexivity.
Qed.

(** ** Rule 3: restart

    Past the last padding cell the head falls off the written tape; [D]
    walks home in a four-step cycle that eats two ones per turn. *)

Lemma loopD : forall k R,
  csteps tm_wd (4 * k) (StD, (S0 :: rep [S1] (2 * k + 1) ++ [S0], S0, R))
    = Some (StD, ([S0; S1; S0], S0, rep [S1] (2 * k) ++ R)).
Proof.
  induction k as [|k IH]; intros R.
  - cbn [Nat.mul Nat.add rep app]. reflexivity.
  - replace (2 * S k + 1) with (S (S (2 * k + 1))) by lia.
    replace (4 * S k) with (1 + (1 + (1 + (1 + 4 * k)))) by lia.
    rewrite (rep1_cons S1 (S (2 * k + 1))), (rep1_cons S1 (2 * k + 1)).
    cbn [app].
    go hD0. go hD0. go hD1. go hA1.
    rewrite IH.
    replace (2 * S k) with (S (S (2 * k))) by lia.
    rewrite !rep1_snoc. reflexivity.
Qed.

Lemma termD : forall R,
  csteps tm_wd 8 (StD, ([S0; S1; S0], S0, R))
    = Some (StC, ([], S0, rep [S1] 4 ++ R)).
Proof.
  intros R. go hD0. go hD0. go hD1. go hA0. go hB0. go hC1. go hC0. go hB0.
  reflexivity.
Qed.

Lemma rule_restart : forall c,
  csteps tm_wd (6 * c + 11) (Anc (repeat true c) 0) = Some (Anc [] (S c)).
Proof.
  intros c. unfold Anc. cbn [enc]. rewrite app_nil_l.
  change (rep [S1; S1] (S 0)) with [S1; S1].
  replace (6 * c + 11) with (1 + (2 * c + (1 + (1 + (4 * c + 8))))) by lia.
  go hC0.
  gorun (passR c [S0] [S1; S1]). cbn [chd ctl].
  go hB1. go hA1.
  replace (S0 :: S1 :: rep [S1] (2 * c) ++ [S0])
     with (S0 :: rep [S1] (2 * c + 1) ++ [S0])
     by (replace (2 * c + 1) with (S (2 * c)) by lia; reflexivity).
  gorun (loopD c []). rewrite termD, app_nil_r.
  rewrite <- rep_add, (rep_dbl S1 (S (S c))).
  replace (4 + 2 * c) with (2 * S (S c)) by lia. reflexivity.
Qed.

(** ** The abstract state, and its orbit

    A lap is one rule, so the family is the orbit of [(w, m)] under
    [nxt]: [bump] is the increment that stays inside the word, and its
    failure is exactly "the word is solid ones". *)

Fixpoint bump (w : list bool) : option (list bool) :=
  match w with
  | [] => None
  | false :: t => Some (true :: t)
  | true :: t => match bump t with Some t' => Some (false :: t') | None => None end
  end.

Lemma bump_some : forall w w', bump w = Some w' ->
  exists c t, w = repeat true c ++ false :: t /\ w' = repeat false c ++ true :: t.
Proof.
  induction w as [|b w IH]; intros w' H; [discriminate|].
  destruct b; cbn [bump] in H.
  - destruct (bump w) as [t'|] eqn:E; [|discriminate].
    injection H as <-. destruct (IH t' eq_refl) as (c & t & -> & ->).
    exists (S c), t. split; reflexivity.
  - injection H as <-. exists 0, w. split; reflexivity.
Qed.

Lemma bump_none : forall w, bump w = None -> w = repeat true (length w).
Proof.
  induction w as [|b w IH]; intro H; [reflexivity|].
  destruct b; cbn [bump] in H; [|discriminate].
  destruct (bump w) as [t'|] eqn:E; [discriminate|].
  cbn [length repeat]. rewrite <- (IH eq_refl). reflexivity.
Qed.

Definition nxt (s : list bool * nat) : list bool * nat :=
  match bump (fst s) with
  | Some w' => (w', snd s)
  | None => match snd s with
            | S m => (repeat false (S (length (fst s))), m)
            | O => ([], S (length (fst s)))
            end
  end.

Fixpoint stt (n : nat) : list bool * nat :=
  match n with O => ([], 0) | S k => nxt (stt k) end.

Definition AncS (s : list bool * nat) : cconf := Anc (fst s) (snd s).

Lemma lap_nxt : forall s,
  exists n, csteps tm_wd n (AncS s) = Some (AncS (nxt s)) /\ 0 < n.
Proof.
  intros [w m]. unfold AncS, nxt; cbn [fst snd].
  destruct (bump w) as [w'|] eqn:E.
  - destruct (bump_some w w' E) as (c & t & -> & ->). cbn [fst snd].
    exists (4 * c + 2). split; [apply rule_count | lia].
  - remember (length w) as c eqn:Ec.
    assert (Hw : w = repeat true c) by (rewrite Ec; apply bump_none; exact E).
    rewrite Hw. destruct m as [|m]; cbn [fst snd].
    + exists (6 * c + 11). split; [apply rule_restart | lia].
    + exists (4 * c + 8). split; [apply rule_widen | lia].
Qed.

(** ** Visits

    [StC] and [StB] open every lap; [StA] and [StD] belong to the
    overflow, which a word reaches after [togo] more laps -- [togo w] is
    [2^|w| - 1 - val w], written without powers so the descent is
    structural. *)

Fixpoint togo (w : list bool) : nat :=
  match w with
  | [] => 0
  | false :: t => S (2 * togo t)
  | true :: t => 2 * togo t
  end.

Lemma togo_bump : forall w w', bump w = Some w' -> togo w' < togo w.
Proof.
  induction w as [|b w IH]; intros w' H; [discriminate|].
  destruct b; cbn [bump] in H.
  - destruct (bump w) as [t'|] eqn:E; [|discriminate].
    injection H as <-. specialize (IH t' eq_refl). cbn [togo]. lia.
  - injection H as <-. cbn [togo]. lia.
Qed.

Lemma togo_zero : forall w, togo w = 0 -> bump w = None.
Proof.
  induction w as [|b w IH]; intro H; [reflexivity|].
  destruct b; cbn [togo] in H; cbn [bump].
  - rewrite (IH ltac:(lia)). reflexivity.
  - discriminate.
Qed.

(** At an overflow the head runs off the top of the word: [StA] on the
    last padding cell it can still read, [StD] one step past it. *)
Lemma ovf_vis : forall c P,
  (exists cc, csteps tm_wd (2 * c + 2)
      (StC, ([], S0, enc (repeat true c) ++ S1 :: S1 :: P))
      = Some cc /\ fst cc = StA)
  /\ (exists cc, csteps tm_wd (2 * c + 3)
      (StC, ([], S0, enc (repeat true c) ++ S1 :: S1 :: P))
      = Some cc /\ fst cc = StD).
Proof.
  intros c P.
  assert (HA : csteps tm_wd (2 * c + 2)
                 (StC, ([], S0, enc (repeat true c) ++ S1 :: S1 :: P))
               = Some (StA, (S1 :: rep [S1] (2 * c) ++ [S0], S1, P))).
  { replace (2 * c + 2) with (1 + (2 * c + 1)) by lia.
    go hC0. gorun (passR c [S0] (S1 :: S1 :: P)). cbn [chd ctl].
    go hB1. reflexivity. }
  split.
  - exists (StA, (S1 :: rep [S1] (2 * c) ++ [S0], S1, P)).
    split; [exact HA | reflexivity].
  - replace (2 * c + 3) with ((2 * c + 2) + 1) by lia.
    rewrite csteps_add, HA.
    eexists. split; [go hA1; reflexivity | reflexivity].
Qed.

Lemma ovf_AD : forall w m, bump w = None ->
  (exists k cc, csteps tm_wd k (Anc w m) = Some cc /\ fst cc = StA)
  /\ (exists k cc, csteps tm_wd k (Anc w m) = Some cc /\ fst cc = StD).
Proof.
  intros w m E.
  remember (length w) as c eqn:Ec.
  assert (Hw : w = repeat true c) by (rewrite Ec; apply bump_none; exact E).
  rewrite Hw. unfold Anc. rewrite (rep2_cons m).
  destruct (ovf_vis c (rep [S1; S1] m)) as (HA & HD).
  split.
  - destruct HA as (cc & H1 & H2). exists (2 * c + 2), cc. split; assumption.
  - destruct HD as (cc & H1 & H2). exists (2 * c + 3), cc. split; assumption.
Qed.

Lemma reach_ovf : forall n w m, togo w <= n ->
  (exists k cc, csteps tm_wd k (Anc w m) = Some cc /\ fst cc = StA)
  /\ (exists k cc, csteps tm_wd k (Anc w m) = Some cc /\ fst cc = StD).
Proof.
  induction n as [|n IH]; intros w m Hle.
  - apply ovf_AD, togo_zero. lia.
  - destruct (bump w) as [w'|] eqn:E; [|apply ovf_AD; exact E].
    assert (Hlt : togo w' < togo w) by (apply togo_bump; exact E).
    destruct (bump_some w w' E) as (c & t & Hw & Hw').
    destruct (IH w' m ltac:(lia)) as (HA & HD).
    rewrite Hw' in HA, HD. rewrite Hw.
    split.
    + destruct HA as (k & cc & H1 & H2). exists (4 * c + 2 + k), cc.
      split; [rewrite csteps_add, rule_count; exact H1 | exact H2].
    + destruct HD as (k & cc & H1 & H2). exists (4 * c + 2 + k), cc.
      split; [rewrite csteps_add, rule_count; exact H1 | exact H2].
Qed.

(** ** Bootstrap and the theorem *)

Definition Cf (p : positive) : cconf := AncS (stt (Pos.to_nat p)).

Lemma boot_wd : exists t0, stepn tm_wd t0 InitES = Some (lift (Cf 1)).
Proof.
  exists 16.
  assert (H : match csteps tm_wd 16 c0 with
              | Some c => ceqb c (Cf 1)
              | None => false
              end = true) by (vm_compute; reflexivity).
  destruct (csteps tm_wd 16 c0) as [c|] eqn:E; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ E).
  f_equal. apply ceqb_lift. exact H.
Qed.

(** 1RB0RD_1LC1RA_0RB0LC_1LD0LA never quasihalts. *)
Theorem nqh_1RB0RD_1LC1RA_0RB0LC_1LD0LA : NeverQuasiHaltsSt tm_wd.
Proof.
  apply (glue_neverqh tm_wd Cf 1).
  - exact boot_wd.
  - intros p _. unfold Cf. rewrite Pos2Nat.inj_succ. cbn [stt].
    destruct (lap_nxt (stt (Pos.to_nat p))) as (n & Hn & Hpos).
    exists n, (AncS (nxt (stt (Pos.to_nat p)))).
    split; [exact Hn | split; [reflexivity | exact Hpos]].
  - intros p q _. unfold Cf, AncS.
    destruct (stt (Pos.to_nat p)) as [w m]. cbn [fst snd].
    destruct q.
    + destruct (reach_ovf (togo w) w m (le_n _)) as (HA & _). exact HA.
    + exists 1. unfold Anc. eexists. split; [go hC0; reflexivity | reflexivity].
    + exists 0. eexists. split; reflexivity.
    + destruct (reach_ovf (togo w) w m (le_n _)) as (_ & HD). exact HD.
Qed.

Theorem tm_wd_nonhalt : NonHalt tm_wd.
Proof. apply never_qh_nonhalt, nqh_1RB0RD_1LC1RA_0RB0LC_1LD0LA. Qed.
