(** * Tower_20: 1RB0RD_1LC1LB_1RA0LB_1LC1RA -- the gadget, sweep and
    re-encoding layers.

    BBB [tower] certificate #20.  BBB's decode is a 14-template FSM over
    [(template, r)] closed by [rmin]; that is its route to a step-count
    BOUND, which [NeverQuasiHaltsSt] does not need, and it is not what this
    file builds.

    Read at the LEFT RECORD -- head on the leftmost visited cell, [StC],
    reading blank, left list empty -- the machine is a COUNTER IN THE
    ALPHABET [b = 110], [a = 10].  After a three-record boot (t = 4, 18, 28)
    the family settles at t = 50 and STRICTLY ALTERNATES between two leads
    over the same tail:

      A(r,rest)   (StC, ([], S0, 1 1 0 1 0     ++ b^r ++ rest))
      B(r,rest)   (StC, ([], S0, 1 0 1 1 1 1 0 ++ b^r ++ rest))

    and the LEADING b-RUN IS THE LAP INDEX -- 0, 1, 2, ... with no
    exceptions over the 303 A-anchors reachable in 400,000 steps.  One long
    lap is [r -> r+1].

    [ruleA] is [A -> B] in a constant 10 steps, uniform in the tail; both
    left lists are empty, so there is no [L] to quantify over.  That is
    wave4 #15's [ruleA] again.

    The long lap [B(r,rest) -> A(r+1,rest')] is four phases:

      1. [entry10], a uniform window, leaving the left debris
         [E = [1;0;1;0;1;1]] and [R = 1 ++ b^r ++ rest];
      2. [out5s]: [out5] iterated over the b-run, one block at a time,
         laying [1;0;1] per block -- so the left list becomes
         [lay r E = (101)^r ++ E], John's repeated-101 bouncer body;
      3. THE MIDDLE, which runs on into [rest] and turns around;
      4. THE RETURN, which is the RE-ENCODER: [rb3] eats [1;0;1] off the
         left and emits the block [b = 110]; [rb2] eats [0;1] and emits
         [a = 10].  ONE BLOCK PER UNIT -- that is why the alphabet is real
         and not a way of looking at the tape, and it is why the S(n)
         record-shape search misses this machine.

    Phase 4 over [lay r E] is [bk_lay] below, and it is where the [+1] of
    the counter comes from: the sweep emits [b^r] and then, off [E],
    [b], [a], [b].  Emissions prepend, so the tape comes out as

      1 1 0 1 0 ++ b^(r+1) ++ ...

    -- the A-type lead with the run one longer.  The spare [b] in the entry
    debris IS the increment.

    Every gadget below was checked against a CTape-faithful mirror before
    any Coq was written -- EXHAUSTIVELY, over every [(L,R)] with
    [|L|,|R| <= 4], 961 contexts ([tools/counters/lap20.py]) -- and the
    whole lap was replayed symbolically from those gadgets alone and diffed
    against the raw simulator, configuration AND step count AND
    [r -> r+1], for every anchor reachable in 400,000 steps
    ([tools/counters/asm20.py]).  A sampled check is not a check: #15's
    deposit passed a 42-context sample and failed 496 of the 961.

    [Print Assumptions] on everything here = [functional_extensionality_dep]
    only. *)

From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement CTape.
Import ListNotations.

Definition mk (w : Sym) (d : Dir) (n : St) : option Trans :=
  Some (mkTrans w d n).

(** 1RB0RD_1LC1LB_1RA0LB_1LC1RA *)
Definition tm_20 : TM := fun q s =>
  match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S0 DR StD
  | StB, S0 => mk S1 DL StC | StB, S1 => mk S1 DL StB
  | StC, S0 => mk S1 DR StA | StC, S1 => mk S0 DL StB
  | StD, S0 => mk S1 DL StC | StD, S1 => mk S1 DR StA
  end.

(** ** The single-step joints

    The transition table, one [reflexivity] each, stated through
    [chd]/[ctl] so they are uniform at the ends of the half-tape lists.
    These are stated as lemmas rather than discharged on the nose: a
    [change] to [Some _] leaves an unreduced [match] and the next
    [rewrite] cannot find its subterm. *)

Lemma jca : forall L R,
  csteps tm_20 1 (StC, (L, S0, R)) = Some (StA, (S1 :: L, chd R, ctl R)).
Proof. reflexivity. Qed.

Lemma jcb : forall L R,
  csteps tm_20 1 (StC, (L, S1, R)) = Some (StB, (ctl L, chd L, S0 :: R)).
Proof. reflexivity. Qed.

Lemma jad : forall L R,
  csteps tm_20 1 (StA, (L, S1, R)) = Some (StD, (S0 :: L, chd R, ctl R)).
Proof. reflexivity. Qed.

Lemma jab : forall L R,
  csteps tm_20 1 (StA, (L, S0, R)) = Some (StB, (S1 :: L, chd R, ctl R)).
Proof. reflexivity. Qed.

Lemma jda : forall L R,
  csteps tm_20 1 (StD, (L, S1, R)) = Some (StA, (S1 :: L, chd R, ctl R)).
Proof. reflexivity. Qed.

Lemma jdc : forall L R,
  csteps tm_20 1 (StD, (L, S0, R)) = Some (StC, (ctl L, chd L, S1 :: R)).
Proof. reflexivity. Qed.

Lemma jbb : forall L R,
  csteps tm_20 1 (StB, (L, S1, R)) = Some (StB, (ctl L, chd L, S1 :: R)).
Proof. reflexivity. Qed.

Lemma jbc : forall L R,
  csteps tm_20 1 (StB, (L, S0, R)) = Some (StC, (ctl L, chd L, S1 :: R)).
Proof. reflexivity. Qed.

(** [cons] forms, so the sweeps rewrite against [cbn]-normal shapes. *)
Lemma jcac : forall L x R,
  csteps tm_20 1 (StC, (L, S0, x :: R)) = Some (StA, (S1 :: L, x, R)).
Proof. reflexivity. Qed.

Lemma jbbc : forall x L R,
  csteps tm_20 1 (StB, (x :: L, S1, R)) = Some (StB, (L, x, S1 :: R)).
Proof. reflexivity. Qed.

(** ** The gadgets

    Each is uniform in the surrounding tape and was checked exhaustively
    over every [(L,R)] with [|L|,|R| <= 4] before being written here. *)

(** The outward unit: eats four cells and hands one back -- net three per
    five steps.  [A1 = 0RD] writes a 0 and [D1 = 1RA] writes a 1, so the
    outward sweep LAYS A UNARY RUN; this packages that over one block. *)
Lemma out5 : forall L R,
  csteps tm_20 5 (StC, (L, S0, S1 :: S1 :: S1 :: S0 :: R))
  = Some (StC, (S1 :: S0 :: S1 :: L, S0, S1 :: R)).
Proof. reflexivity. Qed.

(** The turnaround into [StB]. *)
Lemma cross5 : forall L R,
  csteps tm_20 5 (StC, (L, S0, S1 :: S1 :: S0 :: S1 :: R))
  = Some (StB, (S1 :: S0 :: S1 :: L, S1, S1 :: R)).
Proof. reflexivity. Qed.

(** The [StB] return, which fills with 1s -- one step per cell. *)
Lemma ret3 : forall L R,
  csteps tm_20 3 (StB, (S1 :: S1 :: S0 :: L, S1, R))
  = Some (StB, (L, S0, S1 :: S1 :: S1 :: R)).
Proof. reflexivity. Qed.

Lemma ret2 : forall L R,
  csteps tm_20 2 (StB, (S1 :: S0 :: L, S1, R))
  = Some (StB, (L, S0, S1 :: S1 :: R)).
Proof. reflexivity. Qed.

(** ** The re-encoders

    [rb3] and [rb2] are the whole reason this machine is a counter in
    another alphabet: the outward sweep lays a UNARY run, and the return
    sweep turns that run back into BLOCKS, one block per unit.  That is
    John's "bounces off the lsb and then passes through". *)

Lemma rb3 : forall L R,
  csteps tm_20 3 (StC, (S1 :: S0 :: S1 :: L, S1, R))
  = Some (StC, (L, S1, S1 :: S1 :: S0 :: R)).
Proof. reflexivity. Qed.

Lemma rb2 : forall L R,
  csteps tm_20 2 (StC, (S0 :: S1 :: L, S1, R))
  = Some (StC, (L, S1, S1 :: S0 :: R)).
Proof. reflexivity. Qed.

(** The sweep's last unit, which lands on the new left record.  [C1 = 0LB]
    and [B0 = 1LC] both read [chd L], so -- like #15's deposit -- this one
    is stated through [chd]/[ctl] rather than as a window, and then the END
    of the left list is not a separate case. *)
Lemma rb3e : forall R,
  csteps tm_20 3 (StC, ([S1], S1, R))
  = Some (StC, ([], S0, S1 :: S1 :: S0 :: R)).
Proof. reflexivity. Qed.

(** ** The two leads, and rule A

    Rule A is the whole no-carry lap: one window, constant cost, and both
    left lists are empty so there is no [L] to quantify over. *)

Definition leadA (T : list Sym) : list Sym := S1 :: S1 :: S0 :: S1 :: S0 :: T.
Definition leadB (T : list Sym) : list Sym :=
  S1 :: S0 :: S1 :: S1 :: S1 :: S1 :: S0 :: T.

Lemma ruleA : forall T,
  csteps tm_20 10 (StC, ([], S0, leadA T)) = Some (StC, ([], S0, leadB T)).
Proof. reflexivity. Qed.

(** The long lap's entry: a uniform window off the B-type lead, leaving the
    debris [E] on the left.  [E] is what carries the [+1]. *)
Definition E : list Sym := [S1; S0; S1; S0; S1; S1].

Lemma entry10 : forall T,
  csteps tm_20 10 (StC, ([], S0, leadB T)) = Some (StC, (E, S0, S1 :: T)).
Proof. reflexivity. Qed.

(** ** The block word and the outward sweep

    [blks r X] is [b^r ++ X] and [lay r M] is [(101)^r ++ M]; both take
    their tail as an argument, so composing them is [cbn] rather than [app]
    associativity. *)

Fixpoint blks (r : nat) (X : list Sym) : list Sym :=
  match r with 0 => X | S i => S1 :: S1 :: S0 :: blks i X end.

Fixpoint lay (r : nat) (M : list Sym) : list Sym :=
  match r with 0 => M | S i => S1 :: S0 :: S1 :: lay i M end.

Lemma blks_shift : forall r X,
  blks r (S1 :: S1 :: S0 :: X) = S1 :: S1 :: S0 :: blks r X.
Proof.
  induction r as [|r IH]; intro X; cbn [blks];
    [reflexivity | rewrite IH; reflexivity].
Qed.

Lemma lay_shift : forall r M,
  lay r (S1 :: S0 :: S1 :: M) = S1 :: S0 :: S1 :: lay r M.
Proof.
  induction r as [|r IH]; intro M; cbn [lay];
    [reflexivity | rewrite IH; reflexivity].
Qed.

(** [out5] iterated: the b-run is eaten one block at a time, and the [1]
    the gadget hands back is what lets the next one fire.  An induction on
    the count with the tail universally quantified, so the untouched part of
    the tape never enters. *)
Lemma out5s : forall r M X,
  csteps tm_20 (5 * r) (StC, (M, S0, S1 :: blks r X))
  = Some (StC, (lay r M, S0, S1 :: X)).
Proof.
  induction r as [|r IH]; intros M X.
  - reflexivity.
  - replace (5 * S r) with (5 + 5 * r) by lia.
    cbn [blks lay].
    rewrite csteps_add, out5, IH, lay_shift. reflexivity.
Qed.

(** ** The return sweep

    [Rev W] says the left word [W] is a concatenation of the units the
    return sweep consumes -- [1;0;1] (emit [b]) and [0;1] (emit [a]) --
    ending on the single [1] that lands the head on the new left record.
    [bk] carries the RESULT word alongside, so the sweep and what it
    rebuilds are one induction over the same relation, never two that have
    to be linked afterwards. *)

Inductive Rev : list Sym -> Prop :=
| RevE : Rev [S1]
| Rev3 : forall W, Rev W -> Rev (S1 :: S0 :: S1 :: W)
| Rev2 : forall W, Rev W -> Rev (S0 :: S1 :: W).

Fixpoint rcost (W : list Sym) : nat :=
  match W with
  | S1 :: S0 :: S1 :: t => 3 + rcost t
  | S0 :: S1 :: t => 2 + rcost t
  | _ => 3
  end.

Fixpoint bk (W R : list Sym) : list Sym :=
  match W with
  | S1 :: S0 :: S1 :: t => bk t (S1 :: S1 :: S0 :: R)
  | S0 :: S1 :: t => bk t (S1 :: S0 :: R)
  | _ => S1 :: S1 :: S0 :: R
  end.

Lemma retsweep : forall W, Rev W -> forall R,
  csteps tm_20 (rcost W) (StC, (W, S1, R)) = Some (StC, ([], S0, bk W R)).
Proof.
  induction 1 as [|W HW IH|W HW IH]; intro R.
  - apply rb3e.
  - cbn [rcost bk]. rewrite csteps_add, rb3, IH. reflexivity.
  - cbn [rcost bk]. rewrite csteps_add, rb2, IH. reflexivity.
Qed.

(** The carried [(101)^r] comes back as [b^r], one block per unit. *)
Lemma lay_Rev : forall r W, Rev W -> Rev (lay r W).
Proof.
  induction r as [|r IH]; intros W H; cbn [lay];
    [exact H | apply Rev3, IH, H].
Qed.

Lemma bk_lay : forall r M R, bk (lay r M) R = bk M (blks r R).
Proof.
  induction r as [|r IH]; intros M R; cbn [lay blks].
  - reflexivity.
  - cbn [bk]. rewrite IH, blks_shift. reflexivity.
Qed.

(** The entry debris is sweep-shaped, and what it rebuilds is the A-type
    lead followed by ONE MORE BLOCK.  This is the whole increment: the
    sweep emits [b], then [a], then [b], and [b ++ a = 1 1 0 1 0] is
    exactly [leadA]. *)

Lemma Rev_E : Rev E.
Proof. apply Rev3, Rev2, RevE. Qed.

Lemma bk_E : forall R, bk E R = leadA (S1 :: S1 :: S0 :: R).
Proof. reflexivity. Qed.

Lemma bk_layE : forall r R, bk (lay r E) R = leadA (blks (S r) R).
Proof.
  intros r R. rewrite bk_lay, bk_E. reflexivity.
Qed.

(** ** Splitting the sweep at the middle's debris

    The return sweep runs over [D ++ lay r E], where [D] is whatever the
    middle laid on top.  [RevP] is [Rev] without the terminal unit -- a
    sweep PREFIX -- and [enc] is the word such a prefix emits.  With these
    the sweep splits, so the [r]-dependent half ([bk_layE], the increment)
    is proved once and never re-entered. *)

Inductive RevP : list Sym -> Prop :=
| RevPN : RevP []
| RevP3 : forall D, RevP D -> RevP (S1 :: S0 :: S1 :: D)
| RevP2 : forall D, RevP D -> RevP (S0 :: S1 :: D).

Fixpoint enc (D R : list Sym) : list Sym :=
  match D with
  | S1 :: S0 :: S1 :: t => enc t (S1 :: S1 :: S0 :: R)
  | S0 :: S1 :: t => enc t (S1 :: S0 :: R)
  | _ => R
  end.

Lemma Rev_app : forall D, RevP D -> forall W, Rev W -> Rev (D ++ W).
Proof.
  induction 1 as [|D HD IH|D HD IH]; intros W HW; cbn [app].
  - exact HW.
  - apply Rev3, IH, HW.
  - apply Rev2, IH, HW.
Qed.

Lemma bk_app : forall D, RevP D -> forall W R, bk (D ++ W) R = bk W (enc D R).
Proof.
  induction 1 as [|D HD IH|D HD IH]; intros W R; cbn [app enc];
    [reflexivity | cbn [bk]; apply IH | cbn [bk]; apply IH].
Qed.

(** The prefix's own cost, so the split is additive with no subtraction. *)
Fixpoint pcost (D : list Sym) : nat :=
  match D with
  | S1 :: S0 :: S1 :: t => 3 + pcost t
  | S0 :: S1 :: t => 2 + pcost t
  | _ => 0
  end.

Lemma rcost_app : forall D, RevP D -> forall W,
  rcost (D ++ W) = pcost D + rcost W.
Proof.
  induction 1 as [|D HD IH|D HD IH]; intro W; cbn [app rcost pcost];
    [reflexivity | rewrite IH; lia | rewrite IH; lia].
Qed.

(** ** The anchors

    [(r, rest)] with [r] the lap index -- the leading b-run -- and [rest]
    the tail beyond it.  No closed form for [rest] is needed anywhere:
    [WaveCounter.wglue_neverqh] takes an ARBITRARY anchor type with a total
    successor and a preserved invariant, which is the closer double #32
    used. *)

Definition CfA (a : nat * list Sym) : cconf :=
  (StC, ([], S0, leadA (blks (fst a) (snd a)))).

Definition CfB (a : nat * list Sym) : cconf :=
  (StC, ([], S0, leadB (blks (fst a) (snd a)))).

(** Rule A at the anchors. *)
Lemma lapA : forall a, csteps tm_20 10 (CfA a) = Some (CfB a).
Proof. intros [r rest]. apply ruleA. Qed.

(** The long lap's first two phases, which are all that depend on [r]:
    after them the left list is [lay r E] and the right list is
    [S1 :: rest], and NEITHER mentions [r] again -- the middle runs on
    [rest] alone. *)
Lemma lapB_pre : forall r rest,
  csteps tm_20 (10 + 5 * r) (CfB (r, rest))
  = Some (StC, (lay r E, S0, S1 :: rest)).
Proof.
  intros r rest. unfold CfB; cbn [fst snd].
  rewrite csteps_add, entry10, out5s. reflexivity.
Qed.

(** ...and the last phase, which is likewise uniform in [r]: whatever
    debris [D] the middle leaves on top, the sweep eats it, then eats the
    carried [(101)^r], then eats [E] -- and lands on [CfA (S r, _)].  The
    [+1] is [bk_layE]. *)
Lemma lapB_post : forall D r R, RevP D ->
  csteps tm_20 (pcost D + rcost (lay r E)) (StC, (D ++ lay r E, S1, R))
  = Some (CfA (S r, enc D R)).
Proof.
  intros D r R HD.
  rewrite <- (rcost_app D HD (lay r E)).
  rewrite (retsweep _ (Rev_app D HD _ (lay_Rev r E Rev_E))).
  rewrite (bk_app D HD), bk_layE. reflexivity.
Qed.

(** ** Visits: all four states within four steps of either anchor *)

Lemma visA : forall T,
  csteps tm_20 4 (StC, ([], S0, leadA T))
  = Some (StB, ([S1; S1; S0; S1], S1, S0 :: T)).
Proof. reflexivity. Qed.

Lemma vis20 : forall a q,
  exists k c, csteps tm_20 k (CfA a) = Some c /\ fst c = q.
Proof.
  intros [r rest] q. unfold CfA; cbn [fst snd]. destruct q.
  - exists 1. eexists. split; reflexivity.
  - exists 4. eexists. split; [apply visA | reflexivity].
  - exists 0. eexists. split; reflexivity.
  - exists 2. eexists. split; reflexivity.
Qed.

(** ** The abstract state, and the successor in closed form

    The anchor's tail is a word of 1-RUN LENGTHS: [wruns [n1;n2;...]] is
    [1^n1 0 1^n2 0 ...].  There is no separate lap index -- the leading
    b-run IS the leading run of 2s, because [b = 110 = 1^2 0]
    ([wruns_blks] below) -- so the abstract state is just the word.

    Reading rightward from the anchor the head enters on a 1, so the run it
    actually reads at [n_i] is [n_i + 1].  Hence [n_i] EVEN means the run
    read is odd and the sweep RIDES over it; [n_i] ODD means the run read is
    even, and that is the TURNAROUND.  This is wave4 #15's carry with the
    parities swapped: the "bits" are the run lengths mod 2, the carry rides
    over the even ones and stops at the first odd one.

    Each ride lays an alternating block that the return sweep re-encodes as
    [b a^(n/2-1)], the turn lays [a^((n-1)/2)], and the entry debris
    contributes the spare [b] that is the [+1].  Re-encoding reverses the
    unit order and maps [b -> 2], [a -> 1], which is [nv] below.

    [nv0] is a structural recursion on the list, so [nv] is TOTAL: no fuel,
    and no closed form for the tape, is needed anywhere.  It reproduces the
    orbit's A-anchor word for all 302 laps reachable in 400,000 steps and on
    synthetic anchors the orbit never visits
    ([tools/counters/nv20.py], green). *)

Fixpoint wruns (w : list nat) : list Sym :=
  match w with
  | [] => []
  | n :: t => repeat S1 n ++ S0 :: wruns t
  end.

Fixpoint rep1 (k : nat) (t : list nat) : list nat :=
  match k with 0 => t | S i => 1 :: rep1 i t end.

Fixpoint nv0 (w : list nat) : list nat :=
  match w with
  | [] => []                                    (* excluded by the invariant *)
  | n :: t =>
      if Nat.even n
      then rep1 (Nat.div2 n - 1) (2 :: nv0 t)    (* ride *)
      else match t with
           | [] => rep1 (Nat.div2 n) [2; 1]      (* turn, nothing beyond *)
           | n2 :: t2 => rep1 (Nat.div2 n) ((n2 + 3) :: t2)   (* turn *)
           end
  end.

(** The leading 2 is the entry debris's spare block -- the counter's [+1]. *)
Definition nv (w : list nat) : list nat := 2 :: nv0 w.

Definition CfW (w : list nat) : cconf := (StC, ([], S0, leadA (wruns w))).

(** The bridge to the [blks]/[lay] machinery already proved: a leading run
    of 2s in the run-length word IS the b-run the outward sweep eats. *)
Fixpoint rep2 (r : nat) (v : list nat) : list nat :=
  match r with 0 => v | S i => 2 :: rep2 i v end.

Lemma wruns_blks : forall r v, wruns (rep2 r v) = blks r (wruns v).
Proof.
  induction r as [|r IH]; intro v; cbn [rep2 blks wruns repeat app];
    [reflexivity | rewrite IH; reflexivity].
Qed.

Lemma CfW_blks : forall r v,
  CfW (rep2 r v) = (StC, ([], S0, leadA (blks r (wruns v)))).
Proof. intros r v. unfold CfW. rewrite wruns_blks. reflexivity. Qed.

(** The lap's two settled halves, restated on the run-length word: rule A,
    then the entry and the b-run sweep. *)
Lemma lapA_W : forall w,
  csteps tm_20 10 (CfW w) = Some (StC, ([], S0, leadB (wruns w))).
Proof. intro w. apply ruleA. Qed.

Lemma lapB_pre_W : forall r v,
  csteps tm_20 (10 + 5 * r)
    (StC, ([], S0, leadB (wruns (rep2 r v))))
  = Some (StC, (lay r E, S0, S1 :: wruns v)).
Proof.
  intros r v. rewrite wruns_blks.
  rewrite csteps_add, entry10, out5s. reflexivity.
Qed.

(** ** Boot

    The family settles at t = 50, at the A-type anchor with [r = 0] and
    [rest = 1 0 1 1 1 1]; the three left records before it (t = 4, 18, 28)
    are the boot and belong to no phase.  In run-length form that anchor is
    [w = [1; 4]]. *)

Definition w0_20 : list nat := [1; 4].

Lemma boot20_W : exists t0, stepn tm_20 t0 InitES = Some (lift (CfW w0_20)).
Proof.
  exists 50.
  assert (H : match csteps tm_20 50 c0 with
              | Some c => ceqb c (CfW w0_20)
              | None => false
              end = true) by (vm_compute; reflexivity).
  destruct (csteps tm_20 50 c0) as [c|] eqn:Ec; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ Ec).
  f_equal. apply ceqb_lift. exact H.
Qed.

Definition a0_20 : nat * list Sym := (0, [S1; S0; S1; S1; S1; S1]).

Lemma boot20 : exists t0, stepn tm_20 t0 InitES = Some (lift (CfA a0_20)).
Proof.
  exists 50.
  assert (H : match csteps tm_20 50 c0 with
              | Some c => ceqb c (CfA a0_20)
              | None => false
              end = true) by (vm_compute; reflexivity).
  destruct (csteps tm_20 50 c0) as [c|] eqn:Ec; [|discriminate].
  rewrite <- lift_c0, (csteps_lift _ _ _ _ Ec).
  f_equal. apply ceqb_lift. exact H.
Qed.
