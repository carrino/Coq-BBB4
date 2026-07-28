(** * Tower_20: 1RB0RD_1LC1LB_1RA0LB_1LC1RA -- the gadget, sweep,
    re-encoding and MIDDLE layers.

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
    deposit passed a 42-context sample and failed 496 of the 961.  The
    middle's five new joints and its two windows were checked the same way,
    in the exact form written here ([tools/counters/mid20.py]).

    WHAT IS PROVED.  [lapB_full_ne]/[lapB_full_z]/[lapB_full_end] below are
    the WHOLE long lap -- entry, b-run sweep, middle, return, [+1] -- for
    every tail that HAS an odd entry, i.e. every tail on which the sweep
    turns.  The abstract successor [nv] does NOT preserve "has an odd
    entry" on arbitrary words, so the machine is closed by an INVARIANT:
    the DESCENT DESCRIPTOR ([Vd]/[Ud] below), a finite grammar closed under
    [nv] whose every decode is alive (has an odd entry) and zero-free.  The
    four phase identities of [nv0] are unconditional ([nv0_dec_mut]); the
    level boots do not cycle but grow, and the descriptor captures that
    growth as a nested [UDD] chain.  [nqh_tower20 : NeverQuasiHaltsSt tm_20]
    is the closure, via [WaveCounter.wglue_neverqh].
    [tools/counters/inv20.py] records the reconnaissance that preceded it;
    [tools/counters/desc20.py] validates the descriptor mirror.

    [Print Assumptions nqh_tower20] = [functional_extensionality_dep] only. *)

From Coq Require Import Arith Lia List Bool.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape WaveCounter.
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

(** ** THE MIDDLE: the ride window and the turn window

    After [lapB_pre] the head is at [(StC, (M, S0, S1 :: wruns w))] and sweeps
    RIGHT.  It enters each run on a 1, so the run it actually READS at [n_i]
    is [n_i + 1]: [n_i] EVEN means the run read is odd and the sweep RIDES
    over it; [n_i] ODD means the run read is even, and that is the TURNAROUND.

    Five new joints.  [ad2] and the two walk-backs READ the context, so --
    trap 2 -- they are stated through [chd]/[ctl] rather than as windows.
    Every one of them was checked against the CTape-faithful mirror in the
    EXACT form written here, over all 961 [(L,R)] with [|L|,|R| <= 4]
    ([tools/counters/mid20.py]), before any of this was written. *)

(** The two-step [A]/[D] stride: eats two 1s and lays [1;0]. *)
Lemma ad2 : forall L R,
  csteps tm_20 2 (StA, (L, S1, S1 :: R))
  = Some (StA, (S1 :: S0 :: L, chd R, ctl R)).
Proof. reflexivity. Qed.

(** The ride's last two steps: [A] over the run's terminator, [D0 = 1LC]
    back into [StC] -- which is why an odd run read continues the sweep. *)
Lemma fin2 : forall L R,
  csteps tm_20 2 (StA, (L, S1, S0 :: R)) = Some (StC, (L, S0, S1 :: R)).
Proof. reflexivity. Qed.

(** The turn's three steps.  [A0 = 1RB] BOUNCES the head right into [StB] --
    that is John's "bounces off the lsb", and it is the whole difference
    between an even and an odd run read. *)
Lemma turn3 : forall L R,
  csteps tm_20 3 (StA, (L, S1, S1 :: S0 :: R))
  = Some (StB, (S1 :: S1 :: S0 :: L, chd R, ctl R)).
Proof. reflexivity. Qed.

(** The [StB] walk-back, next run NONEMPTY: [B1;B1;B1;B0], laying four 1s.
    Those four 1s minus the one it consumed are the [+3] of the successor. *)
Lemma wb4 : forall L R,
  csteps tm_20 4 (StB, (S1 :: S1 :: S0 :: L, S1, R))
  = Some (StC, (ctl L, chd L, S1 :: S1 :: S1 :: S1 :: R)).
Proof. reflexivity. Qed.

(** ...and next run EMPTY (or the tape ends): [B0] at once. *)
Lemma wb1 : forall L R,
  csteps tm_20 1 (StB, (S1 :: S1 :: S0 :: L, S0, R))
  = Some (StC, (S1 :: S0 :: L, S1, S1 :: R)).
Proof. reflexivity. Qed.

(** [dbl k L] is [(1 0)^k ++ L]; the ride's debris over [M] is
    [dbl k (S1 :: M)], the ALTERNATING word of length [2k+1].  [arep k M] is
    [(0 1)^k ++ M] -- [a^k] in the block alphabet, and [RevP]-shaped, which
    is what [lapB_post] takes.  [ones2 j Z] is [1^(2j) ++ Z], written as a
    fixpoint so the sweep induction never touches [repeat]/[app]. *)

Fixpoint dbl (k : nat) (L : list Sym) : list Sym :=
  match k with 0 => L | S i => S1 :: S0 :: dbl i L end.

Fixpoint arep (k : nat) (M : list Sym) : list Sym :=
  match k with 0 => M | S i => S0 :: S1 :: arep i M end.

Fixpoint ones2 (j : nat) (Z : list Sym) : list Sym :=
  match j with 0 => Z | S i => S1 :: S1 :: ones2 i Z end.

Lemma dbl_shift : forall k L, dbl k (S1 :: S0 :: L) = S1 :: S0 :: dbl k L.
Proof.
  induction k as [|k IH]; intro L; cbn [dbl];
    [reflexivity | rewrite IH; reflexivity].
Qed.

Lemma dbl_app : forall k A B, dbl k (A ++ B) = dbl k A ++ B.
Proof.
  induction k as [|k IH]; intros A B; cbn [dbl app];
    [reflexivity | rewrite IH; reflexivity].
Qed.

Lemma arep_app : forall k A B, arep k (A ++ B) = arep k A ++ B.
Proof.
  induction k as [|k IH]; intros A B; cbn [arep app];
    [reflexivity | rewrite IH; reflexivity].
Qed.

(** The ride debris, read as a sweep word: [(1 0)^k 1] is [1] then [(0 1)^k].
    This is the bridge between the two shapes and it is used both ways. *)
Lemma dbl_cons : forall k M, dbl k (S1 :: M) = S1 :: arep k M.
Proof.
  induction k as [|k IH]; intro M; cbn [dbl arep];
    [reflexivity | rewrite IH; reflexivity].
Qed.

Lemma ones2_repeat : forall j Z, ones2 j Z = repeat S1 (2 * j) ++ Z.
Proof.
  induction j as [|j IH]; intro Z; cbn [ones2].
  - reflexivity.
  - replace (2 * S j) with (S (S (2 * j))) by lia.
    cbn [repeat app]. rewrite IH. reflexivity.
Qed.

Lemma repeat_S1_snoc : forall n, repeat S1 (n + 1) = repeat S1 n ++ [S1].
Proof.
  induction n as [|n IH]; cbn [repeat app Nat.add];
    [reflexivity | rewrite IH; reflexivity].
Qed.

Lemma ones2_odd : forall k Z, ones2 k (S1 :: Z) = repeat S1 (2 * k + 1) ++ Z.
Proof.
  intros k Z. rewrite ones2_repeat, repeat_S1_snoc, <- app_assoc. reflexivity.
Qed.

(** The [A]/[D] walk over a run: [j] strides, [2j] steps, laying [(1 0)^j].
    Uniform in the tail [Z], so the SAME lemma serves the ride (where [Z]
    starts with the run's terminator) and the turn (where it starts with one
    more 1). *)
Lemma walk : forall j L Z,
  csteps tm_20 (2 * j) (StA, (L, S1, ones2 j Z))
  = Some (StA, (dbl j L, S1, Z)).
Proof.
  induction j as [|j IH]; intros L Z.
  - reflexivity.
  - replace (2 * S j) with (2 + 2 * j) by lia.
    cbn [ones2 dbl].
    rewrite csteps_add, ad2. cbn [chd ctl].
    rewrite IH, dbl_shift. reflexivity.
Qed.

(** THE RIDE.  [n = 2k] EVEN: a constant [n+3] steps, debris [(1 0)^k 1].
    [out5] is the [k = 1] case; [k = 0] is a bare three-step window. *)
Lemma ride : forall k M X,
  csteps tm_20 (2 * k + 3) (StC, (M, S0, S1 :: ones2 k (S0 :: X)))
  = Some (StC, (dbl k (S1 :: M), S0, S1 :: X)).
Proof.
  intros k M X.
  replace (2 * k + 3) with (1 + (2 * k + 2)) by lia.
  rewrite csteps_add, jcac, csteps_add, walk, fin2. reflexivity.
Qed.

Lemma ride_W : forall k M t,
  csteps tm_20 (2 * k + 3) (StC, (M, S0, S1 :: wruns (2 * k :: t)))
  = Some (StC, (dbl k (S1 :: M), S0, S1 :: wruns t)).
Proof.
  intros k M t. cbn [wruns]. rewrite <- ones2_repeat. apply ride.
Qed.

(** The whole EVEN PREFIX ridden in one induction.  [K] is the list of
    half-lengths, so [wev K t] is the word whose even prefix is [2k] for each
    [k] in [K]; no evenness side condition is needed anywhere. *)

Fixpoint wev (K : list nat) (t : list nat) : list nat :=
  match K with [] => t | k :: r => (2 * k) :: wev r t end.

Fixpoint rcostK (K : list nat) : nat :=
  match K with [] => 0 | k :: r => (2 * k + 3) + rcostK r end.

Fixpoint rideL (K : list nat) (M : list Sym) : list Sym :=
  match K with [] => M | k :: r => rideL r (dbl k (S1 :: M)) end.

Fixpoint rideW (K : list nat) : list Sym :=
  match K with [] => [] | k :: r => rideW r ++ dbl k [S1] end.

Lemma rideL_app : forall K M, rideL K M = rideW K ++ M.
Proof.
  induction K as [|k K IH]; intro M; cbn [rideL rideW].
  - reflexivity.
  - rewrite IH. change (S1 :: M) with ([S1] ++ M).
    rewrite dbl_app, app_assoc. reflexivity.
Qed.

Lemma rides : forall K M t,
  csteps tm_20 (rcostK K) (StC, (M, S0, S1 :: wruns (wev K t)))
  = Some (StC, (rideL K M, S0, S1 :: wruns t)).
Proof.
  induction K as [|k K IH]; intros M t; cbn [wev rcostK rideL].
  - reflexivity.
  - rewrite csteps_add, ride_W. apply IH.
Qed.

(** THE TURN.  [n = 2k+1] ODD: the head crosses the run and [A0] bounces it
    into [StB] at step [2k+4], uniform in what follows. *)
Lemma turn_bounce : forall k M X,
  csteps tm_20 (2 * k + 4) (StC, (M, S0, S1 :: ones2 k (S1 :: S0 :: X)))
  = Some (StB, (S1 :: S1 :: S0 :: dbl k (S1 :: M), chd X, ctl X)).
Proof.
  intros k M X.
  replace (2 * k + 4) with (1 + (2 * k + 3)) by lia.
  rewrite csteps_add, jcac, csteps_add, walk, turn3. reflexivity.
Qed.

Lemma turn_word : forall k M t,
  csteps tm_20 (2 * k + 4) (StC, (M, S0, S1 :: wruns ((2 * k + 1) :: t)))
  = Some (StB, (S1 :: S1 :: S0 :: dbl k (S1 :: M),
                chd (wruns t), ctl (wruns t))).
Proof.
  intros k M t. cbn [wruns]. rewrite <- ones2_odd. apply turn_bounce.
Qed.

(** ...and where it lands.  NEXT RUN NONEMPTY: the four-step walk-back, and
    the next entry comes back as [n2 + 3] -- the abstract successor's carry,
    read off the tape.  The debris is [a^k], which is [RevP]. *)
Lemma turn_ne : forall k M n2 t2,
  csteps tm_20 (2 * k + 8)
    (StC, (M, S0, S1 :: wruns ((2 * k + 1) :: S n2 :: t2)))
  = Some (StC, (arep k M, S1, wruns ((S n2 + 3) :: t2))).
Proof.
  intros k M n2 t2.
  replace (2 * k + 8) with ((2 * k + 4) + 4) by lia.
  rewrite csteps_add, turn_word. cbn [wruns repeat app chd ctl].
  rewrite wb4, dbl_cons. cbn [chd ctl].
  replace (S n2 + 3) with (n2 + 4) by lia.
  replace (n2 + 4) with (4 + n2) by lia.
  cbn [wruns repeat app]. reflexivity.
Qed.

(** ...NEXT RUN EMPTY: [B0] at once, and the debris is [b a^k]. *)
Lemma turn_z : forall k M t,
  csteps tm_20 (2 * k + 5)
    (StC, (M, S0, S1 :: wruns ((2 * k + 1) :: 0 :: t)))
  = Some (StC, (dbl (S k) (S1 :: M), S1, S1 :: wruns t)).
Proof.
  intros k M t.
  replace (2 * k + 5) with ((2 * k + 4) + 1) by lia.
  rewrite csteps_add, turn_word. cbn [wruns repeat app chd ctl].
  rewrite wb1. reflexivity.
Qed.

(** ...and the same one-step landing when the TAPE ENDS -- [chd []] is [S0],
    so this is the same branch, not a new one. *)
Lemma turn_end : forall k M,
  csteps tm_20 (2 * k + 5) (StC, (M, S0, S1 :: wruns [2 * k + 1]))
  = Some (StC, (dbl (S k) (S1 :: M), S1, [S1])).
Proof.
  intros k M.
  replace (2 * k + 5) with ((2 * k + 4) + 1) by lia.
  rewrite csteps_add, turn_word. cbn [wruns chd ctl].
  rewrite wb1. reflexivity.
Qed.

(** ** The middle's debris is [RevP]

    [lapB_post] eats [D ++ lay r E] for any [RevP D].  The middle leaves
    [D = arep k [] ++ rideW K], and that is [RevP] exactly when no ridden run
    is empty -- [dbl 0 [S1] = [S1]] is a lone 1, which is [Rev]'s terminal
    unit and not a prefix unit, so a [0] entry would break the decode.  On
    the reachable words every entry is positive, so this is the family's
    wellformedness side condition, [WaveCounter]'s [Forall (1 <= _)] again. *)

Lemma RevP_arep : forall k D, RevP D -> RevP (arep k D).
Proof.
  induction k as [|k IH]; intros D H; cbn [arep];
    [exact H | apply RevP2, IH, H].
Qed.

Lemma RevP_dblS : forall k D, RevP D -> RevP (dbl (S k) [S1] ++ D).
Proof.
  intros k D H. cbn [dbl app]. rewrite dbl_cons. cbn [app].
  apply RevP3. rewrite <- arep_app. apply RevP_arep, H.
Qed.

Lemma RevP_rideW : forall K, Forall (fun k => k <> 0) K ->
  forall D, RevP D -> RevP (rideW K ++ D).
Proof.
  induction 1 as [|k K Hk HK IH]; intros D HD; cbn [rideW].
  - exact HD.
  - rewrite <- app_assoc. apply IH.
    destruct k as [|k]; [contradiction Hk; reflexivity|].
    apply RevP_dblS, HD.
Qed.

(** [Dmid] is the turn-with-a-run-beyond debris [a^k] over the ride's, and
    [Dmidz] the nothing-beyond one, which carries the extra [b]. *)
Definition Dmid (K : list nat) (k : nat) : list Sym :=
  arep k [] ++ rideW K.

Definition Dmidz (K : list nat) (k : nat) : list Sym :=
  dbl (S k) [S1] ++ rideW K.

Lemma Dmid_app : forall K k M, Dmid K k ++ M = arep k (rideW K ++ M).
Proof.
  intros K k M. unfold Dmid. rewrite <- app_assoc, <- arep_app. reflexivity.
Qed.

Lemma Dmidz_app : forall K k M,
  Dmidz K k ++ M = dbl (S k) (S1 :: (rideW K ++ M)).
Proof.
  intros K k M. unfold Dmidz. rewrite <- app_assoc.
  change (S1 :: (rideW K ++ M)) with ([S1] ++ (rideW K ++ M)).
  rewrite dbl_app. reflexivity.
Qed.

Lemma RevP_rideW0 : forall K, Forall (fun x => x <> 0) K -> RevP (rideW K).
Proof.
  intros K HK. rewrite <- (app_nil_r (rideW K)).
  apply RevP_rideW; [exact HK | apply RevPN].
Qed.

Lemma RevP_Dmid : forall K k, Forall (fun x => x <> 0) K ->
  RevP (Dmid K k).
Proof.
  intros K k HK. unfold Dmid. rewrite <- arep_app.
  apply RevP_arep. cbn [app]. apply RevP_rideW0, HK.
Qed.

Lemma RevP_Dmidz : forall K k, Forall (fun x => x <> 0) K ->
  RevP (Dmidz K k).
Proof.
  intros K k HK. unfold Dmidz. apply RevP_dblS, RevP_rideW0, HK.
Qed.

(** ** The middle, in the shape [lapB_post] consumes *)

Lemma middle_ne : forall K k n2 t2 M,
  csteps tm_20 (rcostK K + (2 * k + 8))
    (StC, (M, S0, S1 :: wruns (wev K ((2 * k + 1) :: S n2 :: t2))))
  = Some (StC, (Dmid K k ++ M, S1, wruns ((S n2 + 3) :: t2))).
Proof.
  intros K k n2 t2 M.
  rewrite csteps_add, rides, turn_ne, rideL_app, Dmid_app. reflexivity.
Qed.

Lemma middle_z : forall K k t M,
  csteps tm_20 (rcostK K + (2 * k + 5))
    (StC, (M, S0, S1 :: wruns (wev K ((2 * k + 1) :: 0 :: t))))
  = Some (StC, (Dmidz K k ++ M, S1, S1 :: wruns t)).
Proof.
  intros K k t M.
  rewrite csteps_add, rides, turn_z, rideL_app, Dmidz_app. reflexivity.
Qed.

(** ** THE LONG LAP, for every word that HAS an odd entry

    [lapB_pre] . [middle] . [lapB_post].  The hypothesis is exactly the
    decomposition of the tail as (even prefix) ++ (odd entry) ++ (rest) --
    that is, "the sweep turns".  What is NOT yet proved is that the abstract
    successor PRESERVES the existence of that decomposition; see
    [tools/counters/inv20.py] and NEXT_SESSION.md 2j. *)

Lemma lapB_full_ne : forall r K k n2 t2, Forall (fun x => x <> 0) K ->
  csteps tm_20
    ((10 + 5 * r) + ((rcostK K + (2 * k + 8))
     + (pcost (Dmid K k) + rcost (lay r E))))
    (CfB (r, wruns (wev K ((2 * k + 1) :: S n2 :: t2))))
  = Some (CfA (S r, enc (Dmid K k) (wruns ((S n2 + 3) :: t2)))).
Proof.
  intros r K k n2 t2 HK.
  rewrite csteps_add, lapB_pre, csteps_add, middle_ne.
  apply lapB_post, RevP_Dmid, HK.
Qed.

Lemma lapB_full_z : forall r K k t, Forall (fun x => x <> 0) K ->
  csteps tm_20
    ((10 + 5 * r) + ((rcostK K + (2 * k + 5))
     + (pcost (Dmidz K k) + rcost (lay r E))))
    (CfB (r, wruns (wev K ((2 * k + 1) :: 0 :: t))))
  = Some (CfA (S r, enc (Dmidz K k) (S1 :: wruns t))).
Proof.
  intros r K k t HK.
  rewrite csteps_add, lapB_pre, csteps_add, middle_z.
  apply lapB_post, RevP_Dmidz, HK.
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

(** ================================================================
    THE INVARIANT AND THE CLOSURE (wave-21, 2026-07-28)
    The descent descriptor that closes tower #20, folded in from the
    wave-21 development.  See the header's WHAT IS PROVED paragraph.
    ================================================================ *)

(** ** enc plumbing lemmas *)

Lemma enc_acc_app : forall D, RevP D -> forall R S, enc D (R ++ S) = enc D R ++ S.
Proof.
  induction 1 as [|D HD IH|D HD IH]; intros R S; cbn [enc]; [reflexivity | | ].
  - rewrite <- IH. reflexivity.
  - rewrite <- IH. reflexivity.
Qed.

Lemma enc_app : forall D, RevP D -> forall W R, enc (D ++ W) R = enc W (enc D R).
Proof.
  induction 1 as [|D HD IH|D HD IH]; intros W R; cbn [app enc];
    [reflexivity | apply IH | apply IH].
Qed.

Lemma enc_arep : forall k D R, enc (arep k D) R = enc D (dbl k R).
Proof.
  induction k as [|k IH]; intros D R; cbn [arep dbl].
  - reflexivity.
  - cbn [enc]. rewrite IH, dbl_shift. reflexivity.
Qed.

Lemma enc_dblS : forall j A, enc (dbl (S j) [S1]) A = dbl j (S1 :: S1 :: S0 :: A).
Proof.
  intros j A. cbn [dbl].
  change (S1 :: [])%list with ([S1]). rewrite dbl_cons. cbn [enc].
  rewrite enc_arep. cbn [enc]. reflexivity.
Qed.

(** ** wruns / rep1 / nv0 helpers *)

Lemma wruns_rep1 : forall j w, wruns (rep1 j w) = dbl j (wruns w).
Proof.
  induction j as [|j IH]; intro w; cbn [rep1 dbl].
  - reflexivity.
  - cbn [wruns repeat app]. rewrite IH. reflexivity.
Qed.

Lemma wruns_cons2 : forall w, wruns (2 :: w) = S1 :: S1 :: S0 :: wruns w.
Proof. reflexivity. Qed.

(** ** the ride-debris core *)

Fixpoint ridenv (K : list nat) (rest : list nat) : list nat :=
  match K with
  | [] => rest
  | k :: K' => rep1 (Nat.pred k) (2 :: ridenv K' rest)
  end.

Lemma div2_2k : forall k, Nat.div2 (2 * k) = k.
Proof.
  induction k as [|k IH]; [reflexivity|].
  replace (2 * S k) with (S (S (2 * k))) by lia. cbn [Nat.div2]. rewrite IH. reflexivity.
Qed.

Lemma nv0_wev : forall K X, nv0 (wev K X) = ridenv K (nv0 X).
Proof.
  induction K as [|k K IH]; intro X; cbn [wev ridenv].
  - reflexivity.
  - cbn [nv0]. rewrite Nat.even_mul.
    change (Nat.even 2) with true. cbn [orb].
    rewrite div2_2k, Nat.sub_1_r, IH. reflexivity.
Qed.

Lemma encride_core : forall K, Forall (fun x => x <> 0) K ->
  forall rest, enc (rideW K) (wruns rest) = wruns (ridenv K rest).
Proof.
  induction 1 as [|k K Hk HK IH]; intro rest; cbn [rideW ridenv].
  - reflexivity.
  - destruct k as [|j]; [contradiction Hk; reflexivity|].
    rewrite (enc_app (rideW K) (RevP_rideW0 K HK)).
    rewrite IH, enc_dblS.
    rewrite <- wruns_cons2, <- wruns_rep1. reflexivity.
Qed.

(** ** the two word-successor lemmas *)

Lemma nv0_odd_ne : forall k n2 t2,
  nv0 ((2 * k + 1) :: S n2 :: t2) = rep1 k ((S n2 + 3) :: t2).
Proof.
  intros k n2 t2. cbn [nv0].
  rewrite Nat.add_comm. cbn [Nat.even]. rewrite Nat.even_add_mul_2.
  cbn [orb Nat.even negb].
  replace (2 * k + 1) with (1 + 2 * k) by lia. rewrite Nat.div2_succ_double.
  reflexivity.
Qed.

Lemma nv0_odd_end : forall k, nv0 [2 * k + 1] = rep1 k [2; 1].
Proof.
  intro k. cbn [nv0].
  replace (2 * k + 1) with (1 + 2 * k) by lia.
  rewrite Nat.even_add_mul_2. cbn [orb Nat.even negb].
  rewrite Nat.div2_succ_double. reflexivity.
Qed.

Lemma enc_ne : forall K, Forall (fun x => x <> 0) K -> forall k n2 t2,
  enc (Dmid K k) (wruns ((S n2 + 3) :: t2))
  = wruns (nv0 (wev K ((2 * k + 1) :: S n2 :: t2))).
Proof.
  intros K HK k n2 t2.
  replace (Dmid K k) with (arep k (rideW K)).
  2:{ unfold Dmid. rewrite <- arep_app. cbn [app]. reflexivity. }
  rewrite enc_arep, <- wruns_rep1.
  rewrite (encride_core K HK (rep1 k ((S n2 + 3) :: t2))).
  rewrite nv0_wev, nv0_odd_ne. reflexivity.
Qed.

Lemma enc_end : forall K, Forall (fun x => x <> 0) K -> forall k,
  enc (Dmidz K k) [S1] ++ [S0] = wruns (nv0 (wev K [2 * k + 1])).
Proof.
  intros K HK k. unfold Dmidz.
  rewrite (enc_app (dbl (S k) [S1])).
  2:{ rewrite <- (app_nil_r (dbl (S k) [S1])). apply RevP_dblS. constructor. }
  rewrite enc_dblS.
  rewrite <- (enc_acc_app (rideW K) (RevP_rideW0 K HK)).
  rewrite <- dbl_app.
  change ([S1; S1; S0; S1] ++ [S0]) with (wruns [2; 1]).
  rewrite <- wruns_rep1.
  rewrite (encride_core K HK (rep1 k [2; 1])).
  rewrite nv0_wev, nv0_odd_end. reflexivity.
Qed.

(** ** the "ends with the tape" middle/lap for rest = [] *)

Lemma middle_end : forall K k M,
  csteps tm_20 (rcostK K + (2 * k + 5))
    (StC, (M, S0, S1 :: wruns (wev K [2 * k + 1])))
  = Some (StC, (Dmidz K k ++ M, S1, [S1])).
Proof.
  intros K k M.
  rewrite csteps_add, rides, turn_end, rideL_app, Dmidz_app. reflexivity.
Qed.

Lemma lapB_full_end : forall r K k, Forall (fun x => x <> 0) K ->
  csteps tm_20
    ((10 + 5 * r) + ((rcostK K + (2 * k + 5))
     + (pcost (Dmidz K k) + rcost (lay r E))))
    (CfB (r, wruns (wev K [2 * k + 1])))
  = Some (CfA (S r, enc (Dmidz K k) [S1])).
Proof.
  intros r K k HK.
  rewrite csteps_add, lapB_pre, csteps_add, middle_end.
  apply lapB_post, RevP_Dmidz, HK.
Qed.

(** ** decomposition: a nonzero word with an odd entry is wev K ((2k+1)::rest) *)

Definition hasodd_b (w : list nat) : bool := existsb Nat.odd w.

Lemma decompose : forall w, Forall (fun x => x <> 0) w -> hasodd_b w = true ->
  exists K k rest, w = wev K ((2 * k + 1) :: rest)
    /\ Forall (fun x => x <> 0) K.
Proof.
  induction w as [|a w IH]; intros HF Hodd; [discriminate|].
  inversion HF as [|? ? Ha HFw]; subst.
  destruct (Nat.odd a) eqn:Ea.
  - exists [], (Nat.div2 a), w. split; [|constructor].
    cbn [wev]. f_equal. f_equal.
    pose proof (Nat.div2_odd a) as Hd. rewrite Ea in Hd. cbn [Nat.b2n] in Hd. lia.
  - unfold hasodd_b in Hodd. cbn [existsb] in Hodd. rewrite Ea in Hodd. cbn [orb] in Hodd.
    destruct (IH HFw Hodd) as (K & k & rest & Hw & HK).
    exists (Nat.div2 a :: K), k, rest. split.
    + cbn [wev]. rewrite <- Hw. f_equal.
      pose proof (Nat.div2_odd a) as Hd. rewrite Ea in Hd. cbn [Nat.b2n] in Hd. lia.
    + constructor; [|exact HK].
      intro Hz. apply Ha.
      pose proof (Nat.div2_odd a) as Hd. rewrite Ea in Hd. cbn [Nat.b2n] in Hd. lia.
Qed.


(** ** The descent descriptor: a finite grammar closed under the abstract
    successor, every decode alive and nonzero.  This is the invariant. *)

Inductive Vd : Type :=
| VA0 | VA1 | VD0 (m : nat) | VD1 (m : nat)
| VP0 (u : Ud) | VP1 (u : Ud) | VP2 (u : Ud) | VP3 (u : Ud)
with Ud : Type :=
| UA2 | UA3 | UC0 (n : nat) | UC1 (n : nat)
| UD0 (m : nat) | UD1 (m : nat) | UDD (a : nat) (v : Vd).

Fixpoint decV (v : Vd) : list nat :=
  match v with
  | VA0 => [1; 4]
  | VA1 => [7]
  | VD0 m => 1 :: 5 :: rep2 m [1]
  | VD1 m => 8 :: rep2 m [1]
  | VP0 u => 1 :: 1 :: decU u
  | VP1 u => 4 :: decU u
  | VP2 u => 1 :: 2 :: nv0 (decU u)
  | VP3 u => 5 :: nv0 (decU u)
  end
with decU (u : Ud) : list nat :=
  match u with
  | UA2 => [1; 2; 1]
  | UA3 => [8; 1]
  | UC0 n => rep2 n [1]
  | UC1 n => 5 :: rep2 n [1]
  | UD0 m => 1 :: rep2 (m + 2) [1]
  | UD1 m => 8 :: rep2 (m + 1) [1]
  | UDD a v => 4 :: rep2 a (decV v)
  end.

Fixpoint stepV (v : Vd) : Vd :=
  match v with
  | VA0 => VA1
  | VA1 => VP0 UA2
  | VD0 m => VD1 m
  | VD1 m => VP0 (UD0 m)
  | VP0 u => VP1 u
  | VP1 u => VP2 u
  | VP2 u => VP3 u
  | VP3 u => VP0 (stepU u)
  end
with stepU (u : Ud) : Ud :=
  match u with
  | UA2 => UA3
  | UA3 => UDD 0 (VP0 (UC0 2))
  | UC0 n => UC1 n
  | UC1 0 => UDD 0 VA0
  | UC1 (S n) => UDD 0 (VD0 n)
  | UD0 m => UD1 m
  | UD1 m => UDD 0 (VP0 (UC0 (m + 3)))
  | UDD a v => UDD (a + 1) (stepV v)
  end.

Definition Xf (t : list nat) : list nat :=
  match t with [] => [2; 1] | a :: t' => (a + 3) :: t' end.

Scheme Vd_mut := Induction for Vd Sort Prop
  with Ud_mut := Induction for Ud Sort Prop.
Combined Scheme Vd_Ud_mut from Vd_mut, Ud_mut.

(** rep2 arithmetic and the concrete-head nv0 rewrites *)

Lemma rep2_push : forall n t, rep2 n (2 :: t) = 2 :: rep2 n t.
Proof.
  induction n as [|n IH]; intro t; cbn [rep2]; [reflexivity|].
  rewrite IH. reflexivity.
Qed.

Lemma two_rep2 : forall j, 2 :: rep2 j [2; 1] = rep2 (j + 2) [1].
Proof.
  induction j as [|j IH]; [reflexivity|].
  cbn [rep2]. replace (S j + 2) with (S (j + 2)) by lia. cbn [rep2].
  rewrite <- IH. reflexivity.
Qed.

Lemma nv0_2run : forall n w, nv0 (rep2 n w) = rep2 n (nv0 w).
Proof.
  induction n as [|n IH]; intro w; cbn [rep2]; [reflexivity|].
  transitivity (2 :: nv0 (rep2 n w)); [reflexivity|].
  rewrite IH. reflexivity.
Qed.

Lemma nv0_1 : nv0 [1] = [2; 1].
Proof. reflexivity. Qed.

Lemma nv0_1c : forall a t, nv0 (1 :: a :: t) = (a + 3) :: t.
Proof. reflexivity. Qed.

Lemma nv0_4c : forall L, nv0 (4 :: L) = 1 :: 2 :: nv0 L.
Proof. reflexivity. Qed.

Lemma nv0_8c : forall L, nv0 (8 :: L) = 1 :: 1 :: 1 :: 2 :: nv0 L.
Proof. reflexivity. Qed.

Lemma nv0_5f : forall S, nv0 (5 :: S) = 1 :: 1 :: Xf S.
Proof. intros [|a t]; reflexivity. Qed.

Lemma Xf_rep2_21 : forall n, Xf (rep2 n [2; 1]) = 5 :: rep2 n [1].
Proof.
  intros [|n]; [reflexivity|].
  cbn [rep2 Xf]. rewrite rep2_push. reflexivity.
Qed.

(** The mutual step identity: nv0 acts on decodes as stepV/stepU. *)

Lemma nv0_dec_mut :
  (forall v, nv0 (decV v) = decV (stepV v)) /\
  (forall u, Xf (nv0 (decU u)) = decU (stepU u)).
Proof.
  apply Vd_Ud_mut; intros; cbn [decV decU stepV stepU rep2].
  - reflexivity.                                   (* VA0 *)
  - reflexivity.                                   (* VA1 *)
  - reflexivity.                                   (* VD0 *)
  - rewrite nv0_8c, nv0_2run, nv0_1.               (* VD1 *)
    rewrite two_rep2. reflexivity.
  - rewrite nv0_1c. reflexivity.                   (* VP0 *)
  - rewrite nv0_4c. reflexivity.                   (* VP1 *)
  - rewrite nv0_1c. reflexivity.                   (* VP2 *)
  - rewrite nv0_5f, H. reflexivity.                (* VP3 *)
  - reflexivity.                                   (* UA2 *)
  - reflexivity.                                   (* UA3 *)
  - rewrite nv0_2run, nv0_1. apply Xf_rep2_21.     (* UC0 *)
  - destruct n as [|n].                            (* UC1 *)
    + reflexivity.
    + cbn [rep2]. rewrite nv0_5f. cbn [Xf]. reflexivity.
  - replace (m + 2) with (S (m + 1)) by lia. cbn [rep2].   (* UD0 *)
    rewrite nv0_1c. cbn [Xf]. reflexivity.
  - rewrite nv0_8c, nv0_2run, nv0_1. cbn [Xf].             (* UD1 *)
    rewrite two_rep2. replace (m + 1 + 2) with (m + 3) by lia. reflexivity.
  - rewrite nv0_4c, nv0_2run, H. cbn [Xf].         (* UDD *)
    replace (a + 1) with (S a) by lia. cbn [rep2]. reflexivity.
Qed.

Definition nv0_decV := proj1 nv0_dec_mut.
Definition Xnv0_decU := proj2 nv0_dec_mut.

(** ** Every decode is alive (has an odd entry) and has no zero entry. *)

Lemma Forall_rep1 : forall j X, Forall (fun x => x <> 0) X ->
  Forall (fun x => x <> 0) (rep1 j X).
Proof.
  induction j as [|j IH]; intros X H; cbn [rep1];
    [assumption | constructor; [discriminate | apply IH, H]].
Qed.

Lemma Forall_rep2 : forall n X, Forall (fun x => x <> 0) X ->
  Forall (fun x => x <> 0) (rep2 n X).
Proof.
  induction n as [|n IH]; intros X H; cbn [rep2];
    [assumption | constructor; [discriminate | apply IH, H]].
Qed.

Lemma nv0_nonzero : forall w, Forall (fun x => x <> 0) w ->
  Forall (fun x => x <> 0) (nv0 w).
Proof.
  induction w as [|n t IH]; intro H; cbn [nv0]; [constructor|].
  inversion H as [|? ? Hn Ht]; subst.
  destruct (Nat.even n).
  - apply Forall_rep1. constructor; [discriminate | apply IH, Ht].
  - destruct t as [|n2 t2].
    + apply Forall_rep1. repeat constructor; discriminate.
    + apply Forall_rep1. inversion Ht; subst. constructor; [lia | assumption].
Qed.

Lemma hasodd_rep2 : forall n X, existsb Nat.odd (rep2 n X) = existsb Nat.odd X.
Proof.
  induction n as [|n IH]; intro X; cbn [rep2 existsb]; [reflexivity|].
  cbn [Nat.odd Nat.even]. apply IH.
Qed.

Lemma hasodd_rep2_1 : forall n, existsb Nat.odd (rep2 n [1]) = true.
Proof. intro n. rewrite hasodd_rep2. reflexivity. Qed.

Lemma alive_dec_mut :
  (forall v, existsb Nat.odd (decV v) = true /\ Forall (fun x => x <> 0) (decV v)) /\
  (forall u, existsb Nat.odd (decU u) = true /\ Forall (fun x => x <> 0) (decU u)).
Proof.
  apply Vd_Ud_mut; intros; cbn [decV decU];
    try (split; [reflexivity | repeat constructor; discriminate]).
  - (* VD0 *) split; [reflexivity|].
    repeat constructor; [discriminate|discriminate|].
    apply Forall_rep2. repeat constructor; discriminate.
  - (* VD1 *) split; [cbn [existsb Nat.odd orb]; apply hasodd_rep2_1|].
    constructor; [discriminate|]. apply Forall_rep2. repeat constructor; discriminate.
  - (* VP0 *) destruct H as [_ H2]. split; [reflexivity|].
    repeat constructor; [discriminate|discriminate|exact H2].
  - (* VP1 *) destruct H as [H1 H2]. split.
    + cbn [existsb Nat.odd]. exact H1.
    + constructor; [discriminate|exact H2].
  - (* VP2 *) destruct H as [_ H2]. split; [reflexivity|].
    repeat constructor; [discriminate|discriminate|]. apply nv0_nonzero, H2.
  - (* VP3 *) destruct H as [_ H2]. split; [reflexivity|].
    constructor; [discriminate|]. apply nv0_nonzero, H2.
  - (* UC0 *) split; [apply hasodd_rep2_1|].
    apply Forall_rep2. repeat constructor; discriminate.
  - (* UC1 *) split; [reflexivity|].
    constructor; [discriminate|]. apply Forall_rep2. repeat constructor; discriminate.
  - (* UD0 *) split; [reflexivity|].
    constructor; [discriminate|]. apply Forall_rep2. repeat constructor; discriminate.
  - (* UD1 *) split; [cbn [existsb Nat.odd orb]; apply hasodd_rep2_1|].
    constructor; [discriminate|]. apply Forall_rep2. repeat constructor; discriminate.
  - (* UDD *) destruct H as [H1 H2]. split.
    + cbn [existsb Nat.odd]. rewrite hasodd_rep2. exact H1.
    + constructor; [discriminate|]. apply Forall_rep2, H2.
Qed.

Definition alive_V (v : Vd) := proj1 alive_dec_mut v.

(** ** The glue: package the descriptor into WaveCounter.wglue_neverqh. *)

Lemma blks_snoc : forall r Z, blks r (Z ++ [S0]) = blks r Z ++ [S0].
Proof.
  induction r as [|r IH]; intro Z; cbn [blks]; [reflexivity | rewrite IH; reflexivity].
Qed.

Lemma leadA_snoc : forall W, leadA (W ++ [S0]) = leadA W ++ [S0].
Proof. reflexivity. Qed.

Lemma wev_Forall_tail : forall (P : nat -> Prop) K X, Forall P (wev K X) -> Forall P X.
Proof.
  induction K as [|k K IH]; intros X H; cbn [wev] in H;
    [exact H | inversion H; subst; apply IH; assumption].
Qed.

Definition Cf20 (a : nat * Vd) : cconf := CfA (fst a, wruns (decV (snd a))).
Definition next20 (a : nat * Vd) : nat * Vd := (S (fst a), stepV (snd a)).
Definition a020 : nat * Vd := (0, VA0).

Lemma Hboot20 : exists t0, stepn tm_20 t0 InitES = Some (lift (Cf20 a020)).
Proof. exact boot20_W. Qed.

Lemma Hlap20 : forall a, (fun _ : nat * Vd => True) a ->
  exists n c', csteps tm_20 n (Cf20 a) = Some c'
    /\ lift c' = lift (Cf20 (next20 a)) /\ 0 < n.
Proof.
  intros [r d] _. unfold Cf20, next20; cbn [fst snd].
  destruct (proj1 alive_dec_mut d) as [Hod Hnz].
  destruct (decompose (decV d) Hnz Hod) as (K & k & rest & Hw & HK).
  assert (Hrest : Forall (fun x => x <> 0) rest).
  { pose proof Hnz as Hnz'. rewrite Hw in Hnz'.
    apply wev_Forall_tail in Hnz'. inversion Hnz'; subst; assumption. }
  destruct rest as [|n2 t2].
  - (* rest = [] : the turn ends on the tape *)
    exists (10 + ((10 + 5 * r) + ((rcostK K + (2 * k + 5))
              + (pcost (Dmidz K k) + rcost (lay r E))))),
           (CfA (S r, enc (Dmidz K k) [S1])).
    split; [| split].
    + rewrite Hw, csteps_add, (lapA (r, wruns (wev K [2 * k + 1]))).
      apply (lapB_full_end r K k HK).
    + rewrite <- (nv0_decV d), Hw, <- (enc_end K HK k).
      unfold CfA; cbn [fst snd].
      rewrite blks_snoc, leadA_snoc. symmetry. apply lift_app_blank.
    + lia.
  - (* rest = S n2 :: t2 : the general turn *)
    inversion Hrest as [|? ? Hn2 Ht2]; subst.
    destruct n2 as [|n2]; [congruence|].
    exists (10 + ((10 + 5 * r) + ((rcostK K + (2 * k + 8))
              + (pcost (Dmid K k) + rcost (lay r E))))),
           (CfA (S r, enc (Dmid K k) (wruns ((S n2 + 3) :: t2)))).
    split; [| split].
    + rewrite Hw, csteps_add, (lapA (r, wruns (wev K ((2 * k + 1) :: S n2 :: t2)))).
      apply (lapB_full_ne r K k n2 t2 HK).
    + rewrite <- (nv0_decV d), Hw, (enc_ne K HK k n2 t2). reflexivity.
    + lia.
Qed.

Lemma Hvis20 : forall a q, (fun _ : nat * Vd => True) a ->
  exists k c, csteps tm_20 k (Cf20 a) = Some c /\ fst c = q.
Proof. intros [r d] q _. unfold Cf20; cbn [fst snd]. apply vis20. Qed.

Theorem nqh_tower20 : NeverQuasiHaltsSt tm_20.
Proof.
  apply (wglue_neverqh tm_20 (nat * Vd) next20 (fun _ => True) Cf20 a020).
  - exact I.
  - intros a _. exact I.
  - exact Hboot20.
  - exact Hlap20.
  - exact Hvis20.
Qed.


(** The whole file's axiom footprint. *)
Print Assumptions nqh_tower20.
