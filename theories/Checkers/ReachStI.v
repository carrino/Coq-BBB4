(** * ReachStI: uniform reachability RELATIVISED to a state invariant.

    [ReachSt.ReachSt tm q] asks the [q]-avoiding sub-machine to terminate
    from EVERY configuration.  That is strictly stronger than liveness
    needs, and docs/REACHST_TIER.md section 8e measured exactly how it
    over-shoots on this residue: every counterexample the avoid probe
    reports is a spin-out on an ALL-BLANK tape, or -- on the [1RB---] rows
    -- a step into the machine's own undefined transition.  Neither is a
    configuration the real orbit ever reaches.  The tier's stated next move
    is "a [ReachSt] relativised to an invariant the real orbit satisfies";
    this file is that move, with the invariant kept as small as it can be:

      [I cc]  :=  the STATE of [cc] lies in [allowed].

    On a [1RB---] row [StA] is the start state, fires once at index 0 and is
    the target of no transition, so [allowed = [StB;StC;StD]] holds from
    index 1 onward and the undefined [StA] branch is simply out of scope --
    without which [ReachSt tm StB] is not merely unprovable but FALSE, since
    [(StA, ([], S1, []))] halts before reaching anything.  Where the machine
    is already total the invariant drops nothing and this is [ReachSt]; the
    blank spin-outs that survive are what docs/WAVE34_REACHSTI.md section 4
    reports as still open.

    ** The certificate

    Termination of the goal-avoiding run is witnessed by a measure that is
    linear in the two half-tape [S1] counts, offset by a rank that may read
    ONE cell of context on each side:

      [mu (q,(l,h,r))  =  B * ones l  +  C * ones r  +  rk (q, chd l, h, chd r)]

    [mu] is a [nat], so a strict drop on every goal-avoiding step bounds the
    run outright ([mu_reaches] is a strong induction on it).  The drop is a
    finite check ([drop_ok]): [CTape.ctape_move] moves exactly one cell
    across the head, so

      [DR]:  [ones (w::l) = sval w + ones l]   [ones (ctl r) + sval (chd r) = ones r]
      [DL]:  [ones (w::r) = sval w + ones r]   [ones (ctl l) + sval (chd l) = ones l]

    and every quantity the drop compares is known except the cell freshly
    exposed BEHIND the one being crossed ([chd (ctl r)] resp. [chd (ctl l)]).
    The check quantifies over both its values, so no case is assumed away.

    Nothing about the search that produces [(B, C, rk)] is trusted --
    [tools/reachsti/cert_search.py] is a Bellman-Ford over the difference
    constraints, and a wrong constant makes [drop_ok] evaluate to [false]
    rather than proving anything.

    ** What it delivers

    [reach_sti_recurs] returns [NonHalt] TOGETHER with the liveness of the
    goal state.  Both matter: the never-QH boards consume the liveness, and
    the [1RB---] boards need the [NonHalt] as well -- their [iqh] triple
    cannot get it from anywhere else, since those machines have a genuine
    undefined transition and [ReachSt]'s [Total] premise is unavailable.

    Axiom footprint: [functional_extensionality_dep] (via [CTape.lift]). *)

From Coq Require Import Arith Lia Bool List.
From BBB4 Require Import BBB4_Statement CTape.
Import ListNotations.

(** ** The invariant and its two obligations *)

Definition InAllowed (allowed : list St) (cc : cconf) : Prop :=
  In (fst cc) allowed.

(** [allowed] is TOTAL (no undefined transition escapes it) and CLOSED
    (no step leaves it).  One boolean settles both. *)
Definition all_Sym : list Sym := [S0; S1].

Lemma all_Sym_complete : forall s, In s all_Sym.
Proof. destruct s; simpl; auto. Qed.

Definition st_inb (q : St) (l : list St) : bool :=
  existsb (st_eqb q) l.

Lemma st_inb_In : forall q l, st_inb q l = true -> In q l.
Proof.
  intros q l H. unfold st_inb in H.
  apply existsb_exists in H as (x & Hx & Hq).
  apply st_eqb_spec in Hq. subst. exact Hx.
Qed.

Definition inv_ok (tm : TM) (allowed : list St) : bool :=
  forallb (fun q => forallb (fun h =>
    match tm q h with
    | None => false
    | Some tr => st_inb (t_next tr) allowed
    end) all_Sym) allowed.

Lemma inv_ok_defined : forall tm allowed q h,
  inv_ok tm allowed = true -> In q allowed ->
  exists tr, tm q h = Some tr /\ In (t_next tr) allowed.
Proof.
  intros tm allowed q h H Hq.
  unfold inv_ok in H. rewrite forallb_forall in H.
  specialize (H q Hq). rewrite forallb_forall in H.
  specialize (H h (all_Sym_complete h)).
  destruct (tm q h) as [tr|]; [| discriminate].
  exists tr. split; [reflexivity | apply st_inb_In; exact H].
Qed.

Lemma inv_cstep : forall tm allowed cc,
  inv_ok tm allowed = true -> InAllowed allowed cc ->
  exists cc', cstep tm cc = Some cc' /\ InAllowed allowed cc'.
Proof.
  intros tm allowed [q [[l h] r]] H Hq. unfold InAllowed in *. simpl in Hq.
  destruct (inv_ok_defined tm allowed q h H Hq) as (tr & Etr & Hnext).
  unfold cstep. rewrite Etr. eexists. split; [reflexivity | exact Hnext].
Qed.

(** ** The measure *)

Definition sval (s : Sym) : nat := match s with S0 => 0 | S1 => 1 end.

Fixpoint ones (l : list Sym) : nat :=
  match l with [] => 0 | s :: t => sval s + ones t end.

Lemma ones_chd_ctl : forall l, ones l = sval (chd l) + ones (ctl l).
Proof. destruct l; reflexivity. Qed.

(** The rank's context: the state, the head cell, and one cell each side. *)
Definition mnode : Type := (St * Sym * Sym * Sym)%type.

Definition node_of (cc : cconf) : mnode :=
  let '(q, (l, h, r)) := cc in (q, chd l, h, chd r).

Definition mu (B C : nat) (rk : mnode -> nat) (cc : cconf) : nat :=
  let '(_, (l, _, r)) := cc in
  B * ones l + C * ones r + rk (node_of cc).

(** ** The drop check

    For every allowed non-goal state, every head symbol, and every value of
    the two context cells AND of the cell freshly exposed by the move, the
    measure must strictly drop -- unless the step lands on [qgoal], which is
    where the run is trying to get. *)

Definition drop_ok (tm : TM) (allowed : list St) (qgoal : St)
    (B C : nat) (rk : mnode -> nat) : bool :=
  forallb (fun q =>
    st_eqb q qgoal ||
    forallb (fun a => forallb (fun h => forallb (fun b => forallb (fun x =>
      match tm q h with
      | None => false
      | Some tr =>
          st_eqb (t_next tr) qgoal ||
          (match t_dir tr with
           | DR => Nat.ltb (B * sval (t_write tr)
                            + rk (t_next tr, t_write tr, b, x))
                           (C * sval b + rk (q, a, h, b))
           | DL => Nat.ltb (C * sval (t_write tr)
                            + rk (t_next tr, x, a, t_write tr))
                           (B * sval a + rk (q, a, h, b))
           end)
      end) all_Sym) all_Sym) all_Sym) all_Sym) allowed.

(** One goal-avoiding step strictly drops [mu]. *)
Lemma drop_ok_step : forall tm allowed qgoal B C rk cc cc',
  drop_ok tm allowed qgoal B C rk = true ->
  InAllowed allowed cc -> fst cc <> qgoal ->
  cstep tm cc = Some cc' -> fst cc' <> qgoal ->
  mu B C rk cc' < mu B C rk cc.
Proof.
  intros tm allowed qgoal B C rk [q [[l h] r]] cc' H Hin Hq Hstep Hq'.
  unfold InAllowed in Hin; simpl in Hin, Hq.
  unfold drop_ok in H. rewrite forallb_forall in H.
  specialize (H q Hin).
  apply orb_true_iff in H as [Hg | H].
  { apply st_eqb_spec in Hg. contradiction. }
  rewrite forallb_forall in H. specialize (H (chd l) (all_Sym_complete _)).
  rewrite forallb_forall in H. specialize (H h (all_Sym_complete _)).
  rewrite forallb_forall in H. specialize (H (chd r) (all_Sym_complete _)).
  rewrite forallb_forall in H.
  unfold cstep in Hstep.
  destruct (tm q h) as [tr|] eqn:Etr; [| discriminate].
  injection Hstep as <-.
  destruct (t_dir tr) eqn:Ed.
  - (* DL: (l,h,r) -> (ctl l, chd l, w :: r) *)
    specialize (H (chd (ctl l)) (all_Sym_complete _)).
    apply orb_true_iff in H as [Hg | H].
    { apply st_eqb_spec in Hg. simpl in Hq'. contradiction. }
    apply Nat.ltb_lt in H.
    unfold mu, node_of. simpl.
    rewrite (ones_chd_ctl l). lia.
  - (* DR: (l,h,r) -> (w :: l, chd r, ctl r) *)
    specialize (H (chd (ctl r)) (all_Sym_complete _)).
    apply orb_true_iff in H as [Hg | H].
    { apply st_eqb_spec in Hg. simpl in Hq'. contradiction. }
    apply Nat.ltb_lt in H.
    unfold mu, node_of. simpl.
    rewrite (ones_chd_ctl r). lia.
Qed.

(** ** From the drop to reachability *)

(** The goal-avoiding run cannot outlast [mu]. *)
Lemma mu_reaches : forall tm allowed qgoal B C rk,
  inv_ok tm allowed = true ->
  drop_ok tm allowed qgoal B C rk = true ->
  forall n cc, mu B C rk cc < n -> InAllowed allowed cc ->
  exists k cc', csteps tm k cc = Some cc' /\ fst cc' = qgoal.
Proof.
  intros tm allowed qgoal B C rk Hinv Hdrop n.
  induction n as [|n IH]; intros cc Hlt Hin; [lia|].
  destruct (st_eqb (fst cc) qgoal) eqn:Eq.
  - apply st_eqb_spec in Eq. exists 0, cc. split; [reflexivity | exact Eq].
  - assert (Hne : fst cc <> qgoal)
      by (intro Hc; rewrite <- st_eqb_spec in Hc; congruence).
    destruct (inv_cstep tm allowed cc Hinv Hin) as (cc1 & Hs1 & Hin1).
    destruct (st_eqb (fst cc1) qgoal) eqn:Eq1.
    + apply st_eqb_spec in Eq1. exists 1, cc1.
      split; [cbn [csteps]; rewrite Hs1; reflexivity | exact Eq1].
    + assert (Hne1 : fst cc1 <> qgoal)
        by (intro Hc; rewrite <- st_eqb_spec in Hc; congruence).
      assert (Hd : mu B C rk cc1 < mu B C rk cc)
        by (apply (drop_ok_step tm allowed qgoal B C rk cc cc1);
            assumption).
      destruct (IH cc1 ltac:(lia) Hin1) as (k & cc' & Hk & Hq).
      exists (S k), cc'. split; [cbn [csteps]; rewrite Hs1; exact Hk | exact Hq].
Qed.

(** [ReachSt] on the invariant: from every allowed configuration the
    machine reaches [qgoal]. *)
Theorem reach_sti : forall tm allowed qgoal B C rk cc,
  inv_ok tm allowed = true ->
  drop_ok tm allowed qgoal B C rk = true ->
  InAllowed allowed cc ->
  exists k c', stepn tm k (lift cc) = Some c' /\ fst c' = qgoal.
Proof.
  intros tm allowed qgoal B C rk cc Hinv Hdrop Hin.
  destruct (mu_reaches tm allowed qgoal B C rk Hinv Hdrop
              (S (mu B C rk cc)) cc (Nat.lt_succ_diag_r _) Hin)
    as (k & cc' & Hk & Hq).
  exists k, (lift cc'). split; [apply csteps_lift; exact Hk|].
  rewrite lift_state. exact Hq.
Qed.

(** ** Non-halting and liveness, from a covered prefix

    The invariant is not asked to hold at [c0] -- on a [1RB---] row it
    cannot, since [StA] is not allowed.  It is asked to hold at the end of
    an explicit prefix, which is a [vm_compute] fact. *)

Lemma inv_csteps : forall tm allowed,
  inv_ok tm allowed = true ->
  forall n cc, InAllowed allowed cc ->
  exists cc', csteps tm n cc = Some cc' /\ InAllowed allowed cc'.
Proof.
  intros tm allowed Hinv n.
  induction n as [|n IH]; intros cc Hin.
  - exists cc. split; [reflexivity | exact Hin].
  - destruct (inv_cstep tm allowed cc Hinv Hin) as (cc1 & Hs1 & Hin1).
    destruct (IH cc1 Hin1) as (cc' & Hk & Hin').
    exists cc'. split; [cbn [csteps]; rewrite Hs1; exact Hk | exact Hin'].
Qed.

Theorem reach_sti_recurs : forall tm allowed qgoal B C rk t ct,
  csteps tm t c0 = Some ct ->
  InAllowed allowed ct ->
  inv_ok tm allowed = true ->
  drop_ok tm allowed qgoal B C rk = true ->
  NonHalt tm /\ forall N, exists n, N <= n /\ VisitsAt tm qgoal n.
Proof.
  intros tm allowed qgoal B C rk t ct Hct Hin Hinv Hdrop.
  assert (Hlift : stepn tm t InitES = Some (lift ct))
    by (rewrite <- lift_c0; apply csteps_lift; exact Hct).
  assert (Hrun : forall m, exists cm,
            stepn tm (t + m) InitES = Some (lift cm) /\ InAllowed allowed cm).
  { intro m. destruct (inv_csteps tm allowed Hinv m ct Hin) as (cm & Hm & Hinm).
    exists cm. split; [| exact Hinm].
    rewrite stepn_add, Hlift. apply csteps_lift. exact Hm. }
  split.
  - intros m Hnone.
    destruct (Hrun m) as (cm & Hm & _).
    replace (t + m) with (m + t) in Hm by lia.
    rewrite stepn_add, Hnone in Hm. discriminate.
  - intro N.
    destruct (Hrun N) as (cN & HN & HinN).
    destruct (reach_sti tm allowed qgoal B C rk cN Hinv Hdrop HinN)
      as (k & c' & Hk & Hq).
    exists (t + N + k). split; [lia|].
    exists c'. split; [| exact Hq].
    rewrite stepn_add, HN. exact Hk.
Qed.

(** ** The emitter's entry point

    Three [vm_compute] facts and no existential: [start_ok] runs the explicit
    prefix and checks that it lands inside [allowed], [inv_ok] checks the
    invariant, [drop_ok] checks the measure. *)

Definition start_ok (tm : TM) (allowed : list St) (t : nat) : bool :=
  match csteps tm t c0 with
  | Some ct => st_inb (fst ct) allowed
  | None => false
  end.

Theorem reach_sti_recurs_b : forall tm allowed qgoal B C rk t,
  start_ok tm allowed t = true ->
  inv_ok tm allowed = true ->
  drop_ok tm allowed qgoal B C rk = true ->
  NonHalt tm /\ forall N, exists n, N <= n /\ VisitsAt tm qgoal n.
Proof.
  intros tm allowed qgoal B C rk t Hs Hinv Hdrop.
  unfold start_ok in Hs.
  destruct (csteps tm t c0) as [ct|] eqn:Ect; [| discriminate].
  exact (reach_sti_recurs tm allowed qgoal B C rk t ct Ect
           (st_inb_In _ _ Hs) Hinv Hdrop).
Qed.
