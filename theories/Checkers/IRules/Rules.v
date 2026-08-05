(** * IRules.Rules: inductive rules -- validation and bulk application.

    A v1 rule (BBB docs/irules.md "Rules") is a configuration shape
    [S(u_1, ..., u_m) ->* S(u_1 + d_1, ..., u_m + d_m)] over
    per-run counts: each run carries either a constant count or a
    fresh variable with a step [d_i] and a lower bound [lb_i].

    - **Validation** ([rule_check]) replays one iteration from the
      fresh-variable generalization with the engine, under the
      bounds [lb_i]; it must land exactly on the shifted shape.
      Because the replay is symbolic in the [u_i], soundness
      ([rule_check_sound]) instantiates any count vector above the
      bounds: that is [rule_sem].

    - **Application** ([rule_apply]) fires a matching rule
      [R = e_dec - lb_dec + 1] times in one op (docs/irules.md
      engine op 3): counts become [e_i + d_i * R], the drained run
      [lb_dec - 1] (dropped when 0, sides re-merged and trimmed).
      Soundness ([rule_apply_sound]) is the induction on [R]:
      iteration [r] starts with the decrementing count
      [e_dec - r >= lb_dec] for [r < R].

    The certificate's decrement choice is *untrusted*: the applier
    re-checks, at every decrementing run, that the claimed
    application count matches ([eeqb Rex (eaddc e (1 - lb))]), so no
    uniqueness argument is ever needed. *)

From Coq Require Import Arith ZArith Lia Bool List Setoid.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Checkers.IRules Require Import Expr RLE Engine.
Import ListNotations.
Open Scope Z_scope.

(** ** Rules *)

Inductive RCnt : Set :=
  | RC (val : Z)             (* constant count *)
  | RV (del : Z) (lb : Z).   (* fresh variable: step per application,
                                proven lower bound *)

Definition RRun : Set := (Sym * RCnt)%type.

Record Rule : Set := mkRule {
  r_st : St;
  r_hs : Sym;
  r_L : list RRun;
  r_R : list RRun
}.

(** The fresh-variable generalization: variable runs become [evar]s
    numbered in scan order from [vid]. *)
Fixpoint rstart (vid : nat) (rr : list RRun) : list SRun :=
  match rr with
  | [] => []
  | (s, RC v) :: t => (s, econst v) :: rstart vid t
  | (s, RV _ _) :: t => (s, evar vid) :: rstart (S vid) t
  end.

(** ... and the shifted end shape [u_i + d_i]. *)
Fixpoint rend (vid : nat) (rr : list RRun) : list SRun :=
  match rr with
  | [] => []
  | (s, RC v) :: t => (s, econst v) :: rend vid t
  | (s, RV d _) :: t => (s, eaddc (evar vid) d) :: rend (S vid) t
  end.

(** Lower bounds of the variable runs, in scan order. *)
Fixpoint rlbs (rr : list RRun) : list Z :=
  match rr with
  | [] => []
  | (_, RC _) :: t => rlbs t
  | (_, RV _ lb) :: t => lb :: rlbs t
  end.

Definition rule_lbs (r : Rule) : list Z := rlbs (r_L r) ++ rlbs (r_R r).

Definition rule_start_cfg (r : Rule) : SCfg :=
  mkSCfg (r_st r) (r_hs r)
         (rstart 0 (r_L r))
         (rstart (length (rlbs (r_L r))) (r_R r)).

Definition rule_end_cfg (r : Rule) : SCfg :=
  mkSCfg (r_st r) (r_hs r)
         (rend 0 (r_L r))
         (rend (length (rlbs (r_L r))) (r_R r)).

(** The semantic content of a validated rule: for every count vector
    above the bounds, one application is a real, [F]-exact run. *)
Definition rule_sem (tm : TM) (r : Rule) (F : list Tr) : Prop :=
  forall u : nat -> Z, bge (rule_lbs r) u ->
  exists n, (1 <= n)%nat /\
    Reach tm F n (asem u (rule_start_cfg r)) (asem u (rule_end_cfg r)).

(** ** Configuration equality (decidable, denotation-sound) *)

Fixpoint sruns_eqb (a b : list SRun) : bool :=
  match a, b with
  | [], [] => true
  | (s, e) :: ta, (s', e') :: tb =>
      sym_eqb s s' && eeqb e e' && sruns_eqb ta tb
  | _, _ => false
  end.

Lemma sruns_eqb_den : forall a b nu,
  sruns_eqb a b = true -> dside nu a = dside nu b.
Proof.
  induction a as [|[s e] ta IH]; intros b nu H;
    destruct b as [|[s' e'] tb]; simpl in H; try discriminate.
  - reflexivity.
  - apply andb_prop in H as [H Ht].
    apply andb_prop in H as [Hs He].
    apply sym_eqb_spec in Hs; subst s'.
    rewrite !dside_cons, (cnt_eeqb e e' nu He), (IH tb nu Ht).
    reflexivity.
Qed.

Definition scfg_eqb (a b : SCfg) : bool :=
  st_eqb (s_st a) (s_st b) && sym_eqb (s_hs a) (s_hs b) &&
  sruns_eqb (s_L a) (s_L b) && sruns_eqb (s_R a) (s_R b).

Lemma scfg_eqb_asem : forall a b nu,
  scfg_eqb a b = true -> asem nu a = asem nu b.
Proof.
  intros a b nu H.
  apply andb_prop in H as [H HR].
  apply andb_prop in H as [H HL].
  apply andb_prop in H as [Hst Hhs].
  apply st_eqb_spec in Hst. apply sym_eqb_spec in Hhs.
  unfold asem, dcfg.
  rewrite Hst, Hhs, (sruns_eqb_den _ _ nu HL), (sruns_eqb_den _ _ nu HR).
  reflexivity.
Qed.

(** ** The replay loop

    Shared by rule validation ([rules] = nil) and the meta-cycle
    replay: at each iteration, accept if the end test holds and a
    concrete engine step has happened ([stepped], mirroring the C
    verifier's [ops > 0]); otherwise apply the first matching rule,
    else one engine op. *)

(** Locate a decrementing run and compute the application count
    [R = e - lb + 1].  Untrusted: [app_side] re-validates. *)
Fixpoint find_dec (rr : list RRun) (mr : list SRun) : option Expr :=
  match rr, mr with
  | (_, RV d lb) :: rt, (_, e) :: mt =>
      if d =? -1 then Some (eaddc e (1 - lb)) else find_dec rt mt
  | _ :: rt, _ :: mt => find_dec rt mt
  | _, _ => None
  end.

(** Match one side of a rule against the configuration and produce
    the post-application runs.  All soundness-relevant conditions
    are checked here:
    - constant runs carry exactly their constant;
    - variable runs provably meet their lower bound;
    - a decrementing run ([d = -1]) is consistent with the claimed
      application count and drains to [lb - 1] (dropped when 0);
    - every other variable run has [d >= 0] and steps to
      [e + d * R]. *)
Fixpoint app_side (lo : list Z) (Rex : Expr) (rr : list RRun)
    (mr : list SRun) : option (list SRun) :=
  match rr, mr with
  | [], [] => Some []
  | (s, RC v) :: rt, (s', e) :: mt =>
      if sym_eqb s s' && eeqb e (econst v)
      then option_map (cons (s', e)) (app_side lo Rex rt mt)
      else None
  | (s, RV d lb) :: rt, (s', e) :: mt =>
      if sym_eqb s s' && expr_ge lo e lb then
        if d =? -1 then
          if eeqb Rex (eaddc e (1 - lb)) then
            if lb =? 1 then app_side lo Rex rt mt
            else option_map (cons (s', econst (lb - 1)))
                            (app_side lo Rex rt mt)
          else None
        else if 0 <=? d then
          option_map (cons (s', eaddmul e d Rex)) (app_side lo Rex rt mt)
        else None
      else None
  | _, _ => None
  end.

(** One rule application at the current configuration. *)
Definition rule_apply (lo : list Z) (r : Rule) (c : SCfg)
  : option SCfg :=
  if st_eqb (s_st c) (r_st r) && sym_eqb (s_hs c) (r_hs r) then
    match match find_dec (r_L r) (s_L c) with
          | Some x => Some x
          | None => find_dec (r_R r) (s_R c)
          end with
    | None => None
    | Some Rex =>
        if expr_ge lo Rex 1 then
          match app_side lo Rex (r_L r) (s_L c),
                app_side lo Rex (r_R r) (s_R c) with
          | Some outL, Some outR =>
              match merge_adj lo outL, merge_adj lo outR with
              | Some mL, Some mR =>
                  Some (mkSCfg (s_st c) (s_hs c)
                               (trim_blanks mL) (trim_blanks mR))
              | _, _ => None
              end
          | _, _ => None
          end
        else None
    end
  else None.

(** First matching rule; returns its fired set. *)
Fixpoint try_rules (lo : list Z) (rules : list (Rule * list Tr))
    (c : SCfg) : option (SCfg * list Tr) :=
  match rules with
  | [] => None
  | (r, F) :: rest =>
      match rule_apply lo r c with
      | Some c' => Some (c', F)
      | None => try_rules lo rest c
      end
  end.

(** deduplicating fired-set union: [Tr] has at most 8 values, so the
    accumulated fired set stays tiny instead of growing one entry per
    replay step (measured: ~300k-entry lists, the replay's dominant
    allocation).  [Reach] only depends on [F] up to membership
    ([Reach_set]), so the swap is semantics-preserving. *)
Definition tr_eqb (a b : Tr) : bool :=
  st_eqb (fst a) (fst b) && sym_eqb (snd a) (snd b).

Lemma tr_eqb_spec : forall a b, tr_eqb a b = true <-> a = b.
Proof.
  intros [qa sa] [qb sb]; unfold tr_eqb; simpl.
  split.
  - intro H; apply andb_prop in H as [H1 H2].
    apply st_eqb_spec in H1; apply sym_eqb_spec in H2; congruence.
  - intro H; injection H as <- <-.
    apply andb_true_intro; split;
      [apply st_eqb_spec | apply sym_eqb_spec]; reflexivity.
Qed.

Definition tr_mem (t : Tr) (F : list Tr) : bool :=
  existsb (tr_eqb t) F.

Definition tr_union (F F' : list Tr) : list Tr :=
  fold_right (fun t acc => if tr_mem t acc then acc else t :: acc) F' F.

Lemma tr_mem_in : forall t F, tr_mem t F = true <-> In t F.
Proof.
  intros t F; unfold tr_mem; rewrite existsb_exists.
  split.
  - intros (x & Hx & He). apply tr_eqb_spec in He. subst; assumption.
  - intro H. exists t. split; [assumption | apply tr_eqb_spec; reflexivity].
Qed.

Lemma tr_union_in : forall t F F',
  In t (tr_union F F') <-> In t F \/ In t F'.
Proof.
  intros t F F'; unfold tr_union.
  induction F as [|h F IH]; simpl; [tauto|].
  destruct (tr_mem h (fold_right
              (fun t0 acc => if tr_mem t0 acc then acc else t0 :: acc)
              F' F)) eqn:Hm.
  - apply tr_mem_in in Hm. rewrite IH.
    split; [tauto|].
    intros [[-> | HF] | HF']; rewrite <- IH in *; tauto.
  - simpl. rewrite IH. tauto.
Qed.

Fixpoint replay (tm : TM) (lo : list Z) (rules : list (Rule * list Tr))
    (endt : SCfg -> bool) (fuel : nat) (stepped : bool) (c : SCfg)
  : option (SCfg * list Tr) :=
  match fuel with
  | O => None
  | S fuel' =>
      if stepped && endt c then Some (c, [])
      else
        match try_rules lo rules c with
        | Some (c', F) =>
            match replay tm lo rules endt fuel' stepped c' with
            | Some (cend, F') => Some (cend, tr_union F F')
            | None => None
            end
        | None =>
            match eng_step tm lo c with
            | Some (c', F) =>
                match replay tm lo rules endt fuel' true c' with
                | Some (cend, F') => Some (cend, tr_union F F')
                | None => None
                end
            | None => None
            end
        end
  end.

(** ** Rule validation

    [fuel] bounds the replay length (the C verifier's IVRULEOPS);
    it is a parameter so that checker calls only ever evaluate it
    under [vm_compute] (a large literal in a definition body chokes
    the kernel's lazy conversion at [Qed] time). *)

Definition rule_check (tm : TM) (fuel : nat) (r : Rule)
  : option (list Tr) :=
  match replay tm (rule_lbs r) []
          (fun c => scfg_eqb c (rule_end_cfg r))
          fuel false (rule_start_cfg r) with
  | Some (_, F) => Some F
  | None => None
  end.

(** ** Soundness: sets, replay, validation, application *)

Lemma Reach_set : forall tm F F' n a b,
  (forall t, In t F' <-> In t F) ->
  Reach tm F' n a b -> Reach tm F n a b.
Proof.
  intros tm F F' n a b Hset (Hs & Hc & Hx).
  split; [exact Hs|]. split.
  - intros m Hm. destruct (Hc m Hm) as (cm & Hcm & Hin).
    exists cm. split; [assumption | apply Hset; assumption].
  - intros t Ht. apply Hx, Hset, Ht.
Qed.

Lemma replay_sound : forall tm lo rules endt fuel stepped c cend F,
  replay tm lo rules endt fuel stepped c = Some (cend, F) ->
  forall nu, bge lo nu ->
  (forall r Fr c1 c2, In (r, Fr) rules -> rule_apply lo r c1 = Some c2 ->
     exists n, (1 <= n)%nat /\ Reach tm Fr n (asem nu c1) (asem nu c2)) ->
  endt cend = true /\
  exists n, Reach tm F n (asem nu c) (asem nu cend) /\
            (stepped = false -> (1 <= n)%nat).
Proof.
  intros tm lo rules endt fuel.
  induction fuel as [|fuel IH]; intros stepped c cend F H nu Hb
    Happ; simpl in H; [discriminate|].
  destruct (stepped && endt c) eqn:Hend.
  - injection H as <- <-.
    apply andb_prop in Hend as [Hst Hendc].
    split; [exact Hendc|].
    exists O. split; [apply Reach_refl|].
    intro Hf; rewrite Hf in Hst; discriminate.
  - destruct (try_rules lo rules c) as [[c' Fr]|] eqn:Htry.
    + destruct (replay tm lo rules endt fuel stepped c')
        as [[cend' F']|] eqn:Hrec; [|discriminate].
      injection H as <- <-.
      destruct (IH stepped c' cend' F' Hrec nu Hb Happ)
        as (Hende & n2 & HR2 & _).
      (* the applied rule *)
      assert (Hget : exists r0, In (r0, Fr) rules /\
                     rule_apply lo r0 c = Some c').
      { clear -Htry. induction rules as [|[r0 F0] rest IHr];
          simpl in Htry; [discriminate|].
        destruct (rule_apply lo r0 c) eqn:Ha.
        - injection Htry as <- <-. exists r0. split; [left|]; auto.
        - destruct (IHr Htry) as (r1 & Hin & Ha1).
          exists r1. split; [right|]; assumption. }
      destruct Hget as (r0 & Hin & Ha).
      destruct (Happ r0 Fr c c' Hin Ha) as (n1 & Hn1 & HR1).
      split; [exact Hende|].
      exists (n1 + n2)%nat. split.
      * apply (Reach_set tm (tr_union Fr F') (Fr ++ F'));
          [intro t; rewrite tr_union_in, in_app_iff; tauto|].
        exact (Reach_compose _ _ _ _ _ _ _ _ HR1 HR2).
      * intro; lia.
    + destruct (eng_step tm lo c) as [[c' Fe]|] eqn:Hstep;
        [|discriminate].
      destruct (replay tm lo rules endt fuel true c')
        as [[cend' F']|] eqn:Hrec; [|discriminate].
      injection H as <- <-.
      destruct (IH true c' cend' F' Hrec nu Hb Happ)
        as (Hende & n2 & HR2 & _).
      destruct (eng_step_sound tm lo c c' Fe Hstep nu Hb)
        as (n1 & Hn1 & HR1).
      split; [exact Hende|].
      exists (n1 + n2)%nat. split.
      * apply (Reach_set tm (tr_union Fe F') (Fe ++ F'));
          [intro t; rewrite tr_union_in, in_app_iff; tauto|].
        exact (Reach_compose _ _ _ _ _ _ _ _ HR1 HR2).
      * intro; lia.
Qed.

Theorem rule_check_sound : forall tm fuel r F,
  rule_check tm fuel r = Some F -> rule_sem tm r F.
Proof.
  intros tm fuel r F H u Hu.
  unfold rule_check in H.
  destruct (replay tm (rule_lbs r) []
              (fun c => scfg_eqb c (rule_end_cfg r))
              fuel false (rule_start_cfg r))
    as [[cend F']|] eqn:Hrep; [|discriminate].
  injection H as <-.
  destruct (replay_sound tm (rule_lbs r) [] _ fuel false
              (rule_start_cfg r) cend F' Hrep u Hu
              ltac:(intros ? ? ? ? Hin; destruct Hin))
    as (Hend & n & HR & Hpos).
  exists n. split; [apply Hpos; reflexivity|].
  rewrite <- (scfg_eqb_asem cend (rule_end_cfg r) u Hend).
  exact HR.
Qed.


(** ** Application soundness *)

(** Values of the variable runs at iteration [j]. *)
Fixpoint vvals (nu : nat -> Z) (j : Z) (rr : list RRun) (mr : list SRun)
  : list Z :=
  match rr, mr with
  | (_, RC _) :: rt, _ :: mt => vvals nu j rt mt
  | (_, RV d _) :: rt, (_, e) :: mt =>
      (eval nu e + d * j) :: vvals nu j rt mt
  | _, _ => []
  end.

(** The one inversion principle for [app_side] on a cons. *)
Lemma app_side_cons_inv : forall lo Rex s rc rt s' e mt out,
  app_side lo Rex ((s, rc) :: rt) ((s', e) :: mt) = Some out ->
  s = s' /\
  match rc with
  | RC v =>
      eeqb e (econst v) = true /\
      exists o, app_side lo Rex rt mt = Some o /\ out = (s', e) :: o
  | RV d lb =>
      expr_ge lo e lb = true /\
      exists o, app_side lo Rex rt mt = Some o /\
      ((d = -1 /\ eeqb Rex (eaddc e (1 - lb)) = true /\
        ((lb = 1 /\ out = o) \/
         (lb <> 1 /\ out = (s', econst (lb - 1)) :: o))) \/
       (0 <= d /\ out = (s', eaddmul e d Rex) :: o))
  end.
Proof.
  intros lo Rex s rc rt s' e mt out H.
  destruct rc as [v | d lb]; cbn [app_side] in H.
  - destruct (sym_eqb s s') eqn:Hs; cbn beta iota in H; [|discriminate].
    apply sym_eqb_spec in Hs.
    destruct (eeqb e (econst v)) eqn:He; cbn beta iota in H; [|discriminate].
    destruct (app_side lo Rex rt mt) as [o|] eqn:Ha; cbn beta iota in H;
      [|discriminate].
    injection H as <-.
    split; [auto|]. split; [auto|]. eauto.
  - destruct (sym_eqb s s') eqn:Hs; cbn beta iota in H; [|discriminate].
    apply sym_eqb_spec in Hs.
    destruct (expr_ge lo e lb) eqn:Hge; cbn beta iota in H; [|discriminate].
    destruct (d =? -1) eqn:Hd; cbn beta iota in H.
    + apply Z.eqb_eq in Hd.
      destruct (eeqb Rex (eaddc e (1 - lb))) eqn:HR; cbn beta iota in H;
        [|discriminate].
      destruct (lb =? 1) eqn:Hlb; cbn beta iota in H.
      * apply Z.eqb_eq in Hlb.
        split; [auto|]. split; [auto|].
        exists out. split; [auto|].
        left. split; [auto|]. split; [auto|].
        left. split; [auto | auto].
      * apply Z.eqb_neq in Hlb.
        destruct (app_side lo Rex rt mt) as [o|] eqn:Ha; cbn beta iota in H;
          [|discriminate].
        injection H as <-.
        split; [auto|]. split; [auto|].
        exists o. split; [auto|].
        left. split; [auto|]. split; [auto|].
        right. split; [auto | auto].
    + destruct (0 <=? d) eqn:Hd0; cbn beta iota in H; [|discriminate].
      apply Z.leb_le in Hd0.
      destruct (app_side lo Rex rt mt) as [o|] eqn:Ha; cbn beta iota in H;
        [|discriminate].
      injection H as <-.
      split; [auto|]. split; [auto|].
      exists o. split; [auto|].
      right. split; [auto | auto].
Qed.

Lemma app_side_nil_inv : forall lo Rex rr mr out,
  app_side lo Rex rr mr = Some out ->
  (rr = [] <-> mr = []).
Proof.
  intros lo Rex rr mr out H.
  destruct rr as [|[s rc] rt]; destruct mr as [|[s' e] mt];
    simpl in H; try discriminate;
    try (destruct rc; discriminate);
    split; intro; congruence.
Qed.

Lemma app_side_vlen : forall lo Rex rr mr out nu j,
  app_side lo Rex rr mr = Some out ->
  length (vvals nu j rr mr) = length (rlbs rr).
Proof.
  induction rr as [|[s rc] rt IH]; intros mr out nu j H.
  - destruct mr; [reflexivity|].
    simpl in H. discriminate.
  - destruct mr as [|[s' e] mt].
    + destruct rc; simpl in H; discriminate.
    + destruct (app_side_cons_inv _ _ _ _ _ _ _ _ _ H) as [Hs Hrest].
      destruct rc as [v | d lb]; simpl.
      * destruct Hrest as (_ & o & Ha & _). eapply IH; eauto.
      * destruct Hrest as (_ & o & Ha & _).
        simpl. f_equal. eapply IH; eauto.
Qed.

(** Helper: the value at the current variable slot. *)
Lemma nth_mid : forall (pre : list Z) x rest d,
  nth (length pre) (pre ++ x :: rest) d = x.
Proof. intros. apply nth_middle. Qed.

Lemma nth_mid2 : forall (pre : list Z) x rest ext d,
  nth (length pre) (pre ++ (x :: rest) ++ ext) d = x.
Proof. intros. exact (nth_middle pre (rest ++ ext) x d). Qed.

(** Denotation of the generalization at iteration 0 = the matched
    configuration side. *)
Lemma app_side_den0 : forall lo Rex rr mr out nu,
  app_side lo Rex rr mr = Some out ->
  forall pre ext,
  dside (fun i => nth i (pre ++ vvals nu 0 rr mr ++ ext) 1)
        (rstart (length pre) rr)
  = dside nu mr.
Proof.
  induction rr as [|[s rc] rt IH]; intros mr out nu H pre ext.
  - destruct mr; [reflexivity | simpl in H; discriminate].
  - destruct mr as [|[s' e] mt];
      [destruct rc; simpl in H; discriminate|].
    destruct (app_side_cons_inv _ _ _ _ _ _ _ _ _ H) as [Hs Hrest].
    subst s'.
    destruct rc as [v | d lb]; simpl vvals; simpl rstart;
      rewrite !dside_cons.
    + destruct Hrest as (He & o & Ha & _).
      f_equal.
      * f_equal. unfold cnt.
        rewrite eval_econst, (eeqb_eval _ _ nu He), eval_econst.
        reflexivity.
      * eapply IH; eauto.
    + destruct Hrest as (Hge & o & Ha & _).
      f_equal.
      * f_equal. unfold cnt. rewrite eval_evar.
        rewrite nth_mid2. f_equal. lia.
      * etransitivity;
          [apply dside_ext with
             (g := fun i => nth i ((pre ++ [eval nu e + d * 0])
                                     ++ vvals nu 0 rt mt ++ ext) 1)|].
        { intro i. f_equal. rewrite <- app_assoc. reflexivity. }
        replace (S (length pre))
          with (length (pre ++ [eval nu e + d * 0]))
          by (rewrite app_length; simpl; lia).
        eapply IH; eauto.
Qed.

(** Denotation shift: the end shape at iteration [j] is the start
    shape at iteration [j+1]. *)
Lemma app_side_denS : forall lo Rex rr mr out nu j,
  app_side lo Rex rr mr = Some out ->
  forall pre pre' ext ext', length pre = length pre' ->
  dside (fun i => nth i (pre ++ vvals nu j rr mr ++ ext) 1)
        (rend (length pre) rr)
  = dside (fun i => nth i (pre' ++ vvals nu (j + 1) rr mr ++ ext') 1)
          (rstart (length pre') rr).
Proof.
  induction rr as [|[s rc] rt IH]; intros mr out nu j H pre pre' ext
    ext' Hlen.
  - destruct mr; [reflexivity | simpl in H; discriminate].
  - destruct mr as [|[s' e] mt];
      [destruct rc; simpl in H; discriminate|].
    destruct (app_side_cons_inv _ _ _ _ _ _ _ _ _ H) as [Hs Hrest].
    subst s'.
    destruct rc as [v | d lb]; simpl vvals; simpl rstart; simpl rend;
      rewrite !dside_cons.
    + destruct Hrest as (_ & o & Ha & _).
      f_equal. eapply IH; eauto.
    + destruct Hrest as (_ & o & Ha & _).
      f_equal.
      * f_equal. unfold cnt.
        rewrite eval_eaddc, eval_evar, eval_evar.
        rewrite !nth_mid2.
        f_equal. lia.
      * etransitivity;
          [apply dside_ext with
             (g := fun i => nth i ((pre ++ [eval nu e + d * j])
                                     ++ vvals nu j rt mt ++ ext) 1)|].
        { intro i. f_equal. rewrite <- app_assoc. reflexivity. }
        etransitivity;
          [|apply dside_ext with
              (f := fun i => nth i ((pre' ++ [eval nu e + d * (j + 1)])
                                      ++ vvals nu (j + 1) rt mt
                                      ++ ext') 1)].
        2:{ intro i. f_equal. rewrite <- app_assoc. reflexivity. }
        replace (S (length pre))
          with (length (pre ++ [eval nu e + d * j]))
          by (rewrite app_length; simpl; lia).
        replace (S (length pre'))
          with (length (pre' ++ [eval nu e + d * (j + 1)]))
          by (rewrite app_length; simpl; lia).
        eapply IH; eauto.
        rewrite !app_length; simpl; lia.
Qed.

(** Denotation of the generalization at iteration [eval nu Rex] =
    the post-application side. *)
Lemma app_side_denR : forall lo Rex rr mr out nu,
  app_side lo Rex rr mr = Some out ->
  forall pre ext,
  dside (fun i => nth i (pre ++ vvals nu (eval nu Rex) rr mr ++ ext) 1)
        (rstart (length pre) rr)
  = dside nu out.
Proof.
  induction rr as [|[s rc] rt IH]; intros mr out nu H pre ext.
  - destruct mr; simpl in H; [injection H as <-; reflexivity
                             | discriminate].
  - destruct mr as [|[s' e] mt];
      [destruct rc; simpl in H; discriminate|].
    destruct (app_side_cons_inv _ _ _ _ _ _ _ _ _ H) as [Hs Hrest].
    subst s'.
    set (x := eval nu e + match rc with
                          | RC _ => 0 | RV d _ => d end * eval nu Rex).
    destruct rc as [v | d lb]; simpl vvals; simpl rstart;
      rewrite !dside_cons.
    + destruct Hrest as (He & o & Ha & ->).
      rewrite dside_cons.
      f_equal.
      * f_equal. unfold cnt.
        rewrite eval_econst, (eeqb_eval _ _ nu He), eval_econst.
        reflexivity.
      * eapply IH; eauto.
    + destruct Hrest as (Hge & o & Ha & Hout).
      assert (Hhead : nth (length pre)
                (pre ++ ((eval nu e + d * eval nu Rex)
                           :: vvals nu (eval nu Rex) rt mt) ++ ext) 1
              = eval nu e + d * eval nu Rex).
      { apply nth_mid2. }
      assert (Htail : dside
          (fun i => nth i (pre ++ ((eval nu e + d * eval nu Rex)
                    :: vvals nu (eval nu Rex) rt mt) ++ ext) 1)
          (rstart (S (length pre)) rt) = dside nu o).
      { etransitivity;
          [apply dside_ext with
             (g := fun i => nth i ((pre ++ [eval nu e + d * eval nu Rex])
                                     ++ vvals nu (eval nu Rex) rt mt
                                     ++ ext) 1)|].
        { intro i. f_equal. rewrite <- app_assoc. reflexivity. }
        replace (S (length pre))
          with (length (pre ++ [eval nu e + d * eval nu Rex]))
          by (rewrite app_length; simpl; lia).
        eapply IH; eauto. }
      destruct Hout as [(Hd & HRx & Hdrop) | (Hd0 & ->)].
      * subst d.
        pose proof (eeqb_eval _ _ nu HRx) as HRv.
        rewrite eval_eaddc in HRv.
        destruct Hdrop as [(Hlb & ->) | (Hlb & ->)].
        -- (* drained to 0 and dropped *)
           subst lb.
           replace (cnt (fun i => nth i (pre ++ ((eval nu e + -1 * eval nu Rex) :: vvals nu (eval nu Rex) rt mt) ++ ext) 1) (evar (length pre))) with 0%nat.
           2:{ unfold cnt. rewrite eval_evar, Hhead. lia. }
           simpl repeat. simpl app.
           exact Htail.
        -- (* drained to lb - 1 *)
           rewrite dside_cons.
           f_equal.
           ++ f_equal. unfold cnt.
              rewrite eval_evar, Hhead, eval_econst. lia.
           ++ exact Htail.
      * rewrite dside_cons.
        f_equal.
        -- f_equal. unfold cnt.
           rewrite eval_evar, Hhead, eval_eaddmul. reflexivity.
        -- exact Htail.
Qed.

(** The lower bounds hold at every iteration [0 <= j < eval nu Rex]. *)
Lemma app_side_bge : forall lo Rex rr mr out nu j,
  app_side lo Rex rr mr = Some out -> bge lo nu ->
  0 <= j -> j <= eval nu Rex - 1 ->
  forall i, nth i (rlbs rr) 0 <= nth i (vvals nu j rr mr) 1.
Proof.
  induction rr as [|[s rc] rt IH]; intros mr out nu j H Hb Hj0 Hj1 i.
  - destruct mr; simpl in H; [|discriminate].
    simpl. destruct i; simpl; lia.
  - destruct mr as [|[s' e] mt];
      [destruct rc; simpl in H; discriminate|].
    destruct (app_side_cons_inv _ _ _ _ _ _ _ _ _ H) as [Hs Hrest].
    destruct rc as [v | d lb]; simpl.
    + destruct Hrest as (_ & o & Ha & _). eapply IH; eauto.
    + destruct Hrest as (Hge & o & Ha & Hout).
      destruct i as [|i']; simpl.
      * pose proof (expr_ge_sound lo e lb nu Hge Hb) as Hlbe.
        destruct Hout as [(Hd & HRx & _) | (Hd0 & _)].
        -- subst d.
           pose proof (eeqb_eval _ _ nu HRx) as HRv.
           rewrite eval_eaddc in HRv. lia.
        -- nia.
      * destruct Hout as [(_ & _ & _) | (_ & _)]; eapply IH; eauto.
Qed.

Lemma nth_app_le : forall (l1 l2 v1 v2 : list Z),
  length l1 = length v1 ->
  (forall i, nth i l1 0 <= nth i v1 1) ->
  (forall i, nth i l2 0 <= nth i v2 1) ->
  forall i, nth i (l1 ++ l2) 0 <= nth i (v1 ++ v2) 1.
Proof.
  intros l1 l2 v1 v2 Hlen H1 H2 i.
  destruct (Nat.lt_ge_cases i (length l1)) as [Hlt | Hge].
  - rewrite app_nth1 by assumption.
    rewrite app_nth1 by lia.
    apply H1.
  - rewrite app_nth2 by assumption.
    rewrite app_nth2 by lia.
    rewrite Hlen. apply H2.
Qed.

(** The main application theorem: a matching rule applied
    [R = eval nu Rex >= 1] times in one op. *)
Theorem rule_apply_sound : forall tm lo r F c c',
  rule_apply lo r c = Some c' -> rule_sem tm r F ->
  forall nu, bge lo nu ->
  exists n, (1 <= n)%nat /\ Reach tm F n (asem nu c) (asem nu c').
Proof.
  intros tm lo r F c c' H Hsem nu Hb.
  unfold rule_apply in H.
  destruct (st_eqb (s_st c) (r_st r) && sym_eqb (s_hs c) (r_hs r))
    eqn:Hsh; [|discriminate].
  apply andb_prop in Hsh as [Hst Hhs].
  apply st_eqb_spec in Hst. apply sym_eqb_spec in Hhs.
  destruct (match find_dec (r_L r) (s_L c) with
            | Some x => Some x
            | None => find_dec (r_R r) (s_R c)
            end) as [Rex|]; [|discriminate].
  destruct (expr_ge lo Rex 1) eqn:HR1; [|discriminate].
  destruct (app_side lo Rex (r_L r) (s_L c)) as [outL|] eqn:HappL;
    [|discriminate].
  destruct (app_side lo Rex (r_R r) (s_R c)) as [outR|] eqn:HappR;
    [|discriminate].
  destruct (merge_adj lo outL) as [mL|] eqn:HmL; [|discriminate].
  destruct (merge_adj lo outR) as [mR|] eqn:HmR; [|discriminate].
  injection H as <-.
  pose proof (expr_ge_sound lo Rex 1 nu HR1 Hb) as HrZ.
  pose (VL := fun j => vvals nu j (r_L r) (s_L c)).
  pose (VR := fun j => vvals nu j (r_R r) (s_R c)).
  pose (U := fun j (i : nat) => nth i (VL j ++ VR j) 1).
  assert (HlenL : forall j, length (VL j) = length (rlbs (r_L r)))
    by (intro j; eapply app_side_vlen; eauto).
  (* the matched configuration is the generalization at iteration 0 *)
  assert (HL0 : dside (U 0) (rstart 0 (r_L r)) = dside nu (s_L c))
    by exact (app_side_den0 _ _ _ _ _ _ HappL [] (VR 0)).
  assert (HR0 : dside (U 0) (rstart (length (rlbs (r_L r))) (r_R r))
                = dside nu (s_R c)).
  { etransitivity;
      [apply dside_ext with (g := fun i => nth i (VL 0 ++ VR 0 ++ []) 1)|].
    { intro i. f_equal. rewrite app_nil_r. reflexivity. }
    rewrite <- (HlenL 0).
    exact (app_side_den0 _ _ _ _ _ _ HappR (VL 0) []). }
  assert (Claim0 : asem nu c = asem (U 0) (rule_start_cfg r)).
  { unfold asem, dcfg, rule_start_cfg.
    cbn [s_st s_hs s_L s_R].
    rewrite Hst, Hhs, HL0, HR0. reflexivity. }
  (* iteration shift *)
  assert (ClaimS : forall j,
    asem (U j) (rule_end_cfg r) = asem (U (j + 1)) (rule_start_cfg r)).
  { intro j.
    assert (EL : dside (U j) (rend 0 (r_L r))
                 = dside (U (j + 1)) (rstart 0 (r_L r)))
      by exact (app_side_denS _ _ _ _ _ _ j HappL [] [] (VR j)
                  (VR (j + 1)) eq_refl).
    assert (ER : dside (U j) (rend (length (rlbs (r_L r))) (r_R r))
                 = dside (U (j + 1))
                     (rstart (length (rlbs (r_L r))) (r_R r))).
    { etransitivity;
        [apply dside_ext with (g := fun i => nth i (VL j ++ VR j ++ []) 1)|].
      { intro i. f_equal. rewrite app_nil_r. reflexivity. }
      etransitivity;
        [|apply dside_ext with
            (f := fun i => nth i (VL (j + 1) ++ VR (j + 1) ++ []) 1)].
      2:{ intro i. f_equal. rewrite app_nil_r. reflexivity. }
      rewrite <- (HlenL j) at 1.
      rewrite <- (HlenL (j + 1)).
      apply (app_side_denS lo Rex (r_R r) (s_R c) outR nu j HappR
               (VL j) (VL (j + 1)) [] []).
      rewrite !HlenL. reflexivity. }
    unfold asem, dcfg, rule_end_cfg, rule_start_cfg.
    cbn [s_st s_hs s_L s_R].
    rewrite EL, ER. reflexivity. }
  (* final iteration = the applied configuration *)
  assert (ClaimR : asem (U (eval nu Rex)) (rule_start_cfg r)
                   = asem nu (mkSCfg (s_st c) (s_hs c) outL outR)).
  { assert (EL : dside (U (eval nu Rex)) (rstart 0 (r_L r))
                 = dside nu outL)
      by exact (app_side_denR _ _ _ _ _ _ HappL [] (VR (eval nu Rex))).
    assert (ER : dside (U (eval nu Rex))
                   (rstart (length (rlbs (r_L r))) (r_R r))
                 = dside nu outR).
    { etransitivity;
        [apply dside_ext with
           (g := fun i => nth i (VL (eval nu Rex)
                                   ++ VR (eval nu Rex) ++ []) 1)|].
      { intro i. f_equal. rewrite app_nil_r. reflexivity. }
      rewrite <- (HlenL (eval nu Rex)).
      exact (app_side_denR _ _ _ _ _ _ HappR (VL (eval nu Rex)) []). }
    unfold asem, dcfg, rule_start_cfg.
    cbn [s_st s_hs s_L s_R].
    rewrite Hst, Hhs, EL, ER. reflexivity. }
  (* bounds at every iteration *)
  assert (Hbge : forall j, 0 <= j -> j <= eval nu Rex - 1 ->
                 bge (rule_lbs r) (U j)).
  { intros j Hj0 Hj1 i.
    unfold rule_lbs.
    apply nth_app_le.
    - symmetry. apply HlenL.
    - intro i'. eapply app_side_bge; eauto.
    - intro i'. eapply app_side_bge; eauto. }
  (* the induction on the application count *)
  assert (Hiter : forall m, (1 <= m)%nat -> Z.of_nat m <= eval nu Rex ->
    exists n, (1 <= n)%nat /\
      Reach tm F n (asem (U 0) (rule_start_cfg r))
                   (asem (U (Z.of_nat m)) (rule_start_cfg r))).
  { induction m as [|m IHm]; intros Hm1 Hmr; [lia|].
    destruct m as [|m'].
    - destruct (Hsem (U 0) (Hbge 0 ltac:(lia) ltac:(lia)))
        as (n & Hn & HRch).
      exists n. split; [exact Hn|].
      setoid_rewrite (ClaimS 0) in HRch.
      exact HRch.
    - assert (Hmr' : Z.of_nat (S m') <= eval nu Rex) by lia.
      destruct (IHm ltac:(lia) Hmr') as (n1 & Hn1 & HRch1).
      destruct (Hsem (U (Z.of_nat (S m')))
                  (Hbge (Z.of_nat (S m')) ltac:(lia) ltac:(lia)))
        as (n2 & Hn2 & HRch2).
      setoid_rewrite (ClaimS (Z.of_nat (S m'))) in HRch2.
      replace (Z.of_nat (S m') + 1) with (Z.of_nat (S (S m')))
        in HRch2 by lia.
      exists (n1 + n2)%nat. split; [lia|].
      apply (Reach_set tm F (F ++ F));
        [intro t; rewrite in_app_iff; tauto|].
      exact (Reach_compose _ _ _ _ _ _ _ _ HRch1 HRch2). }
  destruct (Hiter (Z.to_nat (eval nu Rex)) ltac:(lia) ltac:(lia))
    as (n & Hn & HRch).
  exists n. split; [exact Hn|].
  replace (Z.of_nat (Z.to_nat (eval nu Rex))) with (eval nu Rex)
    in HRch by lia.
  setoid_rewrite ClaimR in HRch.
  setoid_rewrite <- Claim0 in HRch.
  (* rebuild: merge + trim preserve the denoted configuration *)
  assert (Hreb : asem nu (mkSCfg (s_st c) (s_hs c)
                            (trim_blanks mL) (trim_blanks mR))
                 = asem nu (mkSCfg (s_st c) (s_hs c) outL outR)).
  { unfold asem, dcfg.
    cbn [s_st s_hs s_L s_R].
    rewrite !lift_cc.
    rewrite !trim_blanks_den.
    rewrite (merge_adj_den lo outL mL nu HmL Hb).
    rewrite (merge_adj_den lo outR mR nu HmR Hb).
    reflexivity. }
  setoid_rewrite Hreb.
  exact HRch.
Qed.
