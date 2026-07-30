(** * Checkers.LadderKernel: rules as DATA, and the one soundness theorem.

    RULE_LADDER.md 5 states the build in four lines, and this file is the
    first two of them:

      1. a rule becomes data -- [lhs : sconf], [rhs : sconf], a count;
      2. ONE soundness theorem, by induction on the rule's position in the
         ladder, with the step case permitted to invoke rules EARLIER in the
         list.  "It is the ladder's well-foundedness that makes it a single
         theorem rather than one per rule."

    The base steps are the existing engine's, unchanged: [LapDecider.sstep]
    and its [sstep_sound] carry every raw-window, cycle, rotation and fold
    case, and this file adds exactly one new step constructor -- [RU i],
    "apply ladder rule [i]".  That is the whole new trust surface on the
    rule side: [rule_sound] below, plus the [vm_compute] that runs
    [check_ladder] on a certificate.

    [RU] applies WINDOW rules only -- both sides fully concrete -- and the
    ladder is validated with both tail flags [false], so an invoked rule
    holds for an arbitrary tail and composes wherever it syntactically
    matches.  Rules whose right-hand side carries a repeated block are still
    validated; they simply cannot be invoked by a later rule, which is a
    checkable restriction rather than an assumption.

    Axiom footprint: [functional_extensionality_dep], via [CTape.lift] in
    the reused engine.  Nothing else. *)

From Coq Require Import Arith Lia Bool List.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Counters Require Import WTape.
From BBB4.Checkers Require Import LapDecider.
Import ListNotations.

(** ** Rules as data *)

Record LRule : Set := mkLRule {
  lr_lhs : sconf;
  lr_rhs : sconf;
  lr_ca  : nat;     (** the count is affine in the carry index: [ca*j + cb] *)
  lr_cb  : nat
}.

(** What it means for a rule to be sound: from its left-hand side, at any
    carry index and against ANY opaque tails the flags permit, the machine
    reaches its right-hand side in exactly [ca*j + cb] steps. *)
Definition RuleSound (tm : TM) (el er : bool) (r : LRule) : Prop :=
  forall XL XR j,
    (el = true -> XL = []) -> (er = true -> XR = []) ->
    csteps tm (lr_ca r * j + lr_cb r) (cden XL XR j (lr_lhs r))
      = Some (cden XL XR j (lr_rhs r)).

(** ** Syntactic equality on configurations *)

Definition sside_eqb (a b : sside) : bool :=
  syms_eqb (s_pre a) (s_pre b) && syms_eqb (s_u a) (s_u b) &&
  (s_a a =? s_a b) && (s_b a =? s_b b) && syms_eqb (s_post a) (s_post b).

Lemma sside_eqb_eq : forall a b, sside_eqb a b = true -> a = b.
Proof.
  intros [p1 u1 a1 b1 q1] [p2 u2 a2 b2 q2] H; unfold sside_eqb in H; simpl in H.
  repeat (apply andb_prop in H as [H ?]).
  apply syms_eqb_eq in H.
  match goal with
  | [ H1 : syms_eqb u1 u2 = true |- _ ] => apply syms_eqb_eq in H1
  end.
  repeat match goal with
         | [ H1 : (_ =? _) = true |- _ ] => apply Nat.eqb_eq in H1
         | [ H1 : syms_eqb _ _ = true |- _ ] => apply syms_eqb_eq in H1
         end.
  subst. reflexivity.
Qed.

Definition sconf_eqb (a b : sconf) : bool :=
  st_eqb (c_st a) (c_st b) && sym_eqb (c_h a) (c_h b) &&
  sside_eqb (c_l a) (c_l b) && sside_eqb (c_r a) (c_r b).

Lemma sconf_eqb_eq : forall a b, sconf_eqb a b = true -> a = b.
Proof.
  intros [q1 l1 h1 r1] [q2 l2 h2 r2] H; unfold sconf_eqb in H; simpl in H.
  repeat (apply andb_prop in H as [H ?]).
  apply st_eqb_spec in H.
  repeat match goal with
         | [ H1 : sym_eqb _ _ = true |- _ ] => apply sym_eqb_spec in H1
         | [ H1 : sside_eqb _ _ = true |- _ ] => apply sside_eqb_eq in H1
         end.
  subst. reflexivity.
Qed.

(** ** Invoking an earlier rule

    A WINDOW rule constrains a bounded prefix of each side and nothing
    beyond it, so it applies wherever that prefix matches and leaves the
    rest of the configuration -- repeated block, fixed suffix, opaque tail
    -- untouched. *)

Definition win_side (s : sside) : bool :=
  match s_u s, s_post s with
  | [], [] => true
  | _, _ => false
  end.

Definition is_window (c : sconf) : bool := win_side (c_l c) && win_side (c_r c).

Lemma win_side_den : forall s X j,
  win_side s = true -> sden X j s = s_pre s ++ X.
Proof.
  intros [p u a b q] X j H; unfold win_side in H; simpl in *.
  destruct u; [|discriminate]. destruct q; [|discriminate].
  unfold sden; simpl. rewrite rep_nil. reflexivity.
Qed.

Definition setside (s : sside) (w : list Sym) : sside :=
  mkS w (s_u s) (s_a s) (s_b s) (s_post s).

Definition apply_win_rule (r : LRule) (c : sconf) : option (sconf * nat * nat) :=
  if is_window (lr_lhs r) && is_window (lr_rhs r) &&
     st_eqb (c_st c) (c_st (lr_lhs r)) && sym_eqb (c_h c) (c_h (lr_lhs r))
  then
    match strip (s_pre (c_l (lr_lhs r))) (s_pre (c_l c)),
          strip (s_pre (c_r (lr_lhs r))) (s_pre (c_r c)) with
    | Some restL, Some restR =>
        Some (mkC (c_st (lr_rhs r))
                  (setside (c_l c) (s_pre (c_l (lr_rhs r)) ++ restL))
                  (c_h (lr_rhs r))
                  (setside (c_r c) (s_pre (c_r (lr_rhs r)) ++ restR)),
              lr_ca r, lr_cb r)
    | _, _ => None
    end
  else None.

(** The tail an invoked rule sees: everything of the outer side that its own
    window does not name. *)
Lemma sden_split : forall s X j rest,
  s_pre s = rest ->
  sden X j s = rest ++ (rep (s_u s) (s_a s * j + s_b s) ++ s_post s ++ X).
Proof.
  intros s X j rest <-. unfold sden. rewrite !app_assoc. reflexivity.
Qed.

Lemma apply_win_rule_sound : forall tm r c c' ca cb,
  RuleSound tm false false r ->
  apply_win_rule r c = Some (c', ca, cb) ->
  forall XL XR j,
  csteps tm (ca * j + cb) (cden XL XR j c) = Some (cden XL XR j c').
Proof.
  intros tm r c c' ca cb Hr H XL XR j.
  unfold apply_win_rule in H.
  destruct (is_window (lr_lhs r) && is_window (lr_rhs r) &&
            st_eqb (c_st c) (c_st (lr_lhs r)) &&
            sym_eqb (c_h c) (c_h (lr_lhs r))) eqn:Eg; [|discriminate].
  unfold is_window in Eg.
  apply andb_prop in Eg as [Eg Ehs0].
  apply andb_prop in Eg as [Eg Est0].
  apply andb_prop in Eg as [Elhs Erhs].
  apply andb_prop in Elhs as [WlL WlR].
  apply andb_prop in Erhs as [WrL WrR].
  apply st_eqb_spec in Est0. apply sym_eqb_spec in Ehs0.
  destruct (strip (s_pre (c_l (lr_lhs r))) (s_pre (c_l c))) as [restL|] eqn:EL;
    [|discriminate].
  destruct (strip (s_pre (c_r (lr_lhs r))) (s_pre (c_r c))) as [restR|] eqn:ER;
    [|discriminate].
  injection H as <- <- <-.
  apply strip_sound in EL. apply strip_sound in ER.
  (* the tails the invoked rule sees *)
  set (YL := restL ++ rep (s_u (c_l c)) (s_a (c_l c) * j + s_b (c_l c))
                  ++ s_post (c_l c) ++ XL).
  set (YR := restR ++ rep (s_u (c_r c)) (s_a (c_r c) * j + s_b (c_r c))
                  ++ s_post (c_r c) ++ XR).
  specialize (Hr YL YR j ltac:(discriminate) ltac:(discriminate)).
  assert (Hsrc : cden YL YR j (lr_lhs r) = cden XL XR j c).
  { unfold cden. rewrite (win_side_den _ _ _ WlL), (win_side_den _ _ _ WlR).
    rewrite <- Est0, <- Ehs0. f_equal. f_equal.
    - unfold YL, sden. rewrite EL, !app_assoc. reflexivity.
    - f_equal. unfold YR, sden. rewrite ER, !app_assoc. reflexivity. }
  assert (Htgt : cden YL YR j (lr_rhs r) = cden XL XR j
                   (mkC (c_st (lr_rhs r))
                        (setside (c_l c) (s_pre (c_l (lr_rhs r)) ++ restL))
                        (c_h (lr_rhs r))
                        (setside (c_r c) (s_pre (c_r (lr_rhs r)) ++ restR)))).
  { unfold cden. rewrite (win_side_den _ _ _ WrL), (win_side_den _ _ _ WrR).
    simpl. f_equal. f_equal.
    - unfold YL, sden, setside; simpl. rewrite !app_assoc. reflexivity.
    - f_equal. unfold YR, sden, setside; simpl. rewrite !app_assoc. reflexivity. }
  rewrite <- Hsrc, <- Htgt. exact Hr.
Qed.

(** ** The step language: base steps, plus invocation of an earlier rule *)

Inductive rstep : Set :=
| RB (s : lstep)   (** a base step of the reused engine *)
| RU (i : nat).    (** apply ladder rule [i] *)

Definition rstep_exec (tm : TM) (el er : bool) (rs : list LRule)
    (s : rstep) (c : sconf) : option (sconf * nat * nat) :=
  match s with
  | RB b => sstep tm el er b c
  | RU i => match nth_error rs i with
            | Some r => apply_win_rule r c
            | None => None
            end
  end.

Lemma rstep_exec_sound : forall tm el er rs s c c' ca cb,
  Forall (RuleSound tm false false) rs ->
  rstep_exec tm el er rs s c = Some (c', ca, cb) ->
  forall XL XR j, (el = true -> XL = []) -> (er = true -> XR = []) ->
  csteps tm (ca * j + cb) (cden XL XR j c) = Some (cden XL XR j c').
Proof.
  intros tm el er rs s c c' ca cb HF H XL XR j HL HR.
  destruct s as [b|i]; simpl in H.
  - exact (sstep_sound tm el er b c c' ca cb H XL XR j HL HR).
  - destruct (nth_error rs i) as [r|] eqn:E; [|discriminate].
    apply (apply_win_rule_sound tm r c c' ca cb); [|exact H].
    rewrite Forall_forall in HF. apply HF.
    eapply nth_error_In; exact E.
Qed.

Fixpoint rrun (tm : TM) (el er : bool) (rs : list LRule) (l : list rstep)
    (c : sconf) : option (sconf * nat * nat) :=
  match l with
  | [] => Some (c, 0, 0)
  | s :: l' =>
      match rstep_exec tm el er rs s c with
      | None => None
      | Some (c1, a1, b1) =>
          match rrun tm el er rs l' c1 with
          | None => None
          | Some (c2, a2, b2) => Some (c2, a1 + a2, b1 + b2)
          end
      end
  end.

Theorem rrun_sound : forall tm el er rs l c c' ca cb,
  Forall (RuleSound tm false false) rs ->
  rrun tm el er rs l c = Some (c', ca, cb) ->
  forall XL XR j, (el = true -> XL = []) -> (er = true -> XR = []) ->
  csteps tm (ca * j + cb) (cden XL XR j c) = Some (cden XL XR j c').
Proof.
  intros tm el er rs l; induction l as [|s l IH];
    intros c c' ca cb HF H XL XR j HL HR; cbn in H.
  - injection H as <- <- <-. reflexivity.
  - destruct (rstep_exec tm el er rs s c) as [[[c1 a1] b1]|] eqn:E1;
      [|discriminate].
    destruct (rrun tm el er rs l c1) as [[[c2 a2] b2]|] eqn:E2; [|discriminate].
    injection H as <- <- <-.
    replace ((a1 + a2) * j + (b1 + b2)) with ((a1 * j + b1) + (a2 * j + b2))
      by lia.
    rewrite csteps_add,
      (rstep_exec_sound tm el er rs s c c1 a1 b1 HF E1 XL XR j HL HR).
    exact (IH c1 c2 a2 b2 HF E2 XL XR j HL HR).
Qed.

(** ** The certificate, and the one theorem

    A ladder is a list of (rule, derivation) pairs.  Rule [i]'s derivation
    may invoke rules [0 .. i-1] and no others -- that is exactly what
    passing the accumulated prefix to [rrun] enforces, and it is what makes
    the induction below well-founded. *)

Definition check_rule (tm : TM) (el er : bool) (rs : list LRule)
    (r : LRule) (l : list rstep) : bool :=
  match rrun tm el er rs l (lr_lhs r) with
  | Some (c, ca, cb) =>
      sconf_eqb c (lr_rhs r) && (ca =? lr_ca r) && (cb =? lr_cb r)
  | None => false
  end.

Lemma check_rule_sound : forall tm el er rs r l,
  Forall (RuleSound tm false false) rs ->
  check_rule tm el er rs r l = true ->
  RuleSound tm el er r.
Proof.
  intros tm el er rs r l HF H. unfold check_rule in H.
  destruct (rrun tm el er rs l (lr_lhs r)) as [[[c ca] cb]|] eqn:E;
    [|discriminate].
  apply andb_prop in H as [H Hcb].
  apply andb_prop in H as [Hc Hca].
  apply sconf_eqb_eq in Hc.
  apply Nat.eqb_eq in Hca. apply Nat.eqb_eq in Hcb.
  subst.
  intros XL XR j HL HR.
  exact (rrun_sound tm el er rs l (lr_lhs r) (lr_rhs r) (lr_ca r) (lr_cb r)
                    HF E XL XR j HL HR).
Qed.

Fixpoint check_ladder (tm : TM) (acc : list LRule)
    (prog : list (LRule * list rstep)) : bool :=
  match prog with
  | [] => true
  | (r, l) :: t => check_rule tm false false acc r l &&
                   check_ladder tm (acc ++ [r]) t
  end.

(** *** [rule_sound] -- the ONE theorem.

    By induction on ladder POSITION.  The step case invokes the rules
    earlier in the list, which is [Forall ... acc] in the induction
    hypothesis, and that is the whole of the ladder's well-foundedness. *)
Theorem rule_sound : forall tm prog acc,
  Forall (RuleSound tm false false) acc ->
  check_ladder tm acc prog = true ->
  Forall (RuleSound tm false false) (acc ++ map fst prog).
Proof.
  intros tm prog; induction prog as [|[r l] t IH]; intros acc HF H; cbn in *.
  - rewrite app_nil_r. exact HF.
  - apply andb_prop in H as [Hr Ht].
    specialize (IH (acc ++ [r])).
    rewrite <- app_assoc in IH. cbn in IH.
    apply IH; [|exact Ht].
    apply Forall_app. split; [exact HF|].
    constructor; [|constructor].
    exact (check_rule_sound tm false false acc r l HF Hr).
Qed.

Corollary rule_sound_nil : forall tm prog,
  check_ladder tm [] prog = true ->
  Forall (RuleSound tm false false) (map fst prog).
Proof.
  intros tm prog H.
  exact (rule_sound tm prog [] (Forall_nil _) H).
Qed.

(** An ARM is a top-level rule: it may invoke every ladder rule, and it is
    validated at whatever tail flags its own pattern needs (the fill arm
    must see the end of the counter, so it runs with the tail known empty).
    Arms are never invoked by anything, so nothing depends on their flags. *)
Definition check_arm (tm : TM) (el er : bool) (rs : list LRule)
    (a : LRule) (l : list rstep) : bool := check_rule tm el er rs a l.

Lemma arm_sound : forall tm el er rs a l,
  Forall (RuleSound tm false false) rs ->
  check_arm tm el er rs a l = true ->
  RuleSound tm el er a.
Proof. intros; eapply check_rule_sound; eassumption. Qed.
