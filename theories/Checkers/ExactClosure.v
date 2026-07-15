(** * ExactClosure: the simplest instance of the closure engine.

    Abstract node = exact head-relative configuration (a canonical
    [cconf], trailing blanks stripped); [covers a c := lift a = c];
    successor = one exact computable step.  The closure is finite
    exactly when the machine's reachable set of head-relative
    configurations from step [t] is finite -- in-place cyclers and
    their pre-periods -- so this instance re-proves the [Cycle]
    checker's never-QH results through the generic engine, without
    even needing the [(n1, p)] parameters.

    Its real purpose is to validate the engine: the n-gram and RepWL
    instances differ only in their (much coarser) node type and
    successor function. *)

From Coq Require Import Arith Lia Bool List.
From BBB4 Require Import BBB4_Statement CTape PosEnc Closure.
Import ListNotations.

(** ** Canonical configurations *)

(** Strip trailing blanks so that equal denotations are equal terms. *)
Fixpoint strip (l : list Sym) : list Sym :=
  match l with
  | [] => []
  | x :: t => match strip t with
              | [] => match x with S0 => [] | S1 => [S1] end
              | t' => x :: t'
              end
  end.

Lemma strip_nthb : forall l n, nthb (strip l) n = nthb l n.
Proof.
  induction l as [|x t IH]; intro n.
  - reflexivity.
  - simpl. destruct (strip t) as [|y t'] eqn:Est.
    + (* strip t = []: t denotes all blanks *)
      assert (Ht : forall m, nthb t m = S0).
      { intro m. rewrite <- IH. apply nthb_nil. }
      destruct x; destruct n; try reflexivity.
      * change (S0 = nthb t n). rewrite Ht. reflexivity.
      * change (nthb [] n = nthb t n). rewrite nthb_nil, Ht. reflexivity.
    + destruct n; [reflexivity |].
      change (nthb (y :: t') n = nthb t n). apply IH.
Qed.

Lemma strip_lift : forall l, lift_side (strip l) = lift_side l.
Proof.
  intros. apply FunctionalExtensionality.functional_extensionality.
  intro n. apply strip_nthb.
Qed.

Definition norm (c : cconf) : cconf :=
  let '(q, (l, h, r)) := c in (q, (strip l, h, strip r)).

Lemma norm_lift : forall c, lift (norm c) = lift c.
Proof.
  intros [q [[l h] r]]. unfold lift, norm; simpl.
  rewrite !strip_lift. reflexivity.
Qed.

(** ** The instance

    Node identity is the injective [positive] encoding [cconf_enc]
    from [PosEnc]; the engine's tries are keyed by it. *)

Definition ec_succs (tm : TM) (a : cconf) : option (list cconf) :=
  match cstep tm a with
  | Some c' => Some [norm c']
  | None => None
  end.

Definition ec_state (a : cconf) : St := fst a.

Definition exact_closure_check_neverqh (tm : TM) (t fuel : nat) : bool :=
  match csteps tm t c0 with
  | Some ct =>
      closure_check_neverqh tm cconf cconf_enc ec_state (ec_succs tm)
        t fuel (norm ct)
  | None => false
  end.

Theorem exact_closure_check_neverqh_sound : forall tm t fuel,
  exact_closure_check_neverqh tm t fuel = true -> NeverQuasiHaltsSt tm.
Proof.
  intros tm t fuel H.
  unfold exact_closure_check_neverqh in H.
  destruct (csteps tm t c0) as [ct|] eqn:Et; [|discriminate].
  apply (closure_check_neverqh_sound tm cconf cconf_enc ec_state
           (ec_succs tm) (fun a c => lift a = c)) in H;
    [assumption | | | |].
  - exact cconf_enc_inj.
  - (* covers_state *)
    intros a c Hc. subst c. reflexivity.
  - (* succs_sound *)
    intros a c Hc. subst c. unfold ec_succs.
    destruct (cstep tm a) as [c'|] eqn:E.
    + rewrite (cstep_lift _ _ _ E).
      exists (norm c'). split; [left; reflexivity | apply norm_lift].
    + exact I.
  - (* start covers *)
    intros ct' Hct'. rewrite Et in Hct'. injection Hct' as <-.
    apply norm_lift.
Qed.
