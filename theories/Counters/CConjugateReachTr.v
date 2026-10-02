(** * Transport positive returns and eventual instruction witnesses.

    The family need not have a computable successor: an existential
    positive return suffices.  Endpoints are compared after [lift], so
    finite blank padding is immaterial.  A concrete destination boot is
    supplied separately from the source machine's initial state. *)
From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
From BBB4.Counters Require Import CConjugateTr LapCertGlueLift TriReachTr.

Definition econj (p : St -> St) (flip : bool) (c : ExecState) : ExecState :=
 let '(q,tp) := c in
 (p q, if flip then mkTape (t_right tp) (t_head tp) (t_left tp) else tp).

Lemma cconj_lift : forall p flip c,
 lift (cconj p flip c) = econj p flip (lift c).
Proof. intros p flip [q [[L h] R]]. destruct flip; reflexivity. Qed.

Section ConjugateReach.
Variable src dst : TM.
Variable p : St -> St.
Variable flip : bool.
Hypothesis Htable : forall q s,
 dst (p q) s = option_map (tconj p flip) (src q s).

Lemma cconj_lift_steps : forall k c d,
 stepn src k (lift c) = Some (lift d) ->
 stepn dst k (lift (cconj p flip c)) = Some (lift (cconj p flip d)).
Proof.
 intros k c d H.
 destruct (stepn_csteps_at _ _ _ _ H) as (e & He & El).
 rewrite (csteps_lift _ _ _ _ (cconj_steps src dst p flip Htable _ _ _ He)).
 rewrite !cconj_lift, El. reflexivity.
Qed.

Lemma cconj_reaches_fire : forall c q s,
 tri_reaches_fire src (q,s) c ->
 tri_reaches_fire dst (p q,s) (cconj p flip c).
Proof.
 intros c q s (k & e & H & Hi).
 destruct (stepn_csteps_at _ _ _ _ H) as (d & Hd & Hl).
 exists k, (lift (cconj p flip d)). split.
 - apply csteps_lift. apply (cconj_steps src dst p flip Htable). exact Hd.
 - rewrite cinstr_lift, (cconj_instr src dst p flip Htable).
   rewrite <- Hl, cinstr_lift in Hi. rewrite Hi. reflexivity.
Qed.

Variable V : Type.
Variable Cf : V -> cconf.
Hypothesis Honto : forall q, exists q0, p q0 = q.
Hypothesis Hboot : exists T x,
 stepn dst T InitES = Some (lift (cconj p flip (Cf x))).
Hypothesis Hprogress : forall x, exists y k,
 0<k /\ stepn src k (lift (Cf x)) = Some (lift (Cf y)).
Hypothesis Hfire : forall x t, tri_reaches_fire src t (Cf x).

Theorem cconj_reach_neverqhtr : NeverQuasiHaltsTr dst.
Proof.
 assert (Reach : forall N, exists T x, N<=T /\
   stepn dst T InitES = Some (lift (cconj p flip (Cf x)))).
 { induction N as [|N IH].
   - destruct Hboot as (T & x & E). exists T,x. split; [lia|exact E].
   - destruct IH as (T & x & HT & E).
     destruct (Hprogress x) as (y & k & Hk & Ek).
     exists (T+k),y. split; [lia|]. rewrite stepn_add,E.
     apply cconj_lift_steps. exact Ek. }
 intros [q s] _ N. destruct (Honto q) as (q0 & <-).
 destruct (Reach N) as (T & x & HT & E).
 destruct (cconj_reaches_fire (Cf x) q0 s (Hfire x (q0,s)))
   as (k & c & Ek & Et).
 exists (T+k). split; [lia|]. exists c. split; [|exact Et].
 rewrite stepn_add,E. exact Ek.
Qed.
End ConjugateReach.
