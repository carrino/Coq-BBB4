(** Isolated prototype: a closed state census with checked leaf certificates.
    Undefined transitions retain their halting case. No deferred constructor
    can be accepted as a completed upper-bound certificate. *)
From Coq Require Import Arith Lia Bool List NArith PArith FSets.FMapPositive.
From BBB24 Require Import Statement Spec CTape Bounds Census CycleCensus
  Closeout BranchCloseout StateOnlyCloseout StateBranchCloseout
  FamilyIndex FamilyTransport Symmetry Mirror OrbitCloseout.
Import ListNotations.

Section StateCertificates.
Variable B : N.
Variable Leaf : Type.
Variable leaf_check : TM -> Leaf -> bool.
Hypothesis leaf_sound : forall family witness,
  leaf_check family witness = true -> forall complete,
  TM_le family complete -> QHBound (N.to_nat B) complete.

Inductive StateCert :=
  | StateInvalid
  | StateLeaf (witness : Leaf)
  | StateBranch (anchor : nat) (children : list StateCert)
  | StateCycle (mirrored : bool) (anchor period width : nat).

Fixpoint state_verify depth family cert :=
  match depth with
  | 0 => false
  | S d => match cert with
    | StateInvalid => false
    | StateLeaf witness => leaf_check family witness
    | StateCycle mirrored anchor period width =>
        cycle_check B B family mirrored anchor period width
    | StateBranch anchor children =>
        (N.of_nat anchor <? B)%N &&
        match csteps family anchor c0 with
        | None => false
        | Some (q,(_,symbol,_)) =>
          match family q symbol with
          | Some _ => false
          | None => forallb (fun code => state_verify d
              (update family q symbol (nat_trans code))
              (nth code children StateInvalid)) (seq 0 16)
          end
        end
    end
  end.

Theorem state_verify_sound : forall depth family cert,
  state_verify depth family cert = true -> forall complete,
  TM_le family complete -> QHBound (N.to_nat B) complete.
Proof.
  induction depth as [|depth IH]; intros family cert H complete Hle; [discriminate|].
  destruct cert as [|witness|anchor children|mirrored anchor period width];
    cbn [state_verify] in H; try discriminate.
  - exact (leaf_sound family witness H complete Hle).
  - apply andb_prop in H as [Hn H]. apply N.ltb_lt in Hn.
    destruct (csteps family anchor c0) as [[q [[l symbol] r]]|] eqn:Erun; [|discriminate].
    destruct (family q symbol) as [tr|] eqn:Efamily; [discriminate|].
    assert (Hnat : anchor < N.to_nat B).
    { rewrite <- (Nat2N.id anchor). apply Nat.compare_lt_iff.
      rewrite <- N2Nat.inj_compare. exact Hn. }
    apply (state_branch_children_sound (N.to_nat B) family anchor q l symbol r
      Hnat Erun Efamily); [|exact Hle].
    intros child Hin target Htarget.
    unfold branch_children in Hin. apply in_map_iff in Hin as (code & <- & Hin).
    apply forallb_forall with (x:=code) in H; [|exact Hin].
    exact (IH _ _ H target Htarget).
  - destruct (cycle_check_sound B B family mirrored anchor period width H) as [Hnh [Hs _]].
    eapply state_bound_extend; eauto.
Qed.

Corollary state_census_upper : forall depth cert,
  state_verify depth empty cert = true -> forall tm, QHBound (N.to_nat B) tm.
Proof.
  intros depth cert H tm. eapply state_verify_sound; [exact H|].
  intros q s. left. reflexivity.
Qed.
End StateCertificates.

Record StateLookup := state_lookup {
  lookup_key : positive;
  lookup_permutation : SymPerm;
  lookup_mirrored : bool
}.

Definition state_lookup_check index family witness :=
  match PositiveMap.find (lookup_key witness) index with
  | None => false
  | Some source => table_leb source
      (image_tm (lookup_permutation witness) (lookup_mirrored witness) family)
  end.

Lemma image_extends : forall p mirrored family complete,
  TM_le family complete -> TM_le (image_tm p mirrored family) (image_tm p mirrored complete).
Proof.
  intros p mirrored family complete Hle. unfold image_tm.
  pose proof (perm_extends p family complete Hle) as Hperm.
  destruct mirrored; [|exact Hperm]. intros q s. unfold mirror_tm.
  destruct (Hperm q s) as [E|E]; rewrite E; auto.
Qed.

Theorem state_lookup_sound : forall B board family witness,
  StateBoardSound B board ->
  state_lookup_check (family_index board) family witness = true ->
  forall complete, TM_le family complete -> QHBound B complete.
Proof.
  intros B board family witness Hboard H complete Hle.
  unfold state_lookup_check in H.
  destruct (PositiveMap.find (lookup_key witness) (family_index board)) as [source|] eqn:E;
    [|discriminate].
  apply table_leb_spec in H.
  eapply image_state_bound_back.
  apply (Hboard source (family_index_member board _ _ E)).
  eapply branch_tm_le_trans; [exact H|]. apply image_extends; exact Hle.
Qed.

Print Assumptions state_verify_sound.
Print Assumptions state_lookup_sound.
