(** Source candidate only.  The packed data is untrusted: acceptance still
    means that the existing StateCensus.state_verify returned true for the
    actual decoded certificate and its actual target family. *)
From Coq Require Import List Bool NArith FSets.FMapPositive.
From BBB24 Require Import Statement Spec Census StateOnlyCloseout FamilyIndex.
From BBB24Burn10StateCensus Require Import StateCensus.
From BBB24GlobalLeaves Require Import GlobalLeaves.
Import ListNotations.

Definition Certificate := StateCert GlobalWitness.
Definition invalid : Certificate := StateInvalid GlobalWitness.
Definition NodeTable := PositiveMap.t Certificate.

Definition read_node (table : NodeTable) (key : N) : Certificate :=
  match key with
  | N0 => invalid
  | Npos p =>
      match PositiveMap.find p table with
      | Some cert => cert
      | None => invalid
      end
  end.

Definition decode_permutation (code : N) : Symmetry.SymPerm :=
  match N.to_nat code with
  | 0 => Symmetry.P123
  | 1 => Symmetry.P132
  | 2 => Symmetry.P213
  | 3 => Symmetry.P231
  | 4 => Symmetry.P312
  | _ => Symmetry.P321
  end.

(** The following conversions are of small bounded payloads, never scoreN.
    Child IDs are positive, one more than their original zero-based ID. *)
Fixpoint decode_children (fuel : nat) (payload : N) (table : NodeTable)
    : list Certificate :=
  match fuel with
  | 0 => []
  | S rest =>
      read_node table (N.modulo payload 8192) ::
      decode_children rest (N.div payload 8192) table
  end.

Definition decode_node (table : NodeTable) (word : N) : Certificate :=
  let tag := N.modulo word 8 in
  let payload := N.div word 8 in
  match N.to_nat tag with
  | 0 =>
      let mirrored := N.odd payload in
      let tail := N.div payload 2 in
      StateCycle GlobalWitness mirrored
        (N.to_nat (N.modulo tail 256))
        (N.to_nat (N.modulo (N.div tail 256) 128))
        (N.to_nat (N.modulo (N.div tail 32768) 16))
  | 1 =>
      match N.div payload 12 with
      | N0 => invalid
      | Npos key => StateLeaf GlobalWitness
          (Known (state_lookup key
            (decode_permutation (N.modulo (N.div payload 2) 6))
            (N.odd payload)))
      end
  | 2 =>
      match N.div payload 12 with
      | N0 => invalid
      | Npos key => StateLeaf GlobalWitness
          (Parent (state_lookup key
            (decode_permutation (N.modulo (N.div payload 2) 6))
            (N.odd payload)))
      end
  | 3 => StateLeaf GlobalWitness
      (Reach (N.div payload 12)
        (decode_permutation (N.modulo (N.div payload 2) 6))
        (N.odd payload))
  | 4 => StateBranch GlobalWitness
      (N.to_nat (N.modulo payload 256))
      (decode_children 16 (N.div payload 256) table)
  | _ => invalid
  end.

Definition compile_step (state : positive * NodeTable) (word : N)
    : positive * NodeTable :=
  let '(next, table) := state in
  (Pos.succ next, PositiveMap.add next (decode_node table word) table).

Definition compile_certificate (words : list N) (root : positive) : Certificate :=
  read_node (snd (fold_left compile_step words
    (xH, PositiveMap.empty Certificate))) (Npos root).

Record UnitData := unit_data {
  unit_family : TM;
  unit_parents : list TM;
  unit_words : list N;
  unit_root : positive;
  unit_depth : nat
}.

Definition unit_certificate data :=
  compile_certificate (unit_words data) (unit_root data).

Definition unit_check (B : N) (global : PositiveMap.t TM) (data : UnitData) :=
  state_verify B GlobalWitness
    (global_leaf_check global (family_index (unit_parents data)))
    (unit_depth data) (unit_family data) (unit_certificate data).

Definition FamilyBound (B : nat) (family : TM) :=
  forall complete, TM_le family complete -> QHBound B complete.

Lemma board_sound_nil : forall B, StateBoardSound B [].
Proof. intros B family H; contradiction. Qed.

Lemma board_sound_cons : forall B head tail,
  FamilyBound B head -> StateBoardSound B tail ->
  StateBoardSound B (head :: tail).
Proof.
  intros B head tail HH HT family [<-|H].
  - exact HH.
  - exact (HT family H).
Qed.

(** This theorem holds for every word list, including malformed inputs.
    The compiler is not trusted: only the original verifier's true result
    and the two explicitly supplied soundness premises justify the bound. *)
Theorem unit_sound : forall B global data,
  IndexSound (N.to_nat B) global ->
  StateBoardSound (N.to_nat B) (unit_parents data) ->
  unit_check B global data = true ->
  FamilyBound (N.to_nat B) (unit_family data).
Proof.
  intros B global data HG HP HC.
  exact (global_certificate_sound B global (family_index (unit_parents data))
    (unit_depth data) (unit_family data) (unit_certificate data)
    HG (board_index_sound (N.to_nat B) (unit_parents data) HP) HC).
Qed.

Print Assumptions unit_sound.
