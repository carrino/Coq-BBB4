(** * Census/Deferred_Defs: compact representation for the deferred list.

    The generated Deferred_XX.v tables store one row of 8 transition
    slots per machine (bbchallenge slot order: A0 A1 B0 B1 C0 C1 D0 D1);
    [row_to_tm] gives a row its meaning as a machine.  The slot
    shorthands keep the generated files small. *)

From Coq Require Import List.
From BBB4 Require Import BBB4_Statement.
Import ListNotations.

Definition row_to_tm (r : list (option Trans)) : TM :=
  fun q s =>
    nth (match q with StA => 0 | StB => 2 | StC => 4 | StD => 6 end +
         match s with S0 => 0 | S1 => 1 end) r None.

Definition tN : option Trans := None.

Definition t0LA := Some (mkTrans S0 DL StA).
Definition t0LB := Some (mkTrans S0 DL StB).
Definition t0LC := Some (mkTrans S0 DL StC).
Definition t0LD := Some (mkTrans S0 DL StD).
Definition t0RA := Some (mkTrans S0 DR StA).
Definition t0RB := Some (mkTrans S0 DR StB).
Definition t0RC := Some (mkTrans S0 DR StC).
Definition t0RD := Some (mkTrans S0 DR StD).
Definition t1LA := Some (mkTrans S1 DL StA).
Definition t1LB := Some (mkTrans S1 DL StB).
Definition t1LC := Some (mkTrans S1 DL StC).
Definition t1LD := Some (mkTrans S1 DL StD).
Definition t1RA := Some (mkTrans S1 DR StA).
Definition t1RB := Some (mkTrans S1 DR StB).
Definition t1RC := Some (mkTrans S1 DR StC).
Definition t1RD := Some (mkTrans S1 DR StD).
