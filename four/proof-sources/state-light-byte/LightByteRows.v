(** Ordinary inductive byte data, with no primitive or specification axioms.
    The decoded board is arbitrary; provider table checks justify its soundness. *)
From Coq Require Import List NArith Strings.Byte.
From BBB24 Require Import StatePipeline.
Import ListNotations.

Record Row5 := row5 {
  byte0 : byte; byte1 : byte; byte2 : byte; byte3 : byte; byte4 : byte
}.

Definition decode_row (row : Row5) : N :=
  (Byte.to_N (byte0 row) + 256 *
    (Byte.to_N (byte1 row) + 256 *
      (Byte.to_N (byte2 row) + 256 *
        (Byte.to_N (byte3 row) + 256 * Byte.to_N (byte4 row)))))%N.

Definition row_machine row := stp_machine (decode_row row).
Definition byte_board rows := map row_machine rows.
