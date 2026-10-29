(** Untrusted candidate filtering only. Every selected target is replayed in
    the Coq kernel using WeightedTail.wt_hybrid_batch_sound. *)
From Coq Require Import Extraction ExtrOcamlBasic ExtrOcamlNatInt.
From BBB24 Require Import WeightedTail WeightedCensus Pipeline.
Extraction "build/weighted-tail-native/weighted_tail.ml"
  wt_hybrid_results wt_ready wt_row_check wc_table wc_score machine_of_codes.
