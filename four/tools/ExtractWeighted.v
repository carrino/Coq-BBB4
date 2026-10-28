(** Untrusted weighted-certificate producer and exact checker probe. *)
From Coq Require Import Extraction ExtrOcamlBasic ExtrOcamlNatInt.
From BBB24 Require Import WeightedCensus Mirror ClosureTr.
Extraction "build/weighted/checkers.ml" wc_check wc_target mirror_tm appears_tr rank_ok_tr compute_ranks_tr.
