(** Untrusted graph production; exact integers and encodings are preserved. *)
From Coq Require Import Extraction ExtrOcamlBasic ExtrOcamlNatInt.
From BBB24 Require Import WeightedCensus Mirror ClosureTr.
From BBB24.Checkers Require Import NGram.
Extraction "build/weighted-v2/weighted_v2.ml"
 wc_graph_check ng_grow ng_explore mirror_tm appears_tr rank_ok_tr compute_ranks_tr.
