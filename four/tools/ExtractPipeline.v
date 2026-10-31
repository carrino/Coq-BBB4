(** Search only. Accepted rows must be replayed inside Coq before they are
    counted as proved. Positive/N/Z encodings must remain arbitrary precision;
    in particular, do not import ExtrOcamlZInt. *)
From Coq Require Import Extraction ExtrOcamlBasic ExtrOcamlNatInt.
From BBB24 Require Import NGramCensus RepWLCensus.
Extraction "build/pipeline/checkers.ml" ng_check rw_check.
