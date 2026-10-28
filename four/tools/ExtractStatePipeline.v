(** Search only; Coq must replay every accepted state-bound certificate. *)
From Coq Require Import Extraction ExtrOcamlBasic ExtrOcamlNatInt.
From BBB24 Require Import StatePipeline.
Extraction "build/state-pipeline/checkers.ml" stp_check.
