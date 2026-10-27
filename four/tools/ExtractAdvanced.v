(** Untrusted search aid for the next closure sweep. Recheck all candidate
    expressions in Coq. Positive, N, and Z must retain exact representations. *)
From Coq Require Import Extraction ExtrOcamlBasic ExtrOcamlNatInt.
From BBB24 Require Import FiniteCensus HistCensus RepWLCensus.
Extraction "build/advanced/checkers.ml" fn_check_mode hn_check_mode rw_check.
