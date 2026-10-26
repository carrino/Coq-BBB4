(** Extraction is an untrusted search aid. Configuration encodings are
    arbitrarily large positives: never use ExtrOcamlZInt here. *)
From Coq Require Import Extraction ExtrOcamlBasic ExtrOcamlNatInt.
From SmallBB Require Import Size StateCheckers NGramCensus RepWLCensus CycleCensus FiniteCensus HistCensus.
Extraction "build/smallbb.ml"
  hn_check_mode fn_check_mode ng_state_check rw_state_check ng_check rw_check cycle_check machine_of_codes.
