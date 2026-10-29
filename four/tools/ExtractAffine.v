(** Untrusted preselection aid. N and Z retain exact representations;
    every accepted certificate must still be replayed in Coq. *)
From Coq Require Import Extraction ExtrOcamlBasic ExtrOcamlNatInt.
From BBB24 Require Import IRuleCensus.
Extraction "build/affine-wave/extracted/checker.ml" ir_check.
