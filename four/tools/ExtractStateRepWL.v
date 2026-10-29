From Coq Require Import Extraction ExtrOcamlBasic ExtrOcamlNatInt.
From BBB24 Require Import StateRepWL.
Extraction "build/state-repwl/checkers.ml" srw_check.
