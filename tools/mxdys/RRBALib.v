From BusyCoq Require RRBA.
Require Import Extraction ExtrOCamlInt63 ExtrOCamlPArray ExtrOcamlNativeString.
Extract Constant PArray.array "'a" => "'a Parray.t".
Extraction NoInline PArray.array.
Recursive Extraction Library RRBA.
