From BBB24Burn43S071FAR Require Import FARForward Sparse DataSchema Checker CheckerSound Data CheckActual.
From BBB24Burn43S071FAR Require Import LocalTable.

Theorem actual_closed : Closed (model certificate c52_localfun).
Proof. exact (check_closed certificate Data.nodeindex c52_localfun actual_checked). Qed.

Print Assumptions actual_closed.
