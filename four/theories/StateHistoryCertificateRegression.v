From Coq Require Import List NArith.
From BBB24 Require Import StateHistoryCertificate.
Import ListNotations.
Definition certB := [ShRank [(2%N,1%N)]].
Example valid : sh_pcheck 0%N 6974420857%N 0 1 0 4%N [0;3;8]%N [0]%N [0]%N [] certB=true.
Proof. vm_compute. reflexivity. Qed.
Example bad_seed : sh_pcheck 0%N 6974420857%N 0 1 0 4%N [0;3;8]%N [] [0]%N [] certB=false.
Proof. vm_compute. reflexivity. Qed.
Example bad_closure : sh_pcheck 0%N 6974420857%N 0 1 0 4%N [0;3]%N [0]%N [0]%N [] certB=false.
Proof. vm_compute. reflexivity. Qed.
Example bad_rank : sh_pcheck 0%N 6974420857%N 0 1 0 4%N [0;3;8]%N [0]%N [0]%N [] [ShRank []]=false.
Proof. vm_compute. reflexivity. Qed.
Example bad_prefix : sh_pcheck 0%N 6974420857%N 0 1 3 4%N [0;3;8]%N [0]%N [0]%N [] certB=false.
Proof. vm_compute. reflexivity. Qed.
Example later_valid : sh_pcheck 3%N 6974420857%N 0 1 3 4%N [0;3;8]%N [0]%N [0]%N [] certB=true.
Proof. vm_compute. reflexivity. Qed.
