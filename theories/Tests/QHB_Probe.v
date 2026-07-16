From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Checkers Require Import Wrap.


Definition tm_qhb_0001 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => None
  | StC, S0 => Some (mkTrans S0 DL StD)
  | StC, S1 => Some (mkTrans S1 DL StC)
  | StD, S0 => Some (mkTrans S1 DR StC)
  | StD, S1 => Some (mkTrans S1 DL StD)
  end.

Theorem qhb_0001 :
  NonHalt tm_qhb_0001
  /\ (forall q' s', QuietAfter tm_qhb_0001 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0001.
Proof.
  apply (ngram_check_qhbound_sound _ StB 1 2 64 136 9).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0002 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => None
  | StC, S0 => Some (mkTrans S0 DR StD)
  | StC, S1 => Some (mkTrans S1 DR StC)
  | StD, S0 => Some (mkTrans S1 DL StC)
  | StD, S1 => Some (mkTrans S1 DR StD)
  end.

Theorem qhb_0002 :
  NonHalt tm_qhb_0002
  /\ (forall q' s', QuietAfter tm_qhb_0002 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0002.
Proof.
  apply (ngram_check_qhbound_sound _ StB 1 2 64 136 9).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0003 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => None
  | StC, S0 => Some (mkTrans S1 DL StD)
  | StC, S1 => Some (mkTrans S0 DR StC)
  | StD, S0 => Some (mkTrans S0 DR StD)
  | StD, S1 => Some (mkTrans S1 DR StC)
  end.

Theorem qhb_0003 :
  NonHalt tm_qhb_0003
  /\ (forall q' s', QuietAfter tm_qhb_0003 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0003.
Proof.
  apply (ngram_check_qhbound_sound _ StB 1 2 64 120 8).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0004 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => None
  | StC, S0 => Some (mkTrans S1 DL StD)
  | StC, S1 => Some (mkTrans S0 DR StC)
  | StD, S0 => Some (mkTrans S1 DR StD)
  | StD, S1 => Some (mkTrans S1 DR StC)
  end.

Theorem qhb_0004 :
  NonHalt tm_qhb_0004
  /\ (forall q' s', QuietAfter tm_qhb_0004 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0004.
Proof.
  apply (ngram_check_qhbound_sound _ StB 1 2 64 128 8).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0005 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => None
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => Some (mkTrans S0 DL StD)
  | StD, S1 => Some (mkTrans S1 DL StC)
  end.

Theorem qhb_0005 :
  NonHalt tm_qhb_0005
  /\ (forall q' s', QuietAfter tm_qhb_0005 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0005.
Proof.
  apply (ngram_check_qhbound_sound _ StB 1 2 64 120 8).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0006 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => None
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => Some (mkTrans S1 DL StD)
  | StD, S1 => Some (mkTrans S1 DL StC)
  end.

Theorem qhb_0006 :
  NonHalt tm_qhb_0006
  /\ (forall q' s', QuietAfter tm_qhb_0006 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0006.
Proof.
  apply (ngram_check_qhbound_sound _ StB 1 2 64 128 8).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0007 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S0 DL StB)
  | StC, S0 => Some (mkTrans S0 DL StD)
  | StC, S1 => Some (mkTrans S1 DL StB)
  | StD, S0 => Some (mkTrans S1 DR StC)
  | StD, S1 => Some (mkTrans S1 DL StD)
  end.

Theorem qhb_0007 :
  NonHalt tm_qhb_0007
  /\ (forall q' s', QuietAfter tm_qhb_0007 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0007.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 144 8).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0008 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S0 DL StB)
  | StC, S0 => Some (mkTrans S1 DR StB)
  | StC, S1 => Some (mkTrans S1 DR StD)
  | StD, S0 => Some (mkTrans S1 DL StD)
  | StD, S1 => Some (mkTrans S1 DL StC)
  end.

Theorem qhb_0008 :
  NonHalt tm_qhb_0008
  /\ (forall q' s', QuietAfter tm_qhb_0008 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0008.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 152 8).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0009 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S0 DL StB)
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S0 DR StB)
  | StD, S0 => Some (mkTrans S1 DL StD)
  | StD, S1 => Some (mkTrans S1 DL StC)
  end.

Theorem qhb_0009 :
  NonHalt tm_qhb_0009
  /\ (forall q' s', QuietAfter tm_qhb_0009 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0009.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 136 8).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0010 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S0 DL StB)
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S1 DL StC)
  | StD, S0 => Some (mkTrans S1 DR StB)
  | StD, S1 => Some (mkTrans S0 DL StB)
  end.

Theorem qhb_0010 :
  NonHalt tm_qhb_0010
  /\ (forall q' s', QuietAfter tm_qhb_0010 q' s' -> S s' <= S 256)
  /\ QuasiHaltsSt tm_qhb_0010.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 256 168 9).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0011 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S0 DL StB)
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S1 DL StC)
  | StD, S0 => Some (mkTrans S1 DR StB)
  | StD, S1 => Some (mkTrans S1 DL StB)
  end.

Theorem qhb_0011 :
  NonHalt tm_qhb_0011
  /\ (forall q' s', QuietAfter tm_qhb_0011 q' s' -> S s' <= S 256)
  /\ QuasiHaltsSt tm_qhb_0011.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 256 184 10).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0012 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S0 DL StB)
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S1 DL StC)
  | StD, S0 => Some (mkTrans S1 DR StB)
  | StD, S1 => Some (mkTrans S1 DL StD)
  end.

Theorem qhb_0012 :
  NonHalt tm_qhb_0012
  /\ (forall q' s', QuietAfter tm_qhb_0012 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0012.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 216 10).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0013 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S0 DL StB)
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S1 DL StD)
  | StD, S0 => Some (mkTrans S1 DR StB)
  | StD, S1 => Some (mkTrans S1 DL StC)
  end.

Theorem qhb_0013 :
  NonHalt tm_qhb_0013
  /\ (forall q' s', QuietAfter tm_qhb_0013 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0013.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 216 10).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0014 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S0 DL StB)
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S1 DR StB)
  | StD, S0 => Some (mkTrans S1 DL StD)
  | StD, S1 => Some (mkTrans S1 DL StC)
  end.

Theorem qhb_0014 :
  NonHalt tm_qhb_0014
  /\ (forall q' s', QuietAfter tm_qhb_0014 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0014.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 144 8).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0015 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S0 DL StC)
  | StC, S0 => Some (mkTrans S0 DL StD)
  | StC, S1 => Some (mkTrans S1 DL StB)
  | StD, S0 => Some (mkTrans S1 DR StC)
  | StD, S1 => Some (mkTrans S1 DL StD)
  end.

Theorem qhb_0015 :
  NonHalt tm_qhb_0015
  /\ (forall q' s', QuietAfter tm_qhb_0015 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0015.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 136 8).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0016 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S0 DL StC)
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S1 DL StC)
  | StD, S0 => Some (mkTrans S0 DL StC)
  | StD, S1 => Some (mkTrans S1 DL StB)
  end.

Theorem qhb_0016 :
  NonHalt tm_qhb_0016
  /\ (forall q' s', QuietAfter tm_qhb_0016 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0016.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 120 8).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0017 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S0 DL StC)
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S1 DL StC)
  | StD, S0 => Some (mkTrans S1 DL StC)
  | StD, S1 => Some (mkTrans S0 DL StB)
  end.

Theorem qhb_0017 :
  NonHalt tm_qhb_0017
  /\ (forall q' s', QuietAfter tm_qhb_0017 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0017.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 120 8).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0018 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S0 DL StC)
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S1 DL StC)
  | StD, S0 => Some (mkTrans S1 DL StC)
  | StD, S1 => Some (mkTrans S1 DL StB)
  end.

Theorem qhb_0018 :
  NonHalt tm_qhb_0018
  /\ (forall q' s', QuietAfter tm_qhb_0018 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0018.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 128 8).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0019 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S0 DL StD)
  | StC, S0 => Some (mkTrans S0 DL StD)
  | StC, S1 => Some (mkTrans S1 DL StB)
  | StD, S0 => Some (mkTrans S1 DR StC)
  | StD, S1 => Some (mkTrans S1 DL StD)
  end.

Theorem qhb_0019 :
  NonHalt tm_qhb_0019
  /\ (forall q' s', QuietAfter tm_qhb_0019 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0019.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 120 8).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0020 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S0 DL StD)
  | StC, S0 => Some (mkTrans S0 DL StD)
  | StC, S1 => Some (mkTrans S1 DL StD)
  | StD, S0 => Some (mkTrans S1 DR StB)
  | StD, S1 => Some (mkTrans S1 DL StB)
  end.

Theorem qhb_0020 :
  NonHalt tm_qhb_0020
  /\ (forall q' s', QuietAfter tm_qhb_0020 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0020.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 144 8).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0021 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S0 DL StD)
  | StC, S0 => Some (mkTrans S0 DL StD)
  | StC, S1 => Some (mkTrans S1 DL StD)
  | StD, S0 => Some (mkTrans S1 DR StB)
  | StD, S1 => Some (mkTrans S1 DL StC)
  end.

Theorem qhb_0021 :
  NonHalt tm_qhb_0021
  /\ (forall q' s', QuietAfter tm_qhb_0021 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0021.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 128 8).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0022 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S0 DL StD)
  | StC, S0 => Some (mkTrans S1 DL StD)
  | StC, S1 => Some (mkTrans S0 DL StB)
  | StD, S0 => Some (mkTrans S1 DR StC)
  | StD, S1 => Some (mkTrans S0 DL StB)
  end.

Theorem qhb_0022 :
  NonHalt tm_qhb_0022
  /\ (forall q' s', QuietAfter tm_qhb_0022 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0022.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 144 8).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0023 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S0 DL StD)
  | StC, S0 => Some (mkTrans S1 DL StD)
  | StC, S1 => Some (mkTrans S0 DL StB)
  | StD, S0 => Some (mkTrans S1 DR StC)
  | StD, S1 => Some (mkTrans S0 DL StC)
  end.

Theorem qhb_0023 :
  NonHalt tm_qhb_0023
  /\ (forall q' s', QuietAfter tm_qhb_0023 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0023.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 136 8).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0024 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S0 DL StD)
  | StC, S0 => Some (mkTrans S1 DL StD)
  | StC, S1 => Some (mkTrans S0 DL StB)
  | StD, S0 => Some (mkTrans S1 DR StC)
  | StD, S1 => Some (mkTrans S1 DL StB)
  end.

Theorem qhb_0024 :
  NonHalt tm_qhb_0024
  /\ (forall q' s', QuietAfter tm_qhb_0024 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0024.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 144 9).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0025 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S0 DL StD)
  | StC, S0 => Some (mkTrans S1 DL StD)
  | StC, S1 => Some (mkTrans S0 DL StB)
  | StD, S0 => Some (mkTrans S1 DR StC)
  | StD, S1 => Some (mkTrans S1 DL StC)
  end.

Theorem qhb_0025 :
  NonHalt tm_qhb_0025
  /\ (forall q' s', QuietAfter tm_qhb_0025 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0025.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 136 9).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0026 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S0 DL StD)
  | StC, S0 => Some (mkTrans S1 DL StD)
  | StC, S1 => Some (mkTrans S0 DL StB)
  | StD, S0 => Some (mkTrans S1 DR StC)
  | StD, S1 => Some (mkTrans S1 DL StD)
  end.

Theorem qhb_0026 :
  NonHalt tm_qhb_0026
  /\ (forall q' s', QuietAfter tm_qhb_0026 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0026.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 120 8).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0027 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S0 DL StD)
  | StC, S0 => Some (mkTrans S1 DL StD)
  | StC, S1 => Some (mkTrans S1 DL StB)
  | StD, S0 => Some (mkTrans S1 DR StB)
  | StD, S1 => Some (mkTrans S0 DL StD)
  end.

Theorem qhb_0027 :
  NonHalt tm_qhb_0027
  /\ (forall q' s', QuietAfter tm_qhb_0027 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0027.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 144 8).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0028 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S0 DL StD)
  | StC, S0 => Some (mkTrans S1 DL StD)
  | StC, S1 => Some (mkTrans S1 DL StB)
  | StD, S0 => Some (mkTrans S1 DR StC)
  | StD, S1 => Some (mkTrans S0 DL StB)
  end.

Theorem qhb_0028 :
  NonHalt tm_qhb_0028
  /\ (forall q' s', QuietAfter tm_qhb_0028 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0028.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 144 9).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0029 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S0 DL StD)
  | StC, S0 => Some (mkTrans S1 DL StD)
  | StC, S1 => Some (mkTrans S1 DL StB)
  | StD, S0 => Some (mkTrans S1 DR StC)
  | StD, S1 => Some (mkTrans S0 DL StC)
  end.

Theorem qhb_0029 :
  NonHalt tm_qhb_0029
  /\ (forall q' s', QuietAfter tm_qhb_0029 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0029.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 136 9).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0030 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S0 DL StD)
  | StC, S0 => Some (mkTrans S1 DL StD)
  | StC, S1 => Some (mkTrans S1 DL StB)
  | StD, S0 => Some (mkTrans S1 DR StC)
  | StD, S1 => Some (mkTrans S0 DR StC)
  end.

Theorem qhb_0030 :
  NonHalt tm_qhb_0030
  /\ (forall q' s', QuietAfter tm_qhb_0030 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0030.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 160 9).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0031 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S0 DL StD)
  | StC, S0 => Some (mkTrans S1 DL StD)
  | StC, S1 => Some (mkTrans S1 DL StB)
  | StD, S0 => Some (mkTrans S1 DR StC)
  | StD, S1 => Some (mkTrans S1 DL StB)
  end.

Theorem qhb_0031 :
  NonHalt tm_qhb_0031
  /\ (forall q' s', QuietAfter tm_qhb_0031 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0031.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 144 9).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0032 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S0 DL StD)
  | StC, S0 => Some (mkTrans S1 DL StD)
  | StC, S1 => Some (mkTrans S1 DL StB)
  | StD, S0 => Some (mkTrans S1 DR StC)
  | StD, S1 => Some (mkTrans S1 DL StC)
  end.

Theorem qhb_0032 :
  NonHalt tm_qhb_0032
  /\ (forall q' s', QuietAfter tm_qhb_0032 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0032.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 136 8).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0033 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S0 DL StD)
  | StC, S0 => Some (mkTrans S1 DL StD)
  | StC, S1 => Some (mkTrans S1 DL StB)
  | StD, S0 => Some (mkTrans S1 DR StC)
  | StD, S1 => Some (mkTrans S1 DL StD)
  end.

Theorem qhb_0033 :
  NonHalt tm_qhb_0033
  /\ (forall q' s', QuietAfter tm_qhb_0033 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0033.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 128 8).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0034 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S0 DL StD)
  | StC, S0 => Some (mkTrans S1 DL StD)
  | StC, S1 => Some (mkTrans S1 DL StB)
  | StD, S0 => Some (mkTrans S1 DR StC)
  | StD, S1 => Some (mkTrans S1 DR StB)
  end.

Theorem qhb_0034 :
  NonHalt tm_qhb_0034
  /\ (forall q' s', QuietAfter tm_qhb_0034 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0034.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 168 8).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0035 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S0 DL StD)
  | StC, S0 => Some (mkTrans S1 DL StD)
  | StC, S1 => Some (mkTrans S1 DL StC)
  | StD, S0 => Some (mkTrans S1 DR StB)
  | StD, S1 => Some (mkTrans S0 DL StD)
  end.

Theorem qhb_0035 :
  NonHalt tm_qhb_0035
  /\ (forall q' s', QuietAfter tm_qhb_0035 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0035.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 128 8).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0036 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S0 DL StD)
  | StC, S0 => Some (mkTrans S1 DR StB)
  | StC, S1 => Some (mkTrans S1 DL StC)
  | StD, S0 => Some (mkTrans S1 DL StB)
  | StD, S1 => Some (mkTrans S0 DR StD)
  end.

Theorem qhb_0036 :
  NonHalt tm_qhb_0036
  /\ (forall q' s', QuietAfter tm_qhb_0036 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0036.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 144 8).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0037 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S0 DL StD)
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S1 DL StB)
  | StD, S0 => Some (mkTrans S1 DR StB)
  | StD, S1 => Some (mkTrans S0 DR StC)
  end.

Theorem qhb_0037 :
  NonHalt tm_qhb_0037
  /\ (forall q' s', QuietAfter tm_qhb_0037 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0037.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 3 64 320 12).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0038 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S0 DL StD)
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S1 DL StD)
  | StD, S0 => Some (mkTrans S1 DR StB)
  | StD, S1 => Some (mkTrans S0 DL StD)
  end.

Theorem qhb_0038 :
  NonHalt tm_qhb_0038
  /\ (forall q' s', QuietAfter tm_qhb_0038 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0038.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 128 8).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0039 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S0 DR StB)
  | StC, S0 => Some (mkTrans S0 DR StD)
  | StC, S1 => Some (mkTrans S1 DL StC)
  | StD, S0 => Some (mkTrans S1 DR StB)
  | StD, S1 => Some (mkTrans S1 DL StB)
  end.

Theorem qhb_0039 :
  NonHalt tm_qhb_0039
  /\ (forall q' s', QuietAfter tm_qhb_0039 q' s' -> S s' <= S 1024)
  /\ QuasiHaltsSt tm_qhb_0039.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 1024 288 10).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0040 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S0 DR StB)
  | StC, S0 => Some (mkTrans S1 DL StD)
  | StC, S1 => Some (mkTrans S0 DR StC)
  | StD, S0 => Some (mkTrans S1 DR StB)
  | StD, S1 => Some (mkTrans S1 DR StD)
  end.

Theorem qhb_0040 :
  NonHalt tm_qhb_0040
  /\ (forall q' s', QuietAfter tm_qhb_0040 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0040.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 192 8).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0041 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S0 DR StB)
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S1 DL StD)
  | StD, S0 => Some (mkTrans S1 DR StB)
  | StD, S1 => Some (mkTrans S0 DR StD)
  end.

Theorem qhb_0041 :
  NonHalt tm_qhb_0041
  /\ (forall q' s', QuietAfter tm_qhb_0041 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0041.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 248 9).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0042 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S0 DR StB)
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S1 DL StD)
  | StD, S0 => Some (mkTrans S1 DR StB)
  | StD, S1 => Some (mkTrans S1 DL StB)
  end.

Theorem qhb_0042 :
  NonHalt tm_qhb_0042
  /\ (forall q' s', QuietAfter tm_qhb_0042 q' s' -> S s' <= S 256)
  /\ QuasiHaltsSt tm_qhb_0042.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 3 256 248 14).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0043 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S0 DR StC)
  | StC, S0 => Some (mkTrans S0 DL StD)
  | StC, S1 => Some (mkTrans S1 DL StB)
  | StD, S0 => Some (mkTrans S1 DR StC)
  | StD, S1 => Some (mkTrans S1 DL StD)
  end.

Theorem qhb_0043 :
  NonHalt tm_qhb_0043
  /\ (forall q' s', QuietAfter tm_qhb_0043 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0043.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 160 8).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0044 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S0 DR StC)
  | StC, S0 => Some (mkTrans S0 DR StD)
  | StC, S1 => Some (mkTrans S1 DR StB)
  | StD, S0 => Some (mkTrans S1 DL StC)
  | StD, S1 => Some (mkTrans S1 DR StD)
  end.

Theorem qhb_0044 :
  NonHalt tm_qhb_0044
  /\ (forall q' s', QuietAfter tm_qhb_0044 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0044.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 136 8).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0045 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S0 DR StC)
  | StC, S0 => Some (mkTrans S1 DL StD)
  | StC, S1 => Some (mkTrans S1 DR StC)
  | StD, S0 => Some (mkTrans S0 DR StC)
  | StD, S1 => Some (mkTrans S1 DR StB)
  end.

Theorem qhb_0045 :
  NonHalt tm_qhb_0045
  /\ (forall q' s', QuietAfter tm_qhb_0045 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0045.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 120 8).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0046 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S0 DR StC)
  | StC, S0 => Some (mkTrans S1 DL StD)
  | StC, S1 => Some (mkTrans S1 DR StC)
  | StD, S0 => Some (mkTrans S1 DR StC)
  | StD, S1 => Some (mkTrans S0 DR StB)
  end.

Theorem qhb_0046 :
  NonHalt tm_qhb_0046
  /\ (forall q' s', QuietAfter tm_qhb_0046 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0046.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 120 8).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0047 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S0 DR StC)
  | StC, S0 => Some (mkTrans S1 DL StD)
  | StC, S1 => Some (mkTrans S1 DR StC)
  | StD, S0 => Some (mkTrans S1 DR StC)
  | StD, S1 => Some (mkTrans S1 DR StB)
  end.

Theorem qhb_0047 :
  NonHalt tm_qhb_0047
  /\ (forall q' s', QuietAfter tm_qhb_0047 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0047.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 128 8).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0048 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S0 DR StC)
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S0 DL StD)
  | StD, S0 => Some (mkTrans S1 DR StB)
  | StD, S1 => Some (mkTrans S1 DL StB)
  end.

Theorem qhb_0048 :
  NonHalt tm_qhb_0048
  /\ (forall q' s', QuietAfter tm_qhb_0048 q' s' -> S s' <= S 256)
  /\ QuasiHaltsSt tm_qhb_0048.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 256 384 11).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0049 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S0 DR StC)
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S1 DL StD)
  | StD, S0 => Some (mkTrans S1 DR StB)
  | StD, S1 => Some (mkTrans S1 DL StB)
  end.

Theorem qhb_0049 :
  NonHalt tm_qhb_0049
  /\ (forall q' s', QuietAfter tm_qhb_0049 q' s' -> S s' <= S 1024)
  /\ QuasiHaltsSt tm_qhb_0049.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 1024 504 12).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0050 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S0 DR StD)
  | StC, S0 => Some (mkTrans S0 DR StD)
  | StC, S1 => Some (mkTrans S1 DR StB)
  | StD, S0 => Some (mkTrans S1 DL StC)
  | StD, S1 => Some (mkTrans S1 DR StD)
  end.

Theorem qhb_0050 :
  NonHalt tm_qhb_0050
  /\ (forall q' s', QuietAfter tm_qhb_0050 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0050.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 120 8).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0051 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S0 DR StD)
  | StC, S0 => Some (mkTrans S1 DR StB)
  | StC, S1 => Some (mkTrans S1 DL StC)
  | StD, S0 => Some (mkTrans S0 DL StD)
  | StD, S1 => Some (mkTrans S1 DL StB)
  end.

Theorem qhb_0051 :
  NonHalt tm_qhb_0051
  /\ (forall q' s', QuietAfter tm_qhb_0051 q' s' -> S s' <= S 1024)
  /\ QuasiHaltsSt tm_qhb_0051.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 1024 168 9).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0052 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S0 DR StD)
  | StC, S0 => Some (mkTrans S1 DR StB)
  | StC, S1 => Some (mkTrans S1 DL StC)
  | StD, S0 => Some (mkTrans S1 DL StD)
  | StD, S1 => Some (mkTrans S0 DL StB)
  end.

Theorem qhb_0052 :
  NonHalt tm_qhb_0052
  /\ (forall q' s', QuietAfter tm_qhb_0052 q' s' -> S s' <= S 1024)
  /\ QuasiHaltsSt tm_qhb_0052.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 1024 184 10).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0053 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S0 DR StD)
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S0 DR StB)
  | StD, S0 => Some (mkTrans S1 DL StC)
  | StD, S1 => Some (mkTrans S0 DR StC)
  end.

Theorem qhb_0053 :
  NonHalt tm_qhb_0053
  /\ (forall q' s', QuietAfter tm_qhb_0053 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0053.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 136 8).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0054 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S0 DR StD)
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S0 DR StB)
  | StD, S0 => Some (mkTrans S1 DL StC)
  | StD, S1 => Some (mkTrans S1 DR StC)
  end.

Theorem qhb_0054 :
  NonHalt tm_qhb_0054
  /\ (forall q' s', QuietAfter tm_qhb_0054 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0054.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 136 9).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0055 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S0 DR StD)
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S0 DR StB)
  | StD, S0 => Some (mkTrans S1 DL StC)
  | StD, S1 => Some (mkTrans S1 DR StD)
  end.

Theorem qhb_0055 :
  NonHalt tm_qhb_0055
  /\ (forall q' s', QuietAfter tm_qhb_0055 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0055.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 120 8).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0056 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S0 DR StD)
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S1 DL StC)
  | StD, S0 => Some (mkTrans S0 DL StC)
  | StD, S1 => Some (mkTrans S1 DL StB)
  end.

Theorem qhb_0056 :
  NonHalt tm_qhb_0056
  /\ (forall q' s', QuietAfter tm_qhb_0056 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0056.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 144 8).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0057 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S0 DR StD)
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S1 DL StC)
  | StD, S0 => Some (mkTrans S1 DL StC)
  | StD, S1 => Some (mkTrans S1 DL StB)
  end.

Theorem qhb_0057 :
  NonHalt tm_qhb_0057
  /\ (forall q' s', QuietAfter tm_qhb_0057 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0057.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 152 8).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0058 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S0 DR StD)
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S1 DR StB)
  | StD, S0 => Some (mkTrans S1 DL StC)
  | StD, S1 => Some (mkTrans S0 DR StC)
  end.

Theorem qhb_0058 :
  NonHalt tm_qhb_0058
  /\ (forall q' s', QuietAfter tm_qhb_0058 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0058.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 136 9).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0059 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S0 DR StD)
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S1 DR StB)
  | StD, S0 => Some (mkTrans S1 DL StC)
  | StD, S1 => Some (mkTrans S1 DR StC)
  end.

Theorem qhb_0059 :
  NonHalt tm_qhb_0059
  /\ (forall q' s', QuietAfter tm_qhb_0059 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0059.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 136 8).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0060 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S0 DR StD)
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S1 DR StB)
  | StD, S0 => Some (mkTrans S1 DL StC)
  | StD, S1 => Some (mkTrans S1 DR StD)
  end.

Theorem qhb_0060 :
  NonHalt tm_qhb_0060
  /\ (forall q' s', QuietAfter tm_qhb_0060 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0060.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 128 8).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0061 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S1 DL StB)
  | StC, S0 => Some (mkTrans S0 DL StD)
  | StC, S1 => Some (mkTrans S0 DL StB)
  | StD, S0 => Some (mkTrans S1 DR StC)
  | StD, S1 => Some (mkTrans S1 DL StD)
  end.

Theorem qhb_0061 :
  NonHalt tm_qhb_0061
  /\ (forall q' s', QuietAfter tm_qhb_0061 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0061.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 144 8).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0062 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S1 DL StB)
  | StC, S0 => Some (mkTrans S0 DL StD)
  | StC, S1 => Some (mkTrans S1 DL StB)
  | StD, S0 => Some (mkTrans S1 DR StC)
  | StD, S1 => Some (mkTrans S1 DL StD)
  end.

Theorem qhb_0062 :
  NonHalt tm_qhb_0062
  /\ (forall q' s', QuietAfter tm_qhb_0062 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0062.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 144 9).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0063 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S1 DL StB)
  | StC, S0 => Some (mkTrans S0 DL StD)
  | StC, S1 => Some (mkTrans S1 DL StD)
  | StD, S0 => Some (mkTrans S1 DR StB)
  | StD, S1 => None
  end.

Theorem qhb_0063 :
  NonHalt tm_qhb_0063
  /\ (forall q' s', QuietAfter tm_qhb_0063 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0063.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 144 9).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0064 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S1 DL StB)
  | StC, S0 => Some (mkTrans S0 DL StD)
  | StC, S1 => Some (mkTrans S1 DL StD)
  | StD, S0 => Some (mkTrans S1 DR StC)
  | StD, S1 => Some (mkTrans S1 DR StB)
  end.

Theorem qhb_0064 :
  NonHalt tm_qhb_0064
  /\ (forall q' s', QuietAfter tm_qhb_0064 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0064.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 192 9).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0065 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S1 DL StB)
  | StC, S0 => Some (mkTrans S1 DL StD)
  | StC, S1 => Some (mkTrans S0 DL StD)
  | StD, S0 => Some (mkTrans S1 DR StC)
  | StD, S1 => Some (mkTrans S1 DR StB)
  end.

Theorem qhb_0065 :
  NonHalt tm_qhb_0065
  /\ (forall q' s', QuietAfter tm_qhb_0065 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0065.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 192 9).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0066 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S1 DL StB)
  | StC, S0 => Some (mkTrans S1 DR StB)
  | StC, S1 => Some (mkTrans S1 DR StD)
  | StD, S0 => Some (mkTrans S0 DL StD)
  | StD, S1 => Some (mkTrans S1 DL StC)
  end.

Theorem qhb_0066 :
  NonHalt tm_qhb_0066
  /\ (forall q' s', QuietAfter tm_qhb_0066 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0066.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 160 9).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0067 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S1 DL StB)
  | StC, S0 => Some (mkTrans S1 DR StB)
  | StC, S1 => Some (mkTrans S1 DR StD)
  | StD, S0 => Some (mkTrans S1 DL StD)
  | StD, S1 => Some (mkTrans S1 DL StC)
  end.

Theorem qhb_0067 :
  NonHalt tm_qhb_0067
  /\ (forall q' s', QuietAfter tm_qhb_0067 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0067.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 160 8).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0068 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S1 DL StB)
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S0 DR StB)
  | StD, S0 => Some (mkTrans S0 DL StD)
  | StD, S1 => Some (mkTrans S1 DL StC)
  end.

Theorem qhb_0068 :
  NonHalt tm_qhb_0068
  /\ (forall q' s', QuietAfter tm_qhb_0068 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0068.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 144 8).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0069 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S1 DL StB)
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S0 DR StB)
  | StD, S0 => Some (mkTrans S1 DL StD)
  | StD, S1 => Some (mkTrans S1 DL StC)
  end.

Theorem qhb_0069 :
  NonHalt tm_qhb_0069
  /\ (forall q' s', QuietAfter tm_qhb_0069 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0069.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 152 8).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0070 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S1 DL StB)
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S1 DL StC)
  | StD, S0 => Some (mkTrans S1 DL StC)
  | StD, S1 => Some (mkTrans S1 DR StB)
  end.

Theorem qhb_0070 :
  NonHalt tm_qhb_0070
  /\ (forall q' s', QuietAfter tm_qhb_0070 q' s' -> S s' <= S 1024)
  /\ QuasiHaltsSt tm_qhb_0070.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 1024 176 9).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0071 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S1 DL StB)
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S1 DR StB)
  | StD, S0 => Some (mkTrans S0 DL StD)
  | StD, S1 => Some (mkTrans S1 DL StC)
  end.

Theorem qhb_0071 :
  NonHalt tm_qhb_0071
  /\ (forall q' s', QuietAfter tm_qhb_0071 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0071.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 160 9).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0072 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S1 DL StB)
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S1 DR StB)
  | StD, S0 => Some (mkTrans S1 DL StD)
  | StD, S1 => Some (mkTrans S1 DL StC)
  end.

Theorem qhb_0072 :
  NonHalt tm_qhb_0072
  /\ (forall q' s', QuietAfter tm_qhb_0072 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0072.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 160 8).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0073 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S1 DL StC)
  | StC, S0 => Some (mkTrans S0 DL StD)
  | StC, S1 => Some (mkTrans S0 DL StB)
  | StD, S0 => Some (mkTrans S1 DR StC)
  | StD, S1 => Some (mkTrans S1 DL StD)
  end.

Theorem qhb_0073 :
  NonHalt tm_qhb_0073
  /\ (forall q' s', QuietAfter tm_qhb_0073 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0073.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 128 8).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0074 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S1 DL StC)
  | StC, S0 => Some (mkTrans S0 DL StD)
  | StC, S1 => Some (mkTrans S1 DL StB)
  | StD, S0 => Some (mkTrans S1 DR StC)
  | StD, S1 => Some (mkTrans S1 DL StD)
  end.

Theorem qhb_0074 :
  NonHalt tm_qhb_0074
  /\ (forall q' s', QuietAfter tm_qhb_0074 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0074.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 136 9).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0075 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S1 DL StC)
  | StC, S0 => Some (mkTrans S1 DR StB)
  | StC, S1 => Some (mkTrans S1 DR StD)
  | StD, S0 => Some (mkTrans S0 DL StB)
  | StD, S1 => Some (mkTrans S1 DL StD)
  end.

Theorem qhb_0075 :
  NonHalt tm_qhb_0075
  /\ (forall q' s', QuietAfter tm_qhb_0075 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0075.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 192 9).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0076 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S1 DL StC)
  | StC, S0 => Some (mkTrans S1 DR StB)
  | StC, S1 => Some (mkTrans S1 DR StD)
  | StD, S0 => Some (mkTrans S1 DL StB)
  | StD, S1 => Some (mkTrans S0 DL StD)
  end.

Theorem qhb_0076 :
  NonHalt tm_qhb_0076
  /\ (forall q' s', QuietAfter tm_qhb_0076 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0076.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 192 9).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0077 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S1 DL StC)
  | StC, S0 => Some (mkTrans S1 DR StB)
  | StC, S1 => Some (mkTrans S1 DR StD)
  | StD, S0 => Some (mkTrans S1 DL StB)
  | StD, S1 => Some (mkTrans S1 DL StD)
  end.

Theorem qhb_0077 :
  NonHalt tm_qhb_0077
  /\ (forall q' s', QuietAfter tm_qhb_0077 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0077.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 192 8).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0078 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S1 DL StC)
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S0 DL StB)
  | StD, S0 => Some (mkTrans S0 DL StB)
  | StD, S1 => Some (mkTrans S0 DR StB)
  end.

Theorem qhb_0078 :
  NonHalt tm_qhb_0078
  /\ (forall q' s', QuietAfter tm_qhb_0078 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0078.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 216 9).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0079 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S1 DL StC)
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S0 DL StB)
  | StD, S0 => Some (mkTrans S0 DL StB)
  | StD, S1 => Some (mkTrans S1 DR StD)
  end.

Theorem qhb_0079 :
  NonHalt tm_qhb_0079
  /\ (forall q' s', QuietAfter tm_qhb_0079 q' s' -> S s' <= S 1024)
  /\ QuasiHaltsSt tm_qhb_0079.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 1024 176 9).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0080 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S1 DL StC)
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S0 DL StB)
  | StD, S0 => Some (mkTrans S1 DL StB)
  | StD, S1 => Some (mkTrans S1 DR StC)
  end.

Theorem qhb_0080 :
  NonHalt tm_qhb_0080
  /\ (forall q' s', QuietAfter tm_qhb_0080 q' s' -> S s' <= S 1024)
  /\ QuasiHaltsSt tm_qhb_0080.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 1024 152 9).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0081 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S1 DL StC)
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S0 DL StB)
  | StD, S0 => Some (mkTrans S1 DR StB)
  | StD, S1 => Some (mkTrans S1 DL StC)
  end.

Theorem qhb_0081 :
  NonHalt tm_qhb_0081
  /\ (forall q' s', QuietAfter tm_qhb_0081 q' s' -> S s' <= S 256)
  /\ QuasiHaltsSt tm_qhb_0081.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 256 176 9).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0082 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S1 DL StC)
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S0 DL StB)
  | StD, S0 => Some (mkTrans S1 DR StB)
  | StD, S1 => Some (mkTrans S1 DL StD)
  end.

Theorem qhb_0082 :
  NonHalt tm_qhb_0082
  /\ (forall q' s', QuietAfter tm_qhb_0082 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0082.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 216 10).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0083 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S1 DL StC)
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => Some (mkTrans S0 DL StB)
  | StD, S1 => Some (mkTrans S1 DL StC)
  end.

Theorem qhb_0083 :
  NonHalt tm_qhb_0083
  /\ (forall q' s', QuietAfter tm_qhb_0083 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0083.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 120 8).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0084 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S1 DL StC)
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => Some (mkTrans S1 DL StB)
  | StD, S1 => Some (mkTrans S0 DL StC)
  end.

Theorem qhb_0084 :
  NonHalt tm_qhb_0084
  /\ (forall q' s', QuietAfter tm_qhb_0084 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0084.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 120 8).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0085 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S1 DL StC)
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => Some (mkTrans S1 DL StB)
  | StD, S1 => Some (mkTrans S1 DL StC)
  end.

Theorem qhb_0085 :
  NonHalt tm_qhb_0085
  /\ (forall q' s', QuietAfter tm_qhb_0085 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0085.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 128 8).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0086 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S1 DL StC)
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S0 DR StD)
  | StD, S0 => Some (mkTrans S1 DL StB)
  | StD, S1 => Some (mkTrans S0 DL StC)
  end.

Theorem qhb_0086 :
  NonHalt tm_qhb_0086
  /\ (forall q' s', QuietAfter tm_qhb_0086 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0086.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 152 8).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0087 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S1 DL StC)
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S1 DL StB)
  | StD, S0 => Some (mkTrans S0 DL StB)
  | StD, S1 => Some (mkTrans S0 DR StB)
  end.

Theorem qhb_0087 :
  NonHalt tm_qhb_0087
  /\ (forall q' s', QuietAfter tm_qhb_0087 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0087.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 232 10).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0088 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S1 DL StC)
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S1 DL StB)
  | StD, S0 => Some (mkTrans S0 DL StB)
  | StD, S1 => Some (mkTrans S0 DR StD)
  end.

Theorem qhb_0088 :
  NonHalt tm_qhb_0088
  /\ (forall q' s', QuietAfter tm_qhb_0088 q' s' -> S s' <= S 1024)
  /\ QuasiHaltsSt tm_qhb_0088.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 1024 168 9).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0089 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S1 DL StC)
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S1 DL StB)
  | StD, S0 => Some (mkTrans S0 DL StB)
  | StD, S1 => Some (mkTrans S1 DR StD)
  end.

Theorem qhb_0089 :
  NonHalt tm_qhb_0089
  /\ (forall q' s', QuietAfter tm_qhb_0089 q' s' -> S s' <= S 1024)
  /\ QuasiHaltsSt tm_qhb_0089.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 1024 184 10).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0090 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S1 DL StC)
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S1 DL StB)
  | StD, S0 => Some (mkTrans S1 DL StB)
  | StD, S1 => Some (mkTrans S0 DR StC)
  end.

Theorem qhb_0090 :
  NonHalt tm_qhb_0090
  /\ (forall q' s', QuietAfter tm_qhb_0090 q' s' -> S s' <= S 1024)
  /\ QuasiHaltsSt tm_qhb_0090.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 1024 184 10).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0091 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S1 DL StC)
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S1 DL StB)
  | StD, S0 => Some (mkTrans S1 DL StB)
  | StD, S1 => Some (mkTrans S1 DR StC)
  end.

Theorem qhb_0091 :
  NonHalt tm_qhb_0091
  /\ (forall q' s', QuietAfter tm_qhb_0091 q' s' -> S s' <= S 1024)
  /\ QuasiHaltsSt tm_qhb_0091.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 1024 176 9).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0092 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S1 DL StC)
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S1 DL StB)
  | StD, S0 => Some (mkTrans S1 DR StB)
  | StD, S1 => Some (mkTrans S0 DL StC)
  end.

Theorem qhb_0092 :
  NonHalt tm_qhb_0092
  /\ (forall q' s', QuietAfter tm_qhb_0092 q' s' -> S s' <= S 256)
  /\ QuasiHaltsSt tm_qhb_0092.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 256 184 10).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0093 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S1 DL StC)
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S1 DL StB)
  | StD, S0 => Some (mkTrans S1 DR StB)
  | StD, S1 => Some (mkTrans S0 DL StD)
  end.

Theorem qhb_0093 :
  NonHalt tm_qhb_0093
  /\ (forall q' s', QuietAfter tm_qhb_0093 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0093.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 216 10).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0094 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S1 DL StC)
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S1 DL StB)
  | StD, S0 => Some (mkTrans S1 DR StB)
  | StD, S1 => Some (mkTrans S1 DL StC)
  end.

Theorem qhb_0094 :
  NonHalt tm_qhb_0094
  /\ (forall q' s', QuietAfter tm_qhb_0094 q' s' -> S s' <= S 256)
  /\ QuasiHaltsSt tm_qhb_0094.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 256 176 9).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0095 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S1 DL StC)
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S1 DL StB)
  | StD, S0 => Some (mkTrans S1 DR StB)
  | StD, S1 => Some (mkTrans S1 DL StD)
  end.

Theorem qhb_0095 :
  NonHalt tm_qhb_0095
  /\ (forall q' s', QuietAfter tm_qhb_0095 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0095.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 208 9).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0096 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S1 DL StD)
  | StC, S0 => Some (mkTrans S0 DL StD)
  | StC, S1 => Some (mkTrans S1 DL StD)
  | StD, S0 => Some (mkTrans S1 DR StB)
  | StD, S1 => Some (mkTrans S0 DL StB)
  end.

Theorem qhb_0096 :
  NonHalt tm_qhb_0096
  /\ (forall q' s', QuietAfter tm_qhb_0096 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0096.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 144 8).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0097 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S1 DL StD)
  | StC, S0 => Some (mkTrans S0 DL StD)
  | StC, S1 => Some (mkTrans S1 DL StD)
  | StD, S0 => Some (mkTrans S1 DR StB)
  | StD, S1 => Some (mkTrans S0 DL StC)
  end.

Theorem qhb_0097 :
  NonHalt tm_qhb_0097
  /\ (forall q' s', QuietAfter tm_qhb_0097 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0097.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 136 8).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0098 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S1 DL StD)
  | StC, S0 => Some (mkTrans S0 DL StD)
  | StC, S1 => Some (mkTrans S1 DL StD)
  | StD, S0 => Some (mkTrans S1 DR StB)
  | StD, S1 => Some (mkTrans S0 DL StD)
  end.

Theorem qhb_0098 :
  NonHalt tm_qhb_0098
  /\ (forall q' s', QuietAfter tm_qhb_0098 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0098.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 120 8).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0099 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S1 DL StD)
  | StC, S0 => Some (mkTrans S0 DL StD)
  | StC, S1 => Some (mkTrans S1 DL StD)
  | StD, S0 => Some (mkTrans S1 DR StB)
  | StD, S1 => Some (mkTrans S1 DL StB)
  end.

Theorem qhb_0099 :
  NonHalt tm_qhb_0099
  /\ (forall q' s', QuietAfter tm_qhb_0099 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0099.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 144 9).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0100 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S1 DL StD)
  | StC, S0 => Some (mkTrans S0 DL StD)
  | StC, S1 => Some (mkTrans S1 DL StD)
  | StD, S0 => Some (mkTrans S1 DR StB)
  | StD, S1 => Some (mkTrans S1 DL StC)
  end.

Theorem qhb_0100 :
  NonHalt tm_qhb_0100
  /\ (forall q' s', QuietAfter tm_qhb_0100 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0100.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 136 9).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0101 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S1 DL StD)
  | StC, S0 => Some (mkTrans S0 DR StD)
  | StC, S1 => Some (mkTrans S1 DL StB)
  | StD, S0 => Some (mkTrans S1 DR StB)
  | StD, S1 => Some (mkTrans S0 DL StB)
  end.

Theorem qhb_0101 :
  NonHalt tm_qhb_0101
  /\ (forall q' s', QuietAfter tm_qhb_0101 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0101.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 184 8).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0102 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S1 DL StD)
  | StC, S0 => Some (mkTrans S0 DR StD)
  | StC, S1 => Some (mkTrans S1 DL StD)
  | StD, S0 => Some (mkTrans S1 DR StB)
  | StD, S1 => Some (mkTrans S0 DL StD)
  end.

Theorem qhb_0102 :
  NonHalt tm_qhb_0102
  /\ (forall q' s', QuietAfter tm_qhb_0102 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0102.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 120 8).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0103 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S1 DL StD)
  | StC, S0 => Some (mkTrans S1 DL StA)
  | StC, S1 => Some (mkTrans S1 DL StD)
  | StD, S0 => Some (mkTrans S1 DR StB)
  | StD, S1 => Some (mkTrans S0 DL StD)
  end.

Theorem qhb_0103 :
  NonHalt tm_qhb_0103
  /\ (forall q' s', QuietAfter tm_qhb_0103 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0103.
Proof.
  apply (ngram_check_qhbound_sound _ StA 3 2 64 120 8).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0104 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S1 DL StD)
  | StC, S0 => Some (mkTrans S1 DL StD)
  | StC, S1 => Some (mkTrans S0 DL StB)
  | StD, S0 => Some (mkTrans S1 DR StB)
  | StD, S1 => Some (mkTrans S0 DL StD)
  end.

Theorem qhb_0104 :
  NonHalt tm_qhb_0104
  /\ (forall q' s', QuietAfter tm_qhb_0104 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0104.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 136 8).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0105 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S1 DL StD)
  | StC, S0 => Some (mkTrans S1 DL StD)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => Some (mkTrans S1 DR StB)
  | StD, S1 => Some (mkTrans S0 DL StD)
  end.

Theorem qhb_0105 :
  NonHalt tm_qhb_0105
  /\ (forall q' s', QuietAfter tm_qhb_0105 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0105.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 128 8).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0106 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S1 DL StD)
  | StC, S0 => Some (mkTrans S1 DL StD)
  | StC, S1 => Some (mkTrans S0 DR StB)
  | StD, S0 => Some (mkTrans S1 DR StB)
  | StD, S1 => Some (mkTrans S0 DL StD)
  end.

Theorem qhb_0106 :
  NonHalt tm_qhb_0106
  /\ (forall q' s', QuietAfter tm_qhb_0106 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0106.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 136 8).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0107 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S1 DL StD)
  | StC, S0 => Some (mkTrans S1 DL StD)
  | StC, S1 => Some (mkTrans S1 DL StB)
  | StD, S0 => Some (mkTrans S1 DR StB)
  | StD, S1 => Some (mkTrans S0 DL StD)
  end.

Theorem qhb_0107 :
  NonHalt tm_qhb_0107
  /\ (forall q' s', QuietAfter tm_qhb_0107 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0107.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 136 8).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0108 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S1 DL StD)
  | StC, S0 => Some (mkTrans S1 DL StD)
  | StC, S1 => Some (mkTrans S1 DL StC)
  | StD, S0 => Some (mkTrans S1 DR StB)
  | StD, S1 => Some (mkTrans S0 DL StD)
  end.

Theorem qhb_0108 :
  NonHalt tm_qhb_0108
  /\ (forall q' s', QuietAfter tm_qhb_0108 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0108.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 136 9).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0109 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S1 DL StD)
  | StC, S0 => Some (mkTrans S1 DL StD)
  | StC, S1 => Some (mkTrans S1 DL StD)
  | StD, S0 => Some (mkTrans S1 DR StB)
  | StD, S1 => Some (mkTrans S0 DL StD)
  end.

Theorem qhb_0109 :
  NonHalt tm_qhb_0109
  /\ (forall q' s', QuietAfter tm_qhb_0109 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0109.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 120 8).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0110 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S1 DL StD)
  | StC, S0 => Some (mkTrans S1 DR StB)
  | StC, S1 => Some (mkTrans S1 DL StC)
  | StD, S0 => None
  | StD, S1 => Some (mkTrans S0 DL StC)
  end.

Theorem qhb_0110 :
  NonHalt tm_qhb_0110
  /\ (forall q' s', QuietAfter tm_qhb_0110 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0110.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 120 8).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0111 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S1 DL StD)
  | StC, S0 => Some (mkTrans S1 DR StB)
  | StC, S1 => Some (mkTrans S1 DL StC)
  | StD, S0 => Some (mkTrans S0 DL StB)
  | StD, S1 => Some (mkTrans S0 DR StB)
  end.

Theorem qhb_0111 :
  NonHalt tm_qhb_0111
  /\ (forall q' s', QuietAfter tm_qhb_0111 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0111.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 160 8).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0112 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S1 DL StD)
  | StC, S0 => Some (mkTrans S1 DR StB)
  | StC, S1 => Some (mkTrans S1 DL StC)
  | StD, S0 => Some (mkTrans S0 DL StC)
  | StD, S1 => Some (mkTrans S0 DR StB)
  end.

Theorem qhb_0112 :
  NonHalt tm_qhb_0112
  /\ (forall q' s', QuietAfter tm_qhb_0112 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0112.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 144 8).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0113 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S1 DL StD)
  | StC, S0 => Some (mkTrans S1 DR StB)
  | StC, S1 => Some (mkTrans S1 DL StC)
  | StD, S0 => Some (mkTrans S1 DL StB)
  | StD, S1 => Some (mkTrans S0 DR StB)
  end.

Theorem qhb_0113 :
  NonHalt tm_qhb_0113
  /\ (forall q' s', QuietAfter tm_qhb_0113 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0113.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 160 9).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0114 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S1 DL StD)
  | StC, S0 => Some (mkTrans S1 DR StB)
  | StC, S1 => Some (mkTrans S1 DL StD)
  | StD, S0 => Some (mkTrans S1 DR StB)
  | StD, S1 => Some (mkTrans S0 DL StD)
  end.

Theorem qhb_0114 :
  NonHalt tm_qhb_0114
  /\ (forall q' s', QuietAfter tm_qhb_0114 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0114.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 120 8).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0115 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S1 DL StD)
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S1 DL StC)
  | StD, S0 => Some (mkTrans S1 DR StB)
  | StD, S1 => Some (mkTrans S0 DL StB)
  end.

Theorem qhb_0115 :
  NonHalt tm_qhb_0115
  /\ (forall q' s', QuietAfter tm_qhb_0115 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0115.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 200 9).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0116 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S1 DL StD)
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S1 DL StD)
  | StD, S0 => Some (mkTrans S1 DR StB)
  | StD, S1 => Some (mkTrans S0 DL StD)
  end.

Theorem qhb_0116 :
  NonHalt tm_qhb_0116
  /\ (forall q' s', QuietAfter tm_qhb_0116 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0116.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 120 8).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0117 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StB)
  | StC, S0 => Some (mkTrans S0 DL StD)
  | StC, S1 => Some (mkTrans S1 DL StD)
  | StD, S0 => Some (mkTrans S1 DR StB)
  | StD, S1 => Some (mkTrans S0 DL StD)
  end.

Theorem qhb_0117 :
  NonHalt tm_qhb_0117
  /\ (forall q' s', QuietAfter tm_qhb_0117 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0117.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 160 9).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0118 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StB)
  | StC, S0 => Some (mkTrans S0 DR StD)
  | StC, S1 => Some (mkTrans S1 DL StD)
  | StD, S0 => Some (mkTrans S1 DR StB)
  | StD, S1 => Some (mkTrans S0 DL StD)
  end.

Theorem qhb_0118 :
  NonHalt tm_qhb_0118
  /\ (forall q' s', QuietAfter tm_qhb_0118 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0118.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 160 9).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0119 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StB)
  | StC, S0 => Some (mkTrans S1 DL StD)
  | StC, S1 => Some (mkTrans S1 DR StD)
  | StD, S0 => Some (mkTrans S0 DR StB)
  | StD, S1 => Some (mkTrans S0 DL StD)
  end.

Theorem qhb_0119 :
  NonHalt tm_qhb_0119
  /\ (forall q' s', QuietAfter tm_qhb_0119 q' s' -> S s' <= S 256)
  /\ QuasiHaltsSt tm_qhb_0119.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 256 288 10).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0120 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StC)
  | StC, S0 => Some (mkTrans S0 DR StD)
  | StC, S1 => Some (mkTrans S0 DR StB)
  | StD, S0 => Some (mkTrans S1 DL StC)
  | StD, S1 => Some (mkTrans S1 DR StD)
  end.

Theorem qhb_0120 :
  NonHalt tm_qhb_0120
  /\ (forall q' s', QuietAfter tm_qhb_0120 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0120.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 128 8).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0121 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StC)
  | StC, S0 => Some (mkTrans S0 DR StD)
  | StC, S1 => Some (mkTrans S1 DR StB)
  | StD, S0 => Some (mkTrans S1 DL StC)
  | StD, S1 => Some (mkTrans S1 DR StD)
  end.

Theorem qhb_0121 :
  NonHalt tm_qhb_0121
  /\ (forall q' s', QuietAfter tm_qhb_0121 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0121.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 136 9).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0122 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StC)
  | StC, S0 => Some (mkTrans S1 DL StD)
  | StC, S1 => Some (mkTrans S0 DR StC)
  | StD, S0 => Some (mkTrans S0 DR StB)
  | StD, S1 => Some (mkTrans S1 DR StC)
  end.

Theorem qhb_0122 :
  NonHalt tm_qhb_0122
  /\ (forall q' s', QuietAfter tm_qhb_0122 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0122.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 120 8).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0123 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StC)
  | StC, S0 => Some (mkTrans S1 DL StD)
  | StC, S1 => Some (mkTrans S0 DR StC)
  | StD, S0 => Some (mkTrans S1 DR StB)
  | StD, S1 => Some (mkTrans S0 DR StC)
  end.

Theorem qhb_0123 :
  NonHalt tm_qhb_0123
  /\ (forall q' s', QuietAfter tm_qhb_0123 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0123.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 120 8).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0124 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StC)
  | StC, S0 => Some (mkTrans S1 DL StD)
  | StC, S1 => Some (mkTrans S0 DR StC)
  | StD, S0 => Some (mkTrans S1 DR StB)
  | StD, S1 => Some (mkTrans S1 DR StC)
  end.

Theorem qhb_0124 :
  NonHalt tm_qhb_0124
  /\ (forall q' s', QuietAfter tm_qhb_0124 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0124.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 128 8).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0125 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StC)
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S0 DR StD)
  | StD, S0 => Some (mkTrans S1 DL StB)
  | StD, S1 => Some (mkTrans S0 DL StC)
  end.

Theorem qhb_0125 :
  NonHalt tm_qhb_0125
  /\ (forall q' s', QuietAfter tm_qhb_0125 q' s' -> S s' <= S 1024)
  /\ QuasiHaltsSt tm_qhb_0125.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 1024 352 10).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0126 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StD)
  | StC, S0 => Some (mkTrans S1 DL StA)
  | StC, S1 => Some (mkTrans S1 DL StD)
  | StD, S0 => Some (mkTrans S1 DR StB)
  | StD, S1 => Some (mkTrans S0 DR StD)
  end.

Theorem qhb_0126 :
  NonHalt tm_qhb_0126
  /\ (forall q' s', QuietAfter tm_qhb_0126 q' s' -> S s' <= S 256)
  /\ QuasiHaltsSt tm_qhb_0126.
Proof.
  apply (ngram_check_qhbound_sound _ StA 3 2 256 224 9).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0127 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StD)
  | StC, S0 => Some (mkTrans S1 DL StD)
  | StC, S1 => Some (mkTrans S0 DR StB)
  | StD, S0 => Some (mkTrans S1 DR StB)
  | StD, S1 => Some (mkTrans S0 DR StD)
  end.

Theorem qhb_0127 :
  NonHalt tm_qhb_0127
  /\ (forall q' s', QuietAfter tm_qhb_0127 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0127.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 272 9).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0128 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StD)
  | StC, S0 => Some (mkTrans S1 DL StD)
  | StC, S1 => Some (mkTrans S0 DR StD)
  | StD, S0 => Some (mkTrans S0 DR StB)
  | StD, S1 => Some (mkTrans S1 DR StC)
  end.

Theorem qhb_0128 :
  NonHalt tm_qhb_0128
  /\ (forall q' s', QuietAfter tm_qhb_0128 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0128.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 184 8).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0129 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StD)
  | StC, S0 => Some (mkTrans S1 DL StD)
  | StC, S1 => Some (mkTrans S1 DL StC)
  | StD, S0 => Some (mkTrans S1 DR StB)
  | StD, S1 => Some (mkTrans S0 DL StD)
  end.

Theorem qhb_0129 :
  NonHalt tm_qhb_0129
  /\ (forall q' s', QuietAfter tm_qhb_0129 q' s' -> S s' <= S 256)
  /\ QuasiHaltsSt tm_qhb_0129.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 256 184 10).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0130 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StD)
  | StC, S0 => Some (mkTrans S1 DL StD)
  | StC, S1 => Some (mkTrans S1 DL StD)
  | StD, S0 => Some (mkTrans S1 DR StB)
  | StD, S1 => Some (mkTrans S0 DR StD)
  end.

Theorem qhb_0130 :
  NonHalt tm_qhb_0130
  /\ (forall q' s', QuietAfter tm_qhb_0130 q' s' -> S s' <= S 256)
  /\ QuasiHaltsSt tm_qhb_0130.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 256 224 9).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0131 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StD)
  | StC, S0 => Some (mkTrans S1 DR StB)
  | StC, S1 => Some (mkTrans S0 DR StD)
  | StD, S0 => Some (mkTrans S1 DL StC)
  | StD, S1 => Some (mkTrans S0 DR StD)
  end.

Theorem qhb_0131 :
  NonHalt tm_qhb_0131
  /\ (forall q' s', QuietAfter tm_qhb_0131 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0131.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 120 8).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0132 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StD)
  | StC, S0 => Some (mkTrans S1 DR StB)
  | StC, S1 => Some (mkTrans S1 DR StD)
  | StD, S0 => Some (mkTrans S1 DL StC)
  | StD, S1 => Some (mkTrans S0 DR StD)
  end.

Theorem qhb_0132 :
  NonHalt tm_qhb_0132
  /\ (forall q' s', QuietAfter tm_qhb_0132 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0132.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 128 8).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0133 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => Some (mkTrans S1 DR StD)
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S1 DL StD)
  | StD, S0 => Some (mkTrans S1 DR StB)
  | StD, S1 => Some (mkTrans S0 DR StD)
  end.

Theorem qhb_0133 :
  NonHalt tm_qhb_0133
  /\ (forall q' s', QuietAfter tm_qhb_0133 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0133.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 224 9).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0134 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DR StC)
  | StB, S1 => None
  | StC, S0 => Some (mkTrans S0 DL StD)
  | StC, S1 => Some (mkTrans S1 DL StC)
  | StD, S0 => Some (mkTrans S1 DR StC)
  | StD, S1 => Some (mkTrans S1 DL StD)
  end.

Theorem qhb_0134 :
  NonHalt tm_qhb_0134
  /\ (forall q' s', QuietAfter tm_qhb_0134 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0134.
Proof.
  apply (ngram_check_qhbound_sound _ StB 1 2 64 136 9).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0135 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DR StC)
  | StB, S1 => None
  | StC, S0 => Some (mkTrans S0 DR StD)
  | StC, S1 => Some (mkTrans S1 DR StC)
  | StD, S0 => Some (mkTrans S1 DL StC)
  | StD, S1 => Some (mkTrans S1 DR StD)
  end.

Theorem qhb_0135 :
  NonHalt tm_qhb_0135
  /\ (forall q' s', QuietAfter tm_qhb_0135 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0135.
Proof.
  apply (ngram_check_qhbound_sound _ StB 1 2 64 136 9).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0136 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DR StC)
  | StB, S1 => None
  | StC, S0 => Some (mkTrans S1 DL StD)
  | StC, S1 => Some (mkTrans S0 DR StC)
  | StD, S0 => Some (mkTrans S0 DR StD)
  | StD, S1 => Some (mkTrans S1 DR StC)
  end.

Theorem qhb_0136 :
  NonHalt tm_qhb_0136
  /\ (forall q' s', QuietAfter tm_qhb_0136 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0136.
Proof.
  apply (ngram_check_qhbound_sound _ StB 1 2 64 120 8).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0137 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DR StC)
  | StB, S1 => None
  | StC, S0 => Some (mkTrans S1 DL StD)
  | StC, S1 => Some (mkTrans S0 DR StC)
  | StD, S0 => Some (mkTrans S1 DR StD)
  | StD, S1 => Some (mkTrans S1 DR StC)
  end.

Theorem qhb_0137 :
  NonHalt tm_qhb_0137
  /\ (forall q' s', QuietAfter tm_qhb_0137 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0137.
Proof.
  apply (ngram_check_qhbound_sound _ StB 1 2 64 128 8).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0138 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DR StC)
  | StB, S1 => None
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => Some (mkTrans S0 DL StD)
  | StD, S1 => Some (mkTrans S1 DL StC)
  end.

Theorem qhb_0138 :
  NonHalt tm_qhb_0138
  /\ (forall q' s', QuietAfter tm_qhb_0138 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0138.
Proof.
  apply (ngram_check_qhbound_sound _ StB 1 2 64 120 8).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0139 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DR StC)
  | StB, S1 => None
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => Some (mkTrans S1 DL StD)
  | StD, S1 => Some (mkTrans S1 DL StC)
  end.

Theorem qhb_0139 :
  NonHalt tm_qhb_0139
  /\ (forall q' s', QuietAfter tm_qhb_0139 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0139.
Proof.
  apply (ngram_check_qhbound_sound _ StB 1 2 64 128 8).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0140 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DR StC)
  | StB, S1 => Some (mkTrans S0 DL StB)
  | StC, S0 => Some (mkTrans S0 DL StD)
  | StC, S1 => Some (mkTrans S1 DR StC)
  | StD, S0 => Some (mkTrans S1 DL StB)
  | StD, S1 => Some (mkTrans S1 DR StB)
  end.

Theorem qhb_0140 :
  NonHalt tm_qhb_0140
  /\ (forall q' s', QuietAfter tm_qhb_0140 q' s' -> S s' <= S 1024)
  /\ QuasiHaltsSt tm_qhb_0140.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 1024 288 10).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0141 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DR StC)
  | StB, S1 => Some (mkTrans S0 DL StB)
  | StC, S0 => Some (mkTrans S1 DL StD)
  | StC, S1 => Some (mkTrans S1 DR StD)
  | StD, S0 => Some (mkTrans S1 DL StB)
  | StD, S1 => Some (mkTrans S0 DL StD)
  end.

Theorem qhb_0141 :
  NonHalt tm_qhb_0141
  /\ (forall q' s', QuietAfter tm_qhb_0141 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0141.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 248 9).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0142 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DR StC)
  | StB, S1 => Some (mkTrans S0 DL StB)
  | StC, S0 => Some (mkTrans S1 DL StD)
  | StC, S1 => Some (mkTrans S1 DR StD)
  | StD, S0 => Some (mkTrans S1 DL StB)
  | StD, S1 => Some (mkTrans S1 DR StB)
  end.

Theorem qhb_0142 :
  NonHalt tm_qhb_0142
  /\ (forall q' s', QuietAfter tm_qhb_0142 q' s' -> S s' <= S 256)
  /\ QuasiHaltsSt tm_qhb_0142.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 3 256 248 14).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0143 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DR StC)
  | StB, S1 => Some (mkTrans S0 DL StB)
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S0 DL StC)
  | StD, S0 => Some (mkTrans S1 DL StB)
  | StD, S1 => Some (mkTrans S1 DL StD)
  end.

Theorem qhb_0143 :
  NonHalt tm_qhb_0143
  /\ (forall q' s', QuietAfter tm_qhb_0143 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0143.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 192 8).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0144 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DR StC)
  | StB, S1 => Some (mkTrans S0 DL StC)
  | StC, S0 => Some (mkTrans S0 DL StD)
  | StC, S1 => Some (mkTrans S1 DL StB)
  | StD, S0 => Some (mkTrans S1 DR StC)
  | StD, S1 => Some (mkTrans S1 DL StD)
  end.

Theorem qhb_0144 :
  NonHalt tm_qhb_0144
  /\ (forall q' s', QuietAfter tm_qhb_0144 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0144.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 136 8).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0145 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DR StC)
  | StB, S1 => Some (mkTrans S0 DL StC)
  | StC, S0 => Some (mkTrans S0 DR StD)
  | StC, S1 => Some (mkTrans S1 DR StB)
  | StD, S0 => Some (mkTrans S1 DL StC)
  | StD, S1 => Some (mkTrans S1 DR StD)
  end.

Theorem qhb_0145 :
  NonHalt tm_qhb_0145
  /\ (forall q' s', QuietAfter tm_qhb_0145 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0145.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 160 8).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0146 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DR StC)
  | StB, S1 => Some (mkTrans S0 DL StC)
  | StC, S0 => Some (mkTrans S1 DL StD)
  | StC, S1 => Some (mkTrans S0 DR StD)
  | StD, S0 => Some (mkTrans S1 DL StB)
  | StD, S1 => Some (mkTrans S1 DR StB)
  end.

Theorem qhb_0146 :
  NonHalt tm_qhb_0146
  /\ (forall q' s', QuietAfter tm_qhb_0146 q' s' -> S s' <= S 256)
  /\ QuasiHaltsSt tm_qhb_0146.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 256 384 11).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0147 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DR StC)
  | StB, S1 => Some (mkTrans S0 DL StC)
  | StC, S0 => Some (mkTrans S1 DL StD)
  | StC, S1 => Some (mkTrans S1 DR StD)
  | StD, S0 => Some (mkTrans S1 DL StB)
  | StD, S1 => Some (mkTrans S1 DR StB)
  end.

Theorem qhb_0147 :
  NonHalt tm_qhb_0147
  /\ (forall q' s', QuietAfter tm_qhb_0147 q' s' -> S s' <= S 1024)
  /\ QuasiHaltsSt tm_qhb_0147.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 1024 504 12).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0148 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DR StC)
  | StB, S1 => Some (mkTrans S0 DL StC)
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S1 DL StC)
  | StD, S0 => Some (mkTrans S0 DL StC)
  | StD, S1 => Some (mkTrans S1 DL StB)
  end.

Theorem qhb_0148 :
  NonHalt tm_qhb_0148
  /\ (forall q' s', QuietAfter tm_qhb_0148 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0148.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 120 8).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0149 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DR StC)
  | StB, S1 => Some (mkTrans S0 DL StC)
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S1 DL StC)
  | StD, S0 => Some (mkTrans S1 DL StC)
  | StD, S1 => Some (mkTrans S0 DL StB)
  end.

Theorem qhb_0149 :
  NonHalt tm_qhb_0149
  /\ (forall q' s', QuietAfter tm_qhb_0149 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0149.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 120 8).
  vm_compute. reflexivity.
Qed.

Definition tm_qhb_0150 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DR StC)
  | StB, S1 => Some (mkTrans S0 DL StC)
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S1 DL StC)
  | StD, S0 => Some (mkTrans S1 DL StC)
  | StD, S1 => Some (mkTrans S1 DL StB)
  end.

Theorem qhb_0150 :
  NonHalt tm_qhb_0150
  /\ (forall q' s', QuietAfter tm_qhb_0150 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qhb_0150.
Proof.
  apply (ngram_check_qhbound_sound _ StA 0 2 64 128 8).
  vm_compute. reflexivity.
Qed.
