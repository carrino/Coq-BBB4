(** Generated probe: lex-gated census-grade QHBound theorems for
    residue machines the PLAIN acyclicity gate rejects -- each closes
    via ngram_check_qhbound_lex_sound with an NgRankE/NgPattE
    certificate over the WRAPPED closure (see
    tools/sweep_qhbound_residue.py / NEXT_SESSION.md). *)
From Coq Require Import List ZArith.
From BBB4 Require Import BBB4_Statement CTape.
From BBB4.Checkers Require Import NGram Wrap.
Import ListNotations.


(** 0RB---_0LC---_1LD1RC_1RC1LD: quiet B s=1; lex-gated QHBound 64 (n=2 t=64, 12 ctx) *)

Definition tm_qlx_001 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => None
  | StC, S0 => Some (mkTrans S1 DL StD)
  | StC, S1 => Some (mkTrans S1 DR StC)
  | StD, S0 => Some (mkTrans S1 DR StC)
  | StD, S1 => Some (mkTrans S1 DL StD)
  end.

Definition cert_qlx_001 (q : St) : list ngcomp :=
  match q with
  | StA =>
  []
  | StB =>
  []
  | StC =>
  [NgRankE
    [(10047%positive, 2);
     (10111%positive, 4);
     (12079%positive, 1);
     (12095%positive, 2);
     (12159%positive, 3)];
   NgPattE [S1] RgL 1
    []
    [12159%positive];
   NgRankE
    [(10047%positive, 2);
     (10111%positive, 4);
     (12079%positive, 1);
     (12095%positive, 2);
     (12159%positive, 3)]]
  | StD =>
  [NgRankE
    [(9598%positive, 1);
     (10046%positive, 2);
     (10110%positive, 2);
     (12094%positive, 4);
     (12158%positive, 3)];
   NgPattE [S1] RgR 1
    []
    [12158%positive];
   NgRankE
    [(9598%positive, 1);
     (10046%positive, 2);
     (10110%positive, 2);
     (12094%positive, 4);
     (12158%positive, 3)]]
  end.

Theorem qlx_001 :
  NonHalt tm_qlx_001
  /\ (forall q' s', QuietAfter tm_qlx_001 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qlx_001.
Proof.
  apply (ngram_check_qhbound_lex_sound _ StB 1 2 64 160 10 cert_qlx_001).
  vm_compute. reflexivity.
Qed.

(** 0RB---_0LC---_1RD1LC_1LC1RD: quiet B s=1; lex-gated QHBound 64 (n=2 t=64, 12 ctx) *)

Definition tm_qlx_002 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => None
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S1 DL StC)
  | StD, S0 => Some (mkTrans S1 DL StC)
  | StD, S1 => Some (mkTrans S1 DR StD)
  end.

Definition cert_qlx_002 (q : St) : list ngcomp :=
  match q with
  | StA =>
  []
  | StB =>
  []
  | StC =>
  [NgRankE
    [(9599%positive, 1);
     (10047%positive, 2);
     (10111%positive, 2);
     (12095%positive, 4);
     (12159%positive, 3)];
   NgPattE [S1] RgR 1
    []
    [12159%positive];
   NgRankE
    [(9599%positive, 1);
     (10047%positive, 2);
     (10111%positive, 2);
     (12095%positive, 4);
     (12159%positive, 3)]]
  | StD =>
  [NgRankE
    [(10046%positive, 2);
     (10110%positive, 4);
     (12078%positive, 1);
     (12094%positive, 2);
     (12158%positive, 3)];
   NgPattE [S1] RgL 1
    []
    [12158%positive];
   NgRankE
    [(10046%positive, 2);
     (10110%positive, 4);
     (12078%positive, 1);
     (12094%positive, 2);
     (12158%positive, 3)]]
  end.

Theorem qlx_002 :
  NonHalt tm_qlx_002
  /\ (forall q' s', QuietAfter tm_qlx_002 q' s' -> S s' <= S 64)
  /\ QuasiHaltsSt tm_qlx_002.
Proof.
  apply (ngram_check_qhbound_lex_sound _ StB 1 2 64 160 10 cert_qlx_002).
  vm_compute. reflexivity.
Qed.

(** 0RB---_0LC---_1RD1LC_1RB1RD: quiet A s=0; lex-gated QHBound 1024 (n=2 t=1024, 16 ctx) *)

Definition tm_qlx_003 : TM := fun q s =>
  match q, s with
  | StA, S0 => Some (mkTrans S0 DR StB)
  | StA, S1 => None
  | StB, S0 => Some (mkTrans S0 DL StC)
  | StB, S1 => None
  | StC, S0 => Some (mkTrans S1 DR StD)
  | StC, S1 => Some (mkTrans S1 DL StC)
  | StD, S0 => Some (mkTrans S1 DR StB)
  | StD, S1 => Some (mkTrans S1 DR StD)
  end.

Definition cert_qlx_003 (q : St) : list ngcomp :=
  match q with
  | StA =>
  []
  | StB =>
  [NgRankE
    [(9534%positive, 7);
     (9598%positive, 10);
     (9599%positive, 1);
     (10030%positive, 6);
     (10046%positive, 7);
     (10047%positive, 2);
     (10110%positive, 9);
     (10111%positive, 2);
     (12074%positive, 5);
     (12078%positive, 6);
     (12094%positive, 7);
     (12095%positive, 4);
     (12158%positive, 8);
     (12159%positive, 3)];
   NgPattE [S1] RgR 1
    []
    [12159%positive];
   NgPattE [S1] RgL 1
    []
    [12158%positive];
   NgRankE
    [(9534%positive, 7);
     (9598%positive, 10);
     (9599%positive, 1);
     (10030%positive, 6);
     (10046%positive, 7);
     (10047%positive, 2);
     (10110%positive, 9);
     (10111%positive, 2);
     (12074%positive, 5);
     (12078%positive, 6);
     (12094%positive, 7);
     (12095%positive, 4);
     (12158%positive, 8);
     (12159%positive, 3)]]
  | StC =>
  [NgRankE
    [(9595%positive, 1);
     (9599%positive, 2);
     (10047%positive, 3);
     (10111%positive, 3);
     (12095%positive, 5);
     (12159%positive, 4)];
   NgPattE [S1] RgR 1
    []
    [12159%positive];
   NgRankE
    [(9595%positive, 1);
     (9599%positive, 2);
     (10047%positive, 3);
     (10111%positive, 3);
     (12095%positive, 5);
     (12159%positive, 4)]]
  | StD =>
  [NgRankE
    [(9534%positive, 2);
     (9593%positive, 6);
     (9598%positive, 5);
     (10030%positive, 1);
     (10046%positive, 2);
     (10110%positive, 4);
     (12078%positive, 1);
     (12094%positive, 2);
     (12158%positive, 3)];
   NgPattE [S1] RgL 1
    []
    [12158%positive];
   NgRankE
    [(9534%positive, 2);
     (9593%positive, 6);
     (9598%positive, 5);
     (10030%positive, 1);
     (10046%positive, 2);
     (10110%positive, 4);
     (12078%positive, 1);
     (12094%positive, 2);
     (12158%positive, 3)]]
  end.

Theorem qlx_003 :
  NonHalt tm_qlx_003
  /\ (forall q' s', QuietAfter tm_qlx_003 q' s' -> S s' <= S 1024)
  /\ QuasiHaltsSt tm_qlx_003.
Proof.
  apply (ngram_check_qhbound_lex_sound _ StA 0 2 1024 192 10 cert_qlx_003).
  vm_compute. reflexivity.
Qed.
