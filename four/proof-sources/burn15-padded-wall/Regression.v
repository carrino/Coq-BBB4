From Coq Require Import List NArith.
From BBB24 Require Import Statement.
From BBB24.Checkers Require Import NGramHist.
From BBB24Burn12HistoryMarker Require Import HistoryMarker.
From BBB24Burn15PaddedWall Require Import PaddedWall.
Import ListNotations.

Definition wall_tm : TM := fun _ s=>Some(match s with
 |S0=>mkTrans S3 DR StB|S1=>mkTrans S2 DR StA
 |S2=>mkTrans S2 DL StB|S3=>mkTrans S2 DL StA end).
Example positive_blank_rank_accepted :
 pw_rank_check wall_tm(pw_rank 1 0 0 0)=true.
Proof. reflexivity. Qed.
Example unchanged_leftward_instruction_accepted :
 pw_cell wall_tm(pw_rank 1 0 0 0)S2=true.
Proof. reflexivity. Qed.
Example closed_boundary_guard_accepted : pw_guard_check wall_tm(pw_guard 9%N)=true.
Proof. reflexivity. Qed.
Example missing_blank_guard_rejected : pw_guard_check wall_tm(pw_guard 8%N)=false.
Proof. reflexivity. Qed.
Example left_escape_guard_rejected : pw_guard_check wall_tm(pw_guard 13%N)=false.
Proof. reflexivity. Qed.
Example unguarded_wall_write_rejected : pw_guard_check wall_tm(pw_guard 1%N)=false.
Proof. reflexivity. Qed.
Example nondecreasing_right_step_rejected : pw_rank_check wall_tm(pw_rank 0 0 0 0)=false.
Proof. reflexivity. Qed.
Example one_blank_pad_installs_wall :
 pw_wall(pw_guard 9%N)(hm_pad 1(StB,([(S1,[])],(S2,[]),[]))).
Proof. reflexivity. Qed.
