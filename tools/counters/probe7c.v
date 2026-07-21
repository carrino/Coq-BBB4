From Coq Require Import Arith Lia Bool List PArith FunctionalExtensionality.
From BBB4 Require Import BBB4_Statement CTape Mirror.
From BBB4.Counters Require Import WTape WaveCounter.
Import ListNotations.
Definition mk (w : Sym) (d : Dir) (n : St) : option Trans := Some (mkTrans w d n).
(* the real #7 machine, side L *)
Definition tm_7 : TM := fun q s =>
  match q, s with
  | StA, S0 => mk S1 DR StB | StA, S1 => mk S0 DL StC
  | StB, S0 => mk S1 DL StA | StB, S1 => mk S1 DR StD
  | StC, S0 => mk S1 DL StA | StC, S1 => mk S1 DL StC
  | StD, S0 => mk S0 DR StD | StD, S1 => mk S1 DR StB
  end.
(* mirror (side R, edge A) *)
Definition tm_7m : TM := fun q s =>
  match q, s with
  | StA, S0 => mk S1 DL StB | StA, S1 => mk S0 DR StC
  | StB, S0 => mk S1 DR StA | StB, S1 => mk S1 DL StD
  | StC, S0 => mk S1 DR StA | StC, S1 => mk S1 DR StC
  | StD, S0 => mk S0 DL StD | StD, S1 => mk S1 DL StB
  end.
(* confirm mirror_tm tm_7 = tm_7m *)
Definition mirror_ok : mirror_tm tm_7 = tm_7m.
Proof. apply functional_extensionality; intro q; apply functional_extensionality; intro s;
  destruct q, s; reflexivity. Qed.

Fixpoint wbody (front : list nat) : list Sym :=
  match front with [] => [S1] | b :: r => rep [S1] b ++ S0 :: wbody r end.
Definition Cf7 (front : list nat) : cconf := (StA, (wbody front, S0, [])).

(* full passes *)
Compute (nextf 1 [4;2;1]).
Compute (ceqb match csteps tm_7m 12 (Cf7 [4;2;1]) with Some c=>c|None=>c0 end (Cf7 (nextf 1 [4;2;1]))).
Compute (ceqb match csteps tm_7m 22 (Cf7 [5;3;1]) with Some c=>c|None=>c0 end (Cf7 (nextf 1 [5;3;1]))).
Compute (ceqb match csteps tm_7m 38 (Cf7 [7;4;2]) with Some c=>c|None=>c0 end (Cf7 (nextf 1 [7;4;2]))).

(* FT 1-step, S1::L form *)
Compute (csteps tm_7m 1 (StA, (S1 :: [S1;S1;S0;S1], S0, []))).   (* Some(StB,([S1;S1;S0;S1],S1,[S1])) *)
(* cross_run7 starts StB alternate B/D, exit stB7 k *)
Compute (csteps tm_7m 1 (StB, ([], S1, [S1;S1]))).              (* k=0 *)
Compute (csteps tm_7m 2 (StB, ([S1], S1, [S1;S1]))).           (* k=1 *)
Compute (csteps tm_7m 3 (StB, ([S1;S1], S1, [S1;S1]))).       (* k=2 *)
Compute (csteps tm_7m 4 (StB, ([S1;S1;S1], S1, [S1;S1]))).   (* k=3 *)
(* sep-continue D0/0L>D : (StD,(S1::rest,S0,R)) -> (StD,(rest,S1,S0::R)) *)
Compute (csteps tm_7m 1 (StD, ([S1;S1;S0], S0, [S1]))).
(* deposit B0/1R>A : (StB,(X,S0,S1::R)) -> (StA,(S1::X,S1,R)) *)
Compute (csteps tm_7m 1 (StB, ([S0;S1], S0, [S1;S1]))).
(* spawn: entry StD (continue), target StA. try 1..3 steps from (StD,([S1],S0,R)) *)
Compute (csteps tm_7m 1 (StD, ([S1], S0, [S1;S1]))).
Compute (csteps tm_7m 2 (StD, ([S1], S0, [S1;S1]))).
Compute (csteps tm_7m 3 (StD, ([S1], S0, [S1;S1]))).
(* return start A1/0R>C : (StA,(L,S1,R)) -> (StC,(S0::L,chd R,ctl R)) *)
Compute (csteps tm_7m 1 (StA, ([S1;S0], S1, [S1;S1]))).
(* Csweep C1/1R>C to sep: (StC,(L,S1,rep[S1]k++S0::R)) -> (StC,(rep[S1](S k)++L,S0,R)) *)
Compute (csteps tm_7m 3 (StC, ([S0], S1, [S1;S1;S0;S1]))).
(* Csweep_blank (terminal region): (StC,(L,S1,rep[S1]k)) -> (StC,(rep[S1](S k)++L,S0,[])) *)
Compute (csteps tm_7m 3 (StC, ([S0], S1, [S1;S1]))).
(* terminal C0/1R>A writes 1: (StC,(L,S0,[])) -> (StA,(S1::L,S0,[])) *)
Compute (csteps tm_7m 1 (StC, ([S1;S1;S0], S0, []))).
(* junction C0/1R>A : (StC,(L,S0,X)) -> (StA,(S1::L,chd X,ctl X)) *)
Compute (csteps tm_7m 1 (StC, ([S1;S0], S0, [S1;S1]))).
