(** Symmetry reduction to seven concrete instruction-recurrence obligations,
    all discharged in Remaining23Solved. *)
From Coq Require Import List.
From SmallBB Require Import Statement StatementTr Size Bounds KnownCensus Mirror SwapSymbols Remaining23.
Import ListNotations.
(* 1LB2LB2RA_1RA2LB1RB *)
Definition remaining23_rep0:TM:=machine_of_codes 2 3 [5;9;10;6;9;7].
(* 1LB2RA0LB_1RB1RA1LA *)
Definition remaining23_rep1:TM:=machine_of_codes 2 3 [5;10;1;7;6;4].
(* 1LB2RA0LB_2RB1RA1LA *)
Definition remaining23_rep2:TM:=machine_of_codes 2 3 [5;10;1;11;6;4].
(* 1LB2RA1LA_1RA2LA2LB *)
Definition remaining23_rep3:TM:=machine_of_codes 2 3 [5;10;4;6;8;9].
(* 1LB2RA1LA_1RA2RA2LB *)
Definition remaining23_rep4:TM:=machine_of_codes 2 3 [5;10;4;6;10;9].
(* 1LB2RB0RB_1RA2LA0RB *)
Definition remaining23_rep5:TM:=machine_of_codes 2 3 [5;11;3;6;8;3].
(* 1LB2RB2RA_1RA2LB1RB *)
Definition remaining23_rep6:TM:=machine_of_codes 2 3 [5;11;10;6;9;7].
Definition remaining23_representatives:list TM:= [remaining23_rep0;remaining23_rep1;remaining23_rep2;remaining23_rep3;remaining23_rep4;remaining23_rep5;remaining23_rep6].
Lemma remaining23_reduce:Forall(QHBoundTr 67)remaining23_representatives->Forall(QHBoundTr 67)remaining23.
Proof.
 intro H. assert(Hnth:forall i tm,nth_error remaining23_representatives i=Some tm->QHBoundTr 67 tm).
 { intros i tm E;rewrite Forall_forall in H;apply H;exact(nth_error_In _ _ E). }
 unfold remaining23.
 constructor.
 { assert(E:(machine_of_codes 2 3 [5;9;10;6;9;7])=remaining23_rep0)by(apply same_table_sound;reflexivity).
   rewrite E;exact(Hnth 0 remaining23_rep0 eq_refl).
 }
 constructor.
 { assert(E:(machine_of_codes 2 3 [5;10;1;7;6;4])=remaining23_rep1)by(apply same_table_sound;reflexivity).
   rewrite E;exact(Hnth 1 remaining23_rep1 eq_refl).
 }
 constructor.
 { assert(E:(machine_of_codes 2 3 [5;10;1;11;6;4])=remaining23_rep2)by(apply same_table_sound;reflexivity).
   rewrite E;exact(Hnth 2 remaining23_rep2 eq_refl).
 }
 constructor.
 { assert(E:(machine_of_codes 2 3 [5;10;4;6;8;9])=remaining23_rep3)by(apply same_table_sound;reflexivity).
   rewrite E;exact(Hnth 3 remaining23_rep3 eq_refl).
 }
 constructor.
 { assert(E:(machine_of_codes 2 3 [5;10;4;6;10;9])=remaining23_rep4)by(apply same_table_sound;reflexivity).
   rewrite E;exact(Hnth 4 remaining23_rep4 eq_refl).
 }
 constructor.
 { assert(E:(machine_of_codes 2 3 [5;11;3;6;8;3])=remaining23_rep5)by(apply same_table_sound;reflexivity).
   rewrite E;exact(Hnth 5 remaining23_rep5 eq_refl).
 }
 constructor.
 { assert(E:(machine_of_codes 2 3 [5;11;10;6;9;7])=remaining23_rep6)by(apply same_table_sound;reflexivity).
   rewrite E;exact(Hnth 6 remaining23_rep6 eq_refl).
 }
 constructor.
 { apply mirror_qhbound. assert(E:(mirror_tm(machine_of_codes 2 3 [7;8;3;5;4;6]))=remaining23_rep1)by(apply same_table_sound;reflexivity).
   rewrite E;exact(Hnth 1 remaining23_rep1 eq_refl).
 }
 constructor.
 { apply mirror_qhbound. assert(E:(mirror_tm(machine_of_codes 2 3 [7;8;3;9;4;6]))=remaining23_rep2)by(apply same_table_sound;reflexivity).
   rewrite E;exact(Hnth 2 remaining23_rep2 eq_refl).
 }
 constructor.
 { apply mirror_qhbound. assert(E:(mirror_tm(machine_of_codes 2 3 [7;8;6;4;8;11]))=remaining23_rep4)by(apply same_table_sound;reflexivity).
   rewrite E;exact(Hnth 4 remaining23_rep4 eq_refl).
 }
 constructor.
 { apply mirror_qhbound. assert(E:(mirror_tm(machine_of_codes 2 3 [7;8;6;4;10;11]))=remaining23_rep3)by(apply same_table_sound;reflexivity).
   rewrite E;exact(Hnth 3 remaining23_rep3 eq_refl).
 }
 constructor.
 { apply mirror_qhbound. assert(E:(mirror_tm(machine_of_codes 2 3 [7;9;1;4;10;1]))=remaining23_rep5)by(apply same_table_sound;reflexivity).
   rewrite E;exact(Hnth 5 remaining23_rep5 eq_refl).
 }
 constructor.
 { apply mirror_qhbound. assert(E:(mirror_tm(machine_of_codes 2 3 [7;9;8;4;11;5]))=remaining23_rep6)by(apply same_table_sound;reflexivity).
   rewrite E;exact(Hnth 6 remaining23_rep6 eq_refl).
 }
 constructor.
 { apply mirror_qhbound. assert(E:(mirror_tm(machine_of_codes 2 3 [7;11;8;4;11;5]))=remaining23_rep0)by(apply same_table_sound;reflexivity).
   rewrite E;exact(Hnth 0 remaining23_rep0 eq_refl).
 }
 constructor.
 { apply swap_qhbound. assert(E:(swap_tm(machine_of_codes 2 3 [9;1;6;7;8;10]))=remaining23_rep2)by(apply same_table_sound;reflexivity).
   rewrite E;exact(Hnth 2 remaining23_rep2 eq_refl).
 }
 constructor.
 { apply swap_qhbound. assert(E:(swap_tm(machine_of_codes 2 3 [9;1;6;11;8;10]))=remaining23_rep1)by(apply same_table_sound;reflexivity).
   rewrite E;exact(Hnth 1 remaining23_rep1 eq_refl).
 }
 constructor.
 { apply swap_qhbound. assert(E:(swap_tm(machine_of_codes 2 3 [9;3;7;10;3;4]))=remaining23_rep5)by(apply same_table_sound;reflexivity).
   rewrite E;exact(Hnth 5 remaining23_rep5 eq_refl).
 }
 constructor.
 { apply swap_qhbound. assert(E:(swap_tm(machine_of_codes 2 3 [9;6;5;10;11;5]))=remaining23_rep0)by(apply same_table_sound;reflexivity).
   rewrite E;exact(Hnth 0 remaining23_rep0 eq_refl).
 }
 constructor.
 { apply swap_qhbound. assert(E:(swap_tm(machine_of_codes 2 3 [9;6;7;10;11;5]))=remaining23_rep6)by(apply same_table_sound;reflexivity).
   rewrite E;exact(Hnth 6 remaining23_rep6 eq_refl).
 }
 constructor.
 { apply swap_qhbound. assert(E:(swap_tm(machine_of_codes 2 3 [9;8;6;10;5;4]))=remaining23_rep3)by(apply same_table_sound;reflexivity).
   rewrite E;exact(Hnth 3 remaining23_rep3 eq_refl).
 }
 constructor.
 { apply swap_qhbound. assert(E:(swap_tm(machine_of_codes 2 3 [9;8;6;10;5;6]))=remaining23_rep4)by(apply same_table_sound;reflexivity).
   rewrite E;exact(Hnth 4 remaining23_rep4 eq_refl).
 }
 constructor.
 { apply mirror_qhbound. apply swap_qhbound. assert(E:(swap_tm(mirror_tm(machine_of_codes 2 3 [11;1;5;8;1;6])))=remaining23_rep5)by(apply same_table_sound;reflexivity).
   rewrite E;exact(Hnth 5 remaining23_rep5 eq_refl).
 }
 constructor.
 { apply mirror_qhbound. apply swap_qhbound. assert(E:(swap_tm(mirror_tm(machine_of_codes 2 3 [11;3;4;5;10;8])))=remaining23_rep2)by(apply same_table_sound;reflexivity).
   rewrite E;exact(Hnth 2 remaining23_rep2 eq_refl).
 }
 constructor.
 { apply mirror_qhbound. apply swap_qhbound. assert(E:(swap_tm(mirror_tm(machine_of_codes 2 3 [11;3;4;9;10;8])))=remaining23_rep1)by(apply same_table_sound;reflexivity).
   rewrite E;exact(Hnth 1 remaining23_rep1 eq_refl).
 }
 constructor.
 { apply mirror_qhbound. apply swap_qhbound. assert(E:(swap_tm(mirror_tm(machine_of_codes 2 3 [11;4;5;8;9;7])))=remaining23_rep6)by(apply same_table_sound;reflexivity).
   rewrite E;exact(Hnth 6 remaining23_rep6 eq_refl).
 }
 constructor.
 { apply mirror_qhbound. apply swap_qhbound. assert(E:(swap_tm(mirror_tm(machine_of_codes 2 3 [11;4;7;8;9;7])))=remaining23_rep0)by(apply same_table_sound;reflexivity).
   rewrite E;exact(Hnth 0 remaining23_rep0 eq_refl).
 }
 constructor.
 { apply mirror_qhbound. apply swap_qhbound. assert(E:(swap_tm(mirror_tm(machine_of_codes 2 3 [11;10;4;8;7;4])))=remaining23_rep4)by(apply same_table_sound;reflexivity).
   rewrite E;exact(Hnth 4 remaining23_rep4 eq_refl).
 }
 constructor.
 { apply mirror_qhbound. apply swap_qhbound. assert(E:(swap_tm(mirror_tm(machine_of_codes 2 3 [11;10;4;8;7;6])))=remaining23_rep3)by(apply same_table_sound;reflexivity).
   rewrite E;exact(Hnth 3 remaining23_rep3 eq_refl).
 }
 constructor. Qed.
