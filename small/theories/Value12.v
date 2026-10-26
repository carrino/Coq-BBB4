(** One state always moves in the same direction from a blank tape, so it
    either halts immediately or visits fresh blank cells forever. *)
From Coq Require Import Arith Lia List.
From SmallBB Require Import Statement StatementTr CTape Size Bounds Spec
 Witness CycleCensus Census.
Import ListNotations.

Definition partial12 (w:Sym)(d:Dir):TM:=fun q s=>match q,s with
 |StA,S0=>Some(mkTrans w d StA)|_,_=>None end.
Lemma partial12_sound:forall w d,NonHalt(partial12 w d) /\ Bounds 1 1(partial12 w d).
Proof.
 intros w d;destruct d.
 - apply(cycle_check_sound 1 1(partial12 w DL)true 0 1 0).
   destruct w;vm_compute;reflexivity.
 - apply(cycle_check_sound 1 1(partial12 w DR)false 0 1 0).
   destruct w;vm_compute;reflexivity.
Qed.
Theorem bbb12_upper:forall tm,Admissible 1 2 tm->Bounds 1 1 tm.
Proof.
 intros tm Had;destruct(tm StA S0)as[[w d q]|]eqn:E.
 - pose proof(admissible_output 1 2 tm Had StA S0(mkTrans w d q)E)as Hout.
   unfold output_ok in Hout;cbn in Hout.
   destruct q;cbn in Hout;try lia.
   destruct(partial12_sound w d)as[Hnh Hb].
   apply(extend_bounds 1 1(partial12 w d)tm Hnh Hb).
   intros q s;destruct q,s;try(left;reflexivity).
   right;exact E.
 - apply(halt_bounds 1 1 tm 1);[lia|lia|].
   cbn[stepn step InitES fst snd t_head]. rewrite E;reflexivity.
Qed.
Lemma empty12_admissible:Admissible 1 2 empty.
Proof. split;[intros q s tr H;discriminate|intros;reflexivity]. Qed.
Lemma empty12_quiet:QuietAfter empty StA 0.
Proof. exact(halt_quiet_state empty 0 c0 eq_refl eq_refl). Qed.
Lemma empty12_quiet_tr:QuietAfterTr empty(StA,S0)0.
Proof.
 split;[exists InitES;split;reflexivity|].
 intros n Hn[c[Hc _]]. destruct n;[lia|]. discriminate.
Qed.
Theorem BBB12_value:BBBSt_is 1 2 1 /\ BBBTr_is 1 2 1.
Proof.
 split;split.
 - exists empty;split;[exact empty12_admissible|].
   exists StA,0;split;[exact empty12_quiet|reflexivity].
 - intros tm B Had(q&s&Hq&<-). exact(proj1(bbb12_upper tm Had)q s Hq).
 - exists empty;split;[exact empty12_admissible|].
   exists(StA,S0),0;split;[exact empty12_quiet_tr|reflexivity].
 - intros tm B Had(t&s&Ht&<-). exact(proj2(bbb12_upper tm Had)t s Ht).
Qed.
Print Assumptions BBB12_value.
