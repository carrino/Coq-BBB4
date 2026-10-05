(** Periodic anchor definitions for the first orbit of block-list core C. *)
From Coq Require Import Arith Lia List FunctionalExtensionality.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Counters Require Import WTape NestCountTr LoopRunTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
Import ListNotations.
Definition bco_tm:TM:=fun q h=>Some(match q,h with
|StA,S0=>mkTrans S1 DR StB|StA,S1=>mkTrans S1 DL StB
|StB,S0=>mkTrans S0 DL StC|StB,S1=>mkTrans S1 DR StD
|StC,S0=>mkTrans S1 DL StA|StC,S1=>mkTrans S1 DL StC
|StD,S0=>mkTrans S1 DR StB|StD,S1=>mkTrans S0 DR StB end).
Definition bco_Q:list Sym:=[S1;S0;S1;S1;S1;S1;S0;S1;S1;S1;S0;S1;S1;S0;S1;S1;S0;S1;S1;S0;S1;S1;S0;S1;S1;S1;S1;S0;S1;S1;S0;S1;S1;S0;S1;S1;S1;S1;S0;S1;S1;S0;S1;S1;S0;S1;S1;S1;S1;S0;S1;S1;S0;S1].
Definition bco_tail:list Sym:=[S1;S0;S1;S1;S1;S1].
Definition bco_anchor(n:nat):cconf:=(StA,([],S0,rep bco_Q n++bco_tail)).
Definition bco_tail2:list Sym:=[S1;S0;S1;S1;S1;S1;S0;S1;S1;S0;S1;S1;S0;S1;S1;S1;S1].
Definition bco_anchor2(n:nat):cconf:=(StA,([],S0,rep bco_Q n++bco_tail2)).
Section Machine.
Variable tm:TM.
Hypothesis Htm:forall q h,tm q h=bco_tm q h.
Local Ltac run:=repeat(cbn[csteps cstep];rewrite ?Htm;
 cbn[bco_tm ctape_move t_dir t_next t_write chd ctl]);reflexivity.
Lemma bco_boot:stepn tm 21 InitES=Some(lift(bco_anchor 0)).
Proof. apply boot_ok;unfold bco_anchor,bco_Q,bco_tail;unfold CTape.c0;cbn[rep app];run. Qed.
Lemma bco_boot_from:forall q k c,
 (match csteps tm k(q,([],S0,[]))with Some e=>ceqb e c|None=>false end)=true->
 stepn tm k(lift(q,([],S0,[])))=Some(lift c).
Proof.
 intros q k c H;destruct(csteps tm k(q,([],S0,[])))as[e|]eqn:E;[|discriminate].
 rewrite(csteps_lift _ _ _ _ E);f_equal;apply ceqb_lift;exact H.
Qed.
Lemma bco_bootD:stepn tm 21(lift(StD,([],S0,[])))=Some(lift(bco_anchor 0)).
Proof. apply bco_boot_from;unfold bco_anchor,bco_Q,bco_tail;cbn[rep app];run. Qed.
Lemma bco_bootB:stepn tm 191(lift(StB,([],S0,[])))=Some(lift(bco_anchor2 0)).
Proof. apply bco_boot_from;unfold bco_anchor2,bco_Q,bco_tail2;cbn[rep app];run. Qed.
Lemma bco_bootC:stepn tm 190(lift(StC,([],S0,[])))=Some(lift(bco_anchor2 0)).
Proof. apply bco_boot_from;unfold bco_anchor2,bco_Q,bco_tail2;cbn[rep app];run. Qed.
Lemma bco_fires:forall n t,Fires tm(bco_anchor n)t.
Proof.
 intros n[q h];destruct q,h;
 [exists 0|exists 9|exists 7|exists 1|exists 8|exists 11|exists 2|exists 4].
 all: destruct n.
 all: eexists;split;[unfold bco_anchor,bco_Q,bco_tail;cbn[rep app];run|reflexivity].
Qed.
Lemma bco_fires2:forall n t,Fires tm(bco_anchor2 n)t.
Proof.
 intros n[q h];destruct q,h;
 [exists 0|exists 9|exists 7|exists 1|exists 8|exists 11|exists 2|exists 4].
 all: destruct n.
 all: eexists;split;[unfold bco_anchor2,bco_Q,bco_tail2;cbn[rep app];run|reflexivity].
Qed.
Lemma bco_tm_eq:tm=bco_tm.
Proof. apply functional_extensionality_dep;intro q;apply functional_extensionality_dep;apply Htm. Qed.
Lemma bco_run_checked:forall k c d,0<k->
 (match csteps tm k c with Some e=>ceqb e d|None=>false end)=true->Reach1 tm c d.
Proof.
 intros k c d HK H;destruct(csteps tm k c)as[e|]eqn:E;[|discriminate].
 exists k;split;[exact HK|]. rewrite(csteps_lift _ _ _ _ E).
 f_equal;apply ceqb_lift;exact H.
Qed.
Lemma bco_base0:Reach1 tm(bco_anchor 0)(bco_anchor 1).
Proof. apply(bco_run_checked 2592);[apply Nat.lt_0_succ|rewrite bco_tm_eq;vm_compute;reflexivity]. Qed.
Lemma bco_base1:Reach1 tm(bco_anchor 1)(bco_anchor 2).
Proof. apply(bco_run_checked 7272);[apply Nat.lt_0_succ|rewrite bco_tm_eq;vm_compute;reflexivity]. Qed.
Lemma bco_base20:Reach1 tm(bco_anchor2 0)(bco_anchor2 1).
Proof. apply(bco_run_checked 3528);[apply Nat.lt_0_succ|rewrite bco_tm_eq;vm_compute;reflexivity]. Qed.
Lemma bco_base21:Reach1 tm(bco_anchor2 1)(bco_anchor2 2).
Proof. apply(bco_run_checked 8208);[apply Nat.lt_0_succ|rewrite bco_tm_eq;vm_compute;reflexivity]. Qed.
End Machine.
