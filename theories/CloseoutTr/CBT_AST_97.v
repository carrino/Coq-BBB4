(** Finite carries ranked by their count of ones. *)
From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Census Require Import Deferred_Defs.
From BBB4.CloseoutTr Require Import CloseoutKitTr.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
From BBB4.Counters Require Import CConjugateTr CConjugateReachTr.
From BBB4.Counters Require Import OnesBudgetTr.
Import ListNotations.
(* spec 0RB0RC_1LC1RC_1LD1RA_1RA0LD *)
Definition r_AST_97_0000:list(option Trans):=[t0RB;t0RC;t1LC;t1RC;t1LD;t1RA;t1RA;t0LD].
(* spec 1RB0LA_0RC0RD_1LD1RD_1LA1RB *)
Definition r_AST_97_0001:list(option Trans):=[t1RB;t0LA;t0RC;t0RD;t1LD;t1RD;t1LA;t1RB].
(* spec 1RB1LB_1RC1LD_1LD0RC_0LA0LB *)
Definition r_AST_97_0002:list(option Trans):=[t1RB;t1LB;t1RC;t1LD;t1LD;t0RC;t0LA;t0LB].
Lemma cv_AST_97_0000:coversTr(row_to_tm r_AST_97_0000).
Proof.
 apply coversTr_nqh,ones_budget_neverqhtr;try reflexivity.
 exists 0,[]. rewrite <-lift_c0. reflexivity.
Qed.
Definition ob_target1(q:St):St:=match q with StA=>StB|StB=>StC|StC=>StD|StD=>StA end.
Definition ob_target2(q:St):St:=match q with StA=>StD|StB=>StA|StC=>StB|StD=>StC end.
Lemma ast97_return:forall L,exists U k,0<k /\
 stepn(row_to_tm r_AST_97_0000)k(lift(ob_anchor L))=Some(lift(ob_anchor U)).
Proof.
 intro L. destruct(ob_frontier_return(row_to_tm r_AST_97_0000)
 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl L)as(k&U&Hk&HS&Ek).
 exists U,k;split;[exact Hk|now apply csteps_lift].
Qed.
Lemma ast97_fires:forall L t,BBB4.Counters.TriReachTr.tri_reaches_fire(row_to_tm r_AST_97_0000)t(ob_anchor L).
Proof.
 intros L t. destruct(ob_all_fires(row_to_tm r_AST_97_0000)
 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl L t)as(k&c&Ek&Hc).
 exists k,(lift c);split;[now apply csteps_lift|now rewrite cinstr_lift].
Qed.
Lemma cv_AST_97_0001:coversTr(row_to_tm r_AST_97_0001).
Proof.
 apply coversTr_nqh.
 assert(Htable:forall q s,row_to_tm r_AST_97_0001(ob_target1 q)s=
 option_map(tconj ob_target1 false)(row_to_tm r_AST_97_0000 q s))by(intros[][];reflexivity).
 apply(cconj_reach_neverqhtr(row_to_tm r_AST_97_0000)(row_to_tm r_AST_97_0001)
 ob_target1 false Htable(list Sym)ob_anchor).
 - intros[];[exists StD|exists StA|exists StB|exists StC];reflexivity.
 - exists 1,[S1]. rewrite <-lift_c0. apply csteps_lift. reflexivity.
 - exact ast97_return.
 - exact ast97_fires.
Qed.
Lemma cv_AST_97_0002:coversTr(row_to_tm r_AST_97_0002).
Proof.
 apply coversTr_nqh.
 assert(Htable:forall q s,row_to_tm r_AST_97_0002(ob_target2 q)s=
 option_map(tconj ob_target2 true)(row_to_tm r_AST_97_0000 q s))by(intros[][];reflexivity).
 apply(cconj_reach_neverqhtr(row_to_tm r_AST_97_0000)(row_to_tm r_AST_97_0002)
 ob_target2 true Htable(list Sym)ob_anchor).
 - intros[];[exists StB|exists StC|exists StD|exists StA];reflexivity.
 - exists 5,[S1;S0;S1]. rewrite <-lift_c0. apply csteps_lift. reflexivity.
 - exact ast97_return.
 - exact ast97_fires.
Qed.
Definition cbtrows_AST_97:list(list(option Trans)) := [r_AST_97_0000;r_AST_97_0001;r_AST_97_0002].
Lemma cbt_AST_97_covers:Forall coversTr(map row_to_tm cbtrows_AST_97).
Proof. exact(Forall_cons _ cv_AST_97_0000(Forall_cons _ cv_AST_97_0001(Forall_cons _ cv_AST_97_0002(Forall_nil _)))). Qed.
