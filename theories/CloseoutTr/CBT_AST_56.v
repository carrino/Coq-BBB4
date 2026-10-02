(** Transition-level closeout batch AST_56: a separator counter.
    Collected by tools/closeouttr/gen_closeout_tr.py. *)
From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Checkers Require Import LapDecider.
From BBB4.Counters Require Import SeparatorTokenTr LapGlueTr.
Import ListNotations.
From BBB4.Census Require Import Deferred_Defs.
From BBB4.CloseoutTr Require Import CloseoutKitTr.
From BBB4.Counters Require Import CConjugateTr.
Local Definition sep_source := row_to_tm [t1RB;t0RA;t0LC;t0RA;t1RA;t1LD;t1LB;t0LD].
Local Lemma sep_source_sweep : srun sep_source false true sep_sweep_chain sep_sc = Some (sep_sd,18,38).
Proof. vm_compute;reflexivity. Qed.
Local Lemma sep_source_fires : forall t, t<>(StD,S1) -> exists ch,
 srun_instr sep_source false true ch sep_sc = Some t.
Proof.
 intros [[] []] H.
 - exists []. reflexivity.
 - exists [(SCycR 3); (SWin 2)]. vm_compute;reflexivity.
 - exists [(SCycR 3); (SWin 2); (SWinR 2)]. vm_compute;reflexivity.
 - exists [(SCycR 3); (SWin 1)]. vm_compute;reflexivity.
 - exists [(SCycR 3); (SWin 2); (SWinR 6); (SCycL 3 0); (SWin 4); (SCycR 3); (SWin 4); (SWinR 6); (SCycL 3 0); (SWin 2)]. vm_compute;reflexivity.
 - exists [(SCycR 3); (SWin 2); (SWinR 3)]. vm_compute;reflexivity.
 - exists [(SCycR 3); (SWin 2); (SWinR 4)]. vm_compute;reflexivity.
 - contradiction H;reflexivity.
Qed.
Local Definition sep_perm (q:St) : St := match q with StA=>StD|StB=>StB|StC=>StC|StD=>StA end.
(* spec 1RB0RA_0RC0LD_1LD1RA_1LB0LD *)
Definition r_AST_56_0000 : list (option Trans) := [t1RB;t0RA;t0RC;t0LD;t1LD;t1RA;t1LB;t0LD].
Lemma cv_AST_56_0000 : coversTr (row_to_tm r_AST_56_0000).
Proof.
 apply coversTr_nqh.
 assert (Htable : forall q s, row_to_tm r_AST_56_0000 (sep_perm q) s =
   option_map (tconj sep_perm true) (sep_source q s)) by (intros [] [];reflexivity).
 apply (cconj_value_neverqhtr sep_source (row_to_tm r_AST_56_0000) sep_perm true Htable
  sep_value sep_next (fun n x => sep_anchor (n+1) x) (sd1,[])).
 - intros [];[exists StD|exists StB|exists StC|exists StA];reflexivity.
 - exists 81. rewrite <- lift_c0.
   remember (csteps (row_to_tm r_AST_56_0000) 81 c0) as z eqn:Ez.
   assert (Hb : match z with Some c => ceqb c (cconj sep_perm true (sep_anchor 1 (sd1,[]))) | None=>false end=true).
   { subst z. vm_cast_no_check (eq_refl true). }
   destruct z as [c|];[|discriminate].
   rewrite (csteps_lift _ _ _ _ (eq_sym Ez)). f_equal. apply ceqb_lift. exact Hb.
 - intros n x. exists (sep_cc x+18*(n+1)+38). split;[|lia].
   replace (S n+1) with (S (n+1)) by lia.
   apply sep_lap;try exact sep_source_sweep;reflexivity.
 - intros n x t. apply sep_fire;try reflexivity. exact sep_source_fires.
Qed.
Definition cbtrows_AST_56 : list (list (option Trans)) := [r_AST_56_0000].
Lemma cbt_AST_56_covers : Forall coversTr (map row_to_tm cbtrows_AST_56).
Proof. exact (Forall_cons _ cv_AST_56_0000 (Forall_nil _)). Qed.
