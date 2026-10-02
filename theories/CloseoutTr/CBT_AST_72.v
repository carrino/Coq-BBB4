From BBB4.Counters Require Import TriReachInvTr.
(** Transition-level closeout: cube rounds with non-affine liveness. *)
From Coq Require Import Arith Lia List Bool.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape Mirror.
From BBB4.Census Require Import Deferred_Defs.
From BBB4.CensusTr Require Import TNF_QHTr.
From BBB4.CloseoutTr Require Import CloseoutKitTr.
From BBB4.Checkers Require Import LapDecider.
From BBB4.Counters Require Import TriGlueTr TriReachTr CubeRoundTr.
Import ListNotations.
(* spec 1RB1LA_1LB0RC_1LD1RC_1LD0LA *)
Definition r_AST_72_0000 : list (option Trans) := [t1RB;t1LA;t1LB;t0RC;t1LD;t1RC;t1LD;t0LA].
Local Definition tm := mirror_tm (row_to_tm r_AST_72_0000).
Local Definition cert : tcert := (mkTC []
      [(mkTF StB S1 [(SB [S1] (mkA 0 [(0,1)]));(SL [S0]);(SB [S1] (mkA 2 [(1,1)]))] [(SB [S1] (mkA 2 [(2,1)]))] 3 [(TSplit 0 1 1 [1;2]);(TLeaf 0);(TLeaf 1)]);
      (mkTF StD S1 [(SB [S1] (mkA 2 [(0,1)]))] [(SB [S1] (mkA 0 [(1,1)]));(SL [S0]);(SB [S1] (mkA 2 [(2,1)]))] 3 [(TSplit 1 1 1 [1;2]);(TLeaf 2);(TLeaf 3)]);
      (mkTF StC S1 [(SB [S1] (mkA 2 [(0,1)]))] [(SL [S0]);(SB [S1] (mkA 2 [(1,1)]))] 2 [(TLeaf 4)]);
      (mkTF StD S1 [(SL [S1])] [(SB [S1] (mkA 2 [(0,1)]));(SL [S0]);(SB [S1] (mkA 2 [(1,1)]))] 2 [(TLeaf 5)]);
      (mkTF StD S0 [(SB [S1] (mkA 3 [(0,1)]))] [(SB [S1] (mkA 2 [(1,1)]))] 2 [(TLeaf 6)]);
      (mkTF StB S1 [(SB [S1] (mkA 1 [(0,1)]));(SL [S0;S1])] [(SB [S1] (mkA 2 [(1,1)]))] 2 [(TLeaf 7)]);
      (mkTF StD S1 [(SB [S1] (mkA 4 [(0,1)]))] [(SB [S1] (mkA 1 [(1,1)]))] 2 [(TLeaf 8)]);
      (mkTF StB S1 [(SB [S1] (mkA 0 [(0,1)]));(SL [S0]);(SB [S1] (mkA 4 [(1,1)]))] [(SL [S1])] 2 [(TSplit 0 1 1 [1;2]);(TLeaf 9);(TLeaf 10)]);
      (mkTF StD S1 [(SB [S1] (mkA 2 [(0,1)]))] [(SB [S1] (mkA 0 [(1,1)]));(SL [S0;S1])] 2 [(TSplit 1 1 1 [1;2]);(TLeaf 11);(TLeaf 12)]);
      (mkTF StC S1 [(SB [S1] (mkA 2 [(0,1)]))] [(SL [S0;S1])] 1 [(TLeaf 13)]);
      (mkTF StD S1 [(SL [S1])] [(SB [S1] (mkA 2 [(0,1)]));(SL [S0;S1])] 1 [(TLeaf 14)]);
      (mkTF StC S1 [(SB [S1] (mkA 4 [(0,1)]))] [(SB [S1] (mkA 2 [(1,1)]))] 2 [(TLeaf 15)]);
      (mkTF StD S1 [(SL [S1])] [(SB [S1] (mkA 6 [(0,1)]))] 1 [(TLeaf 16)]);
      (mkTF StB S1 [(SB [S1] (mkA 5 [(0,1)]));(SL [S0;S1])] [(SL [S1])] 1 [(TLeaf 17)])]
      [(mkTL 0 [(0,0);(1,0);(1,0)] 4 [(mkA 0 [(1,1)]);(mkA 0 [(2,1)])] (mkC StB (mkS [S0] [] 0 0 []) S1 (mkS [] [] 0 0 [])) 0 false false 2 0 [(SWin 2)]);
      (mkTL 0 [(1,1);(1,0);(1,0)] 1 [(mkA 1 [(1,1)]);(mkA 0 [(0,1)]);(mkA 0 [(2,1)])] (mkC StB (mkS [S1] [S1] 1 0 [S0]) S1 (mkS [] [] 0 0 [])) 0 false false 2 0 [(SWin 1); (SCycL 1 0); (SWin 2)]);
      (mkTL 1 [(1,0);(0,0);(1,0)] 2 [(mkA 0 [(0,1)]);(mkA 0 [(2,1)])] (mkC StD (mkS [] [] 0 0 []) S1 (mkS [S0] [] 0 0 [])) 0 false false 0 2 [(SWin 4)]);
      (mkTL 1 [(1,0);(1,1);(1,0)] 0 [(mkA 0 [(1,1)]);(mkA 0 [(0,1)]);(mkA 1 [(2,1)])] (mkC StD (mkS [] [] 0 0 []) S1 (mkS [S1] [S1] 1 0 [S0])) 1 false false 0 2 [(SWin 1); (SCycR 1); (SWin 2)]);
      (mkTL 2 [(1,0);(1,0)] 3 [(mkA 0 [(0,1)]);(mkA 0 [(1,1)])] (mkC StC (mkS [] [S1] 1 2 []) S1 (mkS [S0] [] 0 0 [])) 0 true false 1 1 [(SCycL 1 0); (SWinL 1); (SWin 1)]);
      (mkTL 3 [(1,0);(1,0)] 5 [(mkA 0 [(0,1)]);(mkA 1 [(1,1)])] (mkC StD (mkS [S1] [] 0 0 []) S1 (mkS [S1] [S1] 1 1 [S0])) 0 true false 1 2 [(SWin 1); (SCycR 1); (SWin 2)]);
      (mkTL 4 [(1,0);(1,0)] 6 [(mkA 0 [(0,1)]);(mkA 0 [(1,1)])] (mkC StD (mkS [] [] 0 0 []) S0 (mkS [S1] [S1] 1 1 [])) 1 false true 0 1 [(SWin 1)]);
      (mkTL 5 [(1,0);(1,0)] 1 [(mkA 0 []);(mkA 0 [(0,1)]);(mkA 0 [(1,1)])] (mkC StB (mkS [S1] [S1] 1 0 [S0;S1]) S1 (mkS [] [] 0 0 [])) 0 true false 2 0 [(SWin 1); (SCycL 1 0); (SWin 2)]);
      (mkTL 6 [(1,0);(1,0)] 7 [(mkA 0 [(1,1)]);(mkA 0 [(0,1)])] (mkC StD (mkS [] [] 0 0 []) S1 (mkS [S1] [S1] 1 0 [])) 1 false true 0 1 [(SWin 1); (SCycR 1); (SWinR 1); (SWin 1)]);
      (mkTL 7 [(0,0);(1,0)] 11 [(mkA 0 [(1,1)]);(mkA 0 [])] (mkC StB (mkS [S0] [] 0 0 []) S1 (mkS [S1] [] 0 0 [])) 0 false true 2 1 [(SWin 3); (SWinR 1); (SWin 5)]);
      (mkTL 7 [(1,1);(1,0)] 8 [(mkA 3 [(1,1)]);(mkA 0 [(0,1)])] (mkC StB (mkS [S1] [S1] 1 0 [S0]) S1 (mkS [S1] [] 0 0 [])) 0 false true 2 1 [(SWin 1); (SCycL 1 0); (SWin 2)]);
      (mkTL 8 [(1,0);(0,0)] 9 [(mkA 0 [(0,1)])] (mkC StD (mkS [] [] 0 0 []) S1 (mkS [S0;S1] [] 0 0 [])) 0 false true 0 2 [(SWin 4)]);
      (mkTL 8 [(1,0);(1,1)] 0 [(mkA 0 [(1,1)]);(mkA 0 [(0,1)]);(mkA 0 [])] (mkC StD (mkS [] [] 0 0 []) S1 (mkS [S1] [S1] 1 0 [S0;S1])) 1 false true 0 2 [(SWin 1); (SCycR 1); (SWin 2)]);
      (mkTL 9 [(1,0)] 10 [(mkA 0 [(0,1)])] (mkC StC (mkS [] [S1] 1 2 []) S1 (mkS [S0;S1] [] 0 0 [])) 0 true true 1 1 [(SCycL 1 0); (SWinL 1); (SWin 1)]);
      (mkTL 10 [(1,0)] 5 [(mkA 0 [(0,1)]);(mkA 0 [])] (mkC StD (mkS [S1] [] 0 0 []) S1 (mkS [S1] [S1] 1 1 [S0;S1])) 0 true true 1 2 [(SWin 1); (SCycR 1); (SWin 2)]);
      (mkTL 11 [(1,0);(1,0)] 12 [(mkA 0 [(0,1);(1,1)])] (mkC StC (mkS [] [S1] 1 4 []) S1 (mkS [] [] 0 0 [])) 0 true false 1 0 [(SCycL 1 0); (SWinL 1); (SWin 1)]);
      (mkTL 12 [(1,0)] 13 [(mkA 0 [(0,1)])] (mkC StD (mkS [S1] [] 0 0 []) S1 (mkS [S1] [S1] 1 5 [])) 0 true true 1 1 [(SWin 1); (SCycR 1); (SWinR 1); (SWin 1)]);
      (mkTL 13 [(1,0)] 8 [(mkA 0 []);(mkA 4 [(0,1)])] (mkC StB (mkS [S1] [S1] 1 4 [S0;S1]) S1 (mkS [S1] [] 0 0 [])) 0 true true 2 1 [(SWin 1); (SCycL 1 0); (SWin 2)])]
      1 []
      []
      3000 0 [23;6;1]).
Local Definition fams := tc_fams cert.
Local Definition leaves := tc_leaves cert.
Local Definition H (t : Instr) (i : nat) (v : list nat) := tri_reaches_fire tm t (tanc fams (i,v)).
Local Lemma families_ok : fams_ok tm fams leaves = true.
Proof. vm_compute. reflexivity. Qed.


Local Ltac cube_norm :=
 cbn [fams leaves cert tc_fams tc_leaves nth tl_tgt tl_reg rsub reg1 seq combine map aeval teval a_c a_t fst snd Nat.eqb Nat.mul Nat.add] in *;
 cbv beta iota zeta delta [TriGlueTr.rsub TriGlueTr.reg1 seq combine map aeval teval a_c a_t fst snd Nat.eqb Nat.mul Nat.add nth length] in *;
 rewrite ?Nat.add_0_r in *.

Local Lemma e0 : forall b c t, H t 4 [b;c] -> H t 0 [0;b;c].
Proof.
 intros b c t E.
 pose proof (tri_leaf_back tm fams (nth 0 fams (mkTF StA S0 [] [] 0 []))
   (nth 0 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   (nth 4 fams (mkTF StA S0 [] [] 0 []))
   ltac:(vm_compute;reflexivity) ltac:(reflexivity) [0;b;c] t) as B.
 cube_norm.
 unfold H, tanc in E |- *. cbn [fams cert tc_fams nth_error fst snd] in E |- *.
 match type of B with _ -> tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); apply B
  end end.
 match type of E with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact E
  end end.
Qed.

Local Lemma e1 : forall a b c t, H t 1 [b+1;a;c] -> H t 0 [a+1;b;c].
Proof.
 intros a b c t E.
 pose proof (tri_leaf_back tm fams (nth 0 fams (mkTF StA S0 [] [] 0 []))
   (nth 1 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   (nth 1 fams (mkTF StA S0 [] [] 0 []))
   ltac:(vm_compute;reflexivity) ltac:(reflexivity) [a;b;c] t) as B.
 cube_norm.
 unfold H, tanc in E |- *. cbn [fams cert tc_fams nth_error fst snd] in E |- *.
 match type of B with _ -> tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); apply B
  end end.
 match type of E with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact E
  end end.
Qed.

Local Lemma e2 : forall a c t, H t 2 [a;c] -> H t 1 [a;0;c].
Proof.
 intros a c t E.
 pose proof (tri_leaf_back tm fams (nth 1 fams (mkTF StA S0 [] [] 0 []))
   (nth 2 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   (nth 2 fams (mkTF StA S0 [] [] 0 []))
   ltac:(vm_compute;reflexivity) ltac:(reflexivity) [a;0;c] t) as B.
 cube_norm.
 unfold H, tanc in E |- *. cbn [fams cert tc_fams nth_error fst snd] in E |- *.
 match type of B with _ -> tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); apply B
  end end.
 match type of E with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact E
  end end.
Qed.

Local Lemma e3 : forall a b c t, H t 0 [b;a;c+1] -> H t 1 [a;b+1;c].
Proof.
 intros a b c t E.
 pose proof (tri_leaf_back tm fams (nth 1 fams (mkTF StA S0 [] [] 0 []))
   (nth 3 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   (nth 0 fams (mkTF StA S0 [] [] 0 []))
   ltac:(vm_compute;reflexivity) ltac:(reflexivity) [a;b;c] t) as B.
 cube_norm.
 unfold H, tanc in E |- *. cbn [fams cert tc_fams nth_error fst snd] in E |- *.
 match type of B with _ -> tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); apply B
  end end.
 match type of E with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact E
  end end.
Qed.

Local Lemma e4 : forall a b t, H t 3 [a;b] -> H t 2 [a;b].
Proof.
 intros a b t E.
 pose proof (tri_leaf_back tm fams (nth 2 fams (mkTF StA S0 [] [] 0 []))
   (nth 4 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   (nth 3 fams (mkTF StA S0 [] [] 0 []))
   ltac:(vm_compute;reflexivity) ltac:(reflexivity) [a;b] t) as B.
 cube_norm.
 unfold H, tanc in E |- *. cbn [fams cert tc_fams nth_error fst snd] in E |- *.
 match type of B with _ -> tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); apply B
  end end.
 match type of E with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact E
  end end.
Qed.

Local Lemma e5 : forall a b t, H t 5 [a;b+1] -> H t 3 [a;b].
Proof.
 intros a b t E.
 pose proof (tri_leaf_back tm fams (nth 3 fams (mkTF StA S0 [] [] 0 []))
   (nth 5 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   (nth 5 fams (mkTF StA S0 [] [] 0 []))
   ltac:(vm_compute;reflexivity) ltac:(reflexivity) [a;b] t) as B.
 cube_norm.
 unfold H, tanc in E |- *. cbn [fams cert tc_fams nth_error fst snd] in E |- *.
 match type of B with _ -> tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); apply B
  end end.
 match type of E with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact E
  end end.
Qed.

Local Lemma e6 : forall a b t, H t 6 [a;b] -> H t 4 [a;b].
Proof.
 intros a b t E.
 pose proof (tri_leaf_back tm fams (nth 4 fams (mkTF StA S0 [] [] 0 []))
   (nth 6 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   (nth 6 fams (mkTF StA S0 [] [] 0 []))
   ltac:(vm_compute;reflexivity) ltac:(reflexivity) [a;b] t) as B.
 cube_norm.
 unfold H, tanc in E |- *. cbn [fams cert tc_fams nth_error fst snd] in E |- *.
 match type of B with _ -> tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); apply B
  end end.
 match type of E with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact E
  end end.
Qed.

Local Lemma e7 : forall a b t, H t 1 [0;a;b] -> H t 5 [a;b].
Proof.
 intros a b t E.
 pose proof (tri_leaf_back tm fams (nth 5 fams (mkTF StA S0 [] [] 0 []))
   (nth 7 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   (nth 1 fams (mkTF StA S0 [] [] 0 []))
   ltac:(vm_compute;reflexivity) ltac:(reflexivity) [a;b] t) as B.
 cube_norm.
 unfold H, tanc in E |- *. cbn [fams cert tc_fams nth_error fst snd] in E |- *.
 match type of B with _ -> tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); apply B
  end end.
 match type of E with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact E
  end end.
Qed.

Local Lemma e8 : forall a b t, H t 7 [b;a] -> H t 6 [a;b].
Proof.
 intros a b t E.
 pose proof (tri_leaf_back tm fams (nth 6 fams (mkTF StA S0 [] [] 0 []))
   (nth 8 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   (nth 7 fams (mkTF StA S0 [] [] 0 []))
   ltac:(vm_compute;reflexivity) ltac:(reflexivity) [a;b] t) as B.
 cube_norm.
 unfold H, tanc in E |- *. cbn [fams cert tc_fams nth_error fst snd] in E |- *.
 match type of B with _ -> tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); apply B
  end end.
 match type of E with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact E
  end end.
Qed.

Local Lemma e9 : forall b t, H t 11 [b;0] -> H t 7 [0;b].
Proof.
 intros b t E.
 pose proof (tri_leaf_back tm fams (nth 7 fams (mkTF StA S0 [] [] 0 []))
   (nth 9 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   (nth 11 fams (mkTF StA S0 [] [] 0 []))
   ltac:(vm_compute;reflexivity) ltac:(reflexivity) [0;b] t) as B.
 cube_norm.
 unfold H, tanc in E |- *. cbn [fams cert tc_fams nth_error fst snd] in E |- *.
 match type of B with _ -> tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); apply B
  end end.
 match type of E with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact E
  end end.
Qed.

Local Lemma e10 : forall a b t, H t 8 [b+3;a] -> H t 7 [a+1;b].
Proof.
 intros a b t E.
 pose proof (tri_leaf_back tm fams (nth 7 fams (mkTF StA S0 [] [] 0 []))
   (nth 10 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   (nth 8 fams (mkTF StA S0 [] [] 0 []))
   ltac:(vm_compute;reflexivity) ltac:(reflexivity) [a;b] t) as B.
 cube_norm.
 unfold H, tanc in E |- *. cbn [fams cert tc_fams nth_error fst snd] in E |- *.
 match type of B with _ -> tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); apply B
  end end.
 match type of E with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact E
  end end.
Qed.

Local Lemma e11 : forall a t, H t 9 [a] -> H t 8 [a;0].
Proof.
 intros a t E.
 pose proof (tri_leaf_back tm fams (nth 8 fams (mkTF StA S0 [] [] 0 []))
   (nth 11 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   (nth 9 fams (mkTF StA S0 [] [] 0 []))
   ltac:(vm_compute;reflexivity) ltac:(reflexivity) [a;0] t) as B.
 cube_norm.
 unfold H, tanc in E |- *. cbn [fams cert tc_fams nth_error fst snd] in E |- *.
 match type of B with _ -> tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); apply B
  end end.
 match type of E with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact E
  end end.
Qed.

Local Lemma e12 : forall a b t, H t 0 [b;a;0] -> H t 8 [a;b+1].
Proof.
 intros a b t E.
 pose proof (tri_leaf_back tm fams (nth 8 fams (mkTF StA S0 [] [] 0 []))
   (nth 12 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   (nth 0 fams (mkTF StA S0 [] [] 0 []))
   ltac:(vm_compute;reflexivity) ltac:(reflexivity) [a;b] t) as B.
 cube_norm.
 unfold H, tanc in E |- *. cbn [fams cert tc_fams nth_error fst snd] in E |- *.
 match type of B with _ -> tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); apply B
  end end.
 match type of E with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact E
  end end.
Qed.

Local Lemma e13 : forall a t, H t 10 [a] -> H t 9 [a].
Proof.
 intros a t E.
 pose proof (tri_leaf_back tm fams (nth 9 fams (mkTF StA S0 [] [] 0 []))
   (nth 13 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   (nth 10 fams (mkTF StA S0 [] [] 0 []))
   ltac:(vm_compute;reflexivity) ltac:(reflexivity) [a] t) as B.
 cube_norm.
 unfold H, tanc in E |- *. cbn [fams cert tc_fams nth_error fst snd] in E |- *.
 match type of B with _ -> tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); apply B
  end end.
 match type of E with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact E
  end end.
Qed.

Local Lemma e14 : forall a t, H t 5 [a;0] -> H t 10 [a].
Proof.
 intros a t E.
 pose proof (tri_leaf_back tm fams (nth 10 fams (mkTF StA S0 [] [] 0 []))
   (nth 14 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   (nth 5 fams (mkTF StA S0 [] [] 0 []))
   ltac:(vm_compute;reflexivity) ltac:(reflexivity) [a] t) as B.
 cube_norm.
 unfold H, tanc in E |- *. cbn [fams cert tc_fams nth_error fst snd] in E |- *.
 match type of B with _ -> tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); apply B
  end end.
 match type of E with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact E
  end end.
Qed.

Local Lemma e15 : forall a b t, H t 12 [a+b] -> H t 11 [a;b].
Proof.
 intros a b t E.
 pose proof (tri_leaf_back tm fams (nth 11 fams (mkTF StA S0 [] [] 0 []))
   (nth 15 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   (nth 12 fams (mkTF StA S0 [] [] 0 []))
   ltac:(vm_compute;reflexivity) ltac:(reflexivity) [a;b] t) as B.
 cube_norm.
 unfold H, tanc in E |- *. cbn [fams cert tc_fams nth_error fst snd] in E |- *.
 match type of B with _ -> tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); apply B
  end end.
 match type of E with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact E
  end end.
Qed.

Local Lemma e16 : forall a t, H t 13 [a] -> H t 12 [a].
Proof.
 intros a t E.
 pose proof (tri_leaf_back tm fams (nth 12 fams (mkTF StA S0 [] [] 0 []))
   (nth 16 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   (nth 13 fams (mkTF StA S0 [] [] 0 []))
   ltac:(vm_compute;reflexivity) ltac:(reflexivity) [a] t) as B.
 cube_norm.
 unfold H, tanc in E |- *. cbn [fams cert tc_fams nth_error fst snd] in E |- *.
 match type of B with _ -> tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); apply B
  end end.
 match type of E with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact E
  end end.
Qed.

Local Lemma e17 : forall a t, H t 8 [0;a+4] -> H t 13 [a].
Proof.
 intros a t E.
 pose proof (tri_leaf_back tm fams (nth 13 fams (mkTF StA S0 [] [] 0 []))
   (nth 17 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   (nth 8 fams (mkTF StA S0 [] [] 0 []))
   ltac:(vm_compute;reflexivity) ltac:(reflexivity) [a] t) as B.
 cube_norm.
 unfold H, tanc in E |- *. cbn [fams cert tc_fams nth_error fst snd] in E |- *.
 match type of B with _ -> tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); apply B
  end end.
 match type of E with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact E
  end end.
Qed.

Local Lemma f0 : forall b c t, In t [(StB,S1);(StC,S0);(StD,S0)] -> H t 0 [0;b;c].
Proof.
 intros b c t Et.
 pose proof (tri_leaf_now tm fams (nth 0 fams (mkTF StA S0 [] [] 0 []))
   (nth 0 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   ltac:(vm_compute;reflexivity) t ltac:(vm_compute in Et |- *; tauto) [0;b;c]) as B.
 cube_norm.
 unfold H, tanc. cbn [fams cert tc_fams nth_error fst snd].
 match type of B with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact B
  end end.
Qed.

Local Lemma f1 : forall a b c t, In t [(StB,S1);(StC,S0);(StC,S1);(StD,S1)] -> H t 0 [a+1;b;c].
Proof.
 intros a b c t Et.
 pose proof (tri_leaf_now tm fams (nth 0 fams (mkTF StA S0 [] [] 0 []))
   (nth 1 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   ltac:(vm_compute;reflexivity) t ltac:(vm_compute in Et |- *; tauto) [a;b;c]) as B.
 cube_norm.
 unfold H, tanc. cbn [fams cert tc_fams nth_error fst snd].
 match type of B with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact B
  end end.
Qed.

Local Lemma f2 : forall a c t, In t [(StA,S0);(StB,S0);(StB,S1);(StC,S1);(StD,S1)] -> H t 1 [a;0;c].
Proof.
 intros a c t Et.
 pose proof (tri_leaf_now tm fams (nth 1 fams (mkTF StA S0 [] [] 0 []))
   (nth 2 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   ltac:(vm_compute;reflexivity) t ltac:(vm_compute in Et |- *; tauto) [a;0;c]) as B.
 cube_norm.
 unfold H, tanc. cbn [fams cert tc_fams nth_error fst snd].
 match type of B with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact B
  end end.
Qed.

Local Lemma f3 : forall a b c t, In t [(StA,S0);(StA,S1);(StB,S1);(StD,S1)] -> H t 1 [a;b+1;c].
Proof.
 intros a b c t Et.
 pose proof (tri_leaf_now tm fams (nth 1 fams (mkTF StA S0 [] [] 0 []))
   (nth 3 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   ltac:(vm_compute;reflexivity) t ltac:(vm_compute in Et |- *; tauto) [a;b;c]) as B.
 cube_norm.
 unfold H, tanc. cbn [fams cert tc_fams nth_error fst snd].
 match type of B with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact B
  end end.
Qed.

Local Lemma f4 : forall a b t, In t [(StC,S0);(StC,S1);(StD,S1)] -> H t 2 [a;b].
Proof.
 intros a b t Et.
 pose proof (tri_leaf_now tm fams (nth 2 fams (mkTF StA S0 [] [] 0 []))
   (nth 4 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   ltac:(vm_compute;reflexivity) t ltac:(vm_compute in Et |- *; tauto) [a;b]) as B.
 cube_norm.
 unfold H, tanc. cbn [fams cert tc_fams nth_error fst snd].
 match type of B with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact B
  end end.
Qed.

Local Lemma f5 : forall a b t, In t [(StA,S0);(StA,S1);(StB,S1);(StD,S1)] -> H t 3 [a;b].
Proof.
 intros a b t Et.
 pose proof (tri_leaf_now tm fams (nth 3 fams (mkTF StA S0 [] [] 0 []))
   (nth 5 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   ltac:(vm_compute;reflexivity) t ltac:(vm_compute in Et |- *; tauto) [a;b]) as B.
 cube_norm.
 unfold H, tanc. cbn [fams cert tc_fams nth_error fst snd].
 match type of B with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact B
  end end.
Qed.

Local Lemma f6 : forall a b t, In t [(StD,S0);(StD,S1)] -> H t 4 [a;b].
Proof.
 intros a b t Et.
 pose proof (tri_leaf_now tm fams (nth 4 fams (mkTF StA S0 [] [] 0 []))
   (nth 6 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   ltac:(vm_compute;reflexivity) t ltac:(vm_compute in Et |- *; tauto) [a;b]) as B.
 cube_norm.
 unfold H, tanc. cbn [fams cert tc_fams nth_error fst snd].
 match type of B with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact B
  end end.
Qed.

Local Lemma f7 : forall a b t, In t [(StB,S1);(StC,S0);(StC,S1);(StD,S1)] -> H t 5 [a;b].
Proof.
 intros a b t Et.
 pose proof (tri_leaf_now tm fams (nth 5 fams (mkTF StA S0 [] [] 0 []))
   (nth 7 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   ltac:(vm_compute;reflexivity) t ltac:(vm_compute in Et |- *; tauto) [a;b]) as B.
 cube_norm.
 unfold H, tanc. cbn [fams cert tc_fams nth_error fst snd].
 match type of B with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact B
  end end.
Qed.

Local Lemma f8 : forall a b t, In t [(StA,S0);(StA,S1);(StB,S1);(StD,S1)] -> H t 6 [a;b].
Proof.
 intros a b t Et.
 pose proof (tri_leaf_now tm fams (nth 6 fams (mkTF StA S0 [] [] 0 []))
   (nth 8 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   ltac:(vm_compute;reflexivity) t ltac:(vm_compute in Et |- *; tauto) [a;b]) as B.
 cube_norm.
 unfold H, tanc. cbn [fams cert tc_fams nth_error fst snd].
 match type of B with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact B
  end end.
Qed.

Local Lemma f9 : forall b t, In t [(StA,S0);(StB,S0);(StB,S1);(StC,S0);(StC,S1);(StD,S0);(StD,S1)] -> H t 7 [0;b].
Proof.
 intros b t Et.
 pose proof (tri_leaf_now tm fams (nth 7 fams (mkTF StA S0 [] [] 0 []))
   (nth 9 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   ltac:(vm_compute;reflexivity) t ltac:(vm_compute in Et |- *; tauto) [0;b]) as B.
 cube_norm.
 unfold H, tanc. cbn [fams cert tc_fams nth_error fst snd].
 match type of B with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact B
  end end.
Qed.

Local Lemma f10 : forall a b t, In t [(StB,S1);(StC,S0);(StC,S1);(StD,S1)] -> H t 7 [a+1;b].
Proof.
 intros a b t Et.
 pose proof (tri_leaf_now tm fams (nth 7 fams (mkTF StA S0 [] [] 0 []))
   (nth 10 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   ltac:(vm_compute;reflexivity) t ltac:(vm_compute in Et |- *; tauto) [a;b]) as B.
 cube_norm.
 unfold H, tanc. cbn [fams cert tc_fams nth_error fst snd].
 match type of B with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact B
  end end.
Qed.

Local Lemma f11 : forall a t, In t [(StA,S0);(StB,S0);(StB,S1);(StC,S1);(StD,S1)] -> H t 8 [a;0].
Proof.
 intros a t Et.
 pose proof (tri_leaf_now tm fams (nth 8 fams (mkTF StA S0 [] [] 0 []))
   (nth 11 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   ltac:(vm_compute;reflexivity) t ltac:(vm_compute in Et |- *; tauto) [a;0]) as B.
 cube_norm.
 unfold H, tanc. cbn [fams cert tc_fams nth_error fst snd].
 match type of B with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact B
  end end.
Qed.

Local Lemma f12 : forall a b t, In t [(StA,S0);(StA,S1);(StB,S1);(StD,S1)] -> H t 8 [a;b+1].
Proof.
 intros a b t Et.
 pose proof (tri_leaf_now tm fams (nth 8 fams (mkTF StA S0 [] [] 0 []))
   (nth 12 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   ltac:(vm_compute;reflexivity) t ltac:(vm_compute in Et |- *; tauto) [a;b]) as B.
 cube_norm.
 unfold H, tanc. cbn [fams cert tc_fams nth_error fst snd].
 match type of B with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact B
  end end.
Qed.

Local Lemma f13 : forall a t, In t [(StC,S0);(StC,S1);(StD,S1)] -> H t 9 [a].
Proof.
 intros a t Et.
 pose proof (tri_leaf_now tm fams (nth 9 fams (mkTF StA S0 [] [] 0 []))
   (nth 13 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   ltac:(vm_compute;reflexivity) t ltac:(vm_compute in Et |- *; tauto) [a]) as B.
 cube_norm.
 unfold H, tanc. cbn [fams cert tc_fams nth_error fst snd].
 match type of B with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact B
  end end.
Qed.

Local Lemma f14 : forall a t, In t [(StA,S0);(StA,S1);(StB,S1);(StD,S1)] -> H t 10 [a].
Proof.
 intros a t Et.
 pose proof (tri_leaf_now tm fams (nth 10 fams (mkTF StA S0 [] [] 0 []))
   (nth 14 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   ltac:(vm_compute;reflexivity) t ltac:(vm_compute in Et |- *; tauto) [a]) as B.
 cube_norm.
 unfold H, tanc. cbn [fams cert tc_fams nth_error fst snd].
 match type of B with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact B
  end end.
Qed.

Local Lemma f15 : forall a b t, In t [(StC,S0);(StC,S1);(StD,S1)] -> H t 11 [a;b].
Proof.
 intros a b t Et.
 pose proof (tri_leaf_now tm fams (nth 11 fams (mkTF StA S0 [] [] 0 []))
   (nth 15 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   ltac:(vm_compute;reflexivity) t ltac:(vm_compute in Et |- *; tauto) [a;b]) as B.
 cube_norm.
 unfold H, tanc. cbn [fams cert tc_fams nth_error fst snd].
 match type of B with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact B
  end end.
Qed.

Local Lemma f16 : forall a t, In t [(StA,S0);(StA,S1);(StB,S1);(StD,S1)] -> H t 12 [a].
Proof.
 intros a t Et.
 pose proof (tri_leaf_now tm fams (nth 12 fams (mkTF StA S0 [] [] 0 []))
   (nth 16 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   ltac:(vm_compute;reflexivity) t ltac:(vm_compute in Et |- *; tauto) [a]) as B.
 cube_norm.
 unfold H, tanc. cbn [fams cert tc_fams nth_error fst snd].
 match type of B with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact B
  end end.
Qed.

Local Lemma f17 : forall a t, In t [(StB,S1);(StC,S0);(StC,S1);(StD,S1)] -> H t 13 [a].
Proof.
 intros a t Et.
 pose proof (tri_leaf_now tm fams (nth 13 fams (mkTF StA S0 [] [] 0 []))
   (nth 17 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   ltac:(vm_compute;reflexivity) t ltac:(vm_compute in Et |- *; tauto) [a]) as B.
 cube_norm.
 unfold H, tanc. cbn [fams cert tc_fams nth_error fst snd].
 match type of B with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact B
  end end.
Qed.

Local Ltac cube_now := first [solve [apply f0; simpl; auto] | solve [apply f1; simpl; auto] | solve [apply f2; simpl; auto] | solve [apply f3; simpl; auto] | solve [apply f4; simpl; auto] | solve [apply f5; simpl; auto] | solve [apply f6; simpl; auto] | solve [apply f7; simpl; auto] | solve [apply f8; simpl; auto] | solve [apply f9; simpl; auto] | solve [apply f10; simpl; auto] | solve [apply f11; simpl; auto] | solve [apply f12; simpl; auto] | solve [apply f13; simpl; auto] | solve [apply f14; simpl; auto] | solve [apply f15; simpl; auto] | solve [apply f16; simpl; auto] | solve [apply f17; simpl; auto]].
Local Ltac cube_exact E :=
 match type of E with H ?t ?i ?xs =>
  match goal with |- H t i ?ys =>
   replace ys with xs by (repeat (f_equal; try lia)); exact E
  end end.

Local Lemma cube_parity : forall a, exists k, a=2*k \/ a=2*k+1.
Proof.
 intro a. exists (a/2).
 pose proof (Nat.div_mod a 2 ltac:(lia)).
 pose proof (Nat.mod_upper_bound a 2 ltac:(lia)). lia.
Qed.

Local Lemma cube_loop : forall k a b c t,
 H t 0 [a;b+k;c+k] -> H t 0 [2*k+a;b;c].
Proof.
 induction k as [|k IH]; intros a b c t E.
 - cbn [Nat.mul Nat.add]. cube_exact E.
 - replace (2*S k+a) with ((2*k+a)+1+1) by lia.
   apply e1,e3. apply IH. cube_exact E.
Qed.

Local Lemma cube_D0 : forall a b c, H (StD,S0) 0 [a;b;c].
Proof.
 assert (E : forall m a b, a+2*b=m -> forall c, H (StD,S0) 0 [a;b;c]).
 { induction m as [m IH] using lt_wf_ind. intros a b Em c.
   destruct (cube_parity a) as (k & [-> | ->]).
   - replace (2*k) with (2*k+0) by lia. apply cube_loop,f0. simpl; auto 12.
   - apply cube_loop. change (H (StD,S0) 0 [0+1;b+k;c+k]).
     apply e1,e2,e4,e5,e7,e3.
     eapply IH; [|reflexivity]. lia. }
 intros a b c. exact (E (a+2*b) a b eq_refl c).
Qed.

Local Lemma cube_B0_zero : forall a b, H (StB,S0) 0 [a;b;0].
Proof.
 induction a as [a IH] using lt_wf_ind. intro b.
 destruct (cube_parity a) as (k & E). destruct E as [E|E]; subst a.
 - replace (2*k) with (2*k+0) by lia. apply cube_loop.
   apply e0,e6,e8. cbn [Nat.add].
   destruct k as [|[|k]].
   + apply f9. simpl; auto 12.
   + change (H (StB,S0) 7 [0+1;b+1]). apply e10,f11. simpl; auto 12.
   + replace (S(S k)) with ((k+1)+1) by lia.
     apply e10,e12. apply IH. lia.
 - apply cube_loop. change (H (StB,S0) 0 [0+1;b+k;0+k]).
   apply e1,f2. simpl; auto 12.
Qed.

Local Lemma cube_seven_B0 : forall a b, H (StB,S0) 7 [a;b].
Proof.
 intros [|[|a]] b.
 - apply f9. simpl; auto 12.
 - change (H (StB,S0) 7 [0+1;b]). apply e10,f11. simpl; auto 12.
 - replace (S(S a)) with ((a+1)+1) by lia. apply e10,e12,cube_B0_zero.
Qed.

Local Lemma cube_B0 : forall a b c, H (StB,S0) 0 [a;b;c].
Proof.
 intros a b c. destruct (cube_parity a) as (k & [-> | ->]).
 - replace (2*k) with (2*k+0) by lia. apply cube_loop,e0,e6,e8,cube_seven_B0.
 - apply cube_loop. change (H (StB,S0) 0 [0+1;b+k;c+k]).
   apply e1,f2. simpl; auto 12.
Qed.

Local Lemma cube_seven_C1 : forall a b, H (StC,S1) 7 [a;b].
Proof.
 intros [|a] b.
 - apply f9. simpl; auto 12.
 - replace (S a) with (a+1) by lia. apply f10. simpl; auto 12.
Qed.

Local Opaque H.

Local Lemma cube_zero : forall a b c t, H t 0 [a;b;c].
Proof.
 intros [|[|a]] b c [q h]; destruct q,h;
 try solve [apply cube_D0]; try solve [apply cube_B0].
 all: try solve [apply f0; simpl; auto 12].
 all: try solve [apply e0,f6; simpl; auto 12].
 all: try solve [apply e0,e6,f8; simpl; auto 12].
 all: try solve [apply e0,e6,e8,cube_seven_C1].
 all: replace 1 with (0+1) by lia.
 all: try solve [apply f1; simpl; auto 12].
 all: try solve [apply e1,f2; simpl; auto 12].
 all: try solve [apply e1,e2,e4,f5; simpl; auto 12].
 all: replace (S(S a)) with ((a+1)+1) by lia.
 all: try solve [apply f1; simpl; auto 12].
 all: apply e1,f3; simpl; auto 12.
Qed.

Local Lemma cube_one : forall a b c, 0<a+b -> forall t, H t 1 [a;b;c].
Proof.
 intros a [|b] c Pos t.
 - destruct a as [|a]; [lia|]. replace (S a) with (a+1) by lia.
   apply e2,e4,e5,e7,e3,cube_zero.
 - replace (S b) with (b+1) by lia. apply e3,cube_zero.
Qed.

Local Lemma cube_five : forall a b, 0<a -> forall t, H t 5 [a;b].
Proof. intros a b Pos t. apply e7,cube_one. lia. Qed.

Local Lemma cube_eight : forall a b, 0<a+b -> forall t, H t 8 [a;b].
Proof.
 intros a [|b] Pos t.
 - apply e11,e13,e14,cube_five. lia.
 - replace (S b) with (b+1) by lia. apply e12,cube_zero.
Qed.

Local Lemma cube_seven : forall a b t, H t 7 [a;b].
Proof.
 intros [|a] b t.
 - apply e9,e15,e16,e17,cube_eight. lia.
 - replace (S a) with (a+1) by lia. apply e10,cube_eight. lia.
Qed.
Local Definition cube_inv (a : nat * list nat) : Prop :=
 let x := nth 0 (snd a) 0 in let y := nth 1 (snd a) 0 in
 match fst a with
 | 1 | 8 => 0<x+y
 | 2 | 3 | 5 | 9 | 10 => 0<x
 | _ => True
 end.

Local Lemma cube_inv_next : forall a, Good fams a -> cube_inv a -> cube_inv (tnxt fams leaves a).
Proof.
 apply (tri_leaf_invariant tm fams leaves cube_inv families_ok).
 intros lf EL z. cbn [leaves cert tc_leaves] in EL.
 destruct EL as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]]]]];
 cbv [cube_inv tl_f tl_g tl_tgt tl_reg rsub reg1 seq combine map aeval teval a_c a_t fst snd Nat.eqb Nat.mul Nat.add nth length];
 intros; fold Nat.add in *; try trivial; lia.
Qed.

Local Lemma cube_all : forall a, Good fams a -> cube_inv a -> forall t,
 tri_reaches_fire tm t (tanc fams a).
Proof.
 intros [i v] (F & EF & EL) Pos t. change (H t i v).
 cbn [fst snd] in EF, EL.
 assert (Hi : i < 14).
 { change (i < length fams). apply nth_error_Some. rewrite EF. discriminate. }
 destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]];
 cbn [fams cert tc_fams nth_error] in EF; try discriminate; try lia;
 injection EF as <-; cbn [tf_n] in EL.
 all: repeat match goal with
 | EL : length ?v = S ?n |- _ =>
   let x := fresh "x" in let r := fresh "r" in
   destruct v as [|x r]; [discriminate|]; cbn [length] in EL; apply Nat.succ_inj in EL
 end.
 all: match goal with EL : length ?v = 0 |- _ =>
   apply length_zero_iff_nil in EL; subst v
 end.
 all: unfold cube_inv in Pos; cbn [fst snd nth] in Pos.
 - apply cube_zero.
 - apply cube_one; exact Pos.
 - apply e4,e5,cube_five; exact Pos.
 - apply e5,cube_five; exact Pos.
 - apply e6,e8,cube_seven.
 - apply cube_five; exact Pos.
 - apply e8,cube_seven.
 - apply cube_seven.
 - apply cube_eight; exact Pos.
 - apply e13,e14,cube_five; exact Pos.
 - apply e14,cube_five; exact Pos.
 - apply e15,e16,e17,cube_eight; lia.
 - apply e16,e17,cube_eight; lia.
 - apply e17,cube_eight; lia.
Qed.

Lemma cv_AST_72_0000 : coversTr (row_to_tm r_AST_72_0000).
Proof.
 apply coversTr_nqh, neverqhtr_mirror. change (NeverQuasiHaltsTr tm).
 apply (tri_reach_glue_invariant tm fams leaves cube_inv families_ok (0,[23;6;1])).
 - eexists. split; reflexivity.
 - exact I.
 - exact cube_inv_next.
 - assert (EB : exists c, csteps tm 3000 c0 = Some c /\
     ceqb c (tanc fams (0,[23;6;1])) = true).
   { eexists. split; vm_compute; reflexivity. }
   destruct EB as (c & EC & EE). exists 3000.
   rewrite <- lift_c0.
   pose proof (csteps_lift tm 3000 c0 c EC) as EB.
   rewrite (ceqb_lift _ _ EE) in EB. exact EB.
 - exact cube_all.
Qed.

Definition cbtrows_AST_72 : list (list (option Trans)) := [r_AST_72_0000].
Lemma cbt_AST_72_covers : Forall coversTr (map row_to_tm cbtrows_AST_72).
Proof. constructor; [exact cv_AST_72_0000|constructor]. Qed.
