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
(* spec 1RB1LA_1LB0RC_1LD1RC_0LC0LA *)
Definition r_AST_73_0000 : list (option Trans) := [t1RB;t1LA;t1LB;t0RC;t1LD;t1RC;t0LC;t0LA].
Local Definition tm := mirror_tm (row_to_tm r_AST_73_0000).
Local Definition cert : tcert := (mkTC []
      [(mkTF StC S1 [(SB [S1] (mkA 6 [(0,1)]));(SL [S0]);(SB [S1] (mkA 7 [(1,1)]))] [(SB [S1] (mkA 18 [(2,1)]));(SL [S0]);(SB [S1] (mkA 2 [(3,1)]))] 4 [(TLeaf 0)]);
      (mkTF StD S1 [(SB [S1] (mkA 2 [(0,1)]))] [(SB [S1] (mkA 0 [(1,1)]));(SL [S0]);(SB [S1] (mkA 2 [(2,1)]))] 3 [(TSplit 1 1 1 [1;2]);(TLeaf 1);(TLeaf 2)]);
      (mkTF StB S1 [(SB [S1] (mkA 0 [(0,1)]));(SL [S0]);(SB [S1] (mkA 2 [(1,1)]))] [(SB [S1] (mkA 2 [(2,1)]))] 3 [(TSplit 0 1 1 [1;2]);(TLeaf 3);(TLeaf 4)]);
      (mkTF StC S1 [(SB [S1] (mkA 2 [(0,1)]))] [(SL [S0]);(SB [S1] (mkA 2 [(1,1)]))] 2 [(TLeaf 5)]);
      (mkTF StD S1 [(SL [S1])] [(SB [S1] (mkA 2 [(0,1)]));(SL [S0]);(SB [S1] (mkA 2 [(1,1)]))] 2 [(TLeaf 6)]);
      (mkTF StD S0 [(SB [S1] (mkA 3 [(0,1)]))] [(SB [S1] (mkA 2 [(1,1)]))] 2 [(TLeaf 7)]);
      (mkTF StB S1 [(SB [S1] (mkA 1 [(0,1)]));(SL [S0;S1])] [(SB [S1] (mkA 2 [(1,1)]))] 2 [(TLeaf 8)]);
      (mkTF StD S1 [(SB [S1] (mkA 4 [(0,1)]))] [(SB [S1] (mkA 1 [(1,1)]))] 2 [(TLeaf 9)]);
      (mkTF StB S1 [(SB [S1] (mkA 0 [(0,1)]));(SL [S0]);(SB [S1] (mkA 4 [(1,1)]))] [(SL [S1])] 2 [(TSplit 0 1 1 [1;2]);(TLeaf 10);(TLeaf 11)]);
      (mkTF StD S1 [(SB [S1] (mkA 2 [(0,1)]))] [(SB [S1] (mkA 0 [(1,1)]));(SL [S0;S1])] 2 [(TSplit 1 1 1 [1;2]);(TLeaf 12);(TLeaf 13)]);
      (mkTF StC S1 [(SB [S1] (mkA 2 [(0,1)]))] [(SL [S0;S1])] 1 [(TLeaf 14)]);
      (mkTF StD S1 [(SL [S1])] [(SB [S1] (mkA 2 [(0,1)]));(SL [S0;S1])] 1 [(TLeaf 15)]);
      (mkTF StC S1 [(SB [S1] (mkA 4 [(0,1)]))] [(SB [S1] (mkA 2 [(1,1)]))] 2 [(TLeaf 16)]);
      (mkTF StD S1 [(SL [S1])] [(SB [S1] (mkA 6 [(0,1)]))] 1 [(TLeaf 17)]);
      (mkTF StB S1 [(SB [S1] (mkA 5 [(0,1)]));(SL [S0;S1])] [(SL [S1])] 1 [(TLeaf 18)])]
      [(mkTL 0 [(1,0);(1,0);(1,0);(1,0)] 1 [(mkA 6 [(1,1)]);(mkA 24 [(0,1);(2,1)]);(mkA 0 [(3,1)])] (mkC StC (mkS [] [S1] 1 6 [S0]) S1 (mkS [] [] 0 0 [])) 0 false false 2 0 [(SCycL 1 0); (SWin 2)]);
      (mkTL 1 [(1,0);(0,0);(1,0)] 3 [(mkA 0 [(0,1)]);(mkA 0 [(2,1)])] (mkC StD (mkS [] [] 0 0 []) S1 (mkS [S0] [] 0 0 [])) 0 false false 0 2 [(SWin 4)]);
      (mkTL 1 [(1,0);(1,1);(1,0)] 2 [(mkA 0 [(1,1)]);(mkA 0 [(0,1)]);(mkA 1 [(2,1)])] (mkC StD (mkS [] [] 0 0 []) S1 (mkS [S1] [S1] 1 0 [S0])) 1 false false 0 2 [(SWin 1); (SCycR 1); (SWin 2)]);
      (mkTL 2 [(0,0);(1,0);(1,0)] 5 [(mkA 0 [(1,1)]);(mkA 0 [(2,1)])] (mkC StB (mkS [S0] [] 0 0 []) S1 (mkS [] [] 0 0 [])) 0 false false 2 0 [(SWin 2)]);
      (mkTL 2 [(1,1);(1,0);(1,0)] 1 [(mkA 1 [(1,1)]);(mkA 0 [(0,1)]);(mkA 0 [(2,1)])] (mkC StB (mkS [S1] [S1] 1 0 [S0]) S1 (mkS [] [] 0 0 [])) 0 false false 2 0 [(SWin 1); (SCycL 1 0); (SWin 2)]);
      (mkTL 3 [(1,0);(1,0)] 4 [(mkA 0 [(0,1)]);(mkA 0 [(1,1)])] (mkC StC (mkS [] [S1] 1 2 []) S1 (mkS [S0] [] 0 0 [])) 0 true false 1 1 [(SCycL 1 0); (SWinL 1); (SWin 1)]);
      (mkTL 4 [(1,0);(1,0)] 6 [(mkA 0 [(0,1)]);(mkA 1 [(1,1)])] (mkC StD (mkS [S1] [] 0 0 []) S1 (mkS [S1] [S1] 1 1 [S0])) 0 true false 1 2 [(SWin 1); (SCycR 1); (SWin 2)]);
      (mkTL 5 [(1,0);(1,0)] 7 [(mkA 0 [(0,1)]);(mkA 0 [(1,1)])] (mkC StD (mkS [] [] 0 0 []) S0 (mkS [S1] [S1] 1 1 [])) 1 false true 0 1 [(SWin 3)]);
      (mkTL 6 [(1,0);(1,0)] 1 [(mkA 0 []);(mkA 0 [(0,1)]);(mkA 0 [(1,1)])] (mkC StB (mkS [S1] [S1] 1 0 [S0;S1]) S1 (mkS [] [] 0 0 [])) 0 true false 2 0 [(SWin 1); (SCycL 1 0); (SWin 2)]);
      (mkTL 7 [(1,0);(1,0)] 8 [(mkA 0 [(1,1)]);(mkA 0 [(0,1)])] (mkC StD (mkS [] [] 0 0 []) S1 (mkS [S1] [S1] 1 0 [])) 1 false true 0 1 [(SWin 1); (SCycR 1); (SWinR 1); (SWin 1)]);
      (mkTL 8 [(0,0);(1,0)] 12 [(mkA 0 [(1,1)]);(mkA 0 [])] (mkC StB (mkS [S0] [] 0 0 []) S1 (mkS [S1] [] 0 0 [])) 0 false true 2 1 [(SWin 5); (SWinR 1); (SWin 5)]);
      (mkTL 8 [(1,1);(1,0)] 9 [(mkA 3 [(1,1)]);(mkA 0 [(0,1)])] (mkC StB (mkS [S1] [S1] 1 0 [S0]) S1 (mkS [S1] [] 0 0 [])) 0 false true 2 1 [(SWin 1); (SCycL 1 0); (SWin 2)]);
      (mkTL 9 [(1,0);(0,0)] 10 [(mkA 0 [(0,1)])] (mkC StD (mkS [] [] 0 0 []) S1 (mkS [S0;S1] [] 0 0 [])) 0 false true 0 2 [(SWin 4)]);
      (mkTL 9 [(1,0);(1,1)] 2 [(mkA 0 [(1,1)]);(mkA 0 [(0,1)]);(mkA 0 [])] (mkC StD (mkS [] [] 0 0 []) S1 (mkS [S1] [S1] 1 0 [S0;S1])) 1 false true 0 2 [(SWin 1); (SCycR 1); (SWin 2)]);
      (mkTL 10 [(1,0)] 11 [(mkA 0 [(0,1)])] (mkC StC (mkS [] [S1] 1 2 []) S1 (mkS [S0;S1] [] 0 0 [])) 0 true true 1 1 [(SCycL 1 0); (SWinL 1); (SWin 1)]);
      (mkTL 11 [(1,0)] 6 [(mkA 0 [(0,1)]);(mkA 0 [])] (mkC StD (mkS [S1] [] 0 0 []) S1 (mkS [S1] [S1] 1 1 [S0;S1])) 0 true true 1 2 [(SWin 1); (SCycR 1); (SWin 2)]);
      (mkTL 12 [(1,0);(1,0)] 13 [(mkA 0 [(0,1);(1,1)])] (mkC StC (mkS [] [S1] 1 4 []) S1 (mkS [] [] 0 0 [])) 0 true false 1 0 [(SCycL 1 0); (SWinL 1); (SWin 1)]);
      (mkTL 13 [(1,0)] 14 [(mkA 0 [(0,1)])] (mkC StD (mkS [S1] [] 0 0 []) S1 (mkS [S1] [S1] 1 5 [])) 0 true true 1 1 [(SWin 1); (SCycR 1); (SWinR 1); (SWin 1)]);
      (mkTL 14 [(1,0)] 9 [(mkA 0 []);(mkA 4 [(0,1)])] (mkC StB (mkS [S1] [S1] 1 4 [S0;S1]) S1 (mkS [S1] [] 0 0 [])) 0 true true 2 1 [(SWin 1); (SCycL 1 0); (SWin 2)])]
      1 []
      []
      3000 0 [0;0;0;0]).
Local Definition fams := tc_fams cert.
Local Definition leaves := tc_leaves cert.
Local Definition H (t : Instr) (i : nat) (v : list nat) := tri_reaches_fire tm t (tanc fams (i,v)).
Local Lemma families_ok : fams_ok tm fams leaves = true.
Proof. vm_compute. reflexivity. Qed.


Local Ltac cube_norm :=
 cbn [fams leaves cert tc_fams tc_leaves nth tl_tgt tl_reg rsub reg1 seq combine map aeval teval a_c a_t fst snd Nat.eqb Nat.mul Nat.add] in *;
 cbv beta iota zeta delta [TriGlueTr.rsub TriGlueTr.reg1 seq combine map aeval teval a_c a_t fst snd Nat.eqb Nat.mul Nat.add nth length] in *;
 rewrite ?Nat.add_0_r in *.

Local Lemma e0 : forall a b c d t, H t 1 [b+6;a+c+24;d] -> H t 0 [a;b;c;d].
Proof.
 intros a b c d t E.
 pose proof (tri_leaf_back tm fams (nth 0 fams (mkTF StA S0 [] [] 0 []))
   (nth 0 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   (nth 1 fams (mkTF StA S0 [] [] 0 []))
   ltac:(vm_compute;reflexivity) ltac:(reflexivity) [a;b;c;d] t) as B.
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

Local Lemma e1 : forall a c t, H t 3 [a;c] -> H t 1 [a;0;c].
Proof.
 intros a c t E.
 pose proof (tri_leaf_back tm fams (nth 1 fams (mkTF StA S0 [] [] 0 []))
   (nth 1 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   (nth 3 fams (mkTF StA S0 [] [] 0 []))
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

Local Lemma e2 : forall a b c t, H t 2 [b;a;c+1] -> H t 1 [a;b+1;c].
Proof.
 intros a b c t E.
 pose proof (tri_leaf_back tm fams (nth 1 fams (mkTF StA S0 [] [] 0 []))
   (nth 2 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   (nth 2 fams (mkTF StA S0 [] [] 0 []))
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

Local Lemma e3 : forall b c t, H t 5 [b;c] -> H t 2 [0;b;c].
Proof.
 intros b c t E.
 pose proof (tri_leaf_back tm fams (nth 2 fams (mkTF StA S0 [] [] 0 []))
   (nth 3 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   (nth 5 fams (mkTF StA S0 [] [] 0 []))
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

Local Lemma e4 : forall a b c t, H t 1 [b+1;a;c] -> H t 2 [a+1;b;c].
Proof.
 intros a b c t E.
 pose proof (tri_leaf_back tm fams (nth 2 fams (mkTF StA S0 [] [] 0 []))
   (nth 4 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
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

Local Lemma e5 : forall a b t, H t 4 [a;b] -> H t 3 [a;b].
Proof.
 intros a b t E.
 pose proof (tri_leaf_back tm fams (nth 3 fams (mkTF StA S0 [] [] 0 []))
   (nth 5 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   (nth 4 fams (mkTF StA S0 [] [] 0 []))
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

Local Lemma e6 : forall a b t, H t 6 [a;b+1] -> H t 4 [a;b].
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

Local Lemma e7 : forall a b t, H t 7 [a;b] -> H t 5 [a;b].
Proof.
 intros a b t E.
 pose proof (tri_leaf_back tm fams (nth 5 fams (mkTF StA S0 [] [] 0 []))
   (nth 7 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
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

Local Lemma e8 : forall a b t, H t 1 [0;a;b] -> H t 6 [a;b].
Proof.
 intros a b t E.
 pose proof (tri_leaf_back tm fams (nth 6 fams (mkTF StA S0 [] [] 0 []))
   (nth 8 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
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

Local Lemma e9 : forall a b t, H t 8 [b;a] -> H t 7 [a;b].
Proof.
 intros a b t E.
 pose proof (tri_leaf_back tm fams (nth 7 fams (mkTF StA S0 [] [] 0 []))
   (nth 9 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
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

Local Lemma e10 : forall b t, H t 12 [b;0] -> H t 8 [0;b].
Proof.
 intros b t E.
 pose proof (tri_leaf_back tm fams (nth 8 fams (mkTF StA S0 [] [] 0 []))
   (nth 10 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   (nth 12 fams (mkTF StA S0 [] [] 0 []))
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

Local Lemma e11 : forall a b t, H t 9 [b+3;a] -> H t 8 [a+1;b].
Proof.
 intros a b t E.
 pose proof (tri_leaf_back tm fams (nth 8 fams (mkTF StA S0 [] [] 0 []))
   (nth 11 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   (nth 9 fams (mkTF StA S0 [] [] 0 []))
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

Local Lemma e12 : forall a t, H t 10 [a] -> H t 9 [a;0].
Proof.
 intros a t E.
 pose proof (tri_leaf_back tm fams (nth 9 fams (mkTF StA S0 [] [] 0 []))
   (nth 12 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   (nth 10 fams (mkTF StA S0 [] [] 0 []))
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

Local Lemma e13 : forall a b t, H t 2 [b;a;0] -> H t 9 [a;b+1].
Proof.
 intros a b t E.
 pose proof (tri_leaf_back tm fams (nth 9 fams (mkTF StA S0 [] [] 0 []))
   (nth 13 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   (nth 2 fams (mkTF StA S0 [] [] 0 []))
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

Local Lemma e14 : forall a t, H t 11 [a] -> H t 10 [a].
Proof.
 intros a t E.
 pose proof (tri_leaf_back tm fams (nth 10 fams (mkTF StA S0 [] [] 0 []))
   (nth 14 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   (nth 11 fams (mkTF StA S0 [] [] 0 []))
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

Local Lemma e15 : forall a t, H t 6 [a;0] -> H t 11 [a].
Proof.
 intros a t E.
 pose proof (tri_leaf_back tm fams (nth 11 fams (mkTF StA S0 [] [] 0 []))
   (nth 15 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   (nth 6 fams (mkTF StA S0 [] [] 0 []))
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

Local Lemma e16 : forall a b t, H t 13 [a+b] -> H t 12 [a;b].
Proof.
 intros a b t E.
 pose proof (tri_leaf_back tm fams (nth 12 fams (mkTF StA S0 [] [] 0 []))
   (nth 16 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   (nth 13 fams (mkTF StA S0 [] [] 0 []))
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

Local Lemma e17 : forall a t, H t 14 [a] -> H t 13 [a].
Proof.
 intros a t E.
 pose proof (tri_leaf_back tm fams (nth 13 fams (mkTF StA S0 [] [] 0 []))
   (nth 17 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   (nth 14 fams (mkTF StA S0 [] [] 0 []))
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

Local Lemma e18 : forall a t, H t 9 [0;a+4] -> H t 14 [a].
Proof.
 intros a t E.
 pose proof (tri_leaf_back tm fams (nth 14 fams (mkTF StA S0 [] [] 0 []))
   (nth 18 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   (nth 9 fams (mkTF StA S0 [] [] 0 []))
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

Local Lemma f0 : forall a b c d t, In t [(StC,S0);(StC,S1);(StD,S1)] -> H t 0 [a;b;c;d].
Proof.
 intros a b c d t Et.
 pose proof (tri_leaf_now tm fams (nth 0 fams (mkTF StA S0 [] [] 0 []))
   (nth 0 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   ltac:(vm_compute;reflexivity) t ltac:(vm_compute in Et |- *; tauto) [a;b;c;d]) as B.
 cube_norm.
 unfold H, tanc. cbn [fams cert tc_fams nth_error fst snd].
 match type of B with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact B
  end end.
Qed.

Local Lemma f1 : forall a c t, In t [(StA,S0);(StB,S0);(StB,S1);(StC,S1);(StD,S1)] -> H t 1 [a;0;c].
Proof.
 intros a c t Et.
 pose proof (tri_leaf_now tm fams (nth 1 fams (mkTF StA S0 [] [] 0 []))
   (nth 1 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   ltac:(vm_compute;reflexivity) t ltac:(vm_compute in Et |- *; tauto) [a;0;c]) as B.
 cube_norm.
 unfold H, tanc. cbn [fams cert tc_fams nth_error fst snd].
 match type of B with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact B
  end end.
Qed.

Local Lemma f2 : forall a b c t, In t [(StA,S0);(StA,S1);(StB,S1);(StD,S1)] -> H t 1 [a;b+1;c].
Proof.
 intros a b c t Et.
 pose proof (tri_leaf_now tm fams (nth 1 fams (mkTF StA S0 [] [] 0 []))
   (nth 2 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   ltac:(vm_compute;reflexivity) t ltac:(vm_compute in Et |- *; tauto) [a;b;c]) as B.
 cube_norm.
 unfold H, tanc. cbn [fams cert tc_fams nth_error fst snd].
 match type of B with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact B
  end end.
Qed.

Local Lemma f3 : forall b c t, In t [(StB,S1);(StC,S0);(StD,S0)] -> H t 2 [0;b;c].
Proof.
 intros b c t Et.
 pose proof (tri_leaf_now tm fams (nth 2 fams (mkTF StA S0 [] [] 0 []))
   (nth 3 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   ltac:(vm_compute;reflexivity) t ltac:(vm_compute in Et |- *; tauto) [0;b;c]) as B.
 cube_norm.
 unfold H, tanc. cbn [fams cert tc_fams nth_error fst snd].
 match type of B with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact B
  end end.
Qed.

Local Lemma f4 : forall a b c t, In t [(StB,S1);(StC,S0);(StC,S1);(StD,S1)] -> H t 2 [a+1;b;c].
Proof.
 intros a b c t Et.
 pose proof (tri_leaf_now tm fams (nth 2 fams (mkTF StA S0 [] [] 0 []))
   (nth 4 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   ltac:(vm_compute;reflexivity) t ltac:(vm_compute in Et |- *; tauto) [a;b;c]) as B.
 cube_norm.
 unfold H, tanc. cbn [fams cert tc_fams nth_error fst snd].
 match type of B with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact B
  end end.
Qed.

Local Lemma f5 : forall a b t, In t [(StC,S0);(StC,S1);(StD,S1)] -> H t 3 [a;b].
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

Local Lemma f6 : forall a b t, In t [(StA,S0);(StA,S1);(StB,S1);(StD,S1)] -> H t 4 [a;b].
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

Local Lemma f7 : forall a b t, In t [(StC,S0);(StC,S1);(StD,S0);(StD,S1)] -> H t 5 [a;b].
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

Local Lemma f8 : forall a b t, In t [(StB,S1);(StC,S0);(StC,S1);(StD,S1)] -> H t 6 [a;b].
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

Local Lemma f9 : forall a b t, In t [(StA,S0);(StA,S1);(StB,S1);(StD,S1)] -> H t 7 [a;b].
Proof.
 intros a b t Et.
 pose proof (tri_leaf_now tm fams (nth 7 fams (mkTF StA S0 [] [] 0 []))
   (nth 9 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   ltac:(vm_compute;reflexivity) t ltac:(vm_compute in Et |- *; tauto) [a;b]) as B.
 cube_norm.
 unfold H, tanc. cbn [fams cert tc_fams nth_error fst snd].
 match type of B with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact B
  end end.
Qed.

Local Lemma f10 : forall b t, In t [(StA,S0);(StB,S0);(StB,S1);(StC,S0);(StC,S1);(StD,S0);(StD,S1)] -> H t 8 [0;b].
Proof.
 intros b t Et.
 pose proof (tri_leaf_now tm fams (nth 8 fams (mkTF StA S0 [] [] 0 []))
   (nth 10 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   ltac:(vm_compute;reflexivity) t ltac:(vm_compute in Et |- *; tauto) [0;b]) as B.
 cube_norm.
 unfold H, tanc. cbn [fams cert tc_fams nth_error fst snd].
 match type of B with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact B
  end end.
Qed.

Local Lemma f11 : forall a b t, In t [(StB,S1);(StC,S0);(StC,S1);(StD,S1)] -> H t 8 [a+1;b].
Proof.
 intros a b t Et.
 pose proof (tri_leaf_now tm fams (nth 8 fams (mkTF StA S0 [] [] 0 []))
   (nth 11 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   ltac:(vm_compute;reflexivity) t ltac:(vm_compute in Et |- *; tauto) [a;b]) as B.
 cube_norm.
 unfold H, tanc. cbn [fams cert tc_fams nth_error fst snd].
 match type of B with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact B
  end end.
Qed.

Local Lemma f12 : forall a t, In t [(StA,S0);(StB,S0);(StB,S1);(StC,S1);(StD,S1)] -> H t 9 [a;0].
Proof.
 intros a t Et.
 pose proof (tri_leaf_now tm fams (nth 9 fams (mkTF StA S0 [] [] 0 []))
   (nth 12 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   ltac:(vm_compute;reflexivity) t ltac:(vm_compute in Et |- *; tauto) [a;0]) as B.
 cube_norm.
 unfold H, tanc. cbn [fams cert tc_fams nth_error fst snd].
 match type of B with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact B
  end end.
Qed.

Local Lemma f13 : forall a b t, In t [(StA,S0);(StA,S1);(StB,S1);(StD,S1)] -> H t 9 [a;b+1].
Proof.
 intros a b t Et.
 pose proof (tri_leaf_now tm fams (nth 9 fams (mkTF StA S0 [] [] 0 []))
   (nth 13 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   ltac:(vm_compute;reflexivity) t ltac:(vm_compute in Et |- *; tauto) [a;b]) as B.
 cube_norm.
 unfold H, tanc. cbn [fams cert tc_fams nth_error fst snd].
 match type of B with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact B
  end end.
Qed.

Local Lemma f14 : forall a t, In t [(StC,S0);(StC,S1);(StD,S1)] -> H t 10 [a].
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

Local Lemma f15 : forall a t, In t [(StA,S0);(StA,S1);(StB,S1);(StD,S1)] -> H t 11 [a].
Proof.
 intros a t Et.
 pose proof (tri_leaf_now tm fams (nth 11 fams (mkTF StA S0 [] [] 0 []))
   (nth 15 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   ltac:(vm_compute;reflexivity) t ltac:(vm_compute in Et |- *; tauto) [a]) as B.
 cube_norm.
 unfold H, tanc. cbn [fams cert tc_fams nth_error fst snd].
 match type of B with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact B
  end end.
Qed.

Local Lemma f16 : forall a b t, In t [(StC,S0);(StC,S1);(StD,S1)] -> H t 12 [a;b].
Proof.
 intros a b t Et.
 pose proof (tri_leaf_now tm fams (nth 12 fams (mkTF StA S0 [] [] 0 []))
   (nth 16 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   ltac:(vm_compute;reflexivity) t ltac:(vm_compute in Et |- *; tauto) [a;b]) as B.
 cube_norm.
 unfold H, tanc. cbn [fams cert tc_fams nth_error fst snd].
 match type of B with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact B
  end end.
Qed.

Local Lemma f17 : forall a t, In t [(StA,S0);(StA,S1);(StB,S1);(StD,S1)] -> H t 13 [a].
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

Local Lemma f18 : forall a t, In t [(StB,S1);(StC,S0);(StC,S1);(StD,S1)] -> H t 14 [a].
Proof.
 intros a t Et.
 pose proof (tri_leaf_now tm fams (nth 14 fams (mkTF StA S0 [] [] 0 []))
   (nth 18 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   ltac:(vm_compute;reflexivity) t ltac:(vm_compute in Et |- *; tauto) [a]) as B.
 cube_norm.
 unfold H, tanc. cbn [fams cert tc_fams nth_error fst snd].
 match type of B with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact B
  end end.
Qed.

Local Ltac cube_now := first [solve [apply f0; simpl; auto] | solve [apply f1; simpl; auto] | solve [apply f2; simpl; auto] | solve [apply f3; simpl; auto] | solve [apply f4; simpl; auto] | solve [apply f5; simpl; auto] | solve [apply f6; simpl; auto] | solve [apply f7; simpl; auto] | solve [apply f8; simpl; auto] | solve [apply f9; simpl; auto] | solve [apply f10; simpl; auto] | solve [apply f11; simpl; auto] | solve [apply f12; simpl; auto] | solve [apply f13; simpl; auto] | solve [apply f14; simpl; auto] | solve [apply f15; simpl; auto] | solve [apply f16; simpl; auto] | solve [apply f17; simpl; auto] | solve [apply f18; simpl; auto]].
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
 H t 2 [a;b+k;c+k] -> H t 2 [2*k+a;b;c].
Proof.
 induction k as [|k IH]; intros a b c t E.
 - cbn [Nat.mul Nat.add]. cube_exact E.
 - replace (2*S k+a) with ((2*k+a)+1+1) by lia.
   apply e4,e2. apply IH. cube_exact E.
Qed.

Local Lemma cube_D0 : forall a b c, H (StD,S0) 2 [a;b;c].
Proof.
 assert (E : forall m a b, a+2*b=m -> forall c, H (StD,S0) 2 [a;b;c]).
 { induction m as [m IH] using lt_wf_ind. intros a b Em c.
   destruct (cube_parity a) as (k & [-> | ->]).
   - replace (2*k) with (2*k+0) by lia. apply cube_loop,f3. simpl; auto 12.
   - apply cube_loop. change (H (StD,S0) 2 [0+1;b+k;c+k]).
     apply e4,e1,e5,e6,e8,e2.
     eapply IH; [|reflexivity]. lia. }
 intros a b c. exact (E (a+2*b) a b eq_refl c).
Qed.

Local Lemma cube_B0_zero : forall a b, H (StB,S0) 2 [a;b;0].
Proof.
 induction a as [a IH] using lt_wf_ind. intro b.
 destruct (cube_parity a) as (k & E). destruct E as [E|E]; subst a.
 - replace (2*k) with (2*k+0) by lia. apply cube_loop.
   apply e3,e7,e9. cbn [Nat.add].
   destruct k as [|[|k]].
   + apply f10. simpl; auto 12.
   + change (H (StB,S0) 8 [0+1;b+1]). apply e11,f12. simpl; auto 12.
   + replace (S(S k)) with ((k+1)+1) by lia.
     apply e11,e13. apply IH. lia.
 - apply cube_loop. change (H (StB,S0) 2 [0+1;b+k;0+k]).
   apply e4,f1. simpl; auto 12.
Qed.

Local Lemma cube_seven_B0 : forall a b, H (StB,S0) 8 [a;b].
Proof.
 intros [|[|a]] b.
 - apply f10. simpl; auto 12.
 - change (H (StB,S0) 8 [0+1;b]). apply e11,f12. simpl; auto 12.
 - replace (S(S a)) with ((a+1)+1) by lia. apply e11,e13,cube_B0_zero.
Qed.

Local Lemma cube_B0 : forall a b c, H (StB,S0) 2 [a;b;c].
Proof.
 intros a b c. destruct (cube_parity a) as (k & [-> | ->]).
 - replace (2*k) with (2*k+0) by lia. apply cube_loop,e3,e7,e9,cube_seven_B0.
 - apply cube_loop. change (H (StB,S0) 2 [0+1;b+k;c+k]).
   apply e4,f1. simpl; auto 12.
Qed.

Local Lemma cube_seven_C1 : forall a b, H (StC,S1) 8 [a;b].
Proof.
 intros [|a] b.
 - apply f10. simpl; auto 12.
 - replace (S a) with (a+1) by lia. apply f11. simpl; auto 12.
Qed.

Local Opaque H.

Local Lemma cube_zero : forall a b c t, H t 2 [a;b;c].
Proof.
 intros [|[|a]] b c [q h]; destruct q,h;
 try solve [apply cube_D0]; try solve [apply cube_B0].
 all: try solve [apply f3; simpl; auto 12].
 all: try solve [apply e3,f7; simpl; auto 12].
 all: try solve [apply e3,e7,f9; simpl; auto 12].
 all: try solve [apply e3,e7,e9,cube_seven_C1].
 all: replace 1 with (0+1) by lia.
 all: try solve [apply f4; simpl; auto 12].
 all: try solve [apply e4,f1; simpl; auto 12].
 all: try solve [apply e4,e1,e5,f6; simpl; auto 12].
 all: replace (S(S a)) with ((a+1)+1) by lia.
 all: try solve [apply f4; simpl; auto 12].
 all: apply e4,f2; simpl; auto 12.
Qed.

Local Lemma cube_one : forall a b c, 0<a+b -> forall t, H t 1 [a;b;c].
Proof.
 intros a [|b] c Pos t.
 - destruct a as [|a]; [lia|]. replace (S a) with (a+1) by lia.
   apply e1,e5,e6,e8,e2,cube_zero.
 - replace (S b) with (b+1) by lia. apply e2,cube_zero.
Qed.

Local Lemma cube_five : forall a b, 0<a -> forall t, H t 6 [a;b].
Proof. intros a b Pos t. apply e8,cube_one. lia. Qed.

Local Lemma cube_eight : forall a b, 0<a+b -> forall t, H t 9 [a;b].
Proof.
 intros a [|b] Pos t.
 - apply e12,e14,e15,cube_five. lia.
 - replace (S b) with (b+1) by lia. apply e13,cube_zero.
Qed.

Local Lemma cube_seven : forall a b t, H t 8 [a;b].
Proof.
 intros [|a] b t.
 - apply e10,e16,e17,e18,cube_eight. lia.
 - replace (S a) with (a+1) by lia. apply e11,cube_eight. lia.
Qed.
Local Definition cube_inv (a : nat * list nat) : Prop :=
 let x := nth 0 (snd a) 0 in let y := nth 1 (snd a) 0 in
 match fst a with
 | 1 | 9 => 0<x+y
 | 3 | 4 | 6 | 10 | 11 => 0<x
 | _ => True
 end.

Local Lemma cube_inv_next : forall a, Good fams a -> cube_inv a -> cube_inv (tnxt fams leaves a).
Proof.
 apply (tri_leaf_invariant tm fams leaves cube_inv families_ok).
 intros lf EL z. cbn [leaves cert tc_leaves] in EL.
 destruct EL as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]]]]]];
 cbv [cube_inv tl_f tl_g tl_tgt tl_reg rsub reg1 seq combine map aeval teval a_c a_t fst snd Nat.eqb Nat.mul Nat.add nth length];
 intros; fold Nat.add in *; try trivial; lia.
Qed.

Local Lemma cube_all : forall a, Good fams a -> cube_inv a -> forall t,
 tri_reaches_fire tm t (tanc fams a).
Proof.
 intros [i v] (F & EF & EL) Pos t. change (H t i v).
 cbn [fst snd] in EF, EL.
 assert (Hi : i < 15).
 { change (i < length fams). apply nth_error_Some. rewrite EF. discriminate. }
 destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]];
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
 - apply e0,cube_one; lia.
 - apply cube_one; exact Pos.
 - apply cube_zero.
 - apply e5,e6,cube_five; exact Pos.
 - apply e6,cube_five; exact Pos.
 - apply e7,e9,cube_seven.
 - apply cube_five; exact Pos.
 - apply e9,cube_seven.
 - apply cube_seven.
 - apply cube_eight; exact Pos.
 - apply e14,e15,cube_five; exact Pos.
 - apply e15,cube_five; exact Pos.
 - apply e16,e17,e18,cube_eight; lia.
 - apply e17,e18,cube_eight; lia.
 - apply e18,cube_eight; lia.
Qed.

Lemma cv_AST_73_0000 : coversTr (row_to_tm r_AST_73_0000).
Proof.
 apply coversTr_nqh, neverqhtr_mirror. change (NeverQuasiHaltsTr tm).
 apply (tri_reach_glue_invariant tm fams leaves cube_inv families_ok (0,[0;0;0;0])).
 - eexists. split; reflexivity.
 - exact I.
 - exact cube_inv_next.
 - assert (EB : exists c, csteps tm 3000 c0 = Some c /\
     ceqb c (tanc fams (0,[0;0;0;0])) = true).
   { eexists. split; vm_compute; reflexivity. }
   destruct EB as (c & EC & EE). exists 3000.
   rewrite <- lift_c0.
   pose proof (csteps_lift tm 3000 c0 c EC) as EB.
   rewrite (ceqb_lift _ _ EE) in EB. exact EB.
 - exact cube_all.
Qed.

Definition cbtrows_AST_73 : list (list (option Trans)) := [r_AST_73_0000].
Lemma cbt_AST_73_covers : Forall coversTr (map row_to_tm cbtrows_AST_73).
Proof. constructor; [exact cv_AST_73_0000|constructor]. Qed.
