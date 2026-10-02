(** Transition-level closeout: cube rounds with non-affine liveness. *)
From Coq Require Import Arith Lia List Bool.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape Mirror.
From BBB4.Census Require Import Deferred_Defs.
From BBB4.CensusTr Require Import TNF_QHTr.
From BBB4.CloseoutTr Require Import CloseoutKitTr.
From BBB4.Checkers Require Import LapDecider.
From BBB4.Counters Require Import TriGlueTr TriReachTr CubeRoundTr.
Import ListNotations.
(* spec 1RB1LA_0RC0RD_1LC0LA_1RA0RC *)
Definition r_AST_66_0000 : list (option Trans) := [t1RB;t1LA;t0RC;t0RD;t1LC;t0LA;t1RA;t0RC].
Local Definition tm := mirror_tm (row_to_tm r_AST_66_0000).
Local Definition cert : tcert := (mkTC []
      [(mkTF StB S0 [(SL [S1;S0]);(SB [S1] (mkA 14 [(0,1)]))] [(SB [S1] (mkA 7 [(1,1)]));(SL [S0]);(SB [S1] (mkA 7 [(2,1)]))] 3 [(TLeaf 0)]);
      (mkTF StC S1 [(SB [S1] (mkA 2 [(0,1)]))] [(SB [S1] (mkA 0 [(1,1)]));(SL [S0]);(SB [S1] (mkA 2 [(2,1)]))] 3 [(TSplit 1 1 1 [1;2]);(TLeaf 1);(TLeaf 2)]);
      (mkTF StB S1 [(SB [S1] (mkA 0 [(0,1)]));(SL [S0]);(SB [S1] (mkA 2 [(1,1)]))] [(SB [S1] (mkA 2 [(2,1)]))] 3 [(TSplit 0 1 1 [1;2]);(TLeaf 3);(TLeaf 4)]);
      (mkTF StD S1 [(SB [S1] (mkA 0 [(0,1)]));(SL [S0]);(SB [S1] (mkA 2 [(1,1)]))] [(SL [S0]);(SB [S1] (mkA 2 [(2,1)]))] 3 [(TSplit 0 1 1 [1;2]);(TLeaf 5);(TLeaf 6)]);
      (mkTF StD S0 [(SB [S1] (mkA 2 [(0,1)]))] [(SL [S0]);(SB [S1] (mkA 2 [(1,1)]))] 2 [(TLeaf 7)]);
      (mkTF StD S1 [(SB [S1] (mkA 1 [(0,1)]))] [(SL [S0]);(SB [S1] (mkA 2 [(1,1)]))] 2 [(TLeaf 8)]);
      (mkTF StC S0 [(SB [S1] (mkA 4 [(0,1)]))] [(SB [S1] (mkA 2 [(1,1)]))] 2 [(TLeaf 9)]);
      (mkTF StC S1 [(SB [S1] (mkA 2 [(0,1)]))] [(SB [S1] (mkA 1 [(1,1)]))] 2 [(TLeaf 10)]);
      (mkTF StB S0 [(SB [S1] (mkA 2 [(0,1)]))] [(SB [S1] (mkA 2 [(1,1)]))] 2 [(TLeaf 11)]);
      (mkTF StB S1 [(SB [S1] (mkA 0 [(0,1)]));(SL [S0]);(SB [S1] (mkA 2 [(1,1)]))] [(SL [S1])] 2 [(TSplit 0 1 1 [1;2]);(TLeaf 12);(TLeaf 13)]);
      (mkTF StC S0 [(SL [S1])] [(SB [S1] (mkA 4 [(0,1)]))] 1 [(TLeaf 14)]);
      (mkTF StD S1 [(SB [S1] (mkA 0 [(0,1)]));(SL [S0]);(SB [S1] (mkA 2 [(1,1)]))] [(SL [S0;S1])] 2 [(TSplit 0 1 1 [1;2]);(TLeaf 15);(TLeaf 16)]);
      (mkTF StC S1 [(SB [S1] (mkA 4 [(0,1)]))] [(SB [S1] (mkA 0 [(1,1)]));(SL [S0;S1])] 2 [(TSplit 1 1 1 [1;2]);(TLeaf 17);(TLeaf 18)]);
      (mkTF StD S0 [(SB [S1] (mkA 2 [(0,1)]))] [(SL [S0;S1])] 1 [(TLeaf 19)])]
      [(mkTL 0 [(1,0);(1,0);(1,0)] 1 [(mkA 14 [(0,1)]);(mkA 7 [(1,1)]);(mkA 5 [(2,1)])] (mkC StB (mkS [S1;S0] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 1 0 [(SWin 6)]);
      (mkTL 1 [(1,0);(0,0);(1,0)] 8 [(mkA 0 [(0,1)]);(mkA 1 [(2,1)])] (mkC StC (mkS [] [] 0 0 []) S1 (mkS [S0] [] 0 0 [])) 0 false false 0 2 [(SWin 2)]);
      (mkTL 1 [(1,0);(1,1);(1,0)] 2 [(mkA 0 [(1,1)]);(mkA 0 [(0,1)]);(mkA 1 [(2,1)])] (mkC StC (mkS [] [] 0 0 []) S1 (mkS [S1] [S1] 1 0 [S0])) 1 false false 0 2 [(SWin 1); (SCycR 1); (SWin 2)]);
      (mkTL 2 [(0,0);(1,0);(1,0)] 4 [(mkA 0 [(1,1)]);(mkA 0 [(2,1)])] (mkC StB (mkS [S0] [] 0 0 []) S1 (mkS [] [] 0 0 [])) 0 false false 2 0 [(SWin 1)]);
      (mkTL 2 [(1,1);(1,0);(1,0)] 3 [(mkA 0 [(0,1)]);(mkA 0 [(1,1)]);(mkA 0 [(2,1)])] (mkC StB (mkS [S1] [S1] 1 0 [S0]) S1 (mkS [] [] 0 0 [])) 0 false false 2 0 [(SWin 1)]);
      (mkTL 3 [(0,0);(1,0);(1,0)] 6 [(mkA 0 [(1,1)]);(mkA 0 [(2,1)])] (mkC StD (mkS [S0] [] 0 0 []) S1 (mkS [S0] [] 0 0 [])) 0 false false 2 1 [(SWin 3)]);
      (mkTL 3 [(1,1);(1,0);(1,0)] 1 [(mkA 2 [(1,1)]);(mkA 0 [(0,1)]);(mkA 0 [(2,1)])] (mkC StD (mkS [S1] [S1] 1 0 [S0]) S1 (mkS [S0] [] 0 0 [])) 0 false false 2 1 [(SWin 1); (SCycL 3 1); (SWin 5)]);
      (mkTL 4 [(1,0);(1,0)] 5 [(mkA 0 [(0,1)]);(mkA 1 [(1,1)])] (mkC StD (mkS [S1] [S1] 1 1 []) S0 (mkS [S0] [] 0 0 [])) 0 true false 1 1 [(SWin 5)]);
      (mkTL 5 [(1,0);(1,0)] 1 [(mkA 0 []);(mkA 0 [(0,1)]);(mkA 0 [(1,1)])] (mkC StD (mkS [S1] [S1] 1 0 []) S1 (mkS [S0] [] 0 0 [])) 0 true false 1 1 [(SWin 1); (SCycL 3 1); (SWin 2); (SWinL 1); (SWin 2)]);
      (mkTL 6 [(1,0);(1,0)] 7 [(mkA 3 [(0,1)]);(mkA 0 [(1,1)])] (mkC StC (mkS [] [] 0 0 []) S0 (mkS [S1] [S1] 1 1 [])) 1 false true 0 1 [(SWin 1)]);
      (mkTL 7 [(1,0);(1,0)] 9 [(mkA 0 [(1,1)]);(mkA 0 [(0,1)])] (mkC StC (mkS [] [] 0 0 []) S1 (mkS [S1] [S1] 1 0 [])) 1 false true 0 1 [(SWin 1); (SCycR 1); (SWinR 1); (SWin 1)]);
      (mkTL 8 [(1,0);(1,0)] 10 [(mkA 0 [(0,1);(1,1)])] (mkC StB (mkS [] [S1] 1 2 []) S0 (mkS [] [] 0 0 [])) 0 true false 1 0 [(SCycL 3 0); (SWinL 1); (SWin 1)]);
      (mkTL 9 [(0,0);(1,0)] 13 [(mkA 0 [(1,1)])] (mkC StB (mkS [S0] [] 0 0 []) S1 (mkS [S1] [] 0 0 [])) 0 false true 2 1 [(SWin 1)]);
      (mkTL 9 [(1,1);(1,0)] 11 [(mkA 0 [(0,1)]);(mkA 0 [(1,1)])] (mkC StB (mkS [S1] [S1] 1 0 [S0]) S1 (mkS [S1] [] 0 0 [])) 0 false true 2 1 [(SWin 1)]);
      (mkTL 10 [(1,0)] 7 [(mkA 0 []);(mkA 2 [(0,1)])] (mkC StC (mkS [S1] [] 0 0 []) S0 (mkS [S1] [S1] 1 3 [])) 0 true true 1 1 [(SWin 1)]);
      (mkTL 11 [(0,0);(1,0)] 8 [(mkA 0 [(1,1)]);(mkA 2 [])] (mkC StD (mkS [S0] [] 0 0 []) S1 (mkS [S0;S1] [] 0 0 [])) 0 false true 2 1 [(SWin 4); (SWinR 1); (SWin 10)]);
      (mkTL 11 [(1,1);(1,0)] 12 [(mkA 0 [(1,1)]);(mkA 0 [(0,1)])] (mkC StD (mkS [S1] [S1] 1 0 [S0]) S1 (mkS [S0;S1] [] 0 0 [])) 0 false true 2 1 [(SWin 1); (SCycL 3 1); (SWin 5)]);
      (mkTL 12 [(1,0);(0,0)] 8 [(mkA 2 [(0,1)]);(mkA 0 [])] (mkC StC (mkS [] [] 0 0 []) S1 (mkS [S0;S1] [] 0 0 [])) 0 false true 0 2 [(SWin 2)]);
      (mkTL 12 [(1,0);(1,1)] 2 [(mkA 0 [(1,1)]);(mkA 2 [(0,1)]);(mkA 0 [])] (mkC StC (mkS [] [] 0 0 []) S1 (mkS [S1] [S1] 1 0 [S0;S1])) 1 false true 0 2 [(SWin 1); (SCycR 1); (SWin 2)]);
      (mkTL 13 [(1,0)] 5 [(mkA 0 [(0,1)]);(mkA 0 [])] (mkC StD (mkS [S1] [S1] 1 1 []) S0 (mkS [S0;S1] [] 0 0 [])) 0 true true 1 1 [(SWin 5)])]
      1 []
      []
      3000 0 [0;0;0]).
Local Definition fams := tc_fams cert.
Local Definition leaves := tc_leaves cert.
Local Definition H (t : Instr) (i : nat) (v : list nat) := tri_reaches_fire tm t (tanc fams (i,v)).
Local Lemma families_ok : fams_ok tm fams leaves = true.
Proof. vm_compute. reflexivity. Qed.


Local Ltac cube_norm :=
 cbn [fams leaves cert tc_fams tc_leaves nth tl_tgt tl_reg rsub reg1 seq combine map aeval teval a_c a_t fst snd Nat.eqb Nat.mul Nat.add] in *;
 cbv beta iota zeta delta [TriGlueTr.rsub TriGlueTr.reg1 seq combine map aeval teval a_c a_t fst snd Nat.eqb Nat.mul Nat.add nth length] in *;
 rewrite ?Nat.add_0_r in *.

Local Lemma e0 : forall a b c t, H t 1 [a+14;b+7;c+5] -> H t 0 [a;b;c].
Proof.
 intros a b c t E.
 pose proof (tri_leaf_back tm fams (nth 0 fams (mkTF StA S0 [] [] 0 []))
   (nth 0 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
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

Local Lemma e1 : forall a c t, H t 8 [a;c+1] -> H t 1 [a;0;c].
Proof.
 intros a c t E.
 pose proof (tri_leaf_back tm fams (nth 1 fams (mkTF StA S0 [] [] 0 []))
   (nth 1 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   (nth 8 fams (mkTF StA S0 [] [] 0 []))
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

Local Lemma e3 : forall b c t, H t 4 [b;c] -> H t 2 [0;b;c].
Proof.
 intros b c t E.
 pose proof (tri_leaf_back tm fams (nth 2 fams (mkTF StA S0 [] [] 0 []))
   (nth 3 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
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

Local Lemma e4 : forall a b c t, H t 3 [a;b;c] -> H t 2 [a+1;b;c].
Proof.
 intros a b c t E.
 pose proof (tri_leaf_back tm fams (nth 2 fams (mkTF StA S0 [] [] 0 []))
   (nth 4 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   (nth 3 fams (mkTF StA S0 [] [] 0 []))
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

Local Lemma e5 : forall b c t, H t 6 [b;c] -> H t 3 [0;b;c].
Proof.
 intros b c t E.
 pose proof (tri_leaf_back tm fams (nth 3 fams (mkTF StA S0 [] [] 0 []))
   (nth 5 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   (nth 6 fams (mkTF StA S0 [] [] 0 []))
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

Local Lemma e6 : forall a b c t, H t 1 [b+2;a;c] -> H t 3 [a+1;b;c].
Proof.
 intros a b c t E.
 pose proof (tri_leaf_back tm fams (nth 3 fams (mkTF StA S0 [] [] 0 []))
   (nth 6 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
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

Local Lemma e7 : forall a b t, H t 5 [a;b+1] -> H t 4 [a;b].
Proof.
 intros a b t E.
 pose proof (tri_leaf_back tm fams (nth 4 fams (mkTF StA S0 [] [] 0 []))
   (nth 7 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
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

Local Lemma e8 : forall a b t, H t 1 [0;a;b] -> H t 5 [a;b].
Proof.
 intros a b t E.
 pose proof (tri_leaf_back tm fams (nth 5 fams (mkTF StA S0 [] [] 0 []))
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

Local Lemma e9 : forall a b t, H t 7 [a+3;b] -> H t 6 [a;b].
Proof.
 intros a b t E.
 pose proof (tri_leaf_back tm fams (nth 6 fams (mkTF StA S0 [] [] 0 []))
   (nth 9 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
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

Local Lemma e10 : forall a b t, H t 9 [b;a] -> H t 7 [a;b].
Proof.
 intros a b t E.
 pose proof (tri_leaf_back tm fams (nth 7 fams (mkTF StA S0 [] [] 0 []))
   (nth 10 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
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

Local Lemma e11 : forall a b t, H t 10 [a+b] -> H t 8 [a;b].
Proof.
 intros a b t E.
 pose proof (tri_leaf_back tm fams (nth 8 fams (mkTF StA S0 [] [] 0 []))
   (nth 11 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   (nth 10 fams (mkTF StA S0 [] [] 0 []))
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

Local Lemma e12 : forall b t, H t 13 [b] -> H t 9 [0;b].
Proof.
 intros b t E.
 pose proof (tri_leaf_back tm fams (nth 9 fams (mkTF StA S0 [] [] 0 []))
   (nth 12 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   (nth 13 fams (mkTF StA S0 [] [] 0 []))
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

Local Lemma e13 : forall a b t, H t 11 [a;b] -> H t 9 [a+1;b].
Proof.
 intros a b t E.
 pose proof (tri_leaf_back tm fams (nth 9 fams (mkTF StA S0 [] [] 0 []))
   (nth 13 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   (nth 11 fams (mkTF StA S0 [] [] 0 []))
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

Local Lemma e14 : forall a t, H t 7 [0;a+2] -> H t 10 [a].
Proof.
 intros a t E.
 pose proof (tri_leaf_back tm fams (nth 10 fams (mkTF StA S0 [] [] 0 []))
   (nth 14 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   (nth 7 fams (mkTF StA S0 [] [] 0 []))
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

Local Lemma e15 : forall b t, H t 8 [b;2] -> H t 11 [0;b].
Proof.
 intros b t E.
 pose proof (tri_leaf_back tm fams (nth 11 fams (mkTF StA S0 [] [] 0 []))
   (nth 15 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   (nth 8 fams (mkTF StA S0 [] [] 0 []))
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

Local Lemma e16 : forall a b t, H t 12 [b;a] -> H t 11 [a+1;b].
Proof.
 intros a b t E.
 pose proof (tri_leaf_back tm fams (nth 11 fams (mkTF StA S0 [] [] 0 []))
   (nth 16 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
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

Local Lemma e17 : forall a t, H t 8 [a+2;0] -> H t 12 [a;0].
Proof.
 intros a t E.
 pose proof (tri_leaf_back tm fams (nth 12 fams (mkTF StA S0 [] [] 0 []))
   (nth 17 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   (nth 8 fams (mkTF StA S0 [] [] 0 []))
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

Local Lemma e18 : forall a b t, H t 2 [b;a+2;0] -> H t 12 [a;b+1].
Proof.
 intros a b t E.
 pose proof (tri_leaf_back tm fams (nth 12 fams (mkTF StA S0 [] [] 0 []))
   (nth 18 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
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

Local Lemma e19 : forall a t, H t 5 [a;0] -> H t 13 [a].
Proof.
 intros a t E.
 pose proof (tri_leaf_back tm fams (nth 13 fams (mkTF StA S0 [] [] 0 []))
   (nth 19 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
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

Local Lemma f0 : forall a b c t, In t [(StA,S0);(StB,S0);(StC,S0);(StC,S1)] -> H t 0 [a;b;c].
Proof.
 intros a b c t Et.
 pose proof (tri_leaf_now tm fams (nth 0 fams (mkTF StA S0 [] [] 0 []))
   (nth 0 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   ltac:(vm_compute;reflexivity) t ltac:(vm_compute in Et |- *; tauto) [a;b;c]) as B.
 cube_norm.
 unfold H, tanc. cbn [fams cert tc_fams nth_error fst snd].
 match type of B with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact B
  end end.
Qed.

Local Lemma f1 : forall a c t, In t [(StA,S0);(StB,S0);(StC,S1)] -> H t 1 [a;0;c].
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

Local Lemma f2 : forall a b c t, In t [(StA,S0);(StA,S1);(StB,S1);(StC,S1)] -> H t 1 [a;b+1;c].
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

Local Lemma f3 : forall b c t, In t [(StB,S1);(StD,S0)] -> H t 2 [0;b;c].
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

Local Lemma f4 : forall a b c t, In t [(StB,S1);(StD,S1)] -> H t 2 [a+1;b;c].
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

Local Lemma f5 : forall b c t, In t [(StC,S0);(StD,S1)] -> H t 3 [0;b;c].
Proof.
 intros b c t Et.
 pose proof (tri_leaf_now tm fams (nth 3 fams (mkTF StA S0 [] [] 0 []))
   (nth 5 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   ltac:(vm_compute;reflexivity) t ltac:(vm_compute in Et |- *; tauto) [0;b;c]) as B.
 cube_norm.
 unfold H, tanc. cbn [fams cert tc_fams nth_error fst snd].
 match type of B with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact B
  end end.
Qed.

Local Lemma f6 : forall a b c t, In t [(StA,S0);(StB,S0);(StC,S0);(StC,S1);(StD,S1)] -> H t 3 [a+1;b;c].
Proof.
 intros a b c t Et.
 pose proof (tri_leaf_now tm fams (nth 3 fams (mkTF StA S0 [] [] 0 []))
   (nth 6 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   ltac:(vm_compute;reflexivity) t ltac:(vm_compute in Et |- *; tauto) [a;b;c]) as B.
 cube_norm.
 unfold H, tanc. cbn [fams cert tc_fams nth_error fst snd].
 match type of B with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact B
  end end.
Qed.

Local Lemma f7 : forall a b t, In t [(StA,S0);(StA,S1);(StB,S1);(StD,S0);(StD,S1)] -> H t 4 [a;b].
Proof.
 intros a b t Et.
 pose proof (tri_leaf_now tm fams (nth 4 fams (mkTF StA S0 [] [] 0 []))
   (nth 7 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   ltac:(vm_compute;reflexivity) t ltac:(vm_compute in Et |- *; tauto) [a;b]) as B.
 cube_norm.
 unfold H, tanc. cbn [fams cert tc_fams nth_error fst snd].
 match type of B with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact B
  end end.
Qed.

Local Lemma f8 : forall a b t, In t [(StA,S0);(StB,S0);(StC,S0);(StC,S1);(StD,S1)] -> H t 5 [a;b].
Proof.
 intros a b t Et.
 pose proof (tri_leaf_now tm fams (nth 5 fams (mkTF StA S0 [] [] 0 []))
   (nth 8 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   ltac:(vm_compute;reflexivity) t ltac:(vm_compute in Et |- *; tauto) [a;b]) as B.
 cube_norm.
 unfold H, tanc. cbn [fams cert tc_fams nth_error fst snd].
 match type of B with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact B
  end end.
Qed.

Local Lemma f9 : forall a b t, In t [(StC,S0);(StC,S1)] -> H t 6 [a;b].
Proof.
 intros a b t Et.
 pose proof (tri_leaf_now tm fams (nth 6 fams (mkTF StA S0 [] [] 0 []))
   (nth 9 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   ltac:(vm_compute;reflexivity) t ltac:(vm_compute in Et |- *; tauto) [a;b]) as B.
 cube_norm.
 unfold H, tanc. cbn [fams cert tc_fams nth_error fst snd].
 match type of B with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact B
  end end.
Qed.

Local Lemma f10 : forall a b t, In t [(StA,S0);(StA,S1);(StB,S1);(StC,S1)] -> H t 7 [a;b].
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

Local Lemma f11 : forall a b t, In t [(StB,S0);(StC,S0)] -> H t 8 [a;b].
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

Local Lemma f12 : forall b t, In t [(StB,S1);(StD,S0)] -> H t 9 [0;b].
Proof.
 intros b t Et.
 pose proof (tri_leaf_now tm fams (nth 9 fams (mkTF StA S0 [] [] 0 []))
   (nth 12 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   ltac:(vm_compute;reflexivity) t ltac:(vm_compute in Et |- *; tauto) [0;b]) as B.
 cube_norm.
 unfold H, tanc. cbn [fams cert tc_fams nth_error fst snd].
 match type of B with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact B
  end end.
Qed.

Local Lemma f13 : forall a b t, In t [(StB,S1);(StD,S1)] -> H t 9 [a+1;b].
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

Local Lemma f14 : forall a t, In t [(StC,S0);(StC,S1)] -> H t 10 [a].
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

Local Lemma f15 : forall b t, In t [(StA,S0);(StB,S0);(StC,S0);(StC,S1);(StD,S1)] -> H t 11 [0;b].
Proof.
 intros b t Et.
 pose proof (tri_leaf_now tm fams (nth 11 fams (mkTF StA S0 [] [] 0 []))
   (nth 15 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   ltac:(vm_compute;reflexivity) t ltac:(vm_compute in Et |- *; tauto) [0;b]) as B.
 cube_norm.
 unfold H, tanc. cbn [fams cert tc_fams nth_error fst snd].
 match type of B with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact B
  end end.
Qed.

Local Lemma f16 : forall a b t, In t [(StA,S0);(StB,S0);(StC,S0);(StC,S1);(StD,S1)] -> H t 11 [a+1;b].
Proof.
 intros a b t Et.
 pose proof (tri_leaf_now tm fams (nth 11 fams (mkTF StA S0 [] [] 0 []))
   (nth 16 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   ltac:(vm_compute;reflexivity) t ltac:(vm_compute in Et |- *; tauto) [a;b]) as B.
 cube_norm.
 unfold H, tanc. cbn [fams cert tc_fams nth_error fst snd].
 match type of B with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact B
  end end.
Qed.

Local Lemma f17 : forall a t, In t [(StA,S0);(StB,S0);(StC,S1)] -> H t 12 [a;0].
Proof.
 intros a t Et.
 pose proof (tri_leaf_now tm fams (nth 12 fams (mkTF StA S0 [] [] 0 []))
   (nth 17 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   ltac:(vm_compute;reflexivity) t ltac:(vm_compute in Et |- *; tauto) [a;0]) as B.
 cube_norm.
 unfold H, tanc. cbn [fams cert tc_fams nth_error fst snd].
 match type of B with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact B
  end end.
Qed.

Local Lemma f18 : forall a b t, In t [(StA,S0);(StA,S1);(StB,S1);(StC,S1)] -> H t 12 [a;b+1].
Proof.
 intros a b t Et.
 pose proof (tri_leaf_now tm fams (nth 12 fams (mkTF StA S0 [] [] 0 []))
   (nth 18 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   ltac:(vm_compute;reflexivity) t ltac:(vm_compute in Et |- *; tauto) [a;b]) as B.
 cube_norm.
 unfold H, tanc. cbn [fams cert tc_fams nth_error fst snd].
 match type of B with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact B
  end end.
Qed.

Local Lemma f19 : forall a t, In t [(StA,S0);(StA,S1);(StB,S1);(StD,S0);(StD,S1)] -> H t 13 [a].
Proof.
 intros a t Et.
 pose proof (tri_leaf_now tm fams (nth 13 fams (mkTF StA S0 [] [] 0 []))
   (nth 19 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   ltac:(vm_compute;reflexivity) t ltac:(vm_compute in Et |- *; tauto) [a]) as B.
 cube_norm.
 unfold H, tanc. cbn [fams cert tc_fams nth_error fst snd].
 match type of B with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact B
  end end.
Qed.

Local Ltac cube_now := first [solve [apply f0; simpl; auto] | solve [apply f1; simpl; auto] | solve [apply f2; simpl; auto] | solve [apply f3; simpl; auto] | solve [apply f4; simpl; auto] | solve [apply f5; simpl; auto] | solve [apply f6; simpl; auto] | solve [apply f7; simpl; auto] | solve [apply f8; simpl; auto] | solve [apply f9; simpl; auto] | solve [apply f10; simpl; auto] | solve [apply f11; simpl; auto] | solve [apply f12; simpl; auto] | solve [apply f13; simpl; auto] | solve [apply f14; simpl; auto] | solve [apply f15; simpl; auto] | solve [apply f16; simpl; auto] | solve [apply f17; simpl; auto] | solve [apply f18; simpl; auto] | solve [apply f19; simpl; auto]].

Local Ltac cube_exact E :=
 match type of E with H ?t ?i ?xs =>
  match goal with |- H t i ?ys =>
   replace ys with xs by (repeat (f_equal; try lia)); exact E
  end end.

Local Lemma cube_loop : forall k a b c t,
 H t 2 [a;b+2*k;c+k] -> H t 2 [3*k+a;b;c].
Proof.
 induction k as [|k IH]; intros a b c t E.
 - cbn [Nat.mul Nat.add]. cube_exact E.
 - replace (3*S k+a) with ((3*k+a+1)+1+1) by lia.
   apply e4, e6, e2. apply IH. cube_exact E.
Qed.

Local Lemma cube_D0 : forall a b, H (StD,S0) 9 [a;b].
Proof.
 apply (cube_round_total (fun a b => H (StD,S0) 9 [a;b])).
 - intro b. apply f12. simpl; auto 12.
 - intros k b. replace (3*k+3) with ((3*k)+1+1+1) by lia.
   apply e13, e16, e18.
   replace (3*k) with (3*k+0) by lia. apply (cube_loop k 0 (b+2) 0 (StD,S0)). apply f3. simpl; auto 12.
 - intros b E. change (H (StD,S0) 9 [0+1;b]).
   apply e13, e15, e11, e14, e10. cube_exact E.
 - intros b E. change (H (StD,S0) 9 [1+1;b]).
   apply e13. change (H (StD,S0) 11 [0+1;b]).
   apply e16, e17, e11, e14, e10. cube_exact E.
 - intros k b E. replace (3*k+4) with ((3*k+1)+1+1+1) by lia.
   apply e13, e16, e18. apply (cube_loop k 1 (b+2) 0 (StD,S0)).
   change (H (StD,S0) 2 [0+1;b+2+2*k;0+k]).
   apply e4, e5, e9, e10. cube_exact E.
 - intros k b E. replace (3*k+5) with ((3*k+2)+1+1+1) by lia.
   apply e13, e16, e18. apply (cube_loop k 2 (b+2) 0 (StD,S0)).
   change (H (StD,S0) 2 [1+1;b+2+2*k;0+k]).
   apply e4. change (H (StD,S0) 3 [0+1;b+2+2*k;0+k]).
   apply e6, e1, e11, e14, e10. cube_exact E.
Qed.

Local Lemma cube_A1 : forall a b, H (StA,S1) 9 [a;b].
Proof.
 intros [|[|[|a]]] b.
 - apply e12, f19. simpl; auto 12.
 - change (H (StA,S1) 9 [0+1;b]).
   apply e13, e15, e11, e14, f10. simpl; auto 12.
 - change (H (StA,S1) 9 [1+1;b]). apply e13.
   change (H (StA,S1) 11 [0+1;b]).
   apply e16, e17, e11, e14, f10. simpl; auto 12.
 - replace (S(S(S a))) with ((a+1)+1+1) by lia.
   apply e13, e16, f18. simpl; auto 12.
Qed.

Local Lemma cube_D1 : forall a b, H (StD,S1) 9 [a;b].
Proof.
 intros [|a] b.
 - apply e12, f19. simpl; auto 12.
 - replace (S a) with (a+1) by lia. apply f13. simpl; auto 12.
Qed.

Local Lemma cube_common : forall a b t,
 In t [(StA,S0);(StB,S0);(StB,S1);(StC,S0);(StC,S1)] -> H t 9 [a;b].
Proof.
 intros [|a] b t E.
 - destruct E as [<-|[<-|[<-|[<-|[<-|[]]]]]];
   try solve [apply f12; simpl; auto 12];
   try solve [apply e12, f19; simpl; auto 12];
   apply e12, e19, f8; simpl; auto 12.
 - replace (S a) with (a+1) by lia.
   destruct (instr_eqb t (StB,S1)) eqn:EB.
   + apply instr_eqb_spec in EB. subst t. apply f13. simpl; auto 12.
   + assert (EN : (StB,S1) <> t).
     { intro Et. subst t. discriminate. }
     apply e13. destruct a as [|a].
     * apply f15. simpl in *; tauto.
     * replace (S a) with (a+1) by lia.
       apply f16. simpl in *; tauto.
Qed.

Local Lemma cube_ten : forall a b t, H t 9 [a;b].
Proof.
 intros a b [q s]. destruct q,s;
 try solve [apply cube_common; simpl; auto 12].
 - apply cube_A1.
 - apply cube_D0.
 - apply cube_D1.
Qed.

Local Lemma cube_four : forall a b c t, H t 2 [a;b;c].
Proof.
 induction a as [a IH] using lt_wf_ind. intros b c t.
 destruct a as [|[|[|a]]].
 - destruct t as [q h]; destruct q,h;
   try solve [apply f3; simpl; auto 12];
   try solve [apply e3, f7; simpl; auto 12];
   apply e3, e7, f8; simpl; auto 12.
 - change (H t 2 [0+1;b;c]). apply e4, e5, e9, e10, cube_ten.
 - change (H t 2 [1+1;b;c]). apply e4.
   change (H t 3 [0+1;b;c]). apply e6, e1, e11, e14, e10, cube_ten.
 - replace (S(S(S a))) with ((a+1)+1+1) by lia.
   apply e4, e6, e2. apply IH. lia.
Qed.

Local Lemma cube_six : forall a b c t, H t 1 [a;b;c].
Proof.
 intros a [|b] c t.
 - apply e1, e11, e14, e10, cube_ten.
 - replace (S b) with (b+1) by lia. apply e2, cube_four.
Qed.

Local Lemma cube_three : forall a b t, H t 12 [a;b].
Proof.
 intros a [|b] t.
 - apply e17, e11, e14, e10, cube_ten.
 - replace (S b) with (b+1) by lia. apply e18, cube_four.
Qed.

Local Lemma cube_five : forall a b c t, H t 3 [a;b;c].
Proof.
 intros [|a] b c t.
 - apply e5, e9, e10, cube_ten.
 - replace (S a) with (a+1) by lia. apply e6, cube_six.
Qed.

Local Lemma cube_twelve : forall a b t, H t 11 [a;b].
Proof.
 intros [|a] b t.
 - apply e15, e11, e14, e10, cube_ten.
 - replace (S a) with (a+1) by lia. apply e16, cube_three.
Qed.

Local Lemma cube_all : forall a, Good fams a -> forall t,
 tri_reaches_fire tm t (tanc fams a).
Proof.
 intros [i v] (F & EF & EL) t. change (H t i v).
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
 - apply e0, cube_six.
 - apply cube_six.
 - apply cube_four.
 - apply cube_five.
 - apply e7, e8, cube_six.
 - apply e8, cube_six.
 - apply e9, e10, cube_ten.
 - apply e10, cube_ten.
 - apply e11, e14, e10, cube_ten.
 - apply cube_ten.
 - apply e14, e10, cube_ten.
 - apply cube_twelve.
 - apply cube_three.
 - apply e19, e8, cube_six.
Qed.

Lemma cv_AST_66_0000 : coversTr (row_to_tm r_AST_66_0000).
Proof.
 apply coversTr_nqh, neverqhtr_mirror. change (NeverQuasiHaltsTr tm).
 apply (tri_reach_glue tm fams leaves families_ok (0,[0;0;0])).
 - eexists. split; reflexivity.
 - assert (EB : exists c, csteps tm 3000 c0 = Some c /\
     ceqb c (tanc fams (0,[0;0;0])) = true).
   { eexists. split; vm_compute; reflexivity. }
   destruct EB as (c & EC & EE). exists 3000.
   rewrite <- lift_c0.
   pose proof (csteps_lift tm 3000 c0 c EC) as EB.
   rewrite (ceqb_lift _ _ EE) in EB. exact EB.
 - exact cube_all.
Qed.

Definition cbtrows_AST_66 : list (list (option Trans)) := [r_AST_66_0000].
Lemma cbt_AST_66_covers : Forall coversTr (map row_to_tm cbtrows_AST_66).
Proof. constructor; [exact cv_AST_66_0000|constructor]. Qed.
