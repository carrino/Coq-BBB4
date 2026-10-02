(** Transition-level closeout: cube rounds with non-affine liveness. *)
From Coq Require Import Arith Lia List Bool.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape Mirror.
From BBB4.Census Require Import Deferred_Defs.
From BBB4.CensusTr Require Import TNF_QHTr.
From BBB4.CloseoutTr Require Import CloseoutKitTr.
From BBB4.Checkers Require Import LapDecider.
From BBB4.Counters Require Import TriGlueTr TriReachTr CubeRoundTr.
Import ListNotations.
(* spec 0RB0LD_1LC1RB_0LD0LA_1RD0RB *)
Definition r_AST_74_0000 : list (option Trans) := [t0RB;t0LD;t1LC;t1RB;t0LD;t0LA;t1RD;t0RB].
Local Definition tm := mirror_tm (row_to_tm r_AST_74_0000).
Local Definition cert : tcert := (mkTC []
      [(mkTF StB S0 [(SB [S1] (mkA 13 [(0,1)]));(SL [S0]);(SB [S1] (mkA 5 [(1,1)]))] [(SB [S0;S1;S1;S1] (mkA 2 [(2,1)]));(SB [S1] (mkA 7 [(3,1)]))] 4 [(TLeaf 0)]);
      (mkTF StC S0 [(SB [S1] (mkA 17 [(0,1)]));(SL [S0]);(SB [S1] (mkA 5 [(1,1)]))] [(SB [S0;S1;S1;S1] (mkA 1 [(2,1)]));(SB [S1] (mkA 7 [(3,1)]))] 4 [(TLeaf 1)]);
      (mkTF StD S0 [(SB [S1] (mkA 1 [(0,1)]));(SL [S0]);(SB [S1] (mkA 2 [(1,1)]))] [(SB [S1] (mkA 4 [(2,1)]));(SB [S0;S1;S1;S1] (mkA 0 [(3,1)]));(SB [S1] (mkA 7 [(4,1)]))] 5 [(TLeaf 2)]);
      (mkTF StD S1 [(SB [S1] (mkA 0 [(0,1)]));(SL [S0]);(SB [S1] (mkA 2 [(1,1)]))] [(SB [S1] (mkA 5 [(2,1)]));(SB [S0;S1;S1;S1] (mkA 0 [(3,1)]));(SB [S1] (mkA 7 [(4,1)]))] 5 [(TSplit 0 1 1 [1;2]);(TLeaf 3);(TLeaf 4)]);
      (mkTF StC S1 [(SB [S1] (mkA 2 [(0,1)]))] [(SB [S1] (mkA 0 [(1,1)]));(SL [S0]);(SB [S1] (mkA 5 [(2,1)]));(SB [S0;S1;S1;S1] (mkA 0 [(3,1)]));(SB [S1] (mkA 7 [(4,1)]))] 5 [(TSplit 1 1 1 [1;2]);(TLeaf 5);(TLeaf 6)]);
      (mkTF StA S1 [(SL [S0]);(SB [S1] (mkA 2 [(0,1)]))] [(SB [S1] (mkA 0 [(1,1)]));(SL [S0]);(SB [S1] (mkA 5 [(2,1)]));(SB [S0;S1;S1;S1] (mkA 0 [(3,1)]));(SB [S1] (mkA 7 [(4,1)]))] 5 [(TSplit 1 1 1 [1;2]);(TLeaf 7);(TLeaf 8)]);
      (mkTF StC S0 [(SB [S1] (mkA 2 [(0,1)]))] [(SB [S1] (mkA 5 [(1,1)]));(SB [S0;S1;S1;S1] (mkA 0 [(2,1)]));(SB [S1] (mkA 7 [(3,1)]))] 4 [(TLeaf 9)]);
      (mkTF StC S0 [(SB [S1] (mkA 7 [(0,1)]))] [(SB [S0;S1;S1;S1] (mkA 0 [(1,1)]));(SB [S1] (mkA 7 [(2,1)]))] 3 [(TSplit 1 1 1 [1;2]);(TLeaf 10);(TLeaf 11)]);
      (mkTF StD S0 [(SB [S1] (mkA 2 [(0,1)]))] [(SB [S1] (mkA 4 [(1,1)]));(SB [S0;S1;S1;S1] (mkA 0 [(2,1)]));(SB [S1] (mkA 7 [(3,1)]))] 4 [(TLeaf 12)]);
      (mkTF StD S0 [(SB [S1] (mkA 4 [(0,1)]))] [(SL [S1])] 1 [(TLeaf 13)]);
      (mkTF StD S1 [(SB [S1] (mkA 1 [(0,1)]))] [(SB [S1] (mkA 5 [(1,1)]));(SB [S0;S1;S1;S1] (mkA 0 [(2,1)]));(SB [S1] (mkA 7 [(3,1)]))] 4 [(TLeaf 14)]);
      (mkTF StD S1 [(SB [S1] (mkA 1 [(0,1)]))] [(SB [S1] (mkA 2 [(1,1)]))] 2 [(TLeaf 15)]);
      (mkTF StC S1 [(SL [S1])] [(SB [S1] (mkA 0 [(0,1)]));(SL [S0]);(SB [S1] (mkA 5 [(1,1)]));(SB [S0;S1;S1;S1] (mkA 0 [(2,1)]));(SB [S1] (mkA 7 [(3,1)]))] 4 [(TSplit 0 1 1 [1;2]);(TLeaf 16);(TLeaf 17)]);
      (mkTF StC S1 [(SL [S1])] [(SB [S1] (mkA 0 [(0,1)]));(SL [S0]);(SB [S1] (mkA 2 [(1,1)]))] 2 [(TSplit 0 1 1 [1;2]);(TLeaf 18);(TLeaf 19)]);
      (mkTF StA S1 [(SL [S0;S1])] [(SB [S1] (mkA 0 [(0,1)]));(SL [S0]);(SB [S1] (mkA 5 [(1,1)]));(SB [S0;S1;S1;S1] (mkA 0 [(2,1)]));(SB [S1] (mkA 7 [(3,1)]))] 4 [(TSplit 0 1 1 [1;2]);(TLeaf 20);(TLeaf 21)]);
      (mkTF StA S1 [(SL [S0;S1])] [(SB [S1] (mkA 0 [(0,1)]));(SL [S0]);(SB [S1] (mkA 2 [(1,1)]))] 2 [(TSplit 0 1 1 [1;2]);(TLeaf 22);(TLeaf 23)]);
      (mkTF StD S0 [(SB [S1] (mkA 1 [(0,1)]));(SL [S0;S1])] [(SB [S1] (mkA 6 [(1,1)]));(SB [S0;S1;S1;S1] (mkA 0 [(2,1)]));(SB [S1] (mkA 7 [(3,1)]))] 4 [(TLeaf 24)]);
      (mkTF StD S0 [(SB [S1] (mkA 1 [(0,1)]));(SL [S0;S1])] [(SB [S1] (mkA 3 [(1,1)]))] 2 [(TLeaf 25)]);
      (mkTF StD S1 [(SB [S1] (mkA 0 [(0,1)]));(SL [S0;S1])] [(SB [S1] (mkA 7 [(1,1)]));(SB [S0;S1;S1;S1] (mkA 0 [(2,1)]));(SB [S1] (mkA 7 [(3,1)]))] 4 [(TSplit 0 1 1 [1;2]);(TLeaf 26);(TLeaf 27)]);
      (mkTF StD S1 [(SB [S1] (mkA 0 [(0,1)]));(SL [S0;S1])] [(SB [S1] (mkA 4 [(1,1)]))] 2 [(TSplit 0 1 1 [1;2]);(TLeaf 28);(TLeaf 29)]);
      (mkTF StC S1 [(SB [S1] (mkA 2 [(0,1)]))] [(SB [S1] (mkA 0 [(1,1)]));(SL [S0]);(SB [S1] (mkA 4 [(2,1)]))] 3 [(TSplit 1 1 1 [1;2]);(TLeaf 30);(TLeaf 31)]);
      (mkTF StA S1 [(SL [S0]);(SB [S1] (mkA 2 [(0,1)]))] [(SB [S1] (mkA 0 [(1,1)]));(SL [S0]);(SB [S1] (mkA 4 [(2,1)]))] 3 [(TSplit 1 1 1 [1;2]);(TLeaf 32);(TLeaf 33)]);
      (mkTF StD S0 [(SB [S1] (mkA 1 [(0,1)]));(SL [S0]);(SB [S1] (mkA 2 [(1,1)]))] [(SB [S1] (mkA 5 [(2,1)]))] 3 [(TLeaf 34)]);
      (mkTF StD S1 [(SB [S1] (mkA 0 [(0,1)]));(SL [S0]);(SB [S1] (mkA 2 [(1,1)]))] [(SB [S1] (mkA 6 [(2,1)]))] 3 [(TSplit 0 1 1 [1;2]);(TLeaf 35);(TLeaf 36)]);
      (mkTF StC S0 [(SB [S1] (mkA 2 [(0,1)]))] [(SB [S1] (mkA 2 [(1,1)]))] 2 [(TLeaf 37)]);
      (mkTF StD S0 [(SB [S1] (mkA 2 [(0,1)]))] [(SB [S1] (mkA 6 [(1,1)]))] 2 [(TLeaf 38)])]
      [(mkTL 0 [(1,0);(1,0);(1,0);(1,0)] 1 [(mkA 0 [(0,1)]);(mkA 0 [(1,1)]);(mkA 0 [(2,1)]);(mkA 0 [(3,1)])] (mkC StB (mkS [] [] 0 0 []) S0 (mkS [S0;S1;S1;S1] [S0;S1;S1;S1] 1 1 [])) 2 false false 0 1 [(SWin 10)]);
      (mkTL 1 [(1,0);(1,0);(1,0);(1,0)] 2 [(mkA 16 [(0,1)]);(mkA 3 [(1,1)]);(mkA 0 []);(mkA 0 [(2,1)]);(mkA 0 [(3,1)])] (mkC StC (mkS [] [] 0 0 []) S0 (mkS [S0;S1;S1;S1] [S0;S1;S1;S1] 1 0 [])) 2 false false 0 1 [(SWin 2)]);
      (mkTL 2 [(1,0);(1,0);(1,0);(1,0);(1,0)] 3 [(mkA 0 [(0,1)]);(mkA 0 [(1,1)]);(mkA 0 [(2,1)]);(mkA 0 [(3,1)]);(mkA 0 [(4,1)])] (mkC StD (mkS [S1] [S1] 1 0 [S0]) S0 (mkS [] [] 0 0 [])) 0 false false 2 0 [(SWin 1)]);
      (mkTL 3 [(0,0);(1,0);(1,0);(1,0);(1,0)] 6 [(mkA 1 [(1,1)]);(mkA 0 [(2,1)]);(mkA 0 [(3,1)]);(mkA 0 [(4,1)])] (mkC StD (mkS [S0] [] 0 0 []) S1 (mkS [] [] 0 0 [])) 0 false false 2 0 [(SWin 2)]);
      (mkTL 3 [(1,1);(1,0);(1,0);(1,0);(1,0)] 4 [(mkA 1 [(1,1)]);(mkA 0 [(0,1)]);(mkA 0 [(2,1)]);(mkA 0 [(3,1)]);(mkA 0 [(4,1)])] (mkC StD (mkS [S1] [S1] 1 0 [S0]) S1 (mkS [] [] 0 0 [])) 0 false false 2 0 [(SWin 1); (SCycL 1 0); (SWin 2)]);
      (mkTL 4 [(1,0);(0,0);(1,0);(1,0);(1,0)] 6 [(mkA 1 [(0,1)]);(mkA 0 [(2,1)]);(mkA 0 [(3,1)]);(mkA 0 [(4,1)])] (mkC StC (mkS [] [] 0 0 []) S1 (mkS [S0] [] 0 0 [])) 0 false false 0 2 [(SWin 3)]);
      (mkTL 4 [(1,0);(1,1);(1,0);(1,0);(1,0)] 5 [(mkA 0 [(0,1)]);(mkA 0 [(1,1)]);(mkA 0 [(2,1)]);(mkA 0 [(3,1)]);(mkA 0 [(4,1)])] (mkC StC (mkS [] [] 0 0 []) S1 (mkS [S1] [S1] 1 0 [S0])) 1 false false 0 2 [(SWin 1)]);
      (mkTL 5 [(1,0);(0,0);(1,0);(1,0);(1,0)] 8 [(mkA 0 [(0,1)]);(mkA 3 [(2,1)]);(mkA 0 [(3,1)]);(mkA 0 [(4,1)])] (mkC StA (mkS [S0] [] 0 0 []) S1 (mkS [S0] [] 0 0 [])) 0 false false 1 2 [(SWin 3)]);
      (mkTL 5 [(1,0);(1,1);(1,0);(1,0);(1,0)] 2 [(mkA 0 [(1,1)]);(mkA 0 [(0,1)]);(mkA 2 [(2,1)]);(mkA 0 [(3,1)]);(mkA 0 [(4,1)])] (mkC StA (mkS [S0] [] 0 0 []) S1 (mkS [S1] [S1] 1 0 [S0])) 1 false false 1 2 [(SWin 3); (SCycR 3); (SWin 2)]);
      (mkTL 6 [(1,0);(1,0);(1,0);(1,0)] 7 [(mkA 0 [(0,1);(1,1)]);(mkA 0 [(2,1)]);(mkA 0 [(3,1)])] (mkC StC (mkS [] [] 0 0 []) S0 (mkS [] [S1] 1 5 [])) 1 false false 0 1 [(SCycR 3)]);
      (mkTL 7 [(1,0);(0,0);(1,0)] 9 [(mkA 10 [(0,1);(2,1)])] (mkC StC (mkS [] [] 0 0 []) S0 (mkS [] [S1] 1 7 [])) 2 false true 0 2 [(SCycR 3); (SWinR 1); (SWin 1)]);
      (mkTL 7 [(1,0);(1,1);(1,0)] 8 [(mkA 5 [(0,1)]);(mkA 0 []);(mkA 0 [(1,1)]);(mkA 0 [(2,1)])] (mkC StC (mkS [] [] 0 0 []) S0 (mkS [S0;S1;S1;S1] [S0;S1;S1;S1] 1 0 [])) 1 false false 0 1 [(SWin 2)]);
      (mkTL 8 [(1,0);(1,0);(1,0);(1,0)] 10 [(mkA 0 [(0,1)]);(mkA 0 [(1,1)]);(mkA 0 [(2,1)]);(mkA 0 [(3,1)])] (mkC StD (mkS [S1] [S1] 1 1 []) S0 (mkS [] [] 0 0 [])) 0 true false 1 0 [(SWin 1)]);
      (mkTL 9 [(1,0)] 11 [(mkA 2 [(0,1)]);(mkA 0 [])] (mkC StD (mkS [S1] [S1] 1 3 []) S0 (mkS [S1] [] 0 0 [])) 0 true true 1 1 [(SWin 1)]);
      (mkTL 10 [(1,0);(1,0);(1,0);(1,0)] 12 [(mkA 0 [(0,1)]);(mkA 0 [(1,1)]);(mkA 0 [(2,1)]);(mkA 0 [(3,1)])] (mkC StD (mkS [S1] [S1] 1 0 []) S1 (mkS [] [] 0 0 [])) 0 true false 1 0 [(SWin 1); (SCycL 1 0); (SWinL 1); (SWin 1)]);
      (mkTL 11 [(1,0);(1,0)] 13 [(mkA 0 [(0,1)]);(mkA 0 [(1,1)])] (mkC StD (mkS [S1] [S1] 1 0 []) S1 (mkS [] [] 0 0 [])) 0 true false 1 0 [(SWin 1); (SCycL 1 0); (SWinL 1); (SWin 1)]);
      (mkTL 12 [(0,0);(1,0);(1,0);(1,0)] 6 [(mkA 0 []);(mkA 0 [(1,1)]);(mkA 0 [(2,1)]);(mkA 0 [(3,1)])] (mkC StC (mkS [S1] [] 0 0 []) S1 (mkS [S0] [] 0 0 [])) 0 true false 1 2 [(SWin 3)]);
      (mkTL 12 [(1,1);(1,0);(1,0);(1,0)] 14 [(mkA 0 [(0,1)]);(mkA 0 [(1,1)]);(mkA 0 [(2,1)]);(mkA 0 [(3,1)])] (mkC StC (mkS [S1] [] 0 0 []) S1 (mkS [S1] [S1] 1 0 [S0])) 0 true false 1 2 [(SWin 1)]);
      (mkTL 13 [(0,0);(1,0)] 24 [(mkA 0 []);(mkA 0 [(1,1)])] (mkC StC (mkS [S1] [] 0 0 []) S1 (mkS [S0] [] 0 0 [])) 0 true false 1 2 [(SWin 3)]);
      (mkTL 13 [(1,1);(1,0)] 15 [(mkA 0 [(0,1)]);(mkA 0 [(1,1)])] (mkC StC (mkS [S1] [] 0 0 []) S1 (mkS [S1] [S1] 1 0 [S0])) 0 true false 1 2 [(SWin 1)]);
      (mkTL 14 [(0,0);(1,0);(1,0);(1,0)] 6 [(mkA 2 []);(mkA 0 [(1,1)]);(mkA 0 [(2,1)]);(mkA 0 [(3,1)])] (mkC StA (mkS [S0;S1] [] 0 0 []) S1 (mkS [S0] [] 0 0 [])) 0 true false 1 2 [(SWin 4); (SWinL 1); (SWin 10)]);
      (mkTL 14 [(1,1);(1,0);(1,0);(1,0)] 16 [(mkA 0 [(0,1)]);(mkA 0 [(1,1)]);(mkA 0 [(2,1)]);(mkA 0 [(3,1)])] (mkC StA (mkS [S0;S1] [] 0 0 []) S1 (mkS [S1] [S1] 1 0 [S0])) 0 true false 1 2 [(SWin 3); (SCycR 3); (SWin 2)]);
      (mkTL 15 [(0,0);(1,0)] 24 [(mkA 2 []);(mkA 0 [(1,1)])] (mkC StA (mkS [S0;S1] [] 0 0 []) S1 (mkS [S0] [] 0 0 [])) 0 true false 1 2 [(SWin 4); (SWinL 1); (SWin 10)]);
      (mkTL 15 [(1,1);(1,0)] 17 [(mkA 0 [(0,1)]);(mkA 0 [(1,1)])] (mkC StA (mkS [S0;S1] [] 0 0 []) S1 (mkS [S1] [S1] 1 0 [S0])) 0 true false 1 2 [(SWin 3); (SCycR 3); (SWin 2)]);
      (mkTL 16 [(1,0);(1,0);(1,0);(1,0)] 18 [(mkA 0 [(0,1)]);(mkA 0 [(1,1)]);(mkA 0 [(2,1)]);(mkA 0 [(3,1)])] (mkC StD (mkS [S1] [S1] 1 0 [S0;S1]) S0 (mkS [] [] 0 0 [])) 0 true false 2 0 [(SWin 1)]);
      (mkTL 17 [(1,0);(1,0)] 19 [(mkA 0 [(0,1)]);(mkA 0 [(1,1)])] (mkC StD (mkS [S1] [S1] 1 0 [S0;S1]) S0 (mkS [] [] 0 0 [])) 0 true false 2 0 [(SWin 1)]);
      (mkTL 18 [(0,0);(1,0);(1,0);(1,0)] 6 [(mkA 0 []);(mkA 2 [(1,1)]);(mkA 0 [(2,1)]);(mkA 0 [(3,1)])] (mkC StD (mkS [S0;S1] [] 0 0 []) S1 (mkS [] [] 0 0 [])) 0 true false 2 0 [(SWin 2)]);
      (mkTL 18 [(1,1);(1,0);(1,0);(1,0)] 4 [(mkA 0 []);(mkA 0 [(0,1)]);(mkA 2 [(1,1)]);(mkA 0 [(2,1)]);(mkA 0 [(3,1)])] (mkC StD (mkS [S1] [S1] 1 0 [S0;S1]) S1 (mkS [] [] 0 0 [])) 0 true false 2 0 [(SWin 1); (SCycL 1 0); (SWin 2)]);
      (mkTL 19 [(0,0);(1,0)] 24 [(mkA 0 []);(mkA 2 [(1,1)])] (mkC StD (mkS [S0;S1] [] 0 0 []) S1 (mkS [] [] 0 0 [])) 0 true false 2 0 [(SWin 2)]);
      (mkTL 19 [(1,1);(1,0)] 20 [(mkA 0 []);(mkA 0 [(0,1)]);(mkA 0 [(1,1)])] (mkC StD (mkS [S1] [S1] 1 0 [S0;S1]) S1 (mkS [] [] 0 0 [])) 0 true false 2 0 [(SWin 1); (SCycL 1 0); (SWin 2)]);
      (mkTL 20 [(1,0);(0,0);(1,0)] 24 [(mkA 1 [(0,1)]);(mkA 2 [(2,1)])] (mkC StC (mkS [] [] 0 0 []) S1 (mkS [S0] [] 0 0 [])) 0 false false 0 2 [(SWin 3)]);
      (mkTL 20 [(1,0);(1,1);(1,0)] 21 [(mkA 0 [(0,1)]);(mkA 0 [(1,1)]);(mkA 0 [(2,1)])] (mkC StC (mkS [] [] 0 0 []) S1 (mkS [S1] [S1] 1 0 [S0])) 1 false false 0 2 [(SWin 1)]);
      (mkTL 21 [(1,0);(0,0);(1,0)] 25 [(mkA 0 [(0,1)]);(mkA 0 [(2,1)])] (mkC StA (mkS [S0] [] 0 0 []) S1 (mkS [S0] [] 0 0 [])) 0 false false 1 2 [(SWin 3)]);
      (mkTL 21 [(1,0);(1,1);(1,0)] 22 [(mkA 0 [(1,1)]);(mkA 0 [(0,1)]);(mkA 0 [(2,1)])] (mkC StA (mkS [S0] [] 0 0 []) S1 (mkS [S1] [S1] 1 0 [S0])) 1 false false 1 2 [(SWin 3); (SCycR 3); (SWin 2)]);
      (mkTL 22 [(1,0);(1,0);(1,0)] 23 [(mkA 0 [(0,1)]);(mkA 0 [(1,1)]);(mkA 0 [(2,1)])] (mkC StD (mkS [S1] [S1] 1 0 [S0]) S0 (mkS [] [] 0 0 [])) 0 false false 2 0 [(SWin 1)]);
      (mkTL 23 [(0,0);(1,0);(1,0)] 24 [(mkA 1 [(1,1)]);(mkA 4 [(2,1)])] (mkC StD (mkS [S0] [] 0 0 []) S1 (mkS [] [] 0 0 [])) 0 false false 2 0 [(SWin 2)]);
      (mkTL 23 [(1,1);(1,0);(1,0)] 20 [(mkA 1 [(1,1)]);(mkA 0 [(0,1)]);(mkA 2 [(2,1)])] (mkC StD (mkS [S1] [S1] 1 0 [S0]) S1 (mkS [] [] 0 0 [])) 0 false false 2 0 [(SWin 1); (SCycL 1 0); (SWin 2)]);
      (mkTL 24 [(1,0);(1,0)] 9 [(mkA 0 [(0,1);(1,1)])] (mkC StC (mkS [] [] 0 0 []) S0 (mkS [] [S1] 1 2 [])) 1 false true 0 1 [(SCycR 3); (SWinR 1); (SWin 1)]);
      (mkTL 25 [(1,0);(1,0)] 11 [(mkA 0 [(0,1)]);(mkA 5 [(1,1)])] (mkC StD (mkS [S1] [S1] 1 1 []) S0 (mkS [] [] 0 0 [])) 0 true false 1 0 [(SWin 1)])]
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

Local Lemma e0 : forall a b c d t, H t 1 [a;b;c;d] -> H t 0 [a;b;c;d].
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

Local Lemma e1 : forall a b c d t, H t 2 [a+16;b+3;0;c;d] -> H t 1 [a;b;c;d].
Proof.
 intros a b c d t E.
 pose proof (tri_leaf_back tm fams (nth 1 fams (mkTF StA S0 [] [] 0 []))
   (nth 1 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   (nth 2 fams (mkTF StA S0 [] [] 0 []))
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

Local Lemma e2 : forall a b c d e t, H t 3 [a;b;c;d;e] -> H t 2 [a;b;c;d;e].
Proof.
 intros a b c d e t E.
 pose proof (tri_leaf_back tm fams (nth 2 fams (mkTF StA S0 [] [] 0 []))
   (nth 2 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   (nth 3 fams (mkTF StA S0 [] [] 0 []))
   ltac:(vm_compute;reflexivity) ltac:(reflexivity) [a;b;c;d;e] t) as B.
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

Local Lemma e3 : forall b c d e t, H t 6 [b+1;c;d;e] -> H t 3 [0;b;c;d;e].
Proof.
 intros b c d e t E.
 pose proof (tri_leaf_back tm fams (nth 3 fams (mkTF StA S0 [] [] 0 []))
   (nth 3 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   (nth 6 fams (mkTF StA S0 [] [] 0 []))
   ltac:(vm_compute;reflexivity) ltac:(reflexivity) [0;b;c;d;e] t) as B.
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

Local Lemma e4 : forall a b c d e t, H t 4 [b+1;a;c;d;e] -> H t 3 [a+1;b;c;d;e].
Proof.
 intros a b c d e t E.
 pose proof (tri_leaf_back tm fams (nth 3 fams (mkTF StA S0 [] [] 0 []))
   (nth 4 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   (nth 4 fams (mkTF StA S0 [] [] 0 []))
   ltac:(vm_compute;reflexivity) ltac:(reflexivity) [a;b;c;d;e] t) as B.
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

Local Lemma e5 : forall a c d e t, H t 6 [a+1;c;d;e] -> H t 4 [a;0;c;d;e].
Proof.
 intros a c d e t E.
 pose proof (tri_leaf_back tm fams (nth 4 fams (mkTF StA S0 [] [] 0 []))
   (nth 5 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   (nth 6 fams (mkTF StA S0 [] [] 0 []))
   ltac:(vm_compute;reflexivity) ltac:(reflexivity) [a;0;c;d;e] t) as B.
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

Local Lemma e6 : forall a b c d e t, H t 5 [a;b;c;d;e] -> H t 4 [a;b+1;c;d;e].
Proof.
 intros a b c d e t E.
 pose proof (tri_leaf_back tm fams (nth 4 fams (mkTF StA S0 [] [] 0 []))
   (nth 6 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   (nth 5 fams (mkTF StA S0 [] [] 0 []))
   ltac:(vm_compute;reflexivity) ltac:(reflexivity) [a;b;c;d;e] t) as B.
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

Local Lemma e7 : forall a c d e t, H t 8 [a;c+3;d;e] -> H t 5 [a;0;c;d;e].
Proof.
 intros a c d e t E.
 pose proof (tri_leaf_back tm fams (nth 5 fams (mkTF StA S0 [] [] 0 []))
   (nth 7 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   (nth 8 fams (mkTF StA S0 [] [] 0 []))
   ltac:(vm_compute;reflexivity) ltac:(reflexivity) [a;0;c;d;e] t) as B.
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

Local Lemma e8 : forall a b c d e t, H t 2 [b;a;c+2;d;e] -> H t 5 [a;b+1;c;d;e].
Proof.
 intros a b c d e t E.
 pose proof (tri_leaf_back tm fams (nth 5 fams (mkTF StA S0 [] [] 0 []))
   (nth 8 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   (nth 2 fams (mkTF StA S0 [] [] 0 []))
   ltac:(vm_compute;reflexivity) ltac:(reflexivity) [a;b;c;d;e] t) as B.
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

Local Lemma e9 : forall a b c d t, H t 7 [a+b;c;d] -> H t 6 [a;b;c;d].
Proof.
 intros a b c d t E.
 pose proof (tri_leaf_back tm fams (nth 6 fams (mkTF StA S0 [] [] 0 []))
   (nth 9 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   (nth 7 fams (mkTF StA S0 [] [] 0 []))
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

Local Lemma e10 : forall a c t, H t 9 [a+c+10] -> H t 7 [a;0;c].
Proof.
 intros a c t E.
 pose proof (tri_leaf_back tm fams (nth 7 fams (mkTF StA S0 [] [] 0 []))
   (nth 10 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   (nth 9 fams (mkTF StA S0 [] [] 0 []))
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

Local Lemma e11 : forall a b c t, H t 8 [a+5;0;b;c] -> H t 7 [a;b+1;c].
Proof.
 intros a b c t E.
 pose proof (tri_leaf_back tm fams (nth 7 fams (mkTF StA S0 [] [] 0 []))
   (nth 11 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   (nth 8 fams (mkTF StA S0 [] [] 0 []))
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

Local Lemma e12 : forall a b c d t, H t 10 [a;b;c;d] -> H t 8 [a;b;c;d].
Proof.
 intros a b c d t E.
 pose proof (tri_leaf_back tm fams (nth 8 fams (mkTF StA S0 [] [] 0 []))
   (nth 12 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   (nth 10 fams (mkTF StA S0 [] [] 0 []))
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

Local Lemma e13 : forall a t, H t 11 [a+2;0] -> H t 9 [a].
Proof.
 intros a t E.
 pose proof (tri_leaf_back tm fams (nth 9 fams (mkTF StA S0 [] [] 0 []))
   (nth 13 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
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

Local Lemma e14 : forall a b c d t, H t 12 [a;b;c;d] -> H t 10 [a;b;c;d].
Proof.
 intros a b c d t E.
 pose proof (tri_leaf_back tm fams (nth 10 fams (mkTF StA S0 [] [] 0 []))
   (nth 14 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   (nth 12 fams (mkTF StA S0 [] [] 0 []))
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

Local Lemma e15 : forall a b t, H t 13 [a;b] -> H t 11 [a;b].
Proof.
 intros a b t E.
 pose proof (tri_leaf_back tm fams (nth 11 fams (mkTF StA S0 [] [] 0 []))
   (nth 15 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
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

Local Lemma e16 : forall b c d t, H t 6 [0;b;c;d] -> H t 12 [0;b;c;d].
Proof.
 intros b c d t E.
 pose proof (tri_leaf_back tm fams (nth 12 fams (mkTF StA S0 [] [] 0 []))
   (nth 16 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   (nth 6 fams (mkTF StA S0 [] [] 0 []))
   ltac:(vm_compute;reflexivity) ltac:(reflexivity) [0;b;c;d] t) as B.
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

Local Lemma e17 : forall a b c d t, H t 14 [a;b;c;d] -> H t 12 [a+1;b;c;d].
Proof.
 intros a b c d t E.
 pose proof (tri_leaf_back tm fams (nth 12 fams (mkTF StA S0 [] [] 0 []))
   (nth 17 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   (nth 14 fams (mkTF StA S0 [] [] 0 []))
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

Local Lemma e18 : forall b t, H t 24 [0;b] -> H t 13 [0;b].
Proof.
 intros b t E.
 pose proof (tri_leaf_back tm fams (nth 13 fams (mkTF StA S0 [] [] 0 []))
   (nth 18 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   (nth 24 fams (mkTF StA S0 [] [] 0 []))
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

Local Lemma e19 : forall a b t, H t 15 [a;b] -> H t 13 [a+1;b].
Proof.
 intros a b t E.
 pose proof (tri_leaf_back tm fams (nth 13 fams (mkTF StA S0 [] [] 0 []))
   (nth 19 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   (nth 15 fams (mkTF StA S0 [] [] 0 []))
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

Local Lemma e20 : forall b c d t, H t 6 [2;b;c;d] -> H t 14 [0;b;c;d].
Proof.
 intros b c d t E.
 pose proof (tri_leaf_back tm fams (nth 14 fams (mkTF StA S0 [] [] 0 []))
   (nth 20 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   (nth 6 fams (mkTF StA S0 [] [] 0 []))
   ltac:(vm_compute;reflexivity) ltac:(reflexivity) [0;b;c;d] t) as B.
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

Local Lemma e21 : forall a b c d t, H t 16 [a;b;c;d] -> H t 14 [a+1;b;c;d].
Proof.
 intros a b c d t E.
 pose proof (tri_leaf_back tm fams (nth 14 fams (mkTF StA S0 [] [] 0 []))
   (nth 21 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   (nth 16 fams (mkTF StA S0 [] [] 0 []))
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

Local Lemma e22 : forall b t, H t 24 [2;b] -> H t 15 [0;b].
Proof.
 intros b t E.
 pose proof (tri_leaf_back tm fams (nth 15 fams (mkTF StA S0 [] [] 0 []))
   (nth 22 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   (nth 24 fams (mkTF StA S0 [] [] 0 []))
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

Local Lemma e23 : forall a b t, H t 17 [a;b] -> H t 15 [a+1;b].
Proof.
 intros a b t E.
 pose proof (tri_leaf_back tm fams (nth 15 fams (mkTF StA S0 [] [] 0 []))
   (nth 23 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   (nth 17 fams (mkTF StA S0 [] [] 0 []))
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

Local Lemma e24 : forall a b c d t, H t 18 [a;b;c;d] -> H t 16 [a;b;c;d].
Proof.
 intros a b c d t E.
 pose proof (tri_leaf_back tm fams (nth 16 fams (mkTF StA S0 [] [] 0 []))
   (nth 24 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   (nth 18 fams (mkTF StA S0 [] [] 0 []))
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

Local Lemma e25 : forall a b t, H t 19 [a;b] -> H t 17 [a;b].
Proof.
 intros a b t E.
 pose proof (tri_leaf_back tm fams (nth 17 fams (mkTF StA S0 [] [] 0 []))
   (nth 25 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   (nth 19 fams (mkTF StA S0 [] [] 0 []))
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

Local Lemma e26 : forall b c d t, H t 6 [0;b+2;c;d] -> H t 18 [0;b;c;d].
Proof.
 intros b c d t E.
 pose proof (tri_leaf_back tm fams (nth 18 fams (mkTF StA S0 [] [] 0 []))
   (nth 26 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   (nth 6 fams (mkTF StA S0 [] [] 0 []))
   ltac:(vm_compute;reflexivity) ltac:(reflexivity) [0;b;c;d] t) as B.
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

Local Lemma e27 : forall a b c d t, H t 4 [0;a;b+2;c;d] -> H t 18 [a+1;b;c;d].
Proof.
 intros a b c d t E.
 pose proof (tri_leaf_back tm fams (nth 18 fams (mkTF StA S0 [] [] 0 []))
   (nth 27 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   (nth 4 fams (mkTF StA S0 [] [] 0 []))
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

Local Lemma e28 : forall b t, H t 24 [0;b+2] -> H t 19 [0;b].
Proof.
 intros b t E.
 pose proof (tri_leaf_back tm fams (nth 19 fams (mkTF StA S0 [] [] 0 []))
   (nth 28 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   (nth 24 fams (mkTF StA S0 [] [] 0 []))
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

Local Lemma e29 : forall a b t, H t 20 [0;a;b] -> H t 19 [a+1;b].
Proof.
 intros a b t E.
 pose proof (tri_leaf_back tm fams (nth 19 fams (mkTF StA S0 [] [] 0 []))
   (nth 29 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   (nth 20 fams (mkTF StA S0 [] [] 0 []))
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

Local Lemma e30 : forall a c t, H t 24 [a+1;c+2] -> H t 20 [a;0;c].
Proof.
 intros a c t E.
 pose proof (tri_leaf_back tm fams (nth 20 fams (mkTF StA S0 [] [] 0 []))
   (nth 30 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   (nth 24 fams (mkTF StA S0 [] [] 0 []))
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

Local Lemma e31 : forall a b c t, H t 21 [a;b;c] -> H t 20 [a;b+1;c].
Proof.
 intros a b c t E.
 pose proof (tri_leaf_back tm fams (nth 20 fams (mkTF StA S0 [] [] 0 []))
   (nth 31 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   (nth 21 fams (mkTF StA S0 [] [] 0 []))
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

Local Lemma e32 : forall a c t, H t 25 [a;c] -> H t 21 [a;0;c].
Proof.
 intros a c t E.
 pose proof (tri_leaf_back tm fams (nth 21 fams (mkTF StA S0 [] [] 0 []))
   (nth 32 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   (nth 25 fams (mkTF StA S0 [] [] 0 []))
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

Local Lemma e33 : forall a b c t, H t 22 [b;a;c] -> H t 21 [a;b+1;c].
Proof.
 intros a b c t E.
 pose proof (tri_leaf_back tm fams (nth 21 fams (mkTF StA S0 [] [] 0 []))
   (nth 33 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   (nth 22 fams (mkTF StA S0 [] [] 0 []))
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

Local Lemma e34 : forall a b c t, H t 23 [a;b;c] -> H t 22 [a;b;c].
Proof.
 intros a b c t E.
 pose proof (tri_leaf_back tm fams (nth 22 fams (mkTF StA S0 [] [] 0 []))
   (nth 34 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   (nth 23 fams (mkTF StA S0 [] [] 0 []))
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

Local Lemma e35 : forall b c t, H t 24 [b+1;c+4] -> H t 23 [0;b;c].
Proof.
 intros b c t E.
 pose proof (tri_leaf_back tm fams (nth 23 fams (mkTF StA S0 [] [] 0 []))
   (nth 35 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   (nth 24 fams (mkTF StA S0 [] [] 0 []))
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

Local Lemma e36 : forall a b c t, H t 20 [b+1;a;c+2] -> H t 23 [a+1;b;c].
Proof.
 intros a b c t E.
 pose proof (tri_leaf_back tm fams (nth 23 fams (mkTF StA S0 [] [] 0 []))
   (nth 36 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   (nth 20 fams (mkTF StA S0 [] [] 0 []))
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

Local Lemma e37 : forall a b t, H t 9 [a+b] -> H t 24 [a;b].
Proof.
 intros a b t E.
 pose proof (tri_leaf_back tm fams (nth 24 fams (mkTF StA S0 [] [] 0 []))
   (nth 37 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
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

Local Lemma e38 : forall a b t, H t 11 [a;b+5] -> H t 25 [a;b].
Proof.
 intros a b t E.
 pose proof (tri_leaf_back tm fams (nth 25 fams (mkTF StA S0 [] [] 0 []))
   (nth 38 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
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

Local Lemma f0 : forall a b c d t, In t [(StB,S0);(StC,S0);(StD,S1)] -> H t 0 [a;b;c;d].
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

Local Lemma f1 : forall a b c d t, In t [(StC,S0);(StD,S0)] -> H t 1 [a;b;c;d].
Proof.
 intros a b c d t Et.
 pose proof (tri_leaf_now tm fams (nth 1 fams (mkTF StA S0 [] [] 0 []))
   (nth 1 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   ltac:(vm_compute;reflexivity) t ltac:(vm_compute in Et |- *; tauto) [a;b;c;d]) as B.
 cube_norm.
 unfold H, tanc. cbn [fams cert tc_fams nth_error fst snd].
 match type of B with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact B
  end end.
Qed.

Local Lemma f2 : forall a b c d e t, In t [(StD,S0);(StD,S1)] -> H t 2 [a;b;c;d;e].
Proof.
 intros a b c d e t Et.
 pose proof (tri_leaf_now tm fams (nth 2 fams (mkTF StA S0 [] [] 0 []))
   (nth 2 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   ltac:(vm_compute;reflexivity) t ltac:(vm_compute in Et |- *; tauto) [a;b;c;d;e]) as B.
 cube_norm.
 unfold H, tanc. cbn [fams cert tc_fams nth_error fst snd].
 match type of B with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact B
  end end.
Qed.

Local Lemma f3 : forall b c d e t, In t [(StB,S0);(StC,S0);(StD,S1)] -> H t 3 [0;b;c;d;e].
Proof.
 intros b c d e t Et.
 pose proof (tri_leaf_now tm fams (nth 3 fams (mkTF StA S0 [] [] 0 []))
   (nth 3 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   ltac:(vm_compute;reflexivity) t ltac:(vm_compute in Et |- *; tauto) [0;b;c;d;e]) as B.
 cube_norm.
 unfold H, tanc. cbn [fams cert tc_fams nth_error fst snd].
 match type of B with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact B
  end end.
Qed.

Local Lemma f4 : forall a b c d e t, In t [(StB,S0);(StB,S1);(StC,S1);(StD,S1)] -> H t 3 [a+1;b;c;d;e].
Proof.
 intros a b c d e t Et.
 pose proof (tri_leaf_now tm fams (nth 3 fams (mkTF StA S0 [] [] 0 []))
   (nth 4 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   ltac:(vm_compute;reflexivity) t ltac:(vm_compute in Et |- *; tauto) [a;b;c;d;e]) as B.
 cube_norm.
 unfold H, tanc. cbn [fams cert tc_fams nth_error fst snd].
 match type of B with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact B
  end end.
Qed.

Local Lemma f5 : forall a c d e t, In t [(StA,S0);(StB,S0);(StC,S0);(StC,S1)] -> H t 4 [a;0;c;d;e].
Proof.
 intros a c d e t Et.
 pose proof (tri_leaf_now tm fams (nth 4 fams (mkTF StA S0 [] [] 0 []))
   (nth 5 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   ltac:(vm_compute;reflexivity) t ltac:(vm_compute in Et |- *; tauto) [a;0;c;d;e]) as B.
 cube_norm.
 unfold H, tanc. cbn [fams cert tc_fams nth_error fst snd].
 match type of B with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact B
  end end.
Qed.

Local Lemma f6 : forall a b c d e t, In t [(StA,S1);(StC,S1)] -> H t 4 [a;b+1;c;d;e].
Proof.
 intros a b c d e t Et.
 pose proof (tri_leaf_now tm fams (nth 4 fams (mkTF StA S0 [] [] 0 []))
   (nth 6 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   ltac:(vm_compute;reflexivity) t ltac:(vm_compute in Et |- *; tauto) [a;b;c;d;e]) as B.
 cube_norm.
 unfold H, tanc. cbn [fams cert tc_fams nth_error fst snd].
 match type of B with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact B
  end end.
Qed.

Local Lemma f7 : forall a c d e t, In t [(StA,S1);(StD,S0)] -> H t 5 [a;0;c;d;e].
Proof.
 intros a c d e t Et.
 pose proof (tri_leaf_now tm fams (nth 5 fams (mkTF StA S0 [] [] 0 []))
   (nth 7 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   ltac:(vm_compute;reflexivity) t ltac:(vm_compute in Et |- *; tauto) [a;0;c;d;e]) as B.
 cube_norm.
 unfold H, tanc. cbn [fams cert tc_fams nth_error fst snd].
 match type of B with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact B
  end end.
Qed.

Local Lemma f8 : forall a b c d e t, In t [(StA,S1);(StB,S0);(StC,S0);(StD,S0);(StD,S1)] -> H t 5 [a;b+1;c;d;e].
Proof.
 intros a b c d e t Et.
 pose proof (tri_leaf_now tm fams (nth 5 fams (mkTF StA S0 [] [] 0 []))
   (nth 8 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   ltac:(vm_compute;reflexivity) t ltac:(vm_compute in Et |- *; tauto) [a;b;c;d;e]) as B.
 cube_norm.
 unfold H, tanc. cbn [fams cert tc_fams nth_error fst snd].
 match type of B with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact B
  end end.
Qed.

Local Lemma f9 : forall a b c d t, In t [(StC,S0)] -> H t 6 [a;b;c;d].
Proof.
 intros a b c d t Et.
 pose proof (tri_leaf_now tm fams (nth 6 fams (mkTF StA S0 [] [] 0 []))
   (nth 9 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   ltac:(vm_compute;reflexivity) t ltac:(vm_compute in Et |- *; tauto) [a;b;c;d]) as B.
 cube_norm.
 unfold H, tanc. cbn [fams cert tc_fams nth_error fst snd].
 match type of B with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact B
  end end.
Qed.

Local Lemma f10 : forall a c t, In t [(StC,S0);(StD,S0)] -> H t 7 [a;0;c].
Proof.
 intros a c t Et.
 pose proof (tri_leaf_now tm fams (nth 7 fams (mkTF StA S0 [] [] 0 []))
   (nth 10 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   ltac:(vm_compute;reflexivity) t ltac:(vm_compute in Et |- *; tauto) [a;0;c]) as B.
 cube_norm.
 unfold H, tanc. cbn [fams cert tc_fams nth_error fst snd].
 match type of B with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact B
  end end.
Qed.

Local Lemma f11 : forall a b c t, In t [(StC,S0);(StD,S0)] -> H t 7 [a;b+1;c].
Proof.
 intros a b c t Et.
 pose proof (tri_leaf_now tm fams (nth 7 fams (mkTF StA S0 [] [] 0 []))
   (nth 11 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   ltac:(vm_compute;reflexivity) t ltac:(vm_compute in Et |- *; tauto) [a;b;c]) as B.
 cube_norm.
 unfold H, tanc. cbn [fams cert tc_fams nth_error fst snd].
 match type of B with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact B
  end end.
Qed.

Local Lemma f12 : forall a b c d t, In t [(StD,S0);(StD,S1)] -> H t 8 [a;b;c;d].
Proof.
 intros a b c d t Et.
 pose proof (tri_leaf_now tm fams (nth 8 fams (mkTF StA S0 [] [] 0 []))
   (nth 12 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   ltac:(vm_compute;reflexivity) t ltac:(vm_compute in Et |- *; tauto) [a;b;c;d]) as B.
 cube_norm.
 unfold H, tanc. cbn [fams cert tc_fams nth_error fst snd].
 match type of B with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact B
  end end.
Qed.

Local Lemma f13 : forall a t, In t [(StD,S0);(StD,S1)] -> H t 9 [a].
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

Local Lemma f14 : forall a b c d t, In t [(StB,S0);(StB,S1);(StC,S1);(StD,S1)] -> H t 10 [a;b;c;d].
Proof.
 intros a b c d t Et.
 pose proof (tri_leaf_now tm fams (nth 10 fams (mkTF StA S0 [] [] 0 []))
   (nth 14 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   ltac:(vm_compute;reflexivity) t ltac:(vm_compute in Et |- *; tauto) [a;b;c;d]) as B.
 cube_norm.
 unfold H, tanc. cbn [fams cert tc_fams nth_error fst snd].
 match type of B with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact B
  end end.
Qed.

Local Lemma f15 : forall a b t, In t [(StB,S0);(StB,S1);(StC,S1);(StD,S1)] -> H t 11 [a;b].
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

Local Lemma f16 : forall b c d t, In t [(StA,S0);(StB,S0);(StC,S0);(StC,S1)] -> H t 12 [0;b;c;d].
Proof.
 intros b c d t Et.
 pose proof (tri_leaf_now tm fams (nth 12 fams (mkTF StA S0 [] [] 0 []))
   (nth 16 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   ltac:(vm_compute;reflexivity) t ltac:(vm_compute in Et |- *; tauto) [0;b;c;d]) as B.
 cube_norm.
 unfold H, tanc. cbn [fams cert tc_fams nth_error fst snd].
 match type of B with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact B
  end end.
Qed.

Local Lemma f17 : forall a b c d t, In t [(StA,S1);(StC,S1)] -> H t 12 [a+1;b;c;d].
Proof.
 intros a b c d t Et.
 pose proof (tri_leaf_now tm fams (nth 12 fams (mkTF StA S0 [] [] 0 []))
   (nth 17 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   ltac:(vm_compute;reflexivity) t ltac:(vm_compute in Et |- *; tauto) [a;b;c;d]) as B.
 cube_norm.
 unfold H, tanc. cbn [fams cert tc_fams nth_error fst snd].
 match type of B with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact B
  end end.
Qed.

Local Lemma f18 : forall b t, In t [(StA,S0);(StB,S0);(StC,S0);(StC,S1)] -> H t 13 [0;b].
Proof.
 intros b t Et.
 pose proof (tri_leaf_now tm fams (nth 13 fams (mkTF StA S0 [] [] 0 []))
   (nth 18 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   ltac:(vm_compute;reflexivity) t ltac:(vm_compute in Et |- *; tauto) [0;b]) as B.
 cube_norm.
 unfold H, tanc. cbn [fams cert tc_fams nth_error fst snd].
 match type of B with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact B
  end end.
Qed.

Local Lemma f19 : forall a b t, In t [(StA,S1);(StC,S1)] -> H t 13 [a+1;b].
Proof.
 intros a b t Et.
 pose proof (tri_leaf_now tm fams (nth 13 fams (mkTF StA S0 [] [] 0 []))
   (nth 19 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   ltac:(vm_compute;reflexivity) t ltac:(vm_compute in Et |- *; tauto) [a;b]) as B.
 cube_norm.
 unfold H, tanc. cbn [fams cert tc_fams nth_error fst snd].
 match type of B with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact B
  end end.
Qed.

Local Lemma f20 : forall b c d t, In t [(StA,S1);(StB,S0);(StC,S0);(StD,S0);(StD,S1)] -> H t 14 [0;b;c;d].
Proof.
 intros b c d t Et.
 pose proof (tri_leaf_now tm fams (nth 14 fams (mkTF StA S0 [] [] 0 []))
   (nth 20 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   ltac:(vm_compute;reflexivity) t ltac:(vm_compute in Et |- *; tauto) [0;b;c;d]) as B.
 cube_norm.
 unfold H, tanc. cbn [fams cert tc_fams nth_error fst snd].
 match type of B with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact B
  end end.
Qed.

Local Lemma f21 : forall a b c d t, In t [(StA,S1);(StB,S0);(StC,S0);(StD,S0);(StD,S1)] -> H t 14 [a+1;b;c;d].
Proof.
 intros a b c d t Et.
 pose proof (tri_leaf_now tm fams (nth 14 fams (mkTF StA S0 [] [] 0 []))
   (nth 21 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   ltac:(vm_compute;reflexivity) t ltac:(vm_compute in Et |- *; tauto) [a;b;c;d]) as B.
 cube_norm.
 unfold H, tanc. cbn [fams cert tc_fams nth_error fst snd].
 match type of B with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact B
  end end.
Qed.

Local Lemma f22 : forall b t, In t [(StA,S1);(StB,S0);(StC,S0);(StD,S0);(StD,S1)] -> H t 15 [0;b].
Proof.
 intros b t Et.
 pose proof (tri_leaf_now tm fams (nth 15 fams (mkTF StA S0 [] [] 0 []))
   (nth 22 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   ltac:(vm_compute;reflexivity) t ltac:(vm_compute in Et |- *; tauto) [0;b]) as B.
 cube_norm.
 unfold H, tanc. cbn [fams cert tc_fams nth_error fst snd].
 match type of B with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact B
  end end.
Qed.

Local Lemma f23 : forall a b t, In t [(StA,S1);(StB,S0);(StC,S0);(StD,S0);(StD,S1)] -> H t 15 [a+1;b].
Proof.
 intros a b t Et.
 pose proof (tri_leaf_now tm fams (nth 15 fams (mkTF StA S0 [] [] 0 []))
   (nth 23 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   ltac:(vm_compute;reflexivity) t ltac:(vm_compute in Et |- *; tauto) [a;b]) as B.
 cube_norm.
 unfold H, tanc. cbn [fams cert tc_fams nth_error fst snd].
 match type of B with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact B
  end end.
Qed.

Local Lemma f24 : forall a b c d t, In t [(StD,S0);(StD,S1)] -> H t 16 [a;b;c;d].
Proof.
 intros a b c d t Et.
 pose proof (tri_leaf_now tm fams (nth 16 fams (mkTF StA S0 [] [] 0 []))
   (nth 24 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   ltac:(vm_compute;reflexivity) t ltac:(vm_compute in Et |- *; tauto) [a;b;c;d]) as B.
 cube_norm.
 unfold H, tanc. cbn [fams cert tc_fams nth_error fst snd].
 match type of B with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact B
  end end.
Qed.

Local Lemma f25 : forall a b t, In t [(StD,S0);(StD,S1)] -> H t 17 [a;b].
Proof.
 intros a b t Et.
 pose proof (tri_leaf_now tm fams (nth 17 fams (mkTF StA S0 [] [] 0 []))
   (nth 25 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   ltac:(vm_compute;reflexivity) t ltac:(vm_compute in Et |- *; tauto) [a;b]) as B.
 cube_norm.
 unfold H, tanc. cbn [fams cert tc_fams nth_error fst snd].
 match type of B with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact B
  end end.
Qed.

Local Lemma f26 : forall b c d t, In t [(StB,S0);(StC,S0);(StD,S1)] -> H t 18 [0;b;c;d].
Proof.
 intros b c d t Et.
 pose proof (tri_leaf_now tm fams (nth 18 fams (mkTF StA S0 [] [] 0 []))
   (nth 26 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   ltac:(vm_compute;reflexivity) t ltac:(vm_compute in Et |- *; tauto) [0;b;c;d]) as B.
 cube_norm.
 unfold H, tanc. cbn [fams cert tc_fams nth_error fst snd].
 match type of B with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact B
  end end.
Qed.

Local Lemma f27 : forall a b c d t, In t [(StB,S0);(StB,S1);(StC,S1);(StD,S1)] -> H t 18 [a+1;b;c;d].
Proof.
 intros a b c d t Et.
 pose proof (tri_leaf_now tm fams (nth 18 fams (mkTF StA S0 [] [] 0 []))
   (nth 27 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   ltac:(vm_compute;reflexivity) t ltac:(vm_compute in Et |- *; tauto) [a;b;c;d]) as B.
 cube_norm.
 unfold H, tanc. cbn [fams cert tc_fams nth_error fst snd].
 match type of B with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact B
  end end.
Qed.

Local Lemma f28 : forall b t, In t [(StB,S0);(StC,S0);(StD,S1)] -> H t 19 [0;b].
Proof.
 intros b t Et.
 pose proof (tri_leaf_now tm fams (nth 19 fams (mkTF StA S0 [] [] 0 []))
   (nth 28 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   ltac:(vm_compute;reflexivity) t ltac:(vm_compute in Et |- *; tauto) [0;b]) as B.
 cube_norm.
 unfold H, tanc. cbn [fams cert tc_fams nth_error fst snd].
 match type of B with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact B
  end end.
Qed.

Local Lemma f29 : forall a b t, In t [(StB,S0);(StB,S1);(StC,S1);(StD,S1)] -> H t 19 [a+1;b].
Proof.
 intros a b t Et.
 pose proof (tri_leaf_now tm fams (nth 19 fams (mkTF StA S0 [] [] 0 []))
   (nth 29 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   ltac:(vm_compute;reflexivity) t ltac:(vm_compute in Et |- *; tauto) [a;b]) as B.
 cube_norm.
 unfold H, tanc. cbn [fams cert tc_fams nth_error fst snd].
 match type of B with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact B
  end end.
Qed.

Local Lemma f30 : forall a c t, In t [(StA,S0);(StB,S0);(StC,S0);(StC,S1)] -> H t 20 [a;0;c].
Proof.
 intros a c t Et.
 pose proof (tri_leaf_now tm fams (nth 20 fams (mkTF StA S0 [] [] 0 []))
   (nth 30 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   ltac:(vm_compute;reflexivity) t ltac:(vm_compute in Et |- *; tauto) [a;0;c]) as B.
 cube_norm.
 unfold H, tanc. cbn [fams cert tc_fams nth_error fst snd].
 match type of B with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact B
  end end.
Qed.

Local Lemma f31 : forall a b c t, In t [(StA,S1);(StC,S1)] -> H t 20 [a;b+1;c].
Proof.
 intros a b c t Et.
 pose proof (tri_leaf_now tm fams (nth 20 fams (mkTF StA S0 [] [] 0 []))
   (nth 31 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   ltac:(vm_compute;reflexivity) t ltac:(vm_compute in Et |- *; tauto) [a;b;c]) as B.
 cube_norm.
 unfold H, tanc. cbn [fams cert tc_fams nth_error fst snd].
 match type of B with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact B
  end end.
Qed.

Local Lemma f32 : forall a c t, In t [(StA,S1);(StD,S0)] -> H t 21 [a;0;c].
Proof.
 intros a c t Et.
 pose proof (tri_leaf_now tm fams (nth 21 fams (mkTF StA S0 [] [] 0 []))
   (nth 32 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   ltac:(vm_compute;reflexivity) t ltac:(vm_compute in Et |- *; tauto) [a;0;c]) as B.
 cube_norm.
 unfold H, tanc. cbn [fams cert tc_fams nth_error fst snd].
 match type of B with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact B
  end end.
Qed.

Local Lemma f33 : forall a b c t, In t [(StA,S1);(StB,S0);(StC,S0);(StD,S0);(StD,S1)] -> H t 21 [a;b+1;c].
Proof.
 intros a b c t Et.
 pose proof (tri_leaf_now tm fams (nth 21 fams (mkTF StA S0 [] [] 0 []))
   (nth 33 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   ltac:(vm_compute;reflexivity) t ltac:(vm_compute in Et |- *; tauto) [a;b;c]) as B.
 cube_norm.
 unfold H, tanc. cbn [fams cert tc_fams nth_error fst snd].
 match type of B with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact B
  end end.
Qed.

Local Lemma f34 : forall a b c t, In t [(StD,S0);(StD,S1)] -> H t 22 [a;b;c].
Proof.
 intros a b c t Et.
 pose proof (tri_leaf_now tm fams (nth 22 fams (mkTF StA S0 [] [] 0 []))
   (nth 34 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   ltac:(vm_compute;reflexivity) t ltac:(vm_compute in Et |- *; tauto) [a;b;c]) as B.
 cube_norm.
 unfold H, tanc. cbn [fams cert tc_fams nth_error fst snd].
 match type of B with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact B
  end end.
Qed.

Local Lemma f35 : forall b c t, In t [(StB,S0);(StC,S0);(StD,S1)] -> H t 23 [0;b;c].
Proof.
 intros b c t Et.
 pose proof (tri_leaf_now tm fams (nth 23 fams (mkTF StA S0 [] [] 0 []))
   (nth 35 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   ltac:(vm_compute;reflexivity) t ltac:(vm_compute in Et |- *; tauto) [0;b;c]) as B.
 cube_norm.
 unfold H, tanc. cbn [fams cert tc_fams nth_error fst snd].
 match type of B with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact B
  end end.
Qed.

Local Lemma f36 : forall a b c t, In t [(StB,S0);(StB,S1);(StC,S1);(StD,S1)] -> H t 23 [a+1;b;c].
Proof.
 intros a b c t Et.
 pose proof (tri_leaf_now tm fams (nth 23 fams (mkTF StA S0 [] [] 0 []))
   (nth 36 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   ltac:(vm_compute;reflexivity) t ltac:(vm_compute in Et |- *; tauto) [a;b;c]) as B.
 cube_norm.
 unfold H, tanc. cbn [fams cert tc_fams nth_error fst snd].
 match type of B with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact B
  end end.
Qed.

Local Lemma f37 : forall a b t, In t [(StC,S0);(StD,S0)] -> H t 24 [a;b].
Proof.
 intros a b t Et.
 pose proof (tri_leaf_now tm fams (nth 24 fams (mkTF StA S0 [] [] 0 []))
   (nth 37 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   ltac:(vm_compute;reflexivity) t ltac:(vm_compute in Et |- *; tauto) [a;b]) as B.
 cube_norm.
 unfold H, tanc. cbn [fams cert tc_fams nth_error fst snd].
 match type of B with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact B
  end end.
Qed.

Local Lemma f38 : forall a b t, In t [(StD,S0);(StD,S1)] -> H t 25 [a;b].
Proof.
 intros a b t Et.
 pose proof (tri_leaf_now tm fams (nth 25 fams (mkTF StA S0 [] [] 0 []))
   (nth 38 leaves (mkTL 0 [] 0 [] (mkC StA (mkS [] [] 0 0 []) S0 (mkS [] [] 0 0 [])) 0 false false 0 0 []))
   ltac:(vm_compute;reflexivity) t ltac:(vm_compute in Et |- *; tauto) [a;b]) as B.
 cube_norm.
 unfold H, tanc. cbn [fams cert tc_fams nth_error fst snd].
 match type of B with tri_reaches_fire _ _ (tinst ?F ?xs) =>
  match goal with |- tri_reaches_fire _ _ (tinst F ?ys) =>
   replace ys with xs by (fold Nat.add; repeat (f_equal; try lia)); exact B
  end end.
Qed.

Local Ltac cube_now := first [solve [apply f0; simpl; auto] | solve [apply f1; simpl; auto] | solve [apply f2; simpl; auto] | solve [apply f3; simpl; auto] | solve [apply f4; simpl; auto] | solve [apply f5; simpl; auto] | solve [apply f6; simpl; auto] | solve [apply f7; simpl; auto] | solve [apply f8; simpl; auto] | solve [apply f9; simpl; auto] | solve [apply f10; simpl; auto] | solve [apply f11; simpl; auto] | solve [apply f12; simpl; auto] | solve [apply f13; simpl; auto] | solve [apply f14; simpl; auto] | solve [apply f15; simpl; auto] | solve [apply f16; simpl; auto] | solve [apply f17; simpl; auto] | solve [apply f18; simpl; auto] | solve [apply f19; simpl; auto] | solve [apply f20; simpl; auto] | solve [apply f21; simpl; auto] | solve [apply f22; simpl; auto] | solve [apply f23; simpl; auto] | solve [apply f24; simpl; auto] | solve [apply f25; simpl; auto] | solve [apply f26; simpl; auto] | solve [apply f27; simpl; auto] | solve [apply f28; simpl; auto] | solve [apply f29; simpl; auto] | solve [apply f30; simpl; auto] | solve [apply f31; simpl; auto] | solve [apply f32; simpl; auto] | solve [apply f33; simpl; auto] | solve [apply f34; simpl; auto] | solve [apply f35; simpl; auto] | solve [apply f36; simpl; auto] | solve [apply f37; simpl; auto] | solve [apply f38; simpl; auto]].
Local Ltac cube_exact E :=
 match type of E with H ?t ?i ?xs =>
  match goal with |- H t i ?ys =>
   replace ys with xs by (repeat (f_equal; try lia)); exact E
  end end.

Local Lemma cube_loop : forall k a b c t,
 H t 20 [a+k;b;c+2*k] -> H t 20 [a;3*k+b;c].
Proof.
 induction k as [|k IH]; intros a b c t E.
 - cbn [Nat.mul Nat.add]. cube_exact E.
 - replace (3*S k+b) with ((3*k+b+1)+1+1) by lia.
   apply e31,e33,e34,e36. apply IH. cube_exact E.
Qed.

Local Lemma cube_A0 : forall a b, H (StA,S0) 13 [a;b].
Proof.
 apply (cube_round_total (fun a b => H (StA,S0) 13 [a;b])).
 - intro b. apply f18. simpl; auto 12.
 - intros k b. replace (3*k+3) with ((3*k)+1+1+1) by lia.
   apply e19,e23,e25,e29.
   replace (3*k) with (3*k+0) by lia. apply (cube_loop k 0 0 b (StA,S0)). apply f30. simpl; auto 12.
 - intros b E. change (H (StA,S0) 13 [0+1;b]).
   apply e19,e22,e37,e13,e15. cube_exact E.
 - intros b E. change (H (StA,S0) 13 [1+1;b]).
   apply e19. change (H (StA,S0) 15 [0+1;b]).
   apply e23,e25,e28,e37,e13,e15. cube_exact E.
 - intros k b E. replace (3*k+4) with ((3*k+1)+1+1+1) by lia.
   apply e19,e23,e25,e29. apply (cube_loop k 0 1 b (StA,S0)).
   change (H (StA,S0) 20 [0+k;0+1;b+2*k]).
   apply e31,e32,e38,e15. cube_exact E.
 - intros k b E. replace (3*k+5) with ((3*k+2)+1+1+1) by lia.
   apply e19,e23,e25,e29. apply (cube_loop k 0 2 b (StA,S0)).
   change (H (StA,S0) 20 [0+k;1+1;b+2*k]).
   apply e31. change (H (StA,S0) 21 [0+k;0+1;b+2*k]).
   apply e33,e34,e35,e37,e13,e15. cube_exact E.
Qed.

Local Lemma cube_A1 : forall a b, H (StA,S1) 13 [a;b].
Proof.
 intros [|a] b.
 - apply e18,e37,e13,e15.
   replace (0+b+2) with ((b+1)+1) by lia. apply f19. simpl; auto 12.
 - replace (S a) with (a+1) by lia. apply f19. simpl; auto 12.
Qed.

Local Lemma cube_D1 : forall a b, H (StB,S1) 13 [a;b].
Proof.
 intros [|[|[|a]]] b.
 - apply e18,e37,e13,f15. simpl; auto 12.
 - change (H (StB,S1) 13 [0+1;b]).
   apply e19,e22,e37,e13,f15. simpl; auto 12.
 - change (H (StB,S1) 13 [1+1;b]). apply e19.
   change (H (StB,S1) 15 [0+1;b]).
   apply e23,e25,e28,e37,e13,f15. simpl; auto 12.
 - replace (S(S(S a))) with ((a+1)+1+1) by lia.
   apply e19,e23,e25,f29. simpl; auto 12.
Qed.

Local Lemma cube_common : forall a b t,
 In t [(StC,S0);(StC,S1);(StD,S0);(StD,S1);(StB,S0)] -> H t 13 [a;b].
Proof.
 intros [|a] b t E.
 - destruct E as [<-|[<-|[<-|[<-|[<-|[]]]]]];
   try solve [apply f18; simpl; auto 12];
   try solve [apply e18,f37; simpl; auto 12];
   apply e18,e37,f13; simpl; auto 12.
 - replace (S a) with (a+1) by lia.
   destruct (instr_eqb t (StC,S1)) eqn:EB.
   + apply instr_eqb_spec in EB. subst t. apply f19. simpl; auto 12.
   + assert (EN : (StC,S1) <> t).
     { intro Et. subst t. discriminate. }
     apply e19. destruct a as [|a].
     * apply f22. simpl in *; tauto.
     * replace (S a) with (a+1) by lia.
       apply f23. simpl in *; tauto.
Qed.

Local Lemma cube_ten : forall a b t, H t 13 [a;b].
Proof.
 intros a b [q s]. destruct q,s;
 try solve [apply cube_common; simpl; auto 12].
 - apply cube_A0.
 - apply cube_A1.
 - apply cube_D1.
Qed.

Local Lemma cube_four : forall b a c t, H t 20 [a;b;c].
Proof.
 induction b as [b IH] using lt_wf_ind. intros a c t.
 destruct b as [|[|[|b]]].
 - apply e30,e37,e13,e15,cube_ten.
 - change (H t 20 [a;0+1;c]). apply e31,e32,e38,e15,cube_ten.
 - change (H t 20 [a;1+1;c]). apply e31.
   change (H t 21 [a;0+1;c]). apply e33,e34,e35,e37,e13,e15,cube_ten.
 - replace (S(S(S b))) with ((b+1)+1+1) by lia.
   apply e31,e33,e34,e36. apply IH. lia.
Qed.

Local Lemma cube_three : forall a b c t, H t 23 [a;b;c].
Proof.
 intros [|a] b c t.
 - apply e35,e37,e13,e15,cube_ten.
 - replace (S a) with (a+1) by lia. apply e36,cube_four.
Qed.

Local Lemma cube_thirteen : forall a b t, H t 19 [a;b].
Proof.
 intros [|a] b t.
 - apply e28,e37,e13,e15,cube_ten.
 - replace (S a) with (a+1) by lia. apply e29,cube_four.
Qed.

Local Lemma cube_five : forall a b c t, H t 21 [a;b;c].
Proof.
 intros a [|b] c t.
 - apply e32,e38,e15,cube_ten.
 - replace (S b) with (b+1) by lia. apply e33,e34,cube_three.
Qed.

Local Lemma cube_eleven : forall a b t, H t 15 [a;b].
Proof.
 intros [|a] b t.
 - apply e22,e37,e13,e15,cube_ten.
 - replace (S a) with (a+1) by lia. apply e23,e25,cube_thirteen.
Qed.
Local Lemma expand_loop : forall k a b c d e t,
 H t 4 [a+k;b;c+2*k;d;e] -> H t 4 [a;3*k+b;c;d;e].
Proof.
 induction k as [|k IH]; intros a b c d e t E.
 - cbn [Nat.mul Nat.add]. cube_exact E.
 - replace (3*S k+b) with ((3*k+b+1)+1+1) by lia.
   apply e6,e8,e2,e4. apply IH. cube_exact E.
Qed.

Local Lemma expand_core : forall d,
 (forall a b e t, H t 6 [a;b;d;e]) ->
 forall a b e t, H t 12 [a;b;d;e].
Proof.
 intros d HS. induction a as [a IH] using lt_wf_ind. intros b e t.
 destruct a as [|[|[|a]]].
 - apply e16,HS.
 - change (H t 12 [0+1;b;d;e]). apply e17,e20,HS.
 - change (H t 12 [1+1;b;d;e]). apply e17.
   change (H t 14 [0+1;b;d;e]). apply e21,e24,e26,HS.
 - replace (S(S(S a))) with ((a+1)+1+1) by lia.
   apply e17,e21,e24,e27.
   assert (Ea : exists k, a=3*k \/ a=3*k+1 \/ a=3*k+2).
   { exists (a/3). pose proof (Nat.div_mod a 3 ltac:(lia)).
     pose proof (Nat.mod_upper_bound a 3 ltac:(lia)). lia. }
   destruct Ea as (k & [Ea|[Ea|Ea]]); subst a.
   + replace (3*k) with (3*k+0) by lia. apply expand_loop,e5,HS.
   + apply expand_loop. change (H t 4 [0+k;0+1;b+2+2*k;d;e]).
     apply e6,e7,e12,e14,IH. lia.
   + apply expand_loop. change (H t 4 [0+k;1+1;b+2+2*k;d;e]).
     apply e6. change (H t 5 [0+k;0+1;b+2+2*k;d;e]).
     apply e8,e2,e3,HS.
Qed.

Local Lemma expand_twelve : forall d a b e t, H t 12 [a;b;d;e].
Proof.
 induction d as [|d IH]; apply expand_core; intros a b e t.
 - apply e9,e10,e13,e15,cube_ten.
 - replace (S d) with (d+1) by lia. apply e9,e11,e12,e14,IH.
Qed.

Local Lemma expand_seven : forall a d e t, H t 7 [a;d;e].
Proof.
 intros a [|d] e t.
 - apply e10,e13,e15,cube_ten.
 - replace (S d) with (d+1) by lia. apply e11,e12,e14,expand_twelve.
Qed.

Local Lemma expand_six : forall a b d e t, H t 6 [a;b;d;e].
Proof. intros. apply e9,expand_seven. Qed.

Local Lemma expand_four : forall b a c d e t, H t 4 [a;b;c;d;e].
Proof.
 induction b as [b IH] using lt_wf_ind. intros a c d e t.
 destruct b as [|[|[|b]]].
 - apply e5,expand_six.
 - change (H t 4 [a;0+1;c;d;e]). apply e6,e7,e12,e14,expand_twelve.
 - change (H t 4 [a;1+1;c;d;e]). apply e6.
   change (H t 5 [a;0+1;c;d;e]). apply e8,e2,e3,expand_six.
 - replace (S(S(S b))) with ((b+1)+1+1) by lia.
   apply e6,e8,e2,e4. apply IH. lia.
Qed.

Local Lemma expand_three : forall a b c d e t, H t 3 [a;b;c;d;e].
Proof.
 intros [|a] b c d e t.
 - apply e3,expand_six.
 - replace (S a) with (a+1) by lia. apply e4,expand_four.
Qed.

Local Lemma expand_five : forall a b c d e t, H t 5 [a;b;c;d;e].
Proof.
 intros a [|b] c d e t.
 - apply e7,e12,e14,expand_twelve.
 - replace (S b) with (b+1) by lia. apply e8,e2,expand_three.
Qed.

Local Lemma expand_eighteen : forall a b d e t, H t 18 [a;b;d;e].
Proof.
 intros [|a] b d e t.
 - apply e26,expand_six.
 - replace (S a) with (a+1) by lia. apply e27,expand_four.
Qed.

Local Lemma expand_fourteen : forall a b d e t, H t 14 [a;b;d;e].
Proof.
 intros [|a] b d e t.
 - apply e20,expand_six.
 - replace (S a) with (a+1) by lia. apply e21,e24,expand_eighteen.
Qed.
Local Lemma cube_all : forall a, Good fams a -> forall t,
 tri_reaches_fire tm t (tanc fams a).
Proof.
 intros [i v] (F & EF & EL) t. change (H t i v).
 cbn [fst snd] in EF, EL.
 assert (Hi : i < 26).
 { change (i < length fams). apply nth_error_Some. rewrite EF. discriminate. }
 destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]];
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
 - apply e0,e1,e2,expand_three.
 - apply e1,e2,expand_three.
 - apply e2,expand_three.
 - apply expand_three.
 - apply expand_four.
 - apply expand_five.
 - apply expand_six.
 - apply expand_seven.
 - apply e12,e14,expand_twelve.
 - apply e13,e15,cube_ten.
 - apply e14,expand_twelve.
 - apply e15,cube_ten.
 - apply expand_twelve.
 - apply cube_ten.
 - apply expand_fourteen.
 - apply cube_eleven.
 - apply e24,expand_eighteen.
 - apply e25,cube_thirteen.
 - apply expand_eighteen.
 - apply cube_thirteen.
 - apply cube_four.
 - apply cube_five.
 - apply e34,cube_three.
 - apply cube_three.
 - apply e37,e13,e15,cube_ten.
 - apply e38,e15,cube_ten.
Qed.

Lemma cv_AST_74_0000 : coversTr (row_to_tm r_AST_74_0000).
Proof.
 apply coversTr_nqh, neverqhtr_mirror. change (NeverQuasiHaltsTr tm).
 apply (tri_reach_glue tm fams leaves families_ok (0,[0;0;0;0])).
 - eexists. split; reflexivity.
 - assert (EB : exists c, csteps tm 3000 c0 = Some c /\
     ceqb c (tanc fams (0,[0;0;0;0])) = true).
   { eexists. split; vm_compute; reflexivity. }
   destruct EB as (c & EC & EE). exists 3000.
   rewrite <- lift_c0.
   pose proof (csteps_lift tm 3000 c0 c EC) as EB.
   rewrite (ceqb_lift _ _ EE) in EB. exact EB.
 - exact cube_all.
Qed.

Definition cbtrows_AST_74 : list (list (option Trans)) := [r_AST_74_0000].
Lemma cbt_AST_74_covers : Forall coversTr (map row_to_tm cbtrows_AST_74).
Proof. constructor; [exact cv_AST_74_0000|constructor]. Qed.
