From Coq Require Import List NArith.
From BBB24 Require Import Statement.
From BBB24.Checkers Require Import NGramHist.
From BBB24Burn12HistoryMarker Require Import HistoryMarker.
From BBB24Burn14RightParity Require Import RightParity.
Import ListNotations.

Example untouched_zero_unmarked : rp_mark 8%N S0=false.
Proof. reflexivity. Qed.
Example written_zero_is_physical_zero :
 rp_parity(rp_mark 8%N)[(S0,[(StB,S3)])]=false.
Proof. reflexivity. Qed.
Example two_marked_cells_cancel :
 rp_parity(rp_mark 8%N)[(S3,[]);(S3,[])]=false.
Proof. reflexivity. Qed.
Example head_is_excluded_from_right_parity :
 rp_right(rp_mark 8%N)(StB,([],(S3,[]),[]))=false.
Proof. reflexivity. Qed.
Example distant_right_marker_counts :
 rp_right(rp_mark 8%N)(StB,([],hblank,[hblank;hblank;(S3,[])]))=true.
Proof. reflexivity. Qed.
Example left_padding_preserves_right_parity :
 rp_right(rp_mark 8%N)(hm_pad 5(StB,([],hblank,[(S3,[])])))=true.
Proof. reflexivity. Qed.
Example invisible_even_B_context_rejected :
 rp_node(fun _=>false)(StB,([],hblank,[hblank;hblank]))=false.
Proof. reflexivity. Qed.
Example consumed_marked_head_flips_parity :
 rp_edge(fun _ _=>Some(mkTrans S0 DR StB))(rp_mark 8%N)
  (fun a=>st_eqb(fst a)StB)(StA,([],hblank,[]))(StB,([],(S3,[]),[]))=true.
Proof. reflexivity. Qed.
Example wrong_successor_color_rejected :
 rp_edge(fun _ _=>Some(mkTrans S0 DR StB))(rp_mark 8%N)
  (fun _=>false)(StA,([],hblank,[]))(StB,([],(S3,[]),[]))=false.
Proof. reflexivity. Qed.
Example blank_mark_rejected : forall tm bits,
 rp_check tm 1%N bits 0 0 1 4 4 4096 131072 128=false.
Proof. reflexivity. Qed.
