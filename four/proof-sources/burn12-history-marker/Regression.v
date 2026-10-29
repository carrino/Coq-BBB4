From Coq Require Import List NArith.
From BBB24 Require Import Statement.
From BBB24.Checkers Require Import NGramHist.
From BBB24Burn12HistoryMarker Require Import HistoryMarker.
Import ListNotations.

Example untouched_blank_unmarked : hm_mark 255%N hblank=false.
Proof. reflexivity. Qed.
Example written_zero_can_be_marked : hm_mark 1%N(S0,[(StA,S0)])=true.
Proof. reflexivity. Qed.
Example symbol_without_history_unmarked : hm_mark 255%N(S3,[])=false.
Proof. reflexivity. Qed.
Example newest_writer_only : hm_mark 1%N(S0,[(StB,S0);(StA,S0)])=false.
Proof. reflexivity. Qed.
Example B_writer_bit : hm_mark 16%N(S0,[(StB,S0)])=true.
Proof. reflexivity. Qed.
Example unmarked_B_head_transports_distant_marker :
 hm_edge(hm_mark 16%N)(StB,([],hblank,[]))(StB,([],hblank,[]))=true.
Proof. reflexivity. Qed.
Example A_entry_needs_visible_marker :
 hm_edge(hm_mark 16%N)(StA,([],hblank,[]))(StB,([],hblank,[]))=false.
Proof. reflexivity. Qed.
Example consumed_only_marker_rejected :
 hm_edge(hm_mark 16%N)(StB,([],(S0,[(StB,S0)]),[]))(StB,([],hblank,[]))=false.
Proof. reflexivity. Qed.
Example marked_zero_counts_at_anchor :
 hm_initial(hm_mark 16%N)(StB,([],hblank,[(S0,[(StB,S0)])]))=true.
Proof. reflexivity. Qed.
