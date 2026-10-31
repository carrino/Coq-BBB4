From Coq Require Import List Arith Bool.
From BBB24 Require Import Statement Spec CTape.
From BBB24Burn20RunSibling Require Import RunSibling.
Import ListNotations.
Example actual_blank_entry : csteps rs_tm 3 c0=Some(rs_main[][]).
Proof. reflexivity. Qed.
Example empty_bit_word_overflow : csteps rs_tm 7(rs_main[][])=Some(rs_main[false][]).
Proof. reflexivity. Qed.
Example first_false_direct : csteps rs_tm 16(rs_main[false;true][S2;S3])=
 Some(rs_main[true;true][S2;S3]).
Proof. reflexivity. Qed.
Example longer_first_false : csteps rs_tm 48(rs_main[true;true;false;false;true][])=
 Some(rs_main[true;true;true;false;true][]).
Proof. reflexivity. Qed.
Example overflow_with_blank_padding : csteps rs_tm 19(rs_main[true;true;true][S0;S0])=
 Some(rs_main[false;false;false;false][S0]).
Proof. reflexivity. Qed.
Example universal_scan_context : csteps rs_tm 9(rs_front StA[S3;S1;S2][S2;S2;S2;S0;S3])=
 Some(rs_front StA[S3;S3;S3;S3;S1;S2][S0;S3]).
Proof. reflexivity. Qed.
Example missing_three_support_breaks_scan :
 csteps rs_tm 3(rs_front StA[S1][S2;S0])<>Some(rs_front StA[S3;S3][S0]).
Proof. discriminate. Qed.
Example missing_outer_three_breaks_pair_grammar :
 csteps rs_tm 5(StA,([S3],S0,[]))<>Some(rs_main[false][]).
Proof. discriminate. Qed.
Example nonblank_tail_invalidates_overflow :
 csteps rs_tm 7(rs_main[][S1])<>Some(rs_main[false][]).
Proof. discriminate. Qed.
Example malformed_false_pair_breaks_macro :
 csteps rs_tm 16(StA,([S3;S1;S3;S3],S0,[]))<>Some(rs_main[true][]).
Proof. discriminate. Qed.

Example frozen_A3_enters_B : rs_tm StA S3=Some(mkTrans S3 DR StB).
Proof. reflexivity. Qed.
Example rejected_3RA_table_is_distinct : rs_tm StA S3<>Some(mkTrans S3 DR StA).
Proof. discriminate. Qed.
