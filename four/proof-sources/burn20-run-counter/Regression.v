From Coq Require Import List Arith Bool.
From BBB24 Require Import Statement Spec CTape.
From BBB24Burn20RunCounter Require Import RunCounter.
Import ListNotations.
Example actual_blank_entry : csteps rc_tm 3 c0=Some(rc_main[][]).
Proof. reflexivity. Qed.
Example empty_bit_word_overflow : csteps rc_tm 7(rc_main[][])=Some(rc_main[false][]).
Proof. reflexivity. Qed.
Example first_false_direct : csteps rc_tm 22(rc_main[false;true][S2;S3])=
 Some(rc_main[true;true][S2;S3]).
Proof. reflexivity. Qed.
Example longer_first_false : csteps rc_tm 70(rc_main[true;true;false;false;true][])=
 Some(rc_main[true;true;true;false;true][]).
Proof. reflexivity. Qed.
Example overflow_with_blank_padding : csteps rc_tm 19(rc_main[true;true;true][S0;S0])=
 Some(rc_main[false;false;false;false][S0]).
Proof. reflexivity. Qed.
Example universal_scan_context : csteps rc_tm 15(rc_front StA[S3;S1;S2][S2;S2;S2;S0;S3])=
 Some(rc_front StA[S3;S3;S3;S3;S1;S2][S0;S3]).
Proof. reflexivity. Qed.
Example missing_three_support_breaks_scan :
 csteps rc_tm 5(rc_front StA[S1][S2;S0])<>Some(rc_front StA[S3;S3][S0]).
Proof. discriminate. Qed.
Example missing_outer_three_breaks_pair_grammar :
 csteps rc_tm 5(StA,([S3],S0,[]))<>Some(rc_main[false][]).
Proof. discriminate. Qed.
Example nonblank_tail_invalidates_overflow :
 csteps rc_tm 7(rc_main[][S1])<>Some(rc_main[false][]).
Proof. discriminate. Qed.
Example malformed_false_pair_breaks_macro :
 csteps rc_tm 22(StA,([S3;S1;S3;S3],S0,[]))<>Some(rc_main[true][]).
Proof. discriminate. Qed.
