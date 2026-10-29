From Coq Require Import List Arith.
From BBB24 Require Import Statement Spec CTape.
From BBB24Burn17QuaternarySibling Require Import QuaternarySibling.
Import ListNotations.

Example actual_entry : csteps qs_tm 3 c0=Some(qs_main[D3]).
Proof. reflexivity. Qed.
Example max_checksum : qs_head[D3;D3;D3]=S0.
Proof. reflexivity. Qed.
Example checksum_wrap : qs_head[D2;D1]=S0.
Proof. reflexivity. Qed.
Example short_increment : csteps qs_tm 2(qs_main[D0;D2])=Some(qs_main[D1;D2]).
Proof. reflexivity. Qed.
Example long_increment : csteps qs_tm 4(qs_main[D1;D2])=Some(qs_main[D2;D2]).
Proof. reflexivity. Qed.
Example carry_increment : csteps qs_tm 6(qs_main[D3;D0])=Some(qs_main[D0;D1]).
Proof. reflexivity. Qed.
Example first_overflow : csteps qs_tm 7(qs_main[D3])=Some(qs_main[D1;D2]).
Proof. reflexivity. Qed.
Example wrong_checksum_excludes_overflow :
 csteps qs_tm 7(StA,([S2;S2],S1,[]))<>Some(qs_main[D1;D2]).
Proof. discriminate. Qed.
