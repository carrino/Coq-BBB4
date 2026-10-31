From Coq Require Import List Arith.
From BBB24 Require Import Statement Spec CTape.
From BBB24Burn16QuaternaryCounter Require Import QuaternaryCounter.
Import ListNotations.

Example actual_entry : csteps qc_tm 3 c0=Some(qc_main[D3]).
Proof. reflexivity. Qed.
Example max_checksum : qc_head[D3;D3;D3]=S0.
Proof. reflexivity. Qed.
Example checksum_wrap : qc_head[D2;D1]=S0.
Proof. reflexivity. Qed.
Example short_increment : csteps qc_tm 2(qc_main[D0;D2])=Some(qc_main[D1;D2]).
Proof. reflexivity. Qed.
Example long_increment : csteps qc_tm 4(qc_main[D1;D2])=Some(qc_main[D2;D2]).
Proof. reflexivity. Qed.
Example carry_increment : csteps qc_tm 6(qc_main[D3;D0])=Some(qc_main[D0;D1]).
Proof. reflexivity. Qed.
Example first_overflow : csteps qc_tm 7(qc_main[D3])=Some(qc_main[D1;D2]).
Proof. reflexivity. Qed.
Example wrong_checksum_excludes_overflow :
 csteps qc_tm 7(StA,([S2;S2],S1,[]))<>Some(qc_main[D1;D2]).
Proof. discriminate. Qed.
