From Coq Require Import List Arith.
From BBB24 Require Import Statement Spec CTape.
From BBB24Burn17ZeroMarker Require Import ZeroMarker.
Import ListNotations.

Example actual_entry : csteps zm_tm 3 c0=Some(zm_main[S2;S2]).
Proof. reflexivity. Qed.
Example first_outer_carry : csteps zm_tm 6(zm_main[S2;S2])=Some(zm_main[S1;S0;S2]).
Proof. reflexivity. Qed.
Example short_increment : csteps zm_tm 2(zm_main[S1;S0;S2])=Some(zm_main[S2;S0;S2]).
Proof. reflexivity. Qed.
Example marker_reaches_boundary : csteps zm_tm 4(zm_main[S2;S0;S2])=Some(zm_main[S0;S2;S2]).
Proof. reflexivity. Qed.
Example safe_marker_expansion : csteps zm_tm 3(zm_main[S0;S2;S2])=Some(zm_main[S2;S2;S2;S2]).
Proof. reflexivity. Qed.
Example marker_shift_arbitrary_context :
 csteps zm_tm 8(StA,([S2;S2;S2;S0;S1;S3],S1,[S2;S1]))=
 Some(StA,([S1;S1;S0;S2;S1;S3],S2,[S2;S1])).
Proof. reflexivity. Qed.
Example checksum_alone_allows_escape : zm_head[S0;S2]=S2 /\
 csteps zm_tm 3(StA,([S0;S2],S2,[]))=Some(StB,([S2;S2;S2],S0,[])).
Proof. split;reflexivity. Qed.
Example parity_excludes_escape_seed : ~zm_word[S0;S2].
Proof. intro H;pose proof(zm_marker_at_boundary_safe 1 H)as E;discriminate. Qed.
