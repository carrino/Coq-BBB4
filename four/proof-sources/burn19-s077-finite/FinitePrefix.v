(** Two compact finite computations, each using binary input counts.
    The ending tape is existential and is not supplied by a native trace. *)
From Coq Require Import List Arith NArith Lia.
From BBB24 Require Import Statement Spec CTape Census.
From BBB24Burn19S077Finite Require Import FiniteEscape.
Import ListNotations.
Lemma s77_escape_checked : s77_endcheck 2501552%N=true.
Proof. vm_compute;reflexivity. Qed.
Lemma s77_last_A_checked : s77_visit_Acheck 2501551%N=true.
Proof. vm_compute;reflexivity. Qed.
Opaque s77_count.
Theorem s77_B_forever : forall k,s77_count 2501552%N<=k ->VisitsAt s77_tm StB k.
Proof. apply s77_B_forever_from_check;exact s77_escape_checked. Qed.
Theorem s77_A_quiet : QuietFrom s77_tm StA(s77_count 2501552%N).
Proof. apply s77_A_quiet_from_check;exact s77_escape_checked. Qed.
Theorem s77_last_A : QuietAfter s77_tm StA(s77_count 2501551%N).
Proof.
 split;[apply s77_visit_Acheck_sound;exact s77_last_A_checked|].
 intros k Hk;apply s77_A_quiet;rewrite s77_escape_successor;lia.
Qed.
Theorem s77_exact_bound : QHBound(s77_count 2501552%N)s77_tm.
Proof. apply s77_bound_from_check;exact s77_escape_checked. Qed.
Theorem s77_attains : AttainsSt s77_tm(s77_count 2501552%N).
Proof. exists StA,(s77_count 2501551%N);split;[exact s77_last_A|symmetry;exact s77_escape_successor]. Qed.
Theorem s77_sound : NonHalt s77_tm /\QHBound(s77_count 4194304%N)s77_tm.
Proof.
 split;[exact s77_nonhalt|].
 intros q s H;pose proof(s77_exact_bound q s H)as Hb.
 eapply Nat.le_trans;[exact Hb|apply s77_count_le;easy].
Qed.
Theorem s77_quasihalts : QuasiHaltsSt s77_tm.
Proof.
 exists StA;split.
 - exists 0,InitES;split;reflexivity.
 - exists(s77_count 2501552%N);exact s77_A_quiet.
Qed.
Theorem s77_below_champion : QHBound score s77_tm.
Proof.
 intros q s H;pose proof(proj2 s77_sound q s H)as Hb.
 eapply Nat.le_trans;[exact Hb|rewrite s77_score_count;apply s77_count_le;unfold scoreN;vm_compute;discriminate].
Qed.
Print Assumptions s77_sound.
Print Assumptions s77_attains.
