From Coq Require Import Arith Lia List.
From SmallBB Require Import Statement StatementTr Size.
Lemma codes23_admissible:forall xs,Admissible 2 3(machine_of_codes 2 3 xs).
Proof.
 intro xs;split.
 - intros q s tr H;unfold machine_of_codes in H.
   destruct((st_index q <? 2) && (sym_index s <? 3))%bool;[|discriminate].
   unfold nat_trans in H.
   set(v:=nth(3*st_index q+sym_index s)xs(6*2))in *.
   destruct(v <? 6*2);[|discriminate]. injection H as <-.
   unfold output_ok;cbn[t_next t_write];split.
   + pose proof(Nat.mod_upper_bound v 2 ltac:(lia)).
     change (st_index(match v mod 2 with 0=>StA|1=>StB|_=>StC end)<2). destruct(v mod 2)as[|[|k]];cbn[st_index];lia.
   + change (sym_index(match v/4 with 0=>S0|1=>S1|_=>S2 end)<3). destruct(v/4)as[|[|k]];cbn[sym_index];lia.
 - intros [] [] H;cbn in H;try(exfalso;lia);reflexivity.
Qed.
