(** The instruction maximum with the additional first-transition restriction
    A0 = 1RB. This restricted maximum differs from the unrestricted value 8. *)
From Coq Require Import Arith Lia List.
From SmallBB Require Import Statement StatementTr CTape Size Bounds Spec
 Witness Census Census22 Mirror.
Import ListNotations.

Definition normalized22 (tm:TM):Prop:=
 Admissible 2 2 tm /\ tm StA S0=Some(mkTrans S1 DR StB).
Definition normalized22_partial:=update empty StA S0(nat_trans 2 7).
Definition normalized22_certificate:=match certificate22 with
 |Branch _ children=>nth 7 children Invalid|_=>Invalid end.
Lemma normalized22_checked:
 verify 2 2 6 7 4 normalized22_partial normalized22_certificate=true.
Proof. native_compute;reflexivity. Qed.
Theorem normalized22_upper:forall tm,normalized22 tm->QHBoundTr 7 tm.
Proof.
 intros tm[Had Hfirst].
 assert(Hle:TM_le normalized22_partial tm).
 { intros q s;destruct q,s;try(left;reflexivity).
   right;exact Hfirst. }
 exact(proj2(verify_sound 2 2 6 7 ltac:(left;auto) 4 normalized22_partial
 normalized22_certificate normalized22_checked tm Had Hle)).
Qed.

(** 1RB1LA_0LA1RA *)
Definition normalized22_champion:TM:=machine_of_codes 2 2 [7;4;0;6].
Lemma normalized22_champion_ok:normalized22 normalized22_champion.
Proof.
 split;[split|reflexivity].
 - intros [] [] tr H;
   cbv[normalized22_champion machine_of_codes nat_trans st_index sym_index nth]in H;
   try discriminate;injection H as <-;unfold output_ok;simpl;lia.
 - intros [] [] H;simpl in H;try(exfalso;lia);reflexivity.
Qed.
Lemma normalized22_champion_quiet:QuietAfterTr normalized22_champion(StB,S0)6.
Proof.
 apply mirror_quiet_tr.
 apply(tr_witness_sound(mirror_tm normalized22_champion)7 5 0(StB,S0)6).
 vm_compute;reflexivity.
Qed.
Theorem BBB22_normalized_instruction_value:
 (exists tm,normalized22 tm /\ AttainsTr tm 7) /\
 (forall tm B,normalized22 tm->AttainsTr tm B->B<=7).
Proof.
 split.
 - exists normalized22_champion;split;[exact normalized22_champion_ok|].
   exists(StB,S0),6;split;[exact normalized22_champion_quiet|reflexivity].
 - intros tm B H(t&s&Hq&<-);exact(normalized22_upper tm H t s Hq).
Qed.
Print Assumptions BBB22_normalized_instruction_value.
