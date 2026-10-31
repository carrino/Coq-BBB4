From Coq Require Import List Arith.
From BBB24 Require Import Statement CTape.
From BBB24Burn36S059Counter Require Import BinaryReturns.
Import ListNotations.
Example actual_blank_main : csteps s59_tm 3 c0=Some(s59_main 0[]).
Proof. exact s59_blank_entry. Qed.
Example earlier_partial_entry : csteps s59_tm 18 c0=Some(StA,([S3;S3;S0;S3;S2],S0,[])).
Proof. reflexivity. Qed.
Example empty_end_increments : csteps s59_tm 72(s59_main 0[])=Some(s59_main 1 s59_O).
Proof. exact(s59_increment 0 0[][]s59_stop_empty). Qed.
Example uncoupled_zero_increments :
 csteps s59_tm 72(s59_main 0 s59_Z)=Some(s59_main 1 s59_O).
Proof. exact(s59_increment 0 0(s59_Z++[])[](s59_stop_zero[])). Qed.
Example two_carries :
 csteps s59_tm 224(s59_main 2(s59_pow s59_O 2++s59_Z++s59_O))=
 Some(s59_main 3(s59_pow s59_Z 2++s59_O++s59_O)).
Proof. exact(s59_increment 2 2(s59_Z++s59_O)s59_O(s59_stop_zero s59_O)). Qed.
Example three_ones_overflow :
 csteps s59_tm 172(s59_main 1(s59_pow s59_O 3))=
 Some(s59_main 2(s59_pow s59_Z 3++s59_O)).
Proof.
 pose proof(s59_increment 1 3[][]s59_stop_empty)as H.
 now rewrite !app_nil_r in H.
Qed.
Definition s59_good s:=s=S0 \/s=S2.
Definition s59_guard l h r:=Forall s59_good l /\(h=S2 \/(h=S0 /\chd r=S2)).
Lemma s59_guard_step : forall l h r,s59_guard l h r ->
 exists l' h' r',cstep s59_tm(StB,(l,h,r))=Some(StB,(l',h',r')) /\s59_guard l' h' r'.
Proof.
 intros l h r[Hl[Hh|[Hh Hr]]];subst h.
 - destruct l as[|x l].
   + exists[],S0,(S2::r);split;[reflexivity|];split;[constructor|right;auto].
   + inversion Hl as[|x' l' Hx Htail];subst.
     exists l,x,(S2::r);split;[reflexivity|];split;[exact Htail|].
     destruct Hx as[Hx|Hx];subst x;[right;auto|left;reflexivity].
 - destruct r as[|x r];[discriminate|];cbn[chd]in Hr;subst x.
   exists(S2::l),S2,r;split;[reflexivity|];split.
   + constructor;[right;reflexivity|exact Hl].
   + left;reflexivity.
Qed.
Theorem s59_guard_forever_B : forall n l h r,s59_guard l h r ->
 exists l' h' r',csteps s59_tm n(StB,(l,h,r))=Some(StB,(l',h',r')) /\s59_guard l' h' r'.
Proof.
 induction n;intros l h r Hg.
 - exists l,h,r;auto.
 - destruct(s59_guard_step l h r Hg)as(l1&h1&r1&E&Hg1).
   destruct(IHn l1 h1 r1 Hg1)as(l'&h'&r'&E'&Hg').
   exists l',h',r';split;[change(match cstep s59_tm(StB,(l,h,r))with Some c=>csteps s59_tm n c|None=>None end=Some(StB,(l',h',r')));now rewrite E|exact Hg'].
Qed.
Example unsafe_empty_context : csteps s59_tm 5(StA,([S3;S3],S0,[]))=
 Some(StB,([S0],S0,[S2])).
Proof. reflexivity. Qed.
Example unsafe_distant_three : csteps s59_tm 17(StA,([S3;S3;S3;S0;S3;S3],S0,[]))=
 Some(StB,([S0],S0,[S2;S3;S2;S2;S2])).
Proof. reflexivity. Qed.
Example empty_guard : s59_guard[S0]S0[S2].
Proof. split;[constructor;[left;reflexivity|constructor]|right;auto]. Qed.
Example distant_three_guard : s59_guard[S0]S0[S2;S3;S2;S2;S2].
Proof. split;[constructor;[left;reflexivity|constructor]|right;auto]. Qed.
Example unsafe_empty_not_main : forall n w,s59_main n w<>(StA,([S3;S3],S0,[])).
Proof. intros[|n]w;discriminate. Qed.
Example unsafe_three_not_main : forall n w,s59_main n w<>(StA,([S3;S3;S3;S0;S3;S3],S0,[])).
Proof. intros[|[|n]]w;discriminate. Qed.
Print Assumptions s59_sound.
