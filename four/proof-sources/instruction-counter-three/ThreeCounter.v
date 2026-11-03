(** A second permanent sentinel, S3, supports the same binary counter.
The two sentinel-reading B rules exchange S1 and S3 at the base block;
positive blocks restore the sentinel. The A2 write remains S3 in both cases.
These are new proofs derived from the earlier block structure, while the
original TwosCounter source and all earlier proof reports remain unchanged. *)
From Coq Require Import List Arith Lia NArith.
From BBB24 Require Import Statement StatementTr Spec CTape Instructions Bounds Census.
From BBB24SparseTwos Require Import TwosCounter.
Import ListNotations.
Section ThreeCounter.
Variable b0:option Trans.
Theorem three_block:forall n,1<=n->forall l r,
 csteps(tc_tm b0)(work n)(at_two(twos n++S3::l)r)=
 Some(front(twos(S n)++S3::l)r).
Proof.
 intro n;induction n using lt_wf_ind;intros Hpos l r.
 assert(Htail:forall p k,1<=k->k+p<=n->forall l r,
  csteps(tc_tm b0)(walk p k)(front(twos k++S3::l)(twos p++r))=
  Some(front(twos(k+p)++S3::l)r)).
 { induction p;intros k Hk Hkn l0 r0.
   - cbn[walk twos repeat app];now rewrite Nat.add_0_r.
   - cbn[walk];rewrite csteps_add.
     change(match csteps(tc_tm b0)(work k)(at_two(twos k++S3::l0)(twos p++r0))with
       Some d=>csteps(tc_tm b0)(walk p(S k))d|None=>None end=
       Some(front(twos(k+S p)++S3::l0)r0)).
     rewrite(H k ltac:(lia)Hk l0(twos p++r0)).
     replace(k+S p)with(S k+p)by lia;apply IHp;lia. }
 assert(Hscan:forall l r,
  csteps(tc_tm b0)(walk n 0)(front(S1::l)(twos n++r))=
  Some(front(twos n++S3::l)r)).
 { intros l0 r0;destruct n as[|p];[lia|].
   change(csteps(tc_tm b0)(3+walk p 1)(front(S1::l0)(S2::(twos p++r0)))=
    Some(front(S2::(twos p++S3::l0))r0)).
   rewrite csteps_add.
   change(csteps(tc_tm b0)(walk p 1)(front(twos 1++S3::l0)(twos p++r0))=
    Some(front(twos(S p)++S3::l0)r0)).
   replace(S p)with(1+p)by lia;apply Htail;lia. }
 replace(work n)with(1+(n+(1+(walk n 0+1))))by(rewrite work_walk;lia).
 rewrite csteps_add.
 change(csteps(tc_tm b0)(n+(1+(walk n 0+1)))(back(twos n++S3::l)(S3::r))=
  Some(front(twos(S n)++S3::l)r)).
 rewrite csteps_add,(left_twos b0),csteps_add.
 change(csteps(tc_tm b0)(walk n 0+1)(front(S1::l)(twos n++S3::r))=
  Some(front(twos(S n)++S3::l)r)).
 rewrite csteps_add,Hscan;reflexivity.
Qed.

Lemma sweep_three_tail:forall p k,1<=k->forall l r,
 csteps(tc_tm b0)(walk p k)(front(twos k++S3::l)(twos p++r))=
 Some(front(twos(k+p)++S3::l)r).
Proof.
 induction p;intros k Hk l r.
 - cbn[walk twos repeat app];now rewrite Nat.add_0_r.
 - cbn[walk];rewrite csteps_add.
   change(match csteps(tc_tm b0)(work k)(at_two(twos k++S3::l)(twos p++r))with
       Some d=>csteps(tc_tm b0)(walk p(S k))d|None=>None end=
       Some(front(twos(k+S p)++S3::l)r)).
   rewrite(three_block k Hk l(twos p++r)).
   replace(k+S p)with(S k+p)by lia;apply IHp;lia.
Qed.
Theorem scan_threes:forall n,1<=n->forall l r,
 csteps(tc_tm b0)(walk n 0)(front(S1::l)(twos n++r))=
 Some(front(twos n++S3::l)r).
Proof.
 intros[|p]Hpos l r;[lia|].
 change(csteps(tc_tm b0)(3+walk p 1)(front(S1::l)(S2::(twos p++r)))=
    Some(front(S2::(twos p++S3::l))r)).
 rewrite csteps_add.
 change(csteps(tc_tm b0)(walk p 1)(front(twos 1++S3::l)(twos p++r))=
    Some(front(twos(S p)++S3::l)r)).
 replace(S p)with(1+p)by lia;apply sweep_three_tail;lia.
Qed.


Variable context:list Sym.
Definition main3 n h:cconf:=(StA,(twos n++S3::context,h,[])).
Lemma start_one:forall n,
 csteps(tc_tm b0)(n+2)(main3 n S1)=Some(front(S1::context)(twos n++[S2])).
Proof.
 intro n;replace(n+2)with(1+(n+1))by lia;rewrite csteps_add.
 change(csteps(tc_tm b0)(n+1)(back(twos n++S3::context)[S2])=Some(front(S1::context)(twos n++[S2]))).
 rewrite csteps_add,(left_twos b0);reflexivity.
Qed.
Lemma start_zero:forall n,
 csteps(tc_tm b0)(n+2)(main3 n S0)=Some(front(S1::context)(twos n++[S1])).
Proof.
 intro n;replace(n+2)with(1+(n+1))by lia;rewrite csteps_add.
 change(csteps(tc_tm b0)(n+1)(back(twos n++S3::context)[S1])=Some(front(S1::context)(twos n++[S1]))).
 rewrite csteps_add,(left_twos b0);reflexivity.
Qed.
Definition phase_one n:=n+2+walk(S n)0.
Definition phase_zero n:=n+2+walk n 0.
Theorem one_phase:forall n,
 csteps(tc_tm b0)(phase_one n)(main3 n S1)=Some(main3(S n)S0).
Proof.
 intro n;unfold phase_one;rewrite csteps_add,start_one,two_shift.
 change(csteps(tc_tm b0)(walk(S n)0)(front(S1::context)(twos(S n)++[]))=Some(main3(S n)S0)).
 rewrite scan_threes by lia;reflexivity.
Qed.
Theorem zero_phase:forall n,
 csteps(tc_tm b0)(phase_zero(S n))(main3(S n)S0)=Some(main3(S n)S1).
Proof.
 intro n;unfold phase_zero;rewrite csteps_add,start_zero.
 rewrite scan_threes by lia;reflexivity.
Qed.
Definition gap n:=phase_one n+phase_zero(S n).
Lemma gap_formula:forall n,gap n+5=16*2^n.
Proof.
 intro n;pose proof(work_walk n);pose proof(work_walk(S n));pose proof(work_formula n).
 unfold gap,phase_one,phase_zero;rewrite walk_snoc;cbn[work Nat.add]in *;lia.
Qed.
Theorem main_next:forall n,
 csteps(tc_tm b0)(gap n)(main3 n S1)=Some(main3(S n)S1).
Proof. intro n;unfold gap;rewrite csteps_add,one_phase;apply zero_phase. Qed.

Lemma returns_from3:forall N,exists k n,1<=n/\N<=k/\
 csteps(tc_tm b0)k(main3 0 S1)=Some(main3 n S1).
Proof.
 intro N;induction N as[|N IH].
 - exists(gap 0),1;repeat split;try lia;apply main_next.
 - destruct IH as(k&n&Hn&Hk&E);exists(k+gap n),(S n);repeat split;try lia.
   + unfold gap,phase_one,phase_zero;lia.
   + rewrite csteps_add,E;apply main_next.
Qed.
Lemma every_from3:forall n,exists d,csteps(tc_tm b0)n(main3 0 S1)=Some d.
Proof.
 intro n;destruct(returns_from3 n)as(k&j&Hj&Hk&E).
 destruct(csteps_prefix(tc_tm b0)n k(main3 0 S1)(main3 j S1)Hk E)as(d&Ed&_).
 exists d;exact Ed.
Qed.
Lemma prefix_hits3:forall n,1<=n->forall tg,tg<>(StB,S0)->exists j d,
 csteps(tc_tm b0)j(main3 n S1)=Some d/\cinstr d=tg.
Proof.
 intros n Hn[q h]Hnot;destruct q,h.
 - exists(phase_one n),(main3(S n)S0);split;[apply one_phase|reflexivity].
 - exists 0;eexists;split;reflexivity.
 - exists(n+2);rewrite start_one;destruct n;[lia|];eexists;split;reflexivity.
 - exists(n+2+2);rewrite csteps_add,start_one;destruct n;[lia|];eexists;split;reflexivity.
 - contradiction.
 - exists(n+2+1);rewrite csteps_add,start_one;destruct n;[lia|];eexists;split;reflexivity.
 - exists 1;destruct n;[lia|];eexists;split;reflexivity.
 - exists(1+n);rewrite csteps_add.
   change(exists d,csteps(tc_tm b0)n(back(twos n++S3::context)[S2])=Some d/\cinstr d=(StB,S3)).
   rewrite (left_twos b0);eexists;split;reflexivity.
Qed.


End ThreeCounter.
