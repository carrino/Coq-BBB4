(** A paired carry with a growing zero spacer.  The two machines differ only
    in the direction of B3; its extra bounce changes costs, not main tapes. *)
From Coq Require Import List Arith Lia Bool.
From BBB24 Require Import Statement Spec CTape Census.
Import ListNotations.

Definition pc_tm (bounce:bool) : TM := fun q h=>Some(match q,h with
 |StA,S0=>mkTrans S1 DL StB |StA,S1=>mkTrans S2 DR StA
 |StA,S2=>mkTrans S0 DR StA |StA,S3=>mkTrans S1 DR StA
 |StB,S0=>mkTrans S3 DR StB |StB,S1=>mkTrans S3 DL StA
 |StB,S2=>mkTrans S2 DL StB
 |StB,S3=>mkTrans S2 (if bounce then DR else DL) StB end).
Definition pc_front q l r:cconf := (q,(l,chd r,ctl r)).
Definition pc_back q l r:cconf := (q,(ctl l,chd l,r)).
Fixpoint pc_pairs (x y:Sym)n := match n with
 |0=>[]|S n=>x::y::pc_pairs x y n end.
Fixpoint pc_digits(ds:list Sym) := match ds with
 |[]=>[]|d::ds=>S1::d::pc_digits ds end.
Definition pc_digit_next d := match d with
 |S0=>S1|S1=>S2|S2=>S0|S3=>S1 end.
Definition pc_zero_cost (b:bool) := if b then 5 else 3.
Definition pc_main k ds:cconf :=
 (StA,(S2::(repeat S0 k++pc_digits ds++[S1]),S0,[])).

Lemma pc_repeat_shift : forall (x:Sym) n l,
 repeat x n++x::l=x::(repeat x n++l).
Proof. intros x n;induction n;intro l;cbn;[reflexivity|now rewrite IHn]. Qed.
Lemma pc_pair_shift : forall x y n l,
 pc_pairs x y n++x::y::l=x::y::(pc_pairs x y n++l).
Proof. intros x y n;induction n;intro l;cbn;[reflexivity|now rewrite IHn]. Qed.
Lemma pc_digits_app : forall ds es,
 pc_digits(ds++es)=pc_digits ds++pc_digits es.
Proof. induction ds;intro es;cbn;[reflexivity|now rewrite IHds]. Qed.
Lemma pc_digits_repeat : forall d n,
 pc_digits(repeat d n)=pc_pairs S1 d n.
Proof. intros d n;induction n;cbn;[reflexivity|now rewrite IHn]. Qed.

Lemma pc_left_twos : forall b n l r,
 csteps(pc_tm b)n(pc_back StB(repeat S2 n++l)r)=
 Some(pc_back StB l(repeat S2 n++r)).
Proof.
 intros b n;induction n;intros l r;[reflexivity|].
 cbn[repeat app pc_back csteps cstep pc_tm ctape_move chd ctl].
 change(csteps(pc_tm b)n(pc_back StB(repeat S2 n++l)(S2::r))=
 Some(pc_back StB l(S2::(repeat S2 n++r)))).
 rewrite IHn,pc_repeat_shift;reflexivity.
Qed.
Lemma pc_one_zero : forall b l r,
 csteps(pc_tm b)(pc_zero_cost b)(pc_back StB(S0::l)(S2::r))=
 Some(pc_back StB l(S2::S2::r)).
Proof. intros b l r;destruct b;reflexivity. Qed.
Lemma pc_left_zeros : forall b n l r,
 csteps(pc_tm b)(pc_zero_cost b*n)
  (pc_back StB(repeat S0 n++l)(S2::r))=
 Some(pc_back StB l(repeat S2(S n)++r)).
Proof.
 intros b n;induction n;intros l r;[rewrite Nat.mul_0_r;reflexivity|].
 replace(pc_zero_cost b*S n)with(pc_zero_cost b+pc_zero_cost b*n)by lia.
 rewrite csteps_add.
 change(match csteps(pc_tm b)(pc_zero_cost b)
   (pc_back StB(S0::(repeat S0 n++l))(S2::r))with
 |Some c=>csteps(pc_tm b)(pc_zero_cost b*n)c|None=>None end=
 Some(pc_back StB l(repeat S2(S(S n))++r))).
 rewrite pc_one_zero,IHn,pc_repeat_shift;reflexivity.
Qed.
Lemma pc_carry_zeros : forall b n l r,
 csteps(pc_tm b)(2*n)(pc_back StB(pc_pairs S1 S0 n++l)r)=
 Some(pc_back StB l(pc_pairs S1 S3 n++r)).
Proof.
 intros b n;induction n;intros l r;[reflexivity|].
 replace(2*S n)with(2+2*n)by lia;rewrite csteps_add.
 change(csteps(pc_tm b)(2*n)
  (pc_back StB(pc_pairs S1 S0 n++l)(S1::S3::r))=
 Some(pc_back StB l(S1::S3::(pc_pairs S1 S3 n++r)))).
 rewrite IHn,pc_pair_shift;reflexivity.
Qed.
Lemma pc_right_pairs : forall b n l r,
 csteps(pc_tm b)(2*n)(pc_front StA l(pc_pairs S1 S3 n++r))=
 Some(pc_front StA(pc_pairs S1 S2 n++l)r).
Proof.
 intros b n;induction n;intros l r;[reflexivity|].
 replace(2*S n)with(2+2*n)by lia;rewrite csteps_add.
 change(csteps(pc_tm b)(2*n)
  (pc_front StA(S1::S2::l)(pc_pairs S1 S3 n++r))=
 Some(pc_front StA(S1::S2::(pc_pairs S1 S2 n++l))r)).
 rewrite IHn,pc_pair_shift;reflexivity.
Qed.
Lemma pc_right_twos : forall b n l r,
 csteps(pc_tm b)n(pc_front StA l(repeat S2 n++r))=
 Some(pc_front StA(repeat S0 n++l)r).
Proof.
 intros b n;induction n;intros l r;[reflexivity|].
 cbn[repeat app pc_front csteps cstep pc_tm ctape_move chd ctl].
 change(csteps(pc_tm b)n(pc_front StA(S0::l)(repeat S2 n++r))=
 Some(pc_front StA(S0::(repeat S0 n++l))r)).
 rewrite IHn,pc_repeat_shift;reflexivity.
Qed.
Lemma pc_nonzero_boundary : forall b d l r,d<>S0 ->
 csteps(pc_tm b)3(pc_back StB(S1::d::l)r)=
 Some(pc_front StA(S1::pc_digit_next d::l)r).
Proof. intros b d l r H;destruct d;[contradiction|reflexivity|reflexivity|reflexivity]. Qed.
Lemma pc_empty_boundary : forall b r,
 csteps(pc_tm b)7(pc_back StB[S1]r)=Some(pc_front StA[S1;S1;S1]r).
Proof. intros b r;reflexivity. Qed.

Theorem pc_nonzero_carry : forall b k n d tail,d<>S0 ->
 csteps(pc_tm b)((pc_zero_cost b+1)*k+4*n+7)
  (pc_main k(repeat S0 n++d::tail))=
 Some(pc_main(S k)(repeat S2 n++pc_digit_next d::tail)).
Proof.
 intros b k n d tail Hd.
 replace((pc_zero_cost b+1)*k+4*n+7)with
  (2+(pc_zero_cost b*k+(2*n+(3+(2*n+(S k+1))))))by lia.
 rewrite csteps_add.
 change(csteps(pc_tm b)(pc_zero_cost b*k+(2*n+(3+(2*n+(S k+1)))))
  (pc_back StB(repeat S0 k++pc_digits(repeat S0 n++d::tail)++[S1])[S2;S1])=
 Some(pc_main(S k)(repeat S2 n++pc_digit_next d::tail))).
 rewrite csteps_add,pc_left_zeros,csteps_add.
 rewrite pc_digits_app,pc_digits_repeat;cbn[pc_digits].
 rewrite <-app_assoc;cbn[app].
 rewrite pc_carry_zeros,csteps_add,pc_nonzero_boundary by exact Hd.
 rewrite csteps_add,pc_right_pairs,csteps_add,pc_right_twos.
 unfold pc_main;rewrite pc_digits_app,pc_digits_repeat;cbn[pc_digits].
 rewrite <-!app_assoc;cbn[app];reflexivity.
Qed.
Theorem pc_zero_carry : forall b k n,
 csteps(pc_tm b)((pc_zero_cost b+1)*k+4*n+11)(pc_main k(repeat S0 n))=
 Some(pc_main(S k)(repeat S2 n++[S1])).
Proof.
 intros b k n.
 replace((pc_zero_cost b+1)*k+4*n+11)with
  (2+(pc_zero_cost b*k+(2*n+(7+(2*n+(S k+1))))))by lia.
 rewrite csteps_add.
 change(csteps(pc_tm b)(pc_zero_cost b*k+(2*n+(7+(2*n+(S k+1)))))
  (pc_back StB(repeat S0 k++pc_digits(repeat S0 n)++[S1])[S2;S1])=
 Some(pc_main(S k)(repeat S2 n++[S1]))).
 rewrite csteps_add,pc_left_zeros,csteps_add,pc_digits_repeat,pc_carry_zeros.
 rewrite csteps_add,pc_empty_boundary,csteps_add,pc_right_pairs.
 rewrite csteps_add,pc_right_twos.
 unfold pc_main;rewrite pc_digits_app,pc_digits_repeat;cbn[pc_digits].
 rewrite <-!app_assoc;cbn[app];reflexivity.
Qed.

Lemma pc_decompose : forall ds,
 (exists n,ds=repeat S0 n) \/
 (exists n d tail,ds=repeat S0 n++d::tail /\ d<>S0).
Proof.
 induction ds as[|d ds IH].
 - left;exists 0;reflexivity.
 - destruct d.
   + destruct IH as[(n&E)|(n&d&tail&E&Hd)];subst ds.
     * left;exists(S n);reflexivity.
     * right;exists(S n),d,tail;split;[reflexivity|exact Hd].
   + right;exists 0,S1,ds;split;[reflexivity|discriminate].
   + right;exists 0,S2,ds;split;[reflexivity|discriminate].
   + right;exists 0,S3,ds;split;[reflexivity|discriminate].
Qed.
Theorem pc_main_next : forall b k ds,exists t ds',0<t /\
 csteps(pc_tm b)t(pc_main k ds)=Some(pc_main(S k)ds').
Proof.
 intros b k ds;destruct(pc_decompose ds)as[(n&E)|(n&d&tail&E&Hd)];subst ds.
 - exists((pc_zero_cost b+1)*k+4*n+11),(repeat S2 n++[S1]);split;[lia|apply pc_zero_carry].
 - exists((pc_zero_cost b+1)*k+4*n+7),(repeat S2 n++pc_digit_next d::tail).
   split;[lia|apply pc_nonzero_carry;exact Hd].
Qed.
Definition pc_entry_steps (b:bool) := if b then 34 else 32.
Example pc_entry : forall b,
 csteps(pc_tm b)(pc_entry_steps b)c0=Some(pc_main 2[S1]).
Proof. intro b;destruct b;reflexivity. Qed.
Lemma pc_returns : forall b N,exists t k ds,N<=t /\
 csteps(pc_tm b)t c0=Some(pc_main k ds).
Proof.
 intros b N;induction N as[|N IH].
 - exists(pc_entry_steps b),2,[S1];split;[lia|apply pc_entry].
 - destruct IH as(t&k&ds&Ht&E);destruct(pc_main_next b k ds)as(j&ds'&Hj&E').
   exists(t+j),(S k),ds';split;[lia|];rewrite csteps_add,E;exact E'.
Qed.
Theorem pc_nonhalt : forall b,NonHalt(pc_tm b).
Proof.
 intros b n Hnone;destruct(pc_returns b n)as(t&k&ds&Ht&E).
 pose proof(csteps_lift(pc_tm b)t c0(pc_main k ds)E)as Hrun;rewrite lift_c0 in Hrun.
 destruct(stepn_prefix(pc_tm b)n t InitES(lift(pc_main k ds))Ht Hrun)as(c&Ec&_);congruence.
Qed.
Theorem pc_A_recurrent : forall b N,exists t,N<=t /\ VisitsAt(pc_tm b)StA t.
Proof.
 intros b N;destruct(pc_returns b N)as(t&k&ds&Ht&E).
 exists t;split;[exact Ht|];exists(lift(pc_main k ds));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift;exact E.
Qed.
Theorem pc_B_recurrent : forall b N,exists t,N<=t /\ VisitsAt(pc_tm b)StB t.
Proof.
 intros b N;destruct(pc_returns b N)as(t&k&ds&Ht&E).
 exists(t+1);split;[lia|].
 exists(lift(pc_back StB(S2::(repeat S0 k++pc_digits ds++[S1]))[S1]));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift;rewrite csteps_add,E;reflexivity.
Qed.
Theorem pc_state_zero : forall b,QHBound 0(pc_tm b).
Proof.
 intros b q s[_ Hquiet];destruct q.
 - destruct(pc_A_recurrent b(S s))as(t&Ht&Hv);exfalso;apply(Hquiet t);[lia|exact Hv].
 - destruct(pc_B_recurrent b(S s))as(t&Ht&Hv);exfalso;apply(Hquiet t);[lia|exact Hv].
Qed.
Theorem pc_sound : forall b,NonHalt(pc_tm b) /\ QHBound 0(pc_tm b).
Proof. intro b;split;[apply pc_nonhalt|apply pc_state_zero]. Qed.
Print Assumptions pc_sound.
