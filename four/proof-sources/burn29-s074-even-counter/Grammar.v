(** A binary right word is accepted precisely when its1-count is even.
    Finite word length controls the forward parse; finite wall length
    controls the backward unwind. *)
From Coq Require Import List Arith Lia Bool Wf_nat.
From BBB24 Require Import Statement CTape.
From BBB24Burn29S074EvenCounter Require Import Programs.
Import ListNotations.
Fixpoint s74_good(p:bool)(w:list Sym):bool := match w with
 |[]=>negb p|S0::w=>s74_good p w|S1::w=>s74_good(negb p)w|_=>false end.
Definition s74_even w := s74_good false w=true.
Lemma s74_good_zeros : forall n p w,s74_good p(repeat S0 n++w)=s74_good p w.
Proof. induction n;intros p w;cbn[repeat app s74_good];[reflexivity|apply IHn]. Qed.
Lemma s74_good_pairs : forall n p w,s74_good p(repeat S1(2*n)++w)=s74_good p w.
Proof.
 induction n;intros p w;[reflexivity|].
 replace(2*S n)with(S(S(2*n)))by lia;cbn[repeat app s74_good].
 rewrite Bool.negb_involutive;apply IHn.
Qed.
Lemma s74_odd_split : forall w,s74_good true w=true ->
 exists n r,w=repeat S0 n++S1::r /\s74_even r.
Proof.
 induction w as[|h w IH];intro H;[discriminate|].
 destruct h;try discriminate.
 - cbn[s74_good]in H;destruct(IH H)as(n&r&E&He);exists(S n),r;cbn;rewrite E;auto.
 - exists 0,w;split;[reflexivity|exact H].
Qed.
Lemma s74_output_even : forall a ns r,s74_even r ->s74_even(s74_output a ns r).
Proof.
 intros a ns r H;unfold s74_even,s74_output in *;rewrite s74_good_zeros.
 change(s74_good false(repeat S1(2*length ns)++r)=true).
 rewrite s74_good_pairs;exact H.
Qed.
Theorem s74_walk : forall w,s74_even w ->forall a ns,
 exists d v,0<d /\s74_even v /\csteps s74_tm d(s74_front StA(s74_wall(a::ns))w)=Some(s74_cut v).
Proof.
 assert(H:forall k w,length w=k ->s74_even w ->forall a ns,
  exists d v,0<d /\s74_even v /\csteps s74_tm d(s74_front StA(s74_wall(a::ns))w)=Some(s74_cut v)).
 {induction k as[k IH]using lt_wf_ind;intros w Hlen He a ns.
  destruct w as[|h w].
  - exists(s74_cost a ns),(s74_output a ns[]);split;[apply s74_cost_pos|].
    split;[apply s74_output_even;reflexivity|apply s74_unwind].
  - destruct h.
    + exists(s74_cost a ns),(s74_output a ns w);split;[apply s74_cost_pos|].
      split;[apply s74_output_even;exact He|apply s74_unwind].
    + unfold s74_even in He;cbn[s74_good]in He.
      destruct(s74_odd_split w He)as(n&r&E&Hr);subst w.
      assert(Hlt:length r<k).
      {cbn[length]in Hlen;rewrite app_length,repeat_length in Hlen;cbn[length]in Hlen;lia. }
      destruct(IH(length r)Hlt r eq_refl Hr n(a::ns))as(d&v&Hd&Hv&Ec).
      exists(n+2+d),v;split;[lia|];split;[exact Hv|].
      rewrite csteps_add,s74_forward;exact Ec.
    + discriminate He.
    + discriminate He. }
 intros w He;exact(H(length w)w eq_refl He).
Qed.
Theorem s74_cut_return : forall w,s74_even w ->
 exists d v,0<d /\s74_even v /\csteps s74_tm d(s74_cut w)=Some(s74_cut v).
Proof.
 intros w He;destruct(s74_walk w He 0[])as(d&v&Hd&Hv&Ec).
 exists(3+d),v;split;[lia|];split;[exact Hv|].
 rewrite csteps_add,s74_boot;exact Ec.
Qed.
Theorem s74_late_cuts : forall N w,s74_even w ->
 exists k v,N<=k /\s74_even v /\csteps s74_tm k(s74_cut w)=Some(s74_cut v).
Proof.
 induction N;intros w He.
 - exists 0,w;split;[lia|];split;[exact He|reflexivity].
 - destruct(s74_cut_return w He)as(d&u&Hd&Hu&Ed).
   destruct(IHN u Hu)as(k&v&Hk&Hv&Ek).
   exists(d+k),v;split;[lia|];split;[exact Hv|].
   rewrite csteps_add,Ed;exact Ek.
Qed.
Print Assumptions s74_walk.
Print Assumptions s74_cut_return.
