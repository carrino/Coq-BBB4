(** Binary transport and a fuel-bounded accelerated checker. The checker is
    sound for every successful input, independently of the blank-orbit test. *)
From Coq Require Import List Arith Lia Bool NArith.
From BBB24 Require Import Statement Spec CTape Census.
From BBB24Burn33S064 Require Import Core.
Import ListNotations.
Definition sk_count := N.to_nat.
Definition sk_bitN(e:bool):N := if e then 1%N else 0%N.
Definition sk_PN b c d e t := sk_P(sk_count b)(sk_count c)(sk_count d)e t.
Definition sk_MN a b e := sk_main(sk_count a)(sk_count b)e.
Definition sk_DN n e := sk_drift(repeat S1(sk_count n)++sk_tail e).
Lemma sk_count_add : forall a b,sk_count(a+b)=sk_count a+sk_count b.
Proof. exact N2Nat.inj_add. Qed.
Lemma sk_count_le : forall a b,(a<=b)%N ->sk_count a<=sk_count b.
Proof. intros a b H;unfold sk_count;apply Nat.compare_le_iff;rewrite <-N2Nat.inj_compare;exact H. Qed.
Lemma sk_count_pos : forall a,a<>0%N ->0<sk_count a.
Proof.
 intros a H;assert(1<=a)%N by lia.
 pose proof(sk_count_le 1 a H0);exact H1.
Qed.
Ltac sk_binary := unfold sk_count;
 repeat first[rewrite N2Nat.inj_add|rewrite N2Nat.inj_mul|rewrite N2Nat.inj_sub].
Lemma sk_compN : forall a b c d e,
 csteps sk_tm(sk_count a)c=Some d ->csteps sk_tm(sk_count b)d=Some e ->
 csteps sk_tm(sk_count(a+b))c=Some e.
Proof. intros a b c d e H H';rewrite sk_count_add,csteps_add,H;exact H'. Qed.
Lemma sk_batchN : forall b c d e t z,(z<=b)%N ->(z<=d)%N ->
 csteps sk_tm(sk_count(2*z*z+(2*c+1)*z)) (sk_PN b c d e t)=
 Some(sk_PN(b-z)(c+2*z)(d-z)e t).
Proof.
 intros b c d e t z Hb Hd.
 pose proof(sk_count_le z b Hb);pose proof(sk_count_le z d Hd).
 unfold sk_PN;sk_binary;fold sk_count in *.
 replace(sk_count b)with((sk_count b-sk_count z)+sk_count z)at 1 by lia.
 replace(sk_count d)with((sk_count d-sk_count z)+sk_count z)at 1 by lia.
 apply sk_batch.
Qed.
Lemma sk_resetN : forall c d e t,c<>0%N ->d<>0%N ->
 csteps sk_tm(sk_count(c+5))(sk_PN 0 c d e t)=
 Some(sk_PN(c-1+sk_bitN e)2(d-1)(negb e)t).
Proof.
 intros c d e t Hc Hd;pose proof(sk_count_pos c Hc);pose proof(sk_count_pos d Hd).
 unfold sk_PN,sk_bitN;destruct e;sk_binary;fold sk_count in *.
 - change(csteps sk_tm(sk_count c+5)(sk_P 0(sk_count c)(sk_count d)true t)=
   Some(sk_P(sk_count c-1+1)2(sk_count d-1)false t)).
   destruct(sk_count c)as[|nc];[lia|];destruct(sk_count d)as[|nd];[lia|].
   replace(S nc+5)with(nc+6)by lia.
   replace(S nc-1+1)with(S nc)by lia;replace(S nd-1)with nd by lia.
   apply sk_reset_true.
 - change(csteps sk_tm(sk_count c+5)(sk_P 0(sk_count c)(sk_count d)false t)=
   Some(sk_P(sk_count c-1+0)2(sk_count d-1)true t)).
   destruct(sk_count c)as[|nc];[lia|];destruct(sk_count d)as[|nd];[lia|].
   replace(S nc+5)with(nc+6)by lia.
   replace(S nc-1+0)with nc by lia;replace(S nd-1)with nd by lia.
   apply sk_reset_false.
Qed.
Lemma sk_startN : forall a b e,
 csteps sk_tm(sk_count(1+a))(sk_MN a b e)=Some(sk_PN b 0 a e S1).
Proof. intros a b e;unfold sk_MN,sk_PN;sk_binary;apply sk_start. Qed.
Lemma sk_end1_emptyN : forall c e,
 csteps sk_tm(sk_count(c+2))(sk_PN 0 c 0 e S1)=
 Some(sk_MN 0(c+1+sk_bitN e)(negb e)).
Proof. intros c [];unfold sk_MN,sk_PN,sk_bitN;sk_binary;apply sk_end1_empty. Qed.
Lemma sk_end1_zeroN : forall b e,b<>0%N ->
 csteps sk_tm(sk_count 4)(sk_PN b 0 0 e S1)=Some(sk_MN 1 b e).
Proof.
 intros b e Hb;pose proof(sk_count_pos b Hb);unfold sk_MN,sk_PN.
 destruct(sk_count b)as[|n];[lia|apply sk_end1_zero].
Qed.
Lemma sk_end1_turnN : forall b c e,b<>0%N ->c<>0%N ->
 csteps sk_tm(sk_count(2*c+5))(sk_PN b c 0 e S1)=
 Some(sk_PN(b-1)2(c-1)e S2).
Proof.
 intros b c e Hb Hc;pose proof(sk_count_pos b Hb);pose proof(sk_count_pos c Hc).
 unfold sk_PN;sk_binary;fold sk_count in *.
 change(csteps sk_tm(2*sk_count c+5)(sk_P(sk_count b)(sk_count c)0 e S1)=
 Some(sk_P(sk_count b-1)2(sk_count c-1)e S2)).
 destruct(sk_count b)as[|nb];[lia|];destruct(sk_count c)as[|nc];[lia|].
 replace(2*S nc+5)with(2*nc+7)by lia.
 replace(S nb-1)with nb by lia;replace(S nc-1)with nc by lia.
 apply sk_end1_turn.
Qed.
Lemma sk_end2_nonemptyN : forall b c e,b<>0%N ->
 csteps sk_tm(sk_count(c+2))(sk_PN b c 0 e S2)=Some(sk_MN(c+1)b e).
Proof.
 intros b c e Hb;pose proof(sk_count_pos b Hb).
 unfold sk_MN,sk_PN;sk_binary;fold sk_count in *.
 change(csteps sk_tm(sk_count c+2)(sk_P(sk_count b)(sk_count c)0 e S2)=
 Some(sk_main(sk_count c+1)(sk_count b)e)).
 replace(sk_count b)with(S(sk_count b-1))by lia.
 replace(sk_count c+1)with(S(sk_count c))by lia;apply sk_end2_nonempty.
Qed.
Lemma sk_end2_emptyN : forall c e,
 csteps sk_tm(sk_count(c+2))(sk_PN 0 c 0 e S2)=
 Some(sk_DN(c+1+sk_bitN e)(negb e)).
Proof. intros c [];unfold sk_DN,sk_PN,sk_bitN;sk_binary;apply sk_end2_empty. Qed.

Record sk_pr := sk_PR { sk_pb:N; sk_pc:N; sk_pe:bool; sk_pt:N }.
Definition sk_charge(k:N)(r:option sk_pr):option sk_pr :=
 match r with None=>None |Some(sk_PR b c e t)=>Some(sk_PR b c e(k+t)%N)end.
Fixpoint sk_phase(fuel:nat)(b c d:N)(e:bool):option sk_pr :=
 if (d=?0)%N then Some(sk_PR b c e 0)else
 match fuel with
 |0=>None
 |S f=>if (b=?0)%N then
   if(c=?0)%N then None else
   sk_charge(c+5)%N(sk_phase f(c-1+sk_bitN e)%N 2(d-1)%N(negb e))
  else let z:=N.min b d in
   sk_charge(2*z*z+(2*c+1)*z)%N(sk_phase f(b-z)%N(c+2*z)%N(d-z)%N e)
 end.
Theorem sk_phase_sound : forall fuel b c d e b' c' e' t h,
 sk_phase fuel b c d e=Some(sk_PR b' c' e' t) ->
 csteps sk_tm(sk_count t)(sk_PN b c d e h)=Some(sk_PN b' c' 0 e' h).
Proof.
 induction fuel as[|fuel IH];intros b c d e b' c' e' t h H;
 cbn[sk_phase]in H;destruct(d=?0)%N eqn:Ed.
 - apply N.eqb_eq in Ed;subst d;injection H as <- <- <- <-;reflexivity.
 - discriminate.
 - apply N.eqb_eq in Ed;subst d;injection H as <- <- <- <-;reflexivity.
 - apply N.eqb_neq in Ed.
   destruct(b=?0)%N eqn:Eb.
   + apply N.eqb_eq in Eb;subst b;destruct(c=?0)%N eqn:Ec;[discriminate|].
     apply N.eqb_neq in Ec.
     destruct(sk_phase fuel(c-1+sk_bitN e)%N 2(d-1)%N(negb e))as[[bb cc ee u]|]eqn:E;[|discriminate].
     cbn[sk_charge]in H;injection H as <- <- <- <-.
     eapply sk_compN;[apply sk_resetN;assumption|].
     eapply IH;exact E.
   + destruct(sk_phase fuel(b-N.min b d)%N(c+2*N.min b d)%N(d-N.min b d)%N e)
     as[[bb cc ee u]|]eqn:E;[|discriminate].
     cbn[sk_charge]in H;injection H as <- <- <- <-.
     eapply sk_compN;[apply sk_batchN;[apply N.le_min_l|apply N.le_min_r]|].
     eapply IH;exact E.
Qed.
Inductive sk_out :=
 |sk_Next(a b:N)(e:bool)(cost:N)
 |sk_Done(n:N)(e:bool)(cost:N).
Definition sk_denote(o:sk_out):cconf :=
 match o with sk_Next a b e _=>sk_MN a b e |sk_Done n e _=>sk_DN n e end.
Definition sk_cost(o:sk_out):N := match o with sk_Next _ _ _ t|sk_Done _ _ t=>t end.
Definition sk_next(fuel:nat)(a b:N)(e:bool):option sk_out :=
 match sk_phase fuel b 0 a e with
 |None=>None
 |Some(sk_PR b c e t)=>
  let base:=(1+a+t)%N in
  if(b=?0)%N then Some(sk_Next 0(c+1+sk_bitN e)%N(negb e)(base+(c+2))%N)
  else if(c=?0)%N then Some(sk_Next 1 b e(base+4)%N)
  else match sk_phase fuel(b-1)%N 2(c-1)%N e with
   |None=>None
   |Some(sk_PR bb cc ee u)=>
    let total:=(base+(2*c+5)+u+(cc+2))%N in
    if(bb=?0)%N then Some(sk_Done(cc+1+sk_bitN ee)%N(negb ee)total)
    else Some(sk_Next(cc+1)%N bb ee total)
   end
 end.
Theorem sk_next_sound : forall fuel a b e o,
 sk_next fuel a b e=Some o ->
 csteps sk_tm(sk_count(sk_cost o))(sk_MN a b e)=Some(sk_denote o).
Proof.
 intros fuel a b e o H;unfold sk_next in H.
 destruct(sk_phase fuel b 0 a e)as[[bb c ee t]|]eqn:E;[|discriminate].
 pose proof(sk_phase_sound fuel b 0 a e bb c ee t S1 E)as Ep.
 pose proof(sk_compN _ _ _ _ _(sk_startN a b e)Ep)as Ebase.
 destruct(bb=?0)%N eqn:Eb.
 - apply N.eqb_eq in Eb;subst bb;injection H as <-.
   cbn[sk_cost sk_denote];eapply sk_compN;[exact Ebase|apply sk_end1_emptyN].
 - apply N.eqb_neq in Eb;destruct(c=?0)%N eqn:Ec.
   + apply N.eqb_eq in Ec;subst c;injection H as <-.
     cbn[sk_cost sk_denote];eapply sk_compN;[exact Ebase|apply sk_end1_zeroN;exact Eb].
   + apply N.eqb_neq in Ec.
     destruct(sk_phase fuel(bb-1)%N 2(c-1)%N ee)as[[bbb cc eee u]|]eqn:E2;[|discriminate].
     pose proof(sk_compN _ _ _ _ _ Ebase(sk_end1_turnN bb c ee Eb Ec))as Eturn.
     pose proof(sk_phase_sound fuel(bb-1)%N 2(c-1)%N ee bbb cc eee u S2 E2)as Ep2.
     pose proof(sk_compN _ _ _ _ _ Eturn Ep2)as Ebase2.
     destruct(bbb=?0)%N eqn:Eb2;injection H as <-;cbn[sk_cost sk_denote].
     * apply N.eqb_eq in Eb2;subst bbb.
       eapply sk_compN;[exact Ebase2|apply sk_end2_emptyN].
     * apply N.eqb_neq in Eb2.
       eapply sk_compN;[exact Ebase2|apply sk_end2_nonemptyN;exact Eb2].
Qed.
Record sk_finish := sk_Finish { sk_fn:N; sk_fe:bool; sk_ft:N }.
Fixpoint sk_run(fuel phasefuel:nat)(a b:N)(e:bool)(total:N):option sk_finish :=
 match fuel with
 |0=>None
 |S f=>match sk_next phasefuel a b e with
   |None=>None
   |Some(sk_Next aa bb ee t)=>sk_run f phasefuel aa bb ee(total+t)%N
   |Some(sk_Done n ee t)=>Some(sk_Finish n ee(total+t)%N)
   end
 end.
Theorem sk_run_sound : forall fuel phasefuel a b e total n ee t ini,
 csteps sk_tm(sk_count total)ini=Some(sk_MN a b e) ->
 sk_run fuel phasefuel a b e total=Some(sk_Finish n ee t) ->
 csteps sk_tm(sk_count t)ini=Some(sk_DN n ee).
Proof.
 induction fuel as[|fuel IH];intros phasefuel a b e total n ee t ini E H;[discriminate|].
 cbn[sk_run]in H;destruct(sk_next phasefuel a b e)as[o|]eqn:Enext;[|discriminate].
 pose proof(sk_next_sound phasefuel a b e o Enext)as Ek.
 destruct o as[aa bb eee k|nn eee k];cbn[sk_cost sk_denote]in Ek.
 - eapply IH;[eapply sk_compN;[exact E|exact Ek]|exact H].
 - injection H as <- <- <-;eapply sk_compN;[exact E|exact Ek].
Qed.
Lemma sk_blank_entry : csteps sk_tm(sk_count 3)c0=Some(sk_MN 0 1 true).
Proof. reflexivity. Qed.
Print Assumptions sk_phase_sound.
Print Assumptions sk_next_sound.
Print Assumptions sk_run_sound.
