(** A four-state crossing transducer is a one-step invariant.  It records
    machine state and parity of twos on the finite left tape.  Its fold over
    the head and right tape always predicts exit in A, excluding a B0 tail.
    This argument needs no termination claim for the nested counter macros. *)
From Coq Require Import List Arith Lia Bool.
From BBB24 Require Import Statement Spec CTape Census TotalCompletion OneStateReach.
Import ListNotations.
Definition s69_tm : TM := fun q h=>Some(match q,h with
 |StA,S0=>mkTrans S1 DL StB |StA,S1=>mkTrans S2 DR StA
 |StA,S2=>mkTrans S1 DL StA |StA,S3=>mkTrans S1 DR StB
 |StB,S0=>mkTrans S2 DR StB |StB,S1=>mkTrans S2 DL StB
 |StB,S2=>mkTrans S3 DL StB |StB,S3=>mkTrans S1 DR StA end).
Definition s69_left := Forall(fun h=>h=S1 \/h=S2).
Definition s69_nonzero := Forall(fun h=>h<>S0).
Fixpoint s69_parity(l:list Sym):bool := match l with
 |[]=>false |h::l=>if match h with S2=>true|_=>false end then negb(s69_parity l)else s69_parity l end.
Definition s69_pass(q:St)(p:bool)(h:Sym):St*bool := match q,h with
 |StA,S0 |StA,S1 =>(StA,negb p)
 |StA,S2 =>(StA,p)
 |StA,S3 =>(StB,p)
 |StB,S0 =>(StB,negb p)
 |StB,S1 =>(if p then StA else StB,true)
 |StB,S2 =>(if p then StB else StA,true)
 |StB,S3 =>(StA,p) end.
Fixpoint s69_scan(q:St)(p:bool)(r:list Sym):St := match r with
 |[]=>q |h::r=>let '(q',p'):=s69_pass q p h in s69_scan q' p' r end.
Definition s69_inv(cc:cconf) := let '(q,(l,h,r)):=cc in
 s69_left l /\s69_nonzero r /\s69_scan q(s69_parity l)(h::r)=StA.
Lemma s69_scan_padding : forall q p r,
 s69_scan q p(chd r::ctl r)=s69_scan q p r.
Proof. intros q p[|h r];[destruct q;reflexivity|reflexivity]. Qed.
Lemma s69_left_tail : forall l,s69_left l->s69_left(ctl l).
Proof. intros[|h l]H;[constructor|inversion H;assumption]. Qed.
Lemma s69_nonzero_tail : forall l,s69_nonzero l->s69_nonzero(ctl l).
Proof. intros[|h l]H;[constructor|inversion H;assumption]. Qed.
Lemma s69_scan_left : forall q h l r,s69_left l ->
 let tr:=match s69_tm q h with Some t=>t|None=>mkTrans S0 DL StA end in
 t_dir tr=DL ->
 s69_scan(t_next tr)(s69_parity(ctl l))(chd l::t_write tr::r)=
 s69_scan q(s69_parity l)(h::r).
Proof.
 intros q h[|x l]r H;[|inversion H as[|? ? Hx Hl];subst];
 destruct q,h;cbn[s69_tm];try discriminate.
 all:try(intros _;reflexivity).
 all:destruct Hx as[Hx|Hx];subst x;cbn[s69_scan s69_pass chd ctl s69_parity];destruct(s69_parity l);reflexivity.
Qed.
Lemma s69_inv_step : forall cc cc',s69_inv cc->cstep s69_tm cc=Some cc'->s69_inv cc'.
Proof.
 intros[q[[l h]r]]cc'[Hl[Hr Hscan]]E;destruct q,h;
 cbn[cstep s69_tm ctape_move]in E;inversion E;subst;clear E;
 cbn[s69_inv].
 all:repeat split.
 all:try(apply s69_left_tail;exact Hl).
 all:try(constructor;[auto|exact Hl]).
 all:try(apply s69_nonzero_tail;exact Hr).
 all:try(constructor;[discriminate|exact Hr]).
 all:try(rewrite s69_scan_padding;exact Hscan).
 all:first[etransitivity;[exact(s69_scan_left StA S0 l r Hl eq_refl)|exact Hscan]
 |etransitivity;[exact(s69_scan_left StA S2 l r Hl eq_refl)|exact Hscan]
 |etransitivity;[exact(s69_scan_left StB S1 l r Hl eq_refl)|exact Hscan]
 |etransitivity;[exact(s69_scan_left StB S2 l r Hl eq_refl)|exact Hscan]].
Qed.
Lemma s69_inv_steps : forall n cc cc',s69_inv cc->csteps s69_tm n cc=Some cc'->s69_inv cc'.
Proof.
 induction n;intros cc cc' H E;cbn[csteps]in E.
 - inversion E;subst;exact H.
 - destruct(cstep s69_tm cc)as[c1|]eqn:E1;[|discriminate].
   eapply IHn;[eapply s69_inv_step;eauto|exact E].
Qed.
Lemma s69_inv_initial : s69_inv c0.
Proof. split;[constructor|split;[constructor|reflexivity]]. Qed.
Lemma s69_total : Total s69_tm.
Proof. intros q h;unfold s69_tm;eexists;reflexivity. Qed.
Lemma s69_B_nonzero_reaches_A : forall l h r,s69_left l->h=S1 \/h=S2 \/h=S3 ->
 ore_reaches s69_tm StA(StB,(l,h,r)).
Proof.
 induction l as[|x l IH];intros h r Hl[H|[H|H]];subst h.
 - exists 6;eexists;split;reflexivity.
 - exists 3;eexists;split;reflexivity.
 - exists 1;eexists;split;reflexivity.
 - inversion Hl as[|? ? Hx Htail];subst.
   destruct Hx as[Hx|Hx];subst x;(eapply ore_reaches_step;[reflexivity|apply IH;auto]).
 - inversion Hl as[|? ? Hx Htail];subst.
   destruct Hx as[Hx|Hx];subst x;(eapply ore_reaches_step;[reflexivity|apply IH;auto]).
 - exists 1;eexists;split;reflexivity.
Qed.
Lemma s69_reaches_A : forall cc,s69_inv cc->ore_reaches s69_tm StA cc.
Proof.
 intros[q[[l h]r]][Hl[Hr Hscan]];destruct q.
 - exists 0,(StA,(l,h,r));split;reflexivity.
 - destruct h.
   + destruct r as[|x r];[discriminate Hscan|].
     inversion Hr as[|? ? Hx Htail];subst.
     eapply ore_reaches_step;[reflexivity|].
     apply s69_B_nonzero_reaches_A;[constructor;auto|].
     destruct x;[contradiction|auto|auto|auto].
   + apply s69_B_nonzero_reaches_A;auto.
   + apply s69_B_nonzero_reaches_A;auto.
   + apply s69_B_nonzero_reaches_A;auto.
Qed.
Lemma s69_B_checked : ore_auto_goal s69_tm StB=true.
Proof. vm_compute;reflexivity. Qed.
Theorem s69_nonhalt : NonHalt s69_tm.
Proof. apply ore_total_nonhalt;exact s69_total. Qed.
Theorem s69_recurrent : forall goal N,exists n,N<=n /\VisitsAt s69_tm goal n.
Proof.
 intros goal N;destruct goal.
 - destruct(ore_total_csteps s69_tm s69_total N c0)as(cc&Eprefix).
   assert(Hinv:s69_inv cc)by(eapply s69_inv_steps;[exact s69_inv_initial|exact Eprefix]).
   destruct(s69_reaches_A cc Hinv)as(k&cc'&Etail&Hstate).
   exists(N+k);split;[lia|];exists(lift cc');split;[|exact Hstate].
   rewrite <-lift_c0;apply csteps_lift;rewrite csteps_add,Eprefix;exact Etail.
 - apply(ore_reaches_recurs s69_tm StB s69_total).
   apply ore_auto_goal_sound;exact s69_B_checked.
Qed.
Theorem s69_state_zero : QHBound 0 s69_tm.
Proof.
 intros q s[_ Hquiet];destruct(s69_recurrent q(S s))as(n&Hn&Hv).
 exfalso;apply(Hquiet n);[lia|exact Hv].
Qed.
Theorem s69_sound : NonHalt s69_tm /\QHBound 0 s69_tm.
Proof. split;[exact s69_nonhalt|exact s69_state_zero]. Qed.
Print Assumptions s69_sound.
