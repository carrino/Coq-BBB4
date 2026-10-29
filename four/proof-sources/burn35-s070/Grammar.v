(** Eight-state regular invariant for the exact normalized scanner.
    Candidate source SHA2565799ccc7ce51cf7c5b3fca568ed2d5a1876565576f2e3659d515da23caf7f73a.
    Every finite law below is checked in Coq, not assumed from synthesis. *)
From Coq Require Import List Arith Lia Bool.
From BBB24 Require Import Statement Spec CTape Census.
From BBB24Burn35S070 Require Import Core.
Import ListNotations.
Inductive st_dfa := st_d0 |st_d1 |st_d2 |st_d3 |st_d4 |st_d5 |st_d6 |st_d7.
Definition st_delta(d:st_dfa)(h:Sym):st_dfa := match h,d with
 |S0,st_d0=>st_d0
 |S0,st_d1=>st_d4
 |S0,st_d2=>st_d2
 |S0,st_d3=>st_d2
 |S0,st_d4=>st_d1
 |S0,st_d5=>st_d0
 |S0,st_d6=>st_d0
 |S0,st_d7=>st_d4
 |S1,st_d0=>st_d1
 |S1,st_d1=>st_d0
 |S1,st_d2=>st_d2
 |S1,st_d3=>st_d2
 |S1,st_d4=>st_d2
 |S1,st_d5=>st_d4
 |S1,st_d6=>st_d2
 |S1,st_d7=>st_d4
 |S2,st_d0=>st_d3
 |S2,st_d1=>st_d2
 |S2,st_d2=>st_d2
 |S2,st_d3=>st_d0
 |S2,st_d4=>st_d6
 |S2,st_d5=>st_d0
 |S2,st_d6=>st_d0
 |S2,st_d7=>st_d0
 |_,_=>st_d2 end.
Definition st_accept(d:st_dfa):bool := match d with st_d1=>true|_=>false end.
Definition st_H(i:st_dfa)(m:st_mode)(o:st_dfa):bool := match i,m,o with
 |st_d0,st_B3,st_d0=>true
 |st_d0,st_B3,st_d1=>true
 |st_d0,st_Copy,st_d0=>true
 |st_d1,st_A,st_d3=>true
 |st_d1,st_A,st_d6=>true
 |st_d1,st_Copy,st_d1=>true
 |st_d2,st_B3,st_d0=>true
 |st_d2,st_B3,st_d1=>true
 |st_d2,st_B3,st_d2=>true
 |st_d2,st_B3,st_d4=>true
 |st_d2,st_A,st_d2=>true
 |st_d2,st_A,st_d3=>true
 |st_d2,st_A,st_d6=>true
 |st_d2,st_B1,st_d0=>true
 |st_d2,st_B1,st_d2=>true
 |st_d2,st_Copy,st_d0=>true
 |st_d2,st_Copy,st_d1=>true
 |st_d2,st_Copy,st_d2=>true
 |st_d2,st_Copy,st_d3=>true
 |st_d2,st_Copy,st_d4=>true
 |st_d2,st_Copy,st_d6=>true
 |st_d3,st_B3,st_d0=>true
 |st_d3,st_B3,st_d4=>true
 |st_d3,st_Copy,st_d3=>true
 |st_d4,st_B1,st_d0=>true
 |st_d4,st_Copy,st_d4=>true
 |st_d6,st_B3,st_d0=>true
 |st_d6,st_Copy,st_d6=>true
 |_,_,_=>false end.
Fixpoint st_read(d:st_dfa)(w:list Sym):st_dfa :=
 match w with []=>d|h::u=>st_read(st_delta d h)u end.
Definition st_digits(w:list Sym):Prop := Forall(fun h=>h<>S3)w.
Definition st_valid w:Prop := st_digits w /\ st_accept(st_read st_d0 w)=true.
Definition st_edge(m:st_mode)(h:Sym):st_mode*list Sym :=
 match m,h with
 |st_B3,S0=>(st_B3,[S1])|st_B3,S1=>(st_A,[S0;S2])|st_B3,S2=>(st_B3,[S0])
 |st_A,S0=>(st_B1,[S2])|st_A,S1=>(st_Copy,[S2])|st_A,S2=>(st_Copy,[S1])
 |st_B1,S0=>(st_Copy,[S1])|st_B1,S1=>(st_A,[S2])|st_B1,S2=>(st_B3,[])
 |_,_=>(st_Copy,[h])end.
Definition st_end(m:st_mode):option(list Sym) :=
 match m with st_B3=>None|st_A=>Some[S2;S1]|st_B1=>Some[S1]|st_Copy=>Some[]end.
Lemma st_read_app : forall w u d,st_read d(w++u)=st_read(st_read d w)u.
Proof. induction w;intros u d;[reflexivity|cbn[st_read app];apply IHw]. Qed.
Lemma st_scan_copy : forall w,st_scan st_Copy w=Some w.
Proof. destruct w;reflexivity. Qed.
Lemma st_emit_nil : forall o,st_emit[]o=o.
Proof. destruct o;reflexivity. Qed.
Lemma st_scan_cons : forall m h w,h<>S3 ->
 st_scan m(h::w)=let '(m',v):=st_edge m h in st_emit v(st_scan m' w).
Proof. intros m h w H;destruct m,h;try contradiction;cbn[st_edge st_scan st_emit];rewrite ?st_scan_copy,?st_emit_nil;reflexivity. Qed.
Lemma st_H_step : forall i m o h,st_H i m o=true ->h<>S3 ->
 let '(m',v):=st_edge m h in
 st_H(st_delta i h)m'(st_read o v)=true /\ st_digits v.
Proof.
 intros i m o h H Hh;destruct i,m,o,h;
 cbn[st_H st_edge st_delta st_read st_accept]in *;try discriminate;try contradiction.
 all: split.
 all: try reflexivity.
 all: unfold st_digits;repeat constructor;discriminate.
Qed.
Lemma st_H_end : forall i m o,st_H i m o=true ->st_accept i=true ->
 exists v,st_end m=Some v /\ st_accept(st_read o v)=true /\ st_digits v.
Proof.
 intros i m o H Ha;destruct i,m,o;cbn[st_H st_accept]in *;try discriminate.
 all: eexists;split;[reflexivity|].
 all: split;[reflexivity|].
 all: unfold st_digits;repeat constructor;discriminate.
Qed.
Theorem st_scan_closed : forall w,st_digits w ->forall i m o,
 st_H i m o=true ->st_accept(st_read i w)=true ->
 exists out,st_scan m w=Some out /\ st_accept(st_read o out)=true /\ st_digits out.
Proof.
 induction w as[|h w IH];intros Hw i m o H Ha.
 - destruct(st_H_end i m o H Ha)as(v&Ev&Hv&Hdv);exists v;split;[destruct m;exact Ev|auto].
 - inversion Hw as[|h' w' Hh Hdw];subst.
   pose proof(st_H_step i m o h H Hh)as He.
   destruct(st_edge m h)as[m' v]eqn:E;destruct He as[HH Hdv].
   destruct(IH Hdw(st_delta i h)m'(st_read o v)HH Ha)as(u&Eu&Hu&Hdu).
   exists(v++u);split.
   + rewrite st_scan_cons by exact Hh;rewrite E,Eu;reflexivity.
   + split;[rewrite st_read_app;exact Hu|apply Forall_app;auto].
Qed.
Theorem st_G_closed : forall w,st_valid w ->exists out,st_G w=Some out /\ st_valid out.
Proof.
 intros w[Hw Ha].
 destruct(st_scan_closed w Hw st_d0 st_B3 st_d0 ltac:(reflexivity)Ha)as(out&Hout&Haout&Hdigits).
 exists(S0::out);split;[unfold st_G;rewrite Hout;reflexivity|].
 split;[constructor;[discriminate|exact Hdigits]|exact Haout].
Qed.
Lemma st_seed_valid : st_valid[S1].
Proof. split;[unfold st_digits;repeat constructor;discriminate|reflexivity]. Qed.
Print Assumptions st_scan_closed.
Print Assumptions st_G_closed.
