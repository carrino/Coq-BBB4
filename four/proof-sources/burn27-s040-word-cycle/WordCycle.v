(** Exact frozen S040. Eleven finite walls share a supported crossing
    through P^n; one complete cycle adds a single 18-cell word. *)
From Coq Require Import List Arith Lia Bool.
From BBB24 Require Import Statement Spec CTape Census TotalCompletion OneStateReach.
Import ListNotations.
Definition s40_tm:TM:=fun q h=>Some(match q,h with
 |StA,S0=>mkTrans S1 DL StB |StA,S1=>mkTrans S2 DL StA
 |StA,S2=>mkTrans S3 DR StA |StA,S3=>mkTrans S0 DR StB
 |StB,S0=>mkTrans S2 DR StB |StB,S1=>mkTrans S2 DR StA
 |StB,S2=>mkTrans S3 DL StA |StB,S3=>mkTrans S1 DL StB end).
Definition s40_front q l r:cconf:=(q,(l,chd r,ctl r)).
Definition s40_back q l r:cconf:=(q,(ctl l,chd l,r)).

Fixpoint s40_word n:list Sym:=match n with 0=>[]|S n=>S3::S3::S2::S3::S3::S0::S2::S0::S2::S0::S2::S0::S3::S3::S2::S3::S3::S0::s40_word n end.

Fixpoint s40_E n:list Sym:=match n with 0=>[]|S n=>S1::S3::S1::S1::S3::S3::S1::S3::S1::S3::S1::S3::S1::S3::S1::S1::S3::S3::s40_E n end.

Fixpoint s40_H n:list Sym:=match n with 0=>[]|S n=>S3::S1::S1::S3::S3::S1::S3::S1::S3::S1::S3::S1::S3::S1::S1::S3::S3::S1::s40_H n end.

Fixpoint s40_V n:list Sym:=match n with 0=>[]|S n=>S3::S2::S3::S3::S0::S2::S0::S2::S0::S2::S0::S3::S3::S2::S3::S3::S0::S3::s40_V n end.

Definition s40_wall i:list Sym:=match i with
|0=>S2::S2::[]
|1=>S2::S0::S3::[]
|2=>S2::S0::S3::S3::S2::[]
|3=>S3::S3::S2::S3::S3::S2::S2::S2::[]
|4=>S3::S3::S2::S3::S3::S0::S3::S2::S2::[]
|5=>S3::S3::S2::S3::S3::S0::S3::S3::S0::S3::[]
|6=>S3::S3::S2::S3::S3::S0::S2::S2::S3::S3::S0::S2::S2::[]
|7=>S3::S3::S2::S3::S3::S0::S2::S0::S3::S3::S3::S0::S2::S2::[]
|8=>S3::S3::S2::S3::S3::S0::S2::S0::S2::S0::S3::S3::S0::S3::S2::[]
|9=>S3::S3::S2::S3::S3::S0::S2::S0::S2::S0::S2::S2::S3::S3::S0::S3::[]
|_=>S3::S3::S2::S3::S3::S0::S2::S0::S2::S0::S2::S0::S3::S3::S3::S0::S3::[] end.

Definition s40_stage i n r:cconf:=(StA,(s40_word n++s40_wall i,S0,r)).
Definition s40_phase i n:=s40_stage i n[].
Definition s40_main n:=s40_phase 0 n.
Definition s40_cost n:=1056*n+577.
Lemma s40_word_app : forall n m,s40_word(n+m)=s40_word n++s40_word m.
Proof. induction n;intro m;cbn;[reflexivity|now rewrite IHn]. Qed.

Lemma s40_P_shift : forall n r,
 s40_word n++S3::S3::S2::S3::S3::S0::S2::S0::S2::S0::S2::S0::S3::S3::S2::S3::S3::S0::r=S3::S3::S2::S3::S3::S0::S2::S0::S2::S0::S2::S0::S3::S3::S2::S3::S3::S0::(s40_word n++r).
Proof. induction n;intro r;cbn;[reflexivity|now rewrite IHn]. Qed.

Lemma s40_E_shift : forall n r,
 s40_E n++S1::S3::S1::S1::S3::S3::S1::S3::S1::S3::S1::S3::S1::S3::S1::S1::S3::S3::r=S1::S3::S1::S1::S3::S3::S1::S3::S1::S3::S1::S3::S1::S3::S1::S1::S3::S3::(s40_E n++r).
Proof. induction n;intro r;cbn;[reflexivity|now rewrite IHn]. Qed.

Lemma s40_V_shift : forall n r,
 s40_V n++S3::S2::S3::S3::S0::S2::S0::S2::S0::S2::S0::S3::S3::S2::S3::S3::S0::S3::r=S3::S2::S3::S3::S0::S2::S0::S2::S0::S2::S0::S3::S3::S2::S3::S3::S0::S3::(s40_V n++r).
Proof. induction n;intro r;cbn;[reflexivity|now rewrite IHn]. Qed.

Lemma s40_E_rotate : forall n r,s40_E n++S1::r=S1::(s40_H n++r).
Proof. induction n;intro r;cbn;[reflexivity|now rewrite IHn]. Qed.
Lemma s40_V_rotate : forall n r,S3::(s40_V n++r)=s40_word n++S3::r.
Proof. induction n;intro r;cbn;[reflexivity|now rewrite IHn]. Qed.

Lemma s40_L66 : forall l r,
 csteps s40_tm 66(s40_back StB(S3::S3::S2::S3::S3::S0::S2::S0::S2::S0::S2::S0::S3::S3::S2::S3::S3::S0::l)r)=
 Some(s40_back StB l(S1::S3::S1::S1::S3::S3::S1::S3::S1::S3::S1::S3::S1::S3::S1::S1::S3::S3::r)).
Proof. reflexivity. Qed.
Lemma s40_R30 : forall l r,
 csteps s40_tm 30(StA,(l,S2,S3::S1::S1::S3::S3::S1::S3::S1::S3::S1::S3::S1::S3::S1::S1::S3::S3::S1::r))=
 Some(StA,(S3::S2::S3::S3::S0::S2::S0::S2::S0::S2::S0::S3::S3::S2::S3::S3::S0::S3::l,S2,r)).
Proof. reflexivity. Qed.
Lemma s40_R30B : forall l r,
 csteps s40_tm 30(StB,(l,S1,S3::S1::S1::S3::S3::S1::S3::S1::S3::S1::S3::S1::S3::S1::S1::S3::S3::S1::r))=
 Some(StA,(S3::S2::S3::S3::S0::S2::S0::S2::S0::S2::S0::S3::S3::S2::S3::S3::S0::S2::l,S2,r)).
Proof. reflexivity. Qed.

Lemma s40_L_scan : forall n l r,
 csteps s40_tm(66*n)(s40_back StB(s40_word n++l)r)=Some(s40_back StB l(s40_E n++r)).
Proof.
 induction n;intros l r;[reflexivity|].
 replace(66*S n)with(66+66*n)by lia;rewrite csteps_add.
 change(match csteps s40_tm 66(s40_back StB(S3::S3::S2::S3::S3::S0::S2::S0::S2::S0::S2::S0::S3::S3::S2::S3::S3::S0::(s40_word n++l))r)with
 |Some cc=>csteps s40_tm(66*n)cc|None=>None end=Some(s40_back StB l(S1::S3::S1::S1::S3::S3::S1::S3::S1::S3::S1::S3::S1::S3::S1::S1::S3::S3::(s40_E n++r)))).
 rewrite s40_L66,IHn,s40_E_shift;reflexivity.
Qed.
Lemma s40_R_scan : forall n l r,
 csteps s40_tm(30*n)(StA,(l,S2,s40_H n++r))=Some(StA,(s40_V n++l,S2,r)).
Proof.
 induction n;intros l r;[reflexivity|].
 replace(30*S n)with(30+30*n)by lia;rewrite csteps_add.
 change(match csteps s40_tm 30(StA,(l,S2,S3::S1::S1::S3::S3::S1::S3::S1::S3::S1::S3::S1::S3::S1::S1::S3::S3::S1::(s40_H n++r)))with
 |Some cc=>csteps s40_tm(30*n)cc|None=>None end=Some(StA,(S3::S2::S3::S3::S0::S2::S0::S2::S0::S2::S0::S3::S3::S2::S3::S3::S0::S3::(s40_V n++l),S2,r))).
 rewrite s40_R30,IHn,s40_V_shift;reflexivity.
Qed.
Theorem s40_B_gate : forall n l r,
 csteps s40_tm(30*n+1)(s40_front StB l(s40_E n++S1::r))=
 Some(s40_front StA(s40_word n++S2::l)r).
Proof.
 intros[|n]l r;[reflexivity|].
 rewrite s40_E_rotate.
 replace(30*S n+1)with(30+(30*n+1))by lia;rewrite csteps_add.
 change(match csteps s40_tm 30(StB,(l,S1,S3::S1::S1::S3::S3::S1::S3::S1::S3::S1::S3::S1::S3::S1::S1::S3::S3::S1::(s40_H n++r)))with
 |Some cc=>csteps s40_tm(30*n+1)cc|None=>None end=
 Some(s40_front StA(S3::S3::S2::S3::S3::S0::S2::S0::S2::S0::S2::S0::S3::S3::S2::S3::S3::S0::(s40_word n++S2::l))r)).
 rewrite s40_R30B,csteps_add,s40_R_scan.
 change(Some(s40_front StA(S3::(s40_V n++S3::S2::S3::S3::S0::S2::S0::S2::S0::S2::S0::S3::S3::S2::S3::S3::S0::S2::l))r)=
 Some(s40_front StA(S3::S3::S2::S3::S3::S0::S2::S0::S2::S0::S2::S0::S3::S3::S2::S3::S3::S0::(s40_word n++S2::l))r)).
 rewrite s40_V_rotate,s40_P_shift;reflexivity.
Qed.
Lemma s40_turn2 : forall l r,
 csteps s40_tm 2(StA,(S2::l,S1,r))=Some(StA,(S3::l,S2,r)).
Proof. reflexivity. Qed.
Theorem s40_A_gate : forall n l r,
 csteps s40_tm(30*n+3)(s40_front StA(S2::l)(s40_E n++S1::r))=
 Some(s40_front StA(s40_word n++S3::S3::l)r).
Proof.
 intros n l r;rewrite s40_E_rotate.
 replace(30*n+3)with(2+(30*n+1))by lia;rewrite csteps_add.
 change(match csteps s40_tm 2(StA,(S2::l,S1,s40_H n++r))with
 |Some cc=>csteps s40_tm(30*n+1)cc|None=>None end=
 Some(s40_front StA(s40_word n++S3::S3::l)r)).
 rewrite s40_turn2,csteps_add,s40_R_scan.
 change(Some(s40_front StA(S3::(s40_V n++S3::l))r)=
 Some(s40_front StA(s40_word n++S3::S3::l)r)).
 rewrite s40_V_rotate;reflexivity.
Qed.

Lemma s40_boundary_0 : forall r,
 csteps s40_tm 3(s40_back StB(S2::S2::[])r)=Some(s40_front StB(S0::S3::[])r).
Proof. reflexivity. Qed.
Theorem s40_row_0 : forall n r,
 csteps s40_tm(96*n+5)(s40_stage 0 n r)=
 Some(s40_front StA(s40_word n++S2::S0::S3::[])r).
Proof.
 intros n r;replace(96*n+5)with(1+(66*n+(3+(30*n+1))))by lia.
 unfold s40_stage;rewrite csteps_add.
 change(csteps s40_tm(66*n+(3+(30*n+1)))
 (s40_back StB(s40_word n++S2::S2::[])(S1::r))=
 Some(s40_front StA(s40_word n++S2::S0::S3::[])r)).
 rewrite csteps_add,s40_L_scan,csteps_add,s40_boundary_0,s40_B_gate;reflexivity.
Qed.

Lemma s40_phase_0 : forall n,
 csteps s40_tm(96*n+5)(s40_phase 0 n)=Some(s40_phase 1 n).
Proof. intro n;exact(s40_row_0 n[]). Qed.

Lemma s40_boundary_1 : forall r,
 csteps s40_tm 9(s40_back StB(S2::S0::S3::[])r)=Some(s40_front StB(S0::S3::S3::S2::[])r).
Proof. reflexivity. Qed.
Theorem s40_row_1 : forall n r,
 csteps s40_tm(96*n+11)(s40_stage 1 n r)=
 Some(s40_front StA(s40_word n++S2::S0::S3::S3::S2::[])r).
Proof.
 intros n r;replace(96*n+11)with(1+(66*n+(9+(30*n+1))))by lia.
 unfold s40_stage;rewrite csteps_add.
 change(csteps s40_tm(66*n+(9+(30*n+1)))
 (s40_back StB(s40_word n++S2::S0::S3::[])(S1::r))=
 Some(s40_front StA(s40_word n++S2::S0::S3::S3::S2::[])r)).
 rewrite csteps_add,s40_L_scan,csteps_add,s40_boundary_1,s40_B_gate;reflexivity.
Qed.

Lemma s40_phase_1 : forall n,
 csteps s40_tm(96*n+11)(s40_phase 1 n)=Some(s40_phase 2 n).
Proof. intro n;exact(s40_row_1 n[]). Qed.

Lemma s40_boundary_2 : forall r,
 csteps s40_tm 27(s40_back StB(S2::S0::S3::S3::S2::[])r)=Some(s40_front StA(S2::S2::S3::S3::S2::S2::S2::[])r).
Proof. reflexivity. Qed.
Theorem s40_row_2 : forall n r,
 csteps s40_tm(96*n+31)(s40_stage 2 n r)=
 Some(s40_front StA(s40_word n++S3::S3::S2::S3::S3::S2::S2::S2::[])r).
Proof.
 intros n r;replace(96*n+31)with(1+(66*n+(27+(30*n+3))))by lia.
 unfold s40_stage;rewrite csteps_add.
 change(csteps s40_tm(66*n+(27+(30*n+3)))
 (s40_back StB(s40_word n++S2::S0::S3::S3::S2::[])(S1::r))=
 Some(s40_front StA(s40_word n++S3::S3::S2::S3::S3::S2::S2::S2::[])r)).
 rewrite csteps_add,s40_L_scan,csteps_add,s40_boundary_2,s40_A_gate;reflexivity.
Qed.

Lemma s40_phase_2 : forall n,
 csteps s40_tm(96*n+31)(s40_phase 2 n)=Some(s40_phase 3 n).
Proof. intro n;exact(s40_row_2 n[]). Qed.

Lemma s40_boundary_3 : forall r,
 csteps s40_tm 39(s40_back StB(S3::S3::S2::S3::S3::S2::S2::S2::[])r)=Some(s40_front StA(S2::S2::S3::S3::S0::S3::S2::S2::[])r).
Proof. reflexivity. Qed.
Theorem s40_row_3 : forall n r,
 csteps s40_tm(96*n+43)(s40_stage 3 n r)=
 Some(s40_front StA(s40_word n++S3::S3::S2::S3::S3::S0::S3::S2::S2::[])r).
Proof.
 intros n r;replace(96*n+43)with(1+(66*n+(39+(30*n+3))))by lia.
 unfold s40_stage;rewrite csteps_add.
 change(csteps s40_tm(66*n+(39+(30*n+3)))
 (s40_back StB(s40_word n++S3::S3::S2::S3::S3::S2::S2::S2::[])(S1::r))=
 Some(s40_front StA(s40_word n++S3::S3::S2::S3::S3::S0::S3::S2::S2::[])r)).
 rewrite csteps_add,s40_L_scan,csteps_add,s40_boundary_3,s40_A_gate;reflexivity.
Qed.

Lemma s40_phase_3 : forall n,
 csteps s40_tm(96*n+43)(s40_phase 3 n)=Some(s40_phase 4 n).
Proof. intro n;exact(s40_row_3 n[]). Qed.

Lemma s40_boundary_4 : forall r,
 csteps s40_tm 47(s40_back StB(S3::S3::S2::S3::S3::S0::S3::S2::S2::[])r)=Some(s40_front StA(S2::S2::S3::S3::S0::S3::S3::S0::S3::[])r).
Proof. reflexivity. Qed.
Theorem s40_row_4 : forall n r,
 csteps s40_tm(96*n+51)(s40_stage 4 n r)=
 Some(s40_front StA(s40_word n++S3::S3::S2::S3::S3::S0::S3::S3::S0::S3::[])r).
Proof.
 intros n r;replace(96*n+51)with(1+(66*n+(47+(30*n+3))))by lia.
 unfold s40_stage;rewrite csteps_add.
 change(csteps s40_tm(66*n+(47+(30*n+3)))
 (s40_back StB(s40_word n++S3::S3::S2::S3::S3::S0::S3::S2::S2::[])(S1::r))=
 Some(s40_front StA(s40_word n++S3::S3::S2::S3::S3::S0::S3::S3::S0::S3::[])r)).
 rewrite csteps_add,s40_L_scan,csteps_add,s40_boundary_4,s40_A_gate;reflexivity.
Qed.

Lemma s40_phase_4 : forall n,
 csteps s40_tm(96*n+51)(s40_phase 4 n)=Some(s40_phase 5 n).
Proof. intro n;exact(s40_row_4 n[]). Qed.

Lemma s40_boundary_5 : forall r,
 csteps s40_tm 77(s40_back StB(S3::S3::S2::S3::S3::S0::S3::S3::S0::S3::[])r)=Some(s40_front StA(S2::S2::S3::S3::S0::S2::S2::S3::S3::S0::S2::S2::[])r).
Proof. reflexivity. Qed.
Theorem s40_row_5 : forall n r,
 csteps s40_tm(96*n+81)(s40_stage 5 n r)=
 Some(s40_front StA(s40_word n++S3::S3::S2::S3::S3::S0::S2::S2::S3::S3::S0::S2::S2::[])r).
Proof.
 intros n r;replace(96*n+81)with(1+(66*n+(77+(30*n+3))))by lia.
 unfold s40_stage;rewrite csteps_add.
 change(csteps s40_tm(66*n+(77+(30*n+3)))
 (s40_back StB(s40_word n++S3::S3::S2::S3::S3::S0::S3::S3::S0::S3::[])(S1::r))=
 Some(s40_front StA(s40_word n++S3::S3::S2::S3::S3::S0::S2::S2::S3::S3::S0::S2::S2::[])r)).
 rewrite csteps_add,s40_L_scan,csteps_add,s40_boundary_5,s40_A_gate;reflexivity.
Qed.

Lemma s40_phase_5 : forall n,
 csteps s40_tm(96*n+81)(s40_phase 5 n)=Some(s40_phase 6 n).
Proof. intro n;exact(s40_row_5 n[]). Qed.

Lemma s40_boundary_6 : forall r,
 csteps s40_tm 43(s40_back StB(S3::S3::S2::S3::S3::S0::S2::S2::S3::S3::S0::S2::S2::[])r)=Some(s40_front StA(S2::S2::S3::S3::S0::S2::S0::S3::S3::S3::S0::S2::S2::[])r).
Proof. reflexivity. Qed.
Theorem s40_row_6 : forall n r,
 csteps s40_tm(96*n+47)(s40_stage 6 n r)=
 Some(s40_front StA(s40_word n++S3::S3::S2::S3::S3::S0::S2::S0::S3::S3::S3::S0::S2::S2::[])r).
Proof.
 intros n r;replace(96*n+47)with(1+(66*n+(43+(30*n+3))))by lia.
 unfold s40_stage;rewrite csteps_add.
 change(csteps s40_tm(66*n+(43+(30*n+3)))
 (s40_back StB(s40_word n++S3::S3::S2::S3::S3::S0::S2::S2::S3::S3::S0::S2::S2::[])(S1::r))=
 Some(s40_front StA(s40_word n++S3::S3::S2::S3::S3::S0::S2::S0::S3::S3::S3::S0::S2::S2::[])r)).
 rewrite csteps_add,s40_L_scan,csteps_add,s40_boundary_6,s40_A_gate;reflexivity.
Qed.

Lemma s40_phase_6 : forall n,
 csteps s40_tm(96*n+47)(s40_phase 6 n)=Some(s40_phase 7 n).
Proof. intro n;exact(s40_row_6 n[]). Qed.

Lemma s40_boundary_7 : forall r,
 csteps s40_tm 65(s40_back StB(S3::S3::S2::S3::S3::S0::S2::S0::S3::S3::S3::S0::S2::S2::[])r)=Some(s40_front StA(S2::S2::S3::S3::S0::S2::S0::S2::S0::S3::S3::S0::S3::S2::[])r).
Proof. reflexivity. Qed.
Theorem s40_row_7 : forall n r,
 csteps s40_tm(96*n+69)(s40_stage 7 n r)=
 Some(s40_front StA(s40_word n++S3::S3::S2::S3::S3::S0::S2::S0::S2::S0::S3::S3::S0::S3::S2::[])r).
Proof.
 intros n r;replace(96*n+69)with(1+(66*n+(65+(30*n+3))))by lia.
 unfold s40_stage;rewrite csteps_add.
 change(csteps s40_tm(66*n+(65+(30*n+3)))
 (s40_back StB(s40_word n++S3::S3::S2::S3::S3::S0::S2::S0::S3::S3::S3::S0::S2::S2::[])(S1::r))=
 Some(s40_front StA(s40_word n++S3::S3::S2::S3::S3::S0::S2::S0::S2::S0::S3::S3::S0::S3::S2::[])r)).
 rewrite csteps_add,s40_L_scan,csteps_add,s40_boundary_7,s40_A_gate;reflexivity.
Qed.

Lemma s40_phase_7 : forall n,
 csteps s40_tm(96*n+69)(s40_phase 7 n)=Some(s40_phase 8 n).
Proof. intro n;exact(s40_row_7 n[]). Qed.

Lemma s40_boundary_8 : forall r,
 csteps s40_tm 83(s40_back StB(S3::S3::S2::S3::S3::S0::S2::S0::S2::S0::S3::S3::S0::S3::S2::[])r)=Some(s40_front StA(S2::S2::S3::S3::S0::S2::S0::S2::S0::S2::S2::S3::S3::S0::S3::[])r).
Proof. reflexivity. Qed.
Theorem s40_row_8 : forall n r,
 csteps s40_tm(96*n+87)(s40_stage 8 n r)=
 Some(s40_front StA(s40_word n++S3::S3::S2::S3::S3::S0::S2::S0::S2::S0::S2::S2::S3::S3::S0::S3::[])r).
Proof.
 intros n r;replace(96*n+87)with(1+(66*n+(83+(30*n+3))))by lia.
 unfold s40_stage;rewrite csteps_add.
 change(csteps s40_tm(66*n+(83+(30*n+3)))
 (s40_back StB(s40_word n++S3::S3::S2::S3::S3::S0::S2::S0::S2::S0::S3::S3::S0::S3::S2::[])(S1::r))=
 Some(s40_front StA(s40_word n++S3::S3::S2::S3::S3::S0::S2::S0::S2::S0::S2::S2::S3::S3::S0::S3::[])r)).
 rewrite csteps_add,s40_L_scan,csteps_add,s40_boundary_8,s40_A_gate;reflexivity.
Qed.

Lemma s40_phase_8 : forall n,
 csteps s40_tm(96*n+87)(s40_phase 8 n)=Some(s40_phase 9 n).
Proof. intro n;exact(s40_row_8 n[]). Qed.

Lemma s40_boundary_9 : forall r,
 csteps s40_tm 51(s40_back StB(S3::S3::S2::S3::S3::S0::S2::S0::S2::S0::S2::S2::S3::S3::S0::S3::[])r)=Some(s40_front StA(S2::S2::S3::S3::S0::S2::S0::S2::S0::S2::S0::S3::S3::S3::S0::S3::[])r).
Proof. reflexivity. Qed.
Theorem s40_row_9 : forall n r,
 csteps s40_tm(96*n+55)(s40_stage 9 n r)=
 Some(s40_front StA(s40_word n++S3::S3::S2::S3::S3::S0::S2::S0::S2::S0::S2::S0::S3::S3::S3::S0::S3::[])r).
Proof.
 intros n r;replace(96*n+55)with(1+(66*n+(51+(30*n+3))))by lia.
 unfold s40_stage;rewrite csteps_add.
 change(csteps s40_tm(66*n+(51+(30*n+3)))
 (s40_back StB(s40_word n++S3::S3::S2::S3::S3::S0::S2::S0::S2::S0::S2::S2::S3::S3::S0::S3::[])(S1::r))=
 Some(s40_front StA(s40_word n++S3::S3::S2::S3::S3::S0::S2::S0::S2::S0::S2::S0::S3::S3::S3::S0::S3::[])r)).
 rewrite csteps_add,s40_L_scan,csteps_add,s40_boundary_9,s40_A_gate;reflexivity.
Qed.

Lemma s40_phase_9 : forall n,
 csteps s40_tm(96*n+55)(s40_phase 9 n)=Some(s40_phase 10 n).
Proof. intro n;exact(s40_row_9 n[]). Qed.

Lemma s40_boundary_10 : forall r,
 csteps s40_tm 93(s40_back StB(S3::S3::S2::S3::S3::S0::S2::S0::S2::S0::S2::S0::S3::S3::S3::S0::S3::[])r)=Some(s40_front StA(S2::S2::S3::S3::S0::S2::S0::S2::S0::S2::S0::S3::S3::S2::S3::S3::S0::S2::S2::[])r).
Proof. reflexivity. Qed.
Theorem s40_row_10 : forall n r,
 csteps s40_tm(96*n+97)(s40_stage 10 n r)=
 Some(s40_front StA(s40_word n++S3::S3::S2::S3::S3::S0::S2::S0::S2::S0::S2::S0::S3::S3::S2::S3::S3::S0::S2::S2::[])r).
Proof.
 intros n r;replace(96*n+97)with(1+(66*n+(93+(30*n+3))))by lia.
 unfold s40_stage;rewrite csteps_add.
 change(csteps s40_tm(66*n+(93+(30*n+3)))
 (s40_back StB(s40_word n++S3::S3::S2::S3::S3::S0::S2::S0::S2::S0::S2::S0::S3::S3::S3::S0::S3::[])(S1::r))=
 Some(s40_front StA(s40_word n++S3::S3::S2::S3::S3::S0::S2::S0::S2::S0::S2::S0::S3::S3::S2::S3::S3::S0::S2::S2::[])r)).
 rewrite csteps_add,s40_L_scan,csteps_add,s40_boundary_10,s40_A_gate;reflexivity.
Qed.

Lemma s40_phase_10 : forall n,
 csteps s40_tm(96*n+97)(s40_phase 10 n)=Some(s40_main(S n)).
Proof. intro n;pose proof(s40_row_10 n[])as E;rewrite s40_P_shift in E;exact E. Qed.
Theorem s40_main_next : forall n,
 csteps s40_tm(s40_cost n)(s40_main n)=Some(s40_main(S n)).
Proof.
 intro n;replace(s40_cost n)with((96*n+5)+((96*n+11)+((96*n+31)+((96*n+43)+((96*n+51)+((96*n+81)+((96*n+47)+((96*n+69)+((96*n+87)+((96*n+55)+((96*n+97))))))))))))by(unfold s40_cost;lia).
 unfold s40_main at 1.
 rewrite csteps_add,s40_phase_0.
 rewrite csteps_add,s40_phase_1.
 rewrite csteps_add,s40_phase_2.
 rewrite csteps_add,s40_phase_3.
 rewrite csteps_add,s40_phase_4.
 rewrite csteps_add,s40_phase_5.
 rewrite csteps_add,s40_phase_6.
 rewrite csteps_add,s40_phase_7.
 rewrite csteps_add,s40_phase_8.
 rewrite csteps_add,s40_phase_9.
 apply s40_phase_10.
Qed.
Example s40_entry : csteps s40_tm 3 c0=Some(s40_main 0).
Proof. reflexivity. Qed.
Lemma s40_returns : forall N,exists t n,N<=t /\csteps s40_tm t c0=Some(s40_main n).
Proof.
 induction N as[|N IH].
 - exists 3,0;split;[lia|exact s40_entry].
 - destruct IH as(t&n&Ht&E);exists(t+s40_cost n),(S n);split.
   + unfold s40_cost;lia.
   + rewrite csteps_add,E;apply s40_main_next.
Qed.
Theorem s40_nonhalt : NonHalt s40_tm.
Proof. apply ore_total_nonhalt;intros q h;destruct q,h;eexists;reflexivity. Qed.
Theorem s40_A_recurrent : forall N,exists t,N<=t /\VisitsAt s40_tm StA t.
Proof.
 intro N;destruct(s40_returns N)as(t&n&Ht&E).
 exists t;split;[exact Ht|];exists(lift(s40_main n));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift;exact E.
Qed.
Theorem s40_B_recurrent : forall N,exists t,N<=t /\VisitsAt s40_tm StB t.
Proof.
 intro N;destruct(s40_returns N)as(t&n&Ht&E).
 exists(t+1);split;[lia|];exists(lift(StB,(ctl(s40_word n++[S2;S2]),chd(s40_word n++[S2;S2]),[S1])));split;[|reflexivity].
 rewrite <-lift_c0;apply csteps_lift;rewrite csteps_add,E;reflexivity.
Qed.
Theorem s40_state_zero : QHBound 0 s40_tm.
Proof.
 intros q s[_ Hquiet];destruct q.
 - destruct(s40_A_recurrent(S s))as(t&Ht&Hv);exfalso;apply(Hquiet t);[lia|exact Hv].
 - destruct(s40_B_recurrent(S s))as(t&Ht&Hv);exfalso;apply(Hquiet t);[lia|exact Hv].
Qed.
Theorem s40_sound : NonHalt s40_tm /\QHBound 0 s40_tm.
Proof. split;[exact s40_nonhalt|exact s40_state_zero]. Qed.
Print Assumptions s40_sound.
