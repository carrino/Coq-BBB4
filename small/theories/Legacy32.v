(** Reuse binary-machine recurrence proofs through an explicit simulation. *)
From Coq Require Import Arith Lia List FunctionalExtensionality.
Require BBB4.BBB4_Statement BBB4.BBBT4_Statement.
From SmallBB Require Import Statement StatementTr CTape Size Bounds.
Module Old := BBB4_Statement.
Module OldTr := BBBT4_Statement.

Definition old_state (swap:bool) (q:St) : Old.St :=
 match q with StA=>Old.StA |StB=>if swap then Old.StC else Old.StB
 |StC=>if swap then Old.StB else Old.StC end.
Definition old_sym (s:Sym) : Old.Sym := match s with S1=>Old.S1|_=>Old.S0 end.
Definition old_dir (d:Dir) : Old.Dir := match d with DL=>Old.DL|DR=>Old.DR end.
Definition old_trans swap (tr:Trans) :=
 Old.mkTrans (old_sym(t_write tr))(old_dir(t_dir tr))(old_state swap(t_next tr)).
Definition old_tape (tp:Tape) := Old.mkTape
 (fun n=>old_sym(t_left tp n))(old_sym(t_head tp))(fun n=>old_sym(t_right tp n)).
Definition old_conf swap (c:ExecState) := (old_state swap(fst c),old_tape(snd c)).
Definition binary_tape (tp:Tape) :=
 t_head tp<>S2 /\ (forall n,t_left tp n<>S2) /\ (forall n,t_right tp n<>S2).
Lemma old_state_inj : forall swap q q',old_state swap q=old_state swap q'->q=q'.
Proof. intros [] [] []; cbn; congruence. Qed.
Lemma old_sym_inj : forall s s',s<>S2->s'<>S2->old_sym s=old_sym s'->s=s'.
Proof. intros [] []; cbn; congruence. Qed.
Lemma old_move : forall d w tp,
 old_tape(tape_move d w tp)=Old.tape_move(old_dir d)(old_sym w)(old_tape tp).
Proof.
 intros [] w [l h r]; unfold old_tape, tape_move, old_dir, Old.tape_move; cbn;
 f_equal; apply functional_extensionality; intro n; destruct n; reflexivity.
Qed.
Lemma binary_move : forall d w tp,w<>S2->binary_tape tp->binary_tape(tape_move d w tp).
Proof.
 intros [] w [l h r] Hw (Hh&Hl&Hr); unfold binary_tape, tape_move; cbn in *;
 repeat split; try auto; intro n; destruct n; cbn [push_side tail_side]; auto.
Qed.
Section Simulation.
Variables (swap:bool)(tm:TM)(legacy:Old.TM).
Hypothesis Had : Admissible 3 2 tm.
Hypothesis Htable : forall q s,s<>S2 ->
 legacy(old_state swap q)(old_sym s)=option_map(old_trans swap)(tm q s).
Lemma binary_step : forall c c',binary_tape(snd c)->step tm c=Some c'->binary_tape(snd c').
Proof.
 intros [q tp] c' Hbin H; cbn [step] in H.
 destruct(tm q(t_head tp))as[tr|]eqn:E;[|discriminate]. injection H as <-.
 cbn [snd]. apply binary_move;[|exact Hbin].
 pose proof(admissible_output 3 2 tm Had q(t_head tp)tr E)as [_ Hs].
 destruct(t_write tr); cbn in Hs; congruence || lia.
Qed.
Lemma old_step : forall c,binary_tape(snd c)->
 Old.step legacy(old_conf swap c)=option_map(old_conf swap)(step tm c).
Proof.
 intros [q tp] (Hh&Hl&Hr). cbn [Old.step old_conf old_tape step fst snd Old.t_head].
 rewrite Htable by exact Hh. destruct(tm q(t_head tp))as[tr|];[|reflexivity].
 cbn [option_map old_conf old_trans Old.t_next Old.t_dir Old.t_write fst snd].
 unfold old_conf; cbn [fst snd]. rewrite old_move. reflexivity.
Qed.
Lemma binary_run : forall n c c',binary_tape(snd c)->stepn tm n c=Some c'->binary_tape(snd c').
Proof.
 induction n; intros c c' Hb H; cbn [stepn]in H;[congruence|].
 destruct(step tm c)as[d|]eqn:E;[|discriminate]. eapply IHn;[eapply binary_step;eauto|exact H].
Qed.
Lemma old_run : forall n c,binary_tape(snd c)->
 Old.stepn legacy n(old_conf swap c)=option_map(old_conf swap)(stepn tm n c).
Proof.
 induction n; intros c Hb;[reflexivity|]. cbn [Old.stepn stepn]. rewrite old_step by exact Hb.
 destruct(step tm c)as[d|]eqn:E;[|reflexivity]. cbn [option_map].
 apply IHn. eapply binary_step;eauto.
Qed.
Lemma binary_init : binary_tape(snd InitES).
Proof. repeat split; discriminate. Qed.
Lemma old_run_init : forall n,
 Old.stepn legacy n Old.InitES=option_map(old_conf swap)(stepn tm n InitES).
Proof. intro n;apply(old_run n InitES binary_init). Qed.
Lemma old_fires : forall q s n,s<>S2 ->
 FiresAt tm(q,s)n <-> OldTr.FiresAt legacy(old_state swap q,old_sym s)n.
Proof.
 intros q s n Hs. split.
 - intros(c&Hc&Hi). exists(old_conf swap c);split;[rewrite old_run_init,Hc;reflexivity|].
   destruct c as [p tp];unfold instr_of in Hi;injection Hi as <- <-;reflexivity.
 - intros(d&Hd&Hi). rewrite old_run_init in Hd.
   destruct(stepn tm n InitES)as[c|]eqn:E;[|discriminate]. injection Hd as <-.
   exists c;split;[exact E|].
   pose proof(binary_run n InitES c binary_init E)as[Hb _].
   destruct c as[p tp];unfold old_conf,old_tape,OldTr.instr_of in Hi;cbn in Hi.
   injection Hi as Hq Hsym. apply old_state_inj in Hq.
   apply old_sym_inj in Hsym;[unfold instr_of;cbn;congruence|exact Hb|exact Hs].
Qed.
Theorem legacy_neverqh : OldTr.NeverQuasiHaltsTr legacy -> NeverQuasiHaltsTr tm.
Proof.
 intros H [q s] (n&c&Hc&Hi) N.
 assert(Hs:s<>S2).
 { pose proof(binary_run n InitES c binary_init Hc)as[Hb _].
   unfold instr_of in Hi;injection Hi as _ <-;exact Hb. }
 destruct(H(old_state swap q,old_sym s)) with(N:=N)as(j&Hj&Hfire).
 - exists n. apply old_fires;[exact Hs|exists c;auto].
 - exists j;split;[exact Hj|apply old_fires;assumption].
Qed.
End Simulation.

Lemma recurrence_bounds : forall bs bi tm,NeverQuasiHaltsTr tm->NonHalt tm /\ Bounds bs bi tm.
Proof.
 intros bs bi tm H;split;[apply never_qh_tr_nonhalt;exact H|].
 pose proof(never_qh_tr_st tm H)as Hst. split.
 - intros q s [Hv Hq]. destruct(Hst q(ex_intro _ s Hv)(S s))as(k&Hk&Hvisit).
   exfalso;apply(Hq k);[lia|exact Hvisit].
 - intros tg s [Hv Hq]. destruct(H tg(ex_intro _ s Hv)(S s))as(k&Hk&Hvisit).
   exfalso;apply(Hq k);[lia|exact Hvisit].
Qed.
