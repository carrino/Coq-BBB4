(** Renaming the two nonblank symbols preserves instruction quasihalting. *)
From Coq Require Import Arith Lia List FunctionalExtensionality.
From SmallBB Require Import Statement StatementTr Bounds Mirror CycleCensus.

Definition swap_sym s:=match s with S0=>S0|S1=>S2|S2=>S1 end.
Lemma swap_sym_inv:forall s,swap_sym(swap_sym s)=s.
Proof. destruct s;reflexivity. Qed.
Definition swap_tape tp:=mkTape(fun i=>swap_sym(t_left tp i))
 (swap_sym(t_head tp))(fun i=>swap_sym(t_right tp i)).
Definition swap_es(c:ExecState):ExecState:=(fst c,swap_tape(snd c)).
Definition swap_trans tr:=mkTrans(swap_sym(t_write tr))(t_dir tr)(t_next tr).
Definition swap_tm(tm:TM):TM:=fun q s=>option_map swap_trans(tm q(swap_sym s)).
Definition swap_instr(t:Instr):Instr:=(fst t,swap_sym(snd t)).
Lemma swap_instr_inv:forall t,swap_instr(swap_instr t)=t.
Proof. intros[q s];unfold swap_instr;cbn;now rewrite swap_sym_inv. Qed.
Lemma swap_instr_es:forall c,instr_of(swap_es c)=swap_instr(instr_of c).
Proof. intros[q tp];reflexivity. Qed.
Lemma swap_move:forall d w tp,
 swap_tape(tape_move d w tp)=tape_move d(swap_sym w)(swap_tape tp).
Proof. intros d w[l h r];destruct d;unfold swap_tape,tape_move;cbn;f_equal;apply functional_extensionality;intro i;destruct i;reflexivity. Qed.
Lemma swap_step:forall tm c,
 step(swap_tm tm)(swap_es c)=option_map swap_es(step tm c).
Proof.
 intros tm[q tp];unfold step,swap_es,swap_tm;cbn[fst snd swap_tape t_head].
 rewrite swap_sym_inv. destruct(tm q(t_head tp))as[[w d q']|];[|reflexivity].
 cbn[option_map swap_trans t_dir t_write t_next swap_es fst snd].
 now rewrite swap_move.
Qed.
Lemma swap_stepn:forall tm n c,
 stepn(swap_tm tm)n(swap_es c)=option_map swap_es(stepn tm n c).
Proof.
 intros tm n;induction n;intro c;[reflexivity|].
 cbn[stepn];rewrite swap_step;destruct(step tm c);cbn[option_map];auto.
Qed.
Lemma swap_init:swap_es InitES=InitES.
Proof. reflexivity. Qed.
Lemma swap_fires:forall tm t n,FiresAt(swap_tm tm)(swap_instr t)n<->FiresAt tm t n.
Proof.
 intros tm t n;split;intros(c&Hr&Ht).
 - rewrite <-swap_init,swap_stepn in Hr.
   destruct(stepn tm n InitES)as[d|]eqn:E;[|discriminate]. injection Hr as <-.
   exists d;split;[exact E|]. rewrite swap_instr_es in Ht.
   apply(f_equal swap_instr)in Ht;now rewrite !swap_instr_inv in Ht.
 - exists(swap_es c);split.
   + rewrite <-swap_init,swap_stepn,Hr;reflexivity.
   + rewrite swap_instr_es,Ht;reflexivity.
Qed.
Lemma swap_qhbound:forall B tm,QHBoundTr B(swap_tm tm)->QHBoundTr B tm.
Proof.
 intros B tm H t s[Hv Hq];apply(H(swap_instr t)s);split.
 - apply swap_fires;exact Hv.
 - intros n Hn Hf;apply(Hq n Hn);apply swap_fires;exact Hf.
Qed.
Lemma mirror_qhbound:forall B tm,QHBoundTr B(mirror_tm tm)->QHBoundTr B tm.
Proof.
 intros B tm H t s[Hv Hq];apply(H t s);split.
 - apply mirror_fires;exact Hv.
 - intros n Hn Hf;apply(Hq n Hn);apply mirror_fires;exact Hf.
Qed.
