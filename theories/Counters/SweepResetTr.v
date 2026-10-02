(** * A finite family of unary sweeps and four-cell reset blocks.

    Every anchor is D0 at the blank left frontier. Two main phases
    increase the leading unary block by four cells, and every second
    phase consumes a trailing [1110] block. Terminal phases produce a
    unary block; its residue-three case resets it to a list of [1110]
    blocks. Thus every case has a positive return to a D0 anchor.

    The symbolic certificates use only the landed lap operations, with
    [ReflectedLapTr] supplying contextual cycles on either side. *)
From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Checkers Require Import LapDecider.
From BBB4.Counters Require Import WTape.
From BBB4.Counters Require Import ReflectedLapTr.
Import ListNotations.

Definition sr_u_s := (mkC StD (mkS [] [] 0 0 []) S0 (mkS [S1;S1;S0;S1;S1;S1;S1;S1] [S1;S1;S1;S1] 1 0 [])).
Definition sr_u_e := (mkC StD (mkS [] [] 0 0 []) S0 (mkS [S1;S1;S0;S1;S1;S1;S1;S1;S1;S1;S1;S1;S1;S1] [S1;S1;S1;S1] 1 0 [])).
Definition sr_u_ch : list rl_step := [(false,SWin 8);(false,SCycR 4);(false,SWinR 8);(false,SCycL 8 0);(false,SWin 32);(true,SCycL 24 4);(false,SWin 23);(false,SWinR 29);(false,SWin 4);(false,SCycL 20 1);(false,SWin 20);(false,SWinL 2);(false,SRotR 3);(false,SRotR 4)].

Definition sr_v_s := (mkC StD (mkS [] [] 0 0 []) S0 (mkS [S1;S1;S0;S1;S1;S1;S1;S1;S1;S1;S1] [S1;S1;S1;S1] 1 0 [S0;S1;S1;S1;S0;S1;S1;S1;S1;S1;S0])).
Definition sr_v_e := (mkC StD (mkS [] [] 0 0 []) S0 (mkS [S1;S1;S0;S1;S1;S1;S1;S1;S1;S1;S1;S1;S1;S1;S1] [S1;S1;S1;S1] 1 0 [S0;S1;S1;S1;S1;S1;S1;S1;S0])).
Definition sr_v_ch : list rl_step := [(false,SWin 11);(false,SCycR 4);(false,SWin 2);(false,SCycL 8 0);(false,SWin 62);(true,SCycL 24 3);(false,SWin 21);(false,SWin 4);(false,SCycL 20 1);(false,SWin 40);(false,SWinL 2);(false,SRotR 4)].

Definition sr_w_s := (mkC StD (mkS [] [] 0 0 []) S0 (mkS [S1;S1;S0;S1;S1;S1;S1;S1;S1;S1;S1] [S1;S1;S1;S1] 1 0 [S0;S1;S1;S1;S1;S1;S1;S1;S0;S1;S1;S1;S0])).
Definition sr_w_e := (mkC StD (mkS [] [] 0 0 []) S0 (mkS [S1;S1;S0;S1;S1;S1;S1;S1;S1;S1;S1;S1;S1;S1;S1] [S1;S1;S1;S1] 1 0 [S0;S1;S1;S1;S0;S1;S1;S1;S1;S1;S0])).
Definition sr_w_ch : list rl_step := [(false,SWin 11);(false,SCycR 4);(false,SWin 2);(false,SCycL 8 0);(false,SWin 62);(true,SCycL 24 3);(false,SWin 33);(false,SWin 4);(false,SCycL 20 1);(false,SWin 40);(false,SWinL 2);(false,SRotR 4)].

Definition sr_t_s := (mkC StD (mkS [] [] 0 0 []) S0 (mkS [S1;S1;S0;S1;S1;S1;S1;S1;S1;S1;S1] [S1;S1;S1;S1] 1 0 [S0;S1;S1;S1;S0;S1;S1;S1])).
Definition sr_t_e := (mkC StD (mkS [] [] 0 0 []) S0 (mkS [S1;S1;S0;S1;S1;S1;S1;S1;S1;S1;S1;S1;S1;S1;S1] [S1;S1;S1;S1] 1 0 [S0;S1;S1;S1;S1;S1])).
Definition sr_t_ch : list rl_step := [(false,SWin 11);(false,SCycR 4);(false,SWin 2);(false,SCycL 8 0);(false,SWin 62);(true,SCycL 24 3);(false,SWin 21);(false,SWin 4);(false,SCycL 20 1);(false,SWin 40);(false,SWinL 2);(false,SRotR 4)].

Definition sr_w0_s := (mkC StD (mkS [] [] 0 0 []) S0 (mkS [S1;S1;S0;S1;S1;S1;S1;S1;S1;S1;S1] [S1;S1;S1;S1] 1 0 [S0;S1;S1;S1;S1;S1;S1;S1;S0;S1])).
Definition sr_w0_e := (mkC StD (mkS [] [] 0 0 []) S0 (mkS [S1;S1;S0;S1;S1;S1;S1;S1;S1;S1;S1;S1;S1;S1;S1] [S1;S1;S1;S1] 1 0 [S0;S1;S1;S1;S0;S1;S1;S1])).
Definition sr_w0_ch : list rl_step := [(false,SWin 11);(false,SCycR 4);(false,SWin 2);(false,SCycL 8 0);(false,SWin 62);(true,SCycL 24 3);(false,SWin 33);(false,SWin 4);(false,SCycL 20 1);(false,SWin 40);(false,SWinL 2);(false,SRotR 4)].

Definition sr_z_s := (mkC StD (mkS [] [] 0 0 []) S0 (mkS [S1;S1;S0;S1;S1;S1;S1;S1;S1;S1;S1] [S1;S1;S1;S1] 1 0 [S0;S1;S1;S1;S1;S1])).
Definition sr_z_e := (mkC StD (mkS [] [] 0 0 []) S0 (mkS [S1;S1;S0;S1;S1;S1;S1;S1;S1;S1;S1;S1;S1;S1;S1;S1;S1;S1;S1;S1] [S1;S1;S1;S1] 1 0 [])).
Definition sr_z_ch : list rl_step := [(false,SWin 11);(false,SCycR 4);(false,SWin 2);(false,SCycL 8 0);(false,SWin 62);(true,SCycL 24 3);(false,SWin 6);(false,SWinR 59);(false,SWin 4);(false,SCycL 20 1);(false,SWin 40);(false,SWinL 2);(false,SRotR 1);(false,SRotR 4);(false,SRotR 4)].

Definition sr_reset_s := (mkC StD (mkS [] [] 0 0 []) S0 (mkS [S1;S1;S0;S1;S1;S1;S1;S1;S1;S1;S1;S1;S1;S1;S1;S1;S1;S1] [S1;S1;S1;S1] 1 0 [])).
Definition sr_reset_e := (mkC StD (mkS [] [] 0 0 []) S0 (mkS [S1;S1;S0;S1;S1;S1;S1;S1;S1;S1;S1;S0;S1;S1;S1;S0;S1;S1;S1;S1;S1;S0] [S1;S1;S1;S0] 1 0 [S1])).
Definition sr_reset_ch : list rl_step := [(false,SWin 18);(false,SCycR 4);(false,SWinR 8);(false,SCycL 8 0);(false,SWin 146);(false,SWinL 2);(false,SRotR 2)].

Definition sr_V := [S0;S1;S1;S1;S0;S1;S1;S1;S1;S1;S0].
Definition sr_W := [S0;S1;S1;S1;S1;S1;S1;S1;S0].
Definition sr_T := [S0;S1;S1;S1;S0;S1;S1;S1].
Definition sr_Z := [S0;S1;S1;S1;S1;S1].
Definition sr_tail k := rep[S1;S1;S1;S0]k++[S1].
Definition sr_conf b n post X : cconf :=
 (StD,([],S0,[S1;S1;S0]++repeat S1(4*n+b)++post++X)).
Inductive sr_value :=
 | srU(n:nat)|srW(n:nat)|srV(n k:nat)|srX(n k:nat)|srT(n:nat)|srZ(n:nat).
Definition sr_anchor x := match x with
 | srU n=>sr_conf 1 n [] [] | srW n=>sr_conf 3 n [] []
 | srV n k=>sr_conf 8 n sr_V(sr_tail k)
 | srX n k=>sr_conf 8 n sr_W(sr_tail k)
 | srT n=>sr_conf 8 n sr_T[] | srZ n=>sr_conf 8 n sr_Z[] end.
Definition sr_next x := match x with
 | srU 0=>srW 1 | srU(S n)=>srW(S(S n))
 | srW 0=>srU 3 | srW 1=>srU 3 | srW 2=>srT 0 | srW(S(S(S n)))=>srV 0 n
 | srV n k=>srX(S n)k
 | srX n 0=>srT(S n) | srX n(S k)=>srV(S n)k
 | srT n=>srZ(S n) | srZ n=>srU(n+4) end.
Lemma sr_rep_ones : forall n,rep[S1;S1;S1;S1]n=repeat S1(4*n).
Proof. induction n;cbn[rep];[reflexivity|]. rewrite IHn. replace(4*S n)with(S(S(S(S(4*n)))))by lia. reflexivity. Qed.
Lemma sr_words : forall b n,repeat S1 b++rep[S1;S1;S1;S1]n=repeat S1(4*n+b).
Proof. intros;rewrite sr_rep_ones,<-repeat_app. f_equal;lia. Qed.
Definition sr_template b post := mkC StD (mkS [] [] 0 0 []) S0
 (mkS ([S1;S1;S0]++repeat S1 b) [S1;S1;S1;S1] 1 0 post).
Lemma sr_den_template : forall b post X n,
 cden [] X n(sr_template b post)=sr_conf b n post X.
Proof.
 intros. unfold cden,sden,sr_template,sr_conf.
 cbn[c_st c_l c_h c_r s_pre s_u s_a s_b s_post].
 rewrite rep_nil. cbn[app]. replace(1*n+0)with n by lia.
 rewrite sr_rep_ones. try rewrite <-!app_assoc.
 rewrite app_assoc with(l:=repeat S1 b),<-repeat_app.
 replace(b+4*n)with(4*n+b)by lia. reflexivity.
Qed.
Section SweepReset.
Variable tm:TM.
Hypothesis sr_u_ok : rl_run tm true true sr_u_ch sr_u_s=Some(sr_u_e,56,126).
Hypothesis sr_v_ok : rl_run tm true false sr_v_ch sr_v_s=Some(sr_v_e,56,142).
Hypothesis sr_w_ok : rl_run tm true false sr_w_ch sr_w_s=Some(sr_w_e,56,154).
Hypothesis sr_t_ok : rl_run tm true true sr_t_ch sr_t_s=Some(sr_t_e,56,142).
Hypothesis sr_w0_ok : rl_run tm true true sr_w0_ch sr_w0_s=Some(sr_w0_e,56,154).
Hypothesis sr_z_ok : rl_run tm true true sr_z_ch sr_z_s=Some(sr_z_e,56,186).
Hypothesis sr_reset_ok : rl_run tm true true sr_reset_ch sr_reset_s=Some(sr_reset_e,12,174).
Hypothesis sr_u0 : csteps tm 70(sr_anchor(srU 0))=Some(sr_anchor(srW 1)).
Hypothesis sr_w0 : csteps tm 182(sr_anchor(srW 0))=Some(sr_anchor(srU 3)).
Hypothesis sr_w1 : csteps tm 182(sr_anchor(srW 1))=Some(sr_anchor(srU 3)).
Hypothesis sr_w2 : csteps tm 162(sr_anchor(srW 2))=Some(sr_anchor(srT 0)).
Lemma sr_u_run : forall n,
 csteps tm(56*n+126)(sr_conf 5 n [] [])=Some(sr_conf 11 n [] []).
Proof.
 intro n. pose proof(rl_run_sound tm true true _ _ _ _ _ sr_u_ok [] [] n ltac:(reflexivity)ltac:(reflexivity))as E.
 change(csteps tm(56*n+126)(cden [] [] n(sr_template 5 []))=Some(cden [] [] n(sr_template 11 [])))in E.
 now rewrite !sr_den_template in E.
Qed.
Lemma sr_v_run : forall n X,
 csteps tm(56*n+142)(sr_conf 8 n sr_V X)=Some(sr_conf 12 n sr_W X).
Proof.
 intros n X. pose proof(rl_run_sound tm true false _ _ _ _ _ sr_v_ok [] X n ltac:(reflexivity)ltac:(discriminate))as E.
 change(csteps tm(56*n+142)(cden [] X n(sr_template 8 sr_V))=Some(cden [] X n(sr_template 12 sr_W)))in E.
 now rewrite !sr_den_template in E.
Qed.
Lemma sr_w_run : forall n X,
 csteps tm(56*n+154)(sr_conf 8 n (sr_W++[S1;S1;S1;S0]) X)=Some(sr_conf 12 n sr_V X).
Proof.
 intros n X. pose proof(rl_run_sound tm true false _ _ _ _ _ sr_w_ok [] X n ltac:(reflexivity)ltac:(discriminate))as E.
 change(csteps tm(56*n+154)(cden [] X n(sr_template 8 (sr_W++[S1;S1;S1;S0])))=Some(cden [] X n(sr_template 12 sr_V)))in E.
 now rewrite !sr_den_template in E.
Qed.
Lemma sr_t_run : forall n,
 csteps tm(56*n+142)(sr_conf 8 n sr_T [])=Some(sr_conf 12 n sr_Z []).
Proof.
 intro n. pose proof(rl_run_sound tm true true _ _ _ _ _ sr_t_ok [] [] n ltac:(reflexivity)ltac:(reflexivity))as E.
 change(csteps tm(56*n+142)(cden [] [] n(sr_template 8 sr_T))=Some(cden [] [] n(sr_template 12 sr_Z)))in E.
 now rewrite !sr_den_template in E.
Qed.
Lemma sr_w0_run : forall n,
 csteps tm(56*n+154)(sr_conf 8 n (sr_W++[S1]) [])=Some(sr_conf 12 n sr_T []).
Proof.
 intro n. pose proof(rl_run_sound tm true true _ _ _ _ _ sr_w0_ok [] [] n ltac:(reflexivity)ltac:(reflexivity))as E.
 change(csteps tm(56*n+154)(cden [] [] n(sr_template 8 (sr_W++[S1])))=Some(cden [] [] n(sr_template 12 sr_T)))in E.
 now rewrite !sr_den_template in E.
Qed.
Lemma sr_z_run : forall n,
 csteps tm(56*n+186)(sr_conf 8 n sr_Z [])=Some(sr_conf 17 n [] []).
Proof.
 intro n. pose proof(rl_run_sound tm true true _ _ _ _ _ sr_z_ok [] [] n ltac:(reflexivity)ltac:(reflexivity))as E.
 change(csteps tm(56*n+186)(cden [] [] n(sr_template 8 sr_Z))=Some(cden [] [] n(sr_template 17 [])))in E.
 now rewrite !sr_den_template in E.
Qed.
Lemma sr_reset_run : forall n,
 csteps tm(12*n+174)(sr_conf 15 n [] [])=Some(sr_anchor(srV 0 n)).
Proof.
 intro n. pose proof(rl_run_sound tm true true _ _ _ _ _ sr_reset_ok [] [] n ltac:(reflexivity)ltac:(reflexivity))as E.
 change(csteps tm(12*n+174)(cden [] [] n(sr_template 15 []))=Some(cden [] [] n sr_reset_e))in E.
 rewrite sr_den_template in E. unfold sr_reset_e,cden,sden in E.
 cbn[c_st c_l c_h c_r s_pre s_u s_a s_b s_post]in E.
 rewrite rep_nil in E. cbn[app]in E. replace(1*n+0)with n in E by lia.
 exact E.
Qed.
Lemma sr_progress : forall x,exists k,0<k /\ csteps tm k(sr_anchor x)=Some(sr_anchor(sr_next x)).
Proof.
 intros [n|n|n k|n k|n|n].
 - destruct n as[|n].
   + exists 70;split;[lia|exact sr_u0].
   + exists(56*n+126);split;[lia|]. pose proof(sr_u_run n)as E.
     unfold sr_next,sr_anchor,sr_conf in *.
     replace(4*S n+1)with(4*n+5)by lia.
     replace(4*S(S n)+3)with(4*n+11)by lia. exact E.
 - destruct n as[|[|[|n]]].
   + exists 182;split;[lia|exact sr_w0].
   + exists 182;split;[lia|exact sr_w1].
   + exists 162;split;[lia|exact sr_w2].
   + exists(12*n+174);split;[lia|]. pose proof(sr_reset_run n)as E.
     unfold sr_next,sr_anchor,sr_conf in *.
     replace(4*S(S(S n))+3)with(4*n+15)by lia. exact E.
 - exists(56*n+142);split;[lia|]. pose proof(sr_v_run n(sr_tail k))as E.
   unfold sr_next,sr_anchor,sr_conf in *.
   replace(4*S n+8)with(4*n+12)by lia. exact E.
 - destruct k as[|k].
   + exists(56*n+154);split;[lia|]. pose proof(sr_w0_run n)as E.
     unfold sr_next,sr_anchor,sr_conf,sr_tail,sr_W in *;cbn[rep app]in *.
     rewrite app_nil_r in E. replace(4*S n+8)with(4*n+12)by lia. exact E.
   + exists(56*n+154);split;[lia|]. pose proof(sr_w_run n(sr_tail k))as E.
     unfold sr_next,sr_anchor,sr_conf,sr_tail,sr_W in *;cbn[rep app]in *.
     replace(4*S n+8)with(4*n+12)by lia. exact E.
 - exists(56*n+142);split;[lia|]. pose proof(sr_t_run n)as E.
   unfold sr_next,sr_anchor,sr_conf in *.
   replace(4*S n+8)with(4*n+12)by lia. exact E.
 - exists(56*n+186);split;[lia|]. pose proof(sr_z_run n)as E.
   unfold sr_next,sr_anchor,sr_conf in *.
   replace(4*(n+4)+1)with(4*n+17)by lia. exact E.
Qed.
Theorem sweep_reset_D0_recurrent :
 (exists T x,stepn tm T InitES=Some(lift(sr_anchor x))) ->
 forall N,exists j,N<=j /\ FiresAt tm (StD,S0) j.
Proof.
 intro Boot.
 assert(Reach:forall N,exists T x,N<=T /\ stepn tm T InitES=Some(lift(sr_anchor x))).
 { induction N as[|N IH].
   - destruct Boot as(T&x&E). exists T,x;split;[lia|exact E].
   - destruct IH as(T&x&HT&E). destruct(sr_progress x)as(k&Hk&Ek).
     exists(T+k),(sr_next x). split;[lia|]. rewrite stepn_add,E. apply csteps_lift;exact Ek. }
 intro N. destruct(Reach N)as(T&x&HT&E).
 exists T. split;[exact HT|]. exists(lift(sr_anchor x)). split;[exact E|]. destruct x;reflexivity.
Qed.
End SweepReset.
