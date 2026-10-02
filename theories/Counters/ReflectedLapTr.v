(** * Compose landed symbolic lap steps in either tape orientation.

    In particular, reflecting [SCycL n m] supplies the contextual right
    cycle without changing the landed symbolic checker. *)
From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement CTape Mirror.
From BBB4.Checkers Require Import LapDecider.
From BBB4.Counters Require Import CConjugateTr.
Import ListNotations.
Definition rl_mirror (c:sconf) : sconf := mkC(c_st c)(c_r c)(c_h c)(c_l c).
Definition rl_step := (bool*lstep)%type.
Definition rl_eval tm el er (st:rl_step) c :=
 let '(flip,s):=st in
 if flip then match sstep(mirror_tm tm) er el s(rl_mirror c) with
 | Some(c',a,b)=>Some(rl_mirror c',a,b)|None=>None end
 else sstep tm el er s c.
Lemma rl_table : forall tm q s,
 tm q s=option_map(tconj(fun q=>q)true)(mirror_tm tm q s).
Proof.
 intros tm q s. unfold mirror_tm. destruct(tm q s)as[[w d r]|];[destruct d|];reflexivity.
Qed.
Lemma rl_eval_sound : forall tm el er st c d a b,
 rl_eval tm el er st c=Some(d,a,b) -> forall XL XR j,
 (el=true -> XL=[]) -> (er=true -> XR=[]) ->
 csteps tm(a*j+b)(cden XL XR j c)=Some(cden XL XR j d).
Proof.
 intros tm el er [[] st] c d a b E XL XR j HL HR;cbn[rl_eval]in E.
 - destruct(sstep(mirror_tm tm)er el st(rl_mirror c))as[[[e x]y]|]eqn:Et;[|discriminate].
   injection E as <- <- <-.
   pose proof(sstep_sound(mirror_tm tm)er el st(rl_mirror c)e x y Et XR XL j HR HL)as F.
   pose proof(cconj_steps(mirror_tm tm)tm(fun q=>q)true(rl_table tm)_ _ _ F)as G.
   change(csteps tm(x*j+y)(cden XL XR j c)=Some(cden XL XR j(rl_mirror e)))in G.
   exact G.
 - eapply sstep_sound;eauto.
Qed.
Fixpoint rl_run tm el er (ch:list rl_step)c :=
 match ch with
 | []=>Some(c,0,0)
 | st::ch=>match rl_eval tm el er st c with
   | Some(c1,a1,b1)=>match rl_run tm el er ch c1 with
     | Some(c2,a2,b2)=>Some(c2,a1+a2,b1+b2)|None=>None end
   | None=>None end
 end.
Theorem rl_run_sound : forall tm el er ch c d a b,
 rl_run tm el er ch c=Some(d,a,b) -> forall XL XR j,
 (el=true -> XL=[]) -> (er=true -> XR=[]) ->
 csteps tm(a*j+b)(cden XL XR j c)=Some(cden XL XR j d).
Proof.
 intros tm el er ch;induction ch as[|st ch IH];intros c d a b E XL XR j HL HR;cbn[rl_run]in E.
 - injection E as <- <- <-. reflexivity.
 - destruct(rl_eval tm el er st c)as[[[e a1]b1]|]eqn:Es;[|discriminate].
   destruct(rl_run tm el er ch e)as[[[f a2]b2]|]eqn:Ef;[|discriminate].
   injection E as <- <- <-.
   replace((a1+a2)*j+(b1+b2))with((a1*j+b1)+(a2*j+b2))by lia.
   rewrite csteps_add,(rl_eval_sound tm el er st c e a1 b1 Es XL XR j HL HR).
   exact(IH e f a2 b2 Ef XL XR j HL HR).
Qed.
