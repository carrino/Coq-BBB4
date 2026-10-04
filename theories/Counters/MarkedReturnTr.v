(** Positive returns within a finite-tape family make every instruction
    reachable from each family member recurrent. The family may carry
    local markers, and endpoints need only agree after [lift]. *)
From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
From BBB4.Counters Require Import CConjugateTr CConjugateReachTr NestCountTr LoopRunTr.

Theorem conjugate_marked_return_fire src dst p flip
 (V:Type) (Cf:V->cconf) target boot x0
 (Htable:forall a b,dst(p a)b=option_map(tconj p flip)(src a b))
 (Hboot:stepn dst boot InitES=Some(lift(cconj p flip(Cf x0))))
 (Hreturn:forall x,exists y,Reach1 src(Cf x)(Cf y))
 (Hfire:forall x,Fires src(Cf x)target) :
 forall N,exists j,N<=j /\ FiresAt dst(p(fst target),snd target)j.
Proof.
 assert(Reach:forall N,exists T x,N<=T /\
   stepn dst T InitES=Some(lift(cconj p flip(Cf x)))).
 { induction N as[|N IH].
   - exists boot,x0;split;[lia|exact Hboot].
   - destruct IH as(T&x&HT&E).
     destruct(Hreturn x)as(y&k&Hk&Ek).
     exists(T+k),y;split;[lia|]. rewrite stepn_add,E.
     apply(cconj_lift_steps src dst p flip Htable). exact Ek. }
 intro N. destruct(Reach N)as(T&x&HT&E).
 destruct(Hfire x)as(k&e&Ek&Hi).
 exists(T+k);split;[lia|]. exists(lift(cconj p flip e));split.
 - rewrite stepn_add,E. apply csteps_lift.
   exact(cconj_steps src dst p flip Htable k _ _ Ek).
 - rewrite cinstr_lift,(cconj_instr src dst p flip Htable),Hi;reflexivity.
Qed.
