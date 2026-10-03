(** A positive finite-tape return makes every instruction reachable from
    each return point recurrent, also after state renaming and reflection. *)
From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Checkers.IRules Require Import AnchorVisitsTr.
From BBB4.Counters Require Import CConjugateTr CConjugateReachTr.
Theorem conjugate_return_fire src dst p flip q s target boot L R
 (Htable:forall a b,dst(p a)b=option_map(tconj p flip)(src a b))
 (Hboot:stepn dst boot InitES=Some(lift(cconj p flip(q,(L,s,R)))))
 (Hreturn:forall U V,exists k U' V',0<k /\
    csteps src k(q,(U,s,V))=Some(q,(U',s,V')))
 (Hfire:forall U V,exists k e,csteps src k(q,(U,s,V))=Some e /\ cinstr e=target) :
 forall N,exists j,N<=j /\ FiresAt dst(p(fst target),snd target)j.
Proof.
 assert(Reach:forall N,exists T U V,N<=T /\
   stepn dst T InitES=Some(lift(cconj p flip(q,(U,s,V))))).
 { induction N as[|N IH].
   - exists boot,L,R;split;[lia|exact Hboot].
   - destruct IH as(T&U&V&HT&E).
     destruct(Hreturn U V)as(k&U'&V'&Hk&Ek).
     exists(T+k),U',V';split;[lia|]. rewrite stepn_add,E.
     apply(cconj_lift_steps src dst p flip Htable). now apply csteps_lift. }
 intro N. destruct(Reach N)as(T&U&V&HT&E).
 destruct(Hfire U V)as(k&e&Ek&Hi).
 exists(T+k);split;[lia|]. exists(lift(cconj p flip e));split.
 - rewrite stepn_add,E. apply csteps_lift. exact(cconj_steps src dst p flip Htable k _ _ Ek).
 - rewrite cinstr_lift,(cconj_instr src dst p flip Htable),Hi;reflexivity.
Qed.
