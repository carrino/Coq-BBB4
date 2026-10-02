(** Positive finite-tape returns yield arbitrarily late instruction visits. *)
From Coq Require Import Arith Lia List.
From BBB4 Require Import BBB4_Statement BBBT4_Statement CTape.
From BBB4.Counters Require Import CConjugateTr CConjugateReachTr.

Theorem conjugate_return_recurrent src dst p flip q s boot L R
 (Htable:forall a b,dst(p a)b=option_map(tconj p flip)(src a b))
 (Hboot:stepn dst boot InitES=Some(lift(cconj p flip(q,(L,s,R)))))
 (Hreturn:forall U V,exists k U' V',0<k /\
    csteps src k(q,(U,s,V))=Some(q,(U',s,V'))) :
 forall N,exists j,N<=j /\ FiresAt dst(p q,s)j.
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
 exists T;split;[exact HT|]. exists(lift(cconj p flip(q,(U,s,V))));split;[exact E|].
 destruct flip;reflexivity.
Qed.
