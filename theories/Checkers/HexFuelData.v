(** * Compact syntax for large fuel certificates.

    This is a data decoder, not a proof checker. Hexadecimal digit lists
    refer to shared positive keys and natural ranks. Their decoded lists
    are passed to the existing checkers, so no correctness axiom or
    theorem about the decoder is needed for certificate soundness.
    All definitions use ordinary inductive Coq data. *)
From Coq Require Import List NArith Hexadecimal.
From BBB4 Require Import PosEnc Records.
Import ListNotations.

Definition hfd_digit (u:Hexadecimal.uint) : option (N * Hexadecimal.uint) :=
 match u with
 | Hexadecimal.Nil => None
 | Hexadecimal.D0 t => Some (0%N,t) | Hexadecimal.D1 t => Some (1%N,t)
 | Hexadecimal.D2 t => Some (2%N,t) | Hexadecimal.D3 t => Some (3%N,t)
 | Hexadecimal.D4 t => Some (4%N,t) | Hexadecimal.D5 t => Some (5%N,t)
 | Hexadecimal.D6 t => Some (6%N,t) | Hexadecimal.D7 t => Some (7%N,t)
 | Hexadecimal.D8 t => Some (8%N,t) | Hexadecimal.D9 t => Some (9%N,t)
 | Hexadecimal.Da t => Some (10%N,t) | Hexadecimal.Db t => Some (11%N,t)
 | Hexadecimal.Dc t => Some (12%N,t) | Hexadecimal.Dd t => Some (13%N,t)
 | Hexadecimal.De t => Some (14%N,t) | Hexadecimal.Df t => Some (15%N,t)
 end.
Fixpoint hfd_take (n:nat)(acc:N)(u:Hexadecimal.uint) : option (N * Hexadecimal.uint) :=
 match n with
 | O => Some(acc,u)
 | S k => match hfd_digit u with
          | None => None
          | Some(d,t) => hfd_take k (16*acc+d)%N t
          end
 end.
Definition hfd_hex(u:Number.uint):Hexadecimal.uint :=
 match u with Number.UIntHexadecimal t=>t | _=>Hexadecimal.Nil end.
Fixpoint hfd_pool_from {A:Type}(xs:list A)(i:positive)(pool:PositiveMap.tree A) :=
 match xs with []=>pool|x::xs=>hfd_pool_from xs (Pos.succ i)(PositiveMap.add i x pool)end.
Definition hfd_pool {A:Type}(xs:list A) := hfd_pool_from xs 1%positive (PositiveMap.empty A).
Definition hfd_get {A:Type}(pool:PositiveMap.tree A)(fallback:A)(i:N):A :=
 match i with
 | N0=>fallback
 | Npos p=>match PositiveMap.find p pool with Some v=>v|None=>fallback end
 end.
(** Positive key differences use little-endian base-eight digits; a nibble
    at least eight marks continuation. Each chunk starts again at key zero. *)
Fixpoint hfd_var(fuel:nat)(scale acc:N)(u:Hexadecimal.uint):option(N*Hexadecimal.uint) :=
 match fuel with
 | O=>None
 | S f=>match hfd_digit u with
        | None=>None
        | Some(d,t)=>if (d <? 8)%N then Some((acc+scale*d)%N,t)
                      else hfd_var f (8*scale)%N (acc+scale*(d-8))%N t
        end
 end.
Fixpoint hfd_dpairs(keys:PositiveMap.tree positive)(ranks:PositiveMap.tree nat)
 (fuel:nat)(previous:N)(u:Hexadecimal.uint):list(positive*nat) :=
 match fuel with
 | O=>[]
 | S f=>match hfd_var 6 1%N 0%N u with
        | Some(delta,t)=>match hfd_take 2 0%N t with
          | Some(v,rest)=>let k:=(previous+delta)%N in
              (hfd_get keys 1%positive k,hfd_get ranks 0 v)::hfd_dpairs keys ranks f k rest
          | None=>[] end
        | None=>[] end
 end.
Fixpoint hfd_dkeys(keys:PositiveMap.tree positive)(fuel:nat)(previous:N)
 (u:Hexadecimal.uint):list positive :=
 match fuel with
 | O=>[]
 | S f=>match hfd_var 6 1%N 0%N u with
        | Some(delta,t)=>let k:=(previous+delta)%N in
            hfd_get keys 1%positive k::hfd_dkeys keys f k t
        | None=>[] end
 end.
Definition hfd_dphi keys ranks(chunks:list Number.uint):list(positive*nat) :=
 concat(map(fun u=>hfd_dpairs keys ranks 128 0%N(hfd_hex u))chunks).
Definition hfd_dgate keys(chunks:list Number.uint):list positive :=
 concat(map(fun u=>hfd_dkeys keys 128 0%N(hfd_hex u))chunks).
