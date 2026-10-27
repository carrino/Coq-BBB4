(* Untrusted supplied-history certificate producer. Every emitted graph and rank
   is rechecked in Coq; this executable is never proof evidence. *)
(* State-only search. All acceptance is replayed through StatePipeline.stp_check. *)
open Checkers

let symbol = function
  | '0' -> S0 | '1' -> S1 | '2' -> S2 | '3' -> S3
  | _ -> invalid_arg "symbol must be 0..3"
let state = function
  | 'A' -> StA | 'B' -> StB | _ -> invalid_arg "state must be A or B"
let state_index = function StA -> 0 | StB -> 1
let symbol_index = function S0 -> 0 | S1 -> 1 | S2 -> 2 | S3 -> 3
let machine text =
  if String.length text <> 25 || text.[12] <> '_' then
    invalid_arg "expected two rows of four transitions";
  let cells = Array.init 8 (fun i ->
    let off = 3 * i + if i >= 4 then 1 else 0 in
    let cell = String.sub text off 3 in
    if cell = "---" then None else
    let t_write = symbol cell.[0]
    and t_dir = match cell.[1] with
      | 'L' -> DL | 'R' -> DR | _ -> invalid_arg "direction must be L or R"
    and t_next = state cell.[2] in
    Some { t_write; t_dir; t_next }) in
  fun q s -> cells.(4 * state_index q + symbol_index s)

let rec positive_of_int n =
  if n = 1 then XH else if n land 1 = 0 then XO (positive_of_int (n lsr 1))
  else XI (positive_of_int (n lsr 1))
let n_of_int n = if n = 0 then N0 else Npos (positive_of_int n)

let cell (s,h) =
 let rec hist = function []->0 | (q,s)::tail -> 1+4*state_index q+symbol_index s+8*hist tail in
 4*hist h+symbol_index s
let list f xs = "[" ^ String.concat "," (List.map f xs) ^ "]"
let integer = string_of_int
let cells xs = list (fun x -> integer(cell x)) xs
let node (q,((l,h),r)) = Printf.sprintf "[%d,%s,%d,%s]" (state_index q) (cells l) (cell h) (cells r)
let meas = function MAll x -> 0,x | MLeft x -> 1,x | MRight x -> 2,x
let kind = function C1->0 | C2->1 | C3->2 | CN->3
let () =
 if Array.length Sys.argv <> 7 then failwith "usage: export K N ANCHOR FUEL ROUNDS INPUT";
 let k=int_of_string Sys.argv.(1) and n=int_of_string Sys.argv.(2) and t=int_of_string Sys.argv.(3) and fuel=int_of_string Sys.argv.(4) and rounds=int_of_string Sys.argv.(5) in
 if k<0 || n<1 || t<0 || fuel<1 || rounds<1 then invalid_arg "invalid history parameters";
 let ic=open_in Sys.argv.(6) in
 try while true do
 let text=input_line ic in let tm=machine text in
 let cc=Option.get(hcsteps tm k t hcconf0) in
 let _,((l,_),r)=cc in let a0=hng_start n cc in
 let ls,rs=hn_grow tm k n a0 fuel rounds (hseed_side n l)(hseed_side n r) in
 let ls=List.sort_uniq compare ls and rs=List.sort_uniq compare rs in
 let nodes=hn_explore tm k n ls rs fuel [] PositiveSet.empty [a0] in
 let tab=Hashtbl.create(List.length nodes) in List.iteri(fun i a->Hashtbl.add tab a i)nodes;
 let index a=Hashtbl.find tab a in
 let rank phi=list(fun(a,n)->Printf.sprintf "[%d,%d]" (index a)n)(List.filter(fun(_,n)->n<>0)phi) in
 let comp = function HnRank phi -> "[0,"^rank phi^"]"
  | HnMeas(m,v,phi,gate)->let typ,c=meas m in
    Printf.sprintf "[1,%d,%d,%d,%s,%s]" typ(kind c)v(rank phi)(list(fun a->integer(index a))gate) in
 let cert q =
  let astate a=fst(hainstr a) in let succ=hng_succs tm k n ls rs in
  if not(appears astate nodes q) then [] else
  let ranks=compute_ranks hctx_enc astate succ nodes q in
  let cert=if rank_ok astate succ nodes q ranks then [HnRank(List.map(fun a->a,ranks a)nodes)]
   else hn_rank_procedure tm k n ls rs nodes(fun a->fst a=q) in
  if not(lex_ok astate succ nodes q(hn_components tm cert)) then failwith "supplied lex rejected";
  cert in
 let ca=cert StA and cb=cert StB in
 Printf.printf "{\"machine\":\"%s\",\"nodes\":%s,\"ls\":%s,\"rs\":%s,\"ca\":%s,\"cb\":%s}\n%!"
 text(list node nodes)(list cells ls)(list cells rs)(list comp ca)(list comp cb)
 done with End_of_file->close_in ic
