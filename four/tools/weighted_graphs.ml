(* Search only. Finite/history use state=false, so acceptance targets BOTH
   state and instruction bounds. Arbitrary positive/N/Z values remain exact. *)
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


let nums xs = "[" ^ String.concat "," (List.map string_of_int xs) ^ "]"
let node (q,((l,h),r)) = Printf.sprintf "[%d,%s,%d,%s]" (state_index q)
  (nums(List.map symbol_index l)) (symbol_index h) (nums(List.map symbol_index r))
exception Row_timeout
let timed seconds f =
 ignore(Unix.setitimer Unix.ITIMER_REAL {Unix.it_interval=0.;it_value=seconds});
 Fun.protect f ~finally:(fun()->ignore(Unix.setitimer Unix.ITIMER_REAL {Unix.it_interval=0.;it_value=0.}))
let symbols=[|S0;S1;S2;S3|]
let states=[|StA;StB|]
let () =
 if Array.length Sys.argv<>7 then failwith "usage: dump INPUT WIDTH ANCHOR FUEL ROUNDS TIMEOUT";
 let input=open_in Sys.argv.(1) and n=int_of_string Sys.argv.(2)
 and t=int_of_string Sys.argv.(3) and fuel=int_of_string Sys.argv.(4)
 and rounds=int_of_string Sys.argv.(5) and timeout=float_of_string Sys.argv.(6) in
 Sys.set_signal Sys.sigalrm(Sys.Signal_handle(fun _->raise Row_timeout));
 let processed=ref 0 and closed=ref 0 and failed=ref 0 and ranked_all=ref 0 in
 (try while true do
 let name=input_line input in let base=machine name in incr processed;
 for mirrored=0 to 1 do try timed timeout(fun()->
 let tm=if mirrored=1 then mirror_tm base else base in
 match csteps tm t c0 with None->()|Some((_,((l,_),r)) as cc)->
 let a0=ng_start n cc in
 let ls,rs=ng_grow tm a0 fuel rounds(gadds(ng_seed_side n l)gempty)(gadds(ng_seed_side n r)gempty)in
 let sl=ng_explore tm ls rs fuel [] PositiveSet.empty[a0]in
 if ng_seed_ok n ls rs cc && closed_tr_b cconf_enc(ng_succs tm ls rs)sl && mem_tr cconf_enc a0 sl then (
 incr closed;
 let ranked=List.filter(fun i->let tg=states.(i/4),symbols.(i mod 4)in
 not(appears_tr cinstr sl tg) ||
 rank_ok_tr cinstr(ng_succs tm ls rs)sl tg(compute_ranks_tr cconf_enc cinstr(ng_succs tm ls rs)sl tg) ||
 lex_ok_tr cinstr(ng_succs tm ls rs)sl tg(List.map(ng_comp_denote tm n)(rank_procedure tm ls rs sl tg)))
 (List.init 8 Fun.id)in
 if List.length ranked=8 then incr ranked_all else (
 let indices=Hashtbl.create(List.length sl)in List.iteri(fun i c->Hashtbl.add indices c i)sl;
 let edges=List.map(fun a->match ng_succs tm ls rs a with Some xs->nums(List.map(Hashtbl.find indices)xs)|None->failwith"halt")sl in
 let trans=List.init 8(fun i->match tm states.(i/4) symbols.(i mod 4)with None->"null"|Some tr->
 nums[symbol_index tr.t_write;(if tr.t_dir=DR then 1 else -1);state_index tr.t_next])in
 Printf.printf "{\"machine\":\"%s\",\"mirror\":%d,\"n\":%d,\"t\":%d,\"fuel\":%d,\"rounds\":%d,\"states\":2,\"symbols\":4,\"nodes\":[%s],\"edges\":[%s],\"trans\":[%s],\"ranked\":%s}\n%!"
 name mirrored n t fuel rounds(String.concat ","(List.map node sl))(String.concat "," edges)(String.concat "," trans)(nums ranked)
 ))
 ) with Row_timeout|Stack_overflow->incr failed done
 done with End_of_file->close_in input);
 Printf.eprintf "processed=%d closed_orientations=%d already_ranked=%d timeouts=%d\n%!" !processed !closed !ranked_all !failed
