(* Search only: expose closed contexts for ordinary candidate templates.
   Every resulting target must pass a Coq weighted-tail or suffix checker. *)
open Weighted_v2
let si=function S0->0|S1->1|S2->2|S3->3
let qi=function StA->0|StB->1
let sym=function '0'->S0|'1'->S1|'2'->S2|'3'->S3|_->invalid_arg "symbol"
let state=function 'A'->StA|'B'->StB|_->invalid_arg "state"
let machine text=
 if String.length text<>25 || text.[12]<>'_' then invalid_arg "machine";
 let table=Array.init 8(fun i->let off=3*i+(if i>=4 then 1 else 0)in
 let cell=String.sub text off 3 in if cell="---" then None else
 Some{t_write=sym cell.[0];t_dir=(match cell.[1]with 'L'->DL|'R'->DR|_->invalid_arg "direction");t_next=state cell.[2]})in
 fun q s->table.(4*qi q+si s)
let word xs=String.concat ""(List.map(fun s->string_of_int(si s))xs)
let node(q,((l,h),r))="\""^(if q=StA then "A" else "B")^word l^string_of_int(si h)^word r^"\""
exception Row_timeout
let active=ref false
let cleanup()=active:=false;ignore(Unix.setitimer Unix.ITIMER_REAL{Unix.it_interval=0.;it_value=0.})
let ()=
 if Array.length Sys.argv<>3 then failwith "usage: ordinary_template_graphs INPUT TIMEOUT";
 let timeout=float_of_string Sys.argv.(2)in
 if not(timeout>0. && timeout<infinity)then invalid_arg "timeout";
 Sys.set_signal Sys.sigalrm(Sys.Signal_handle(fun _->if !active then raise Row_timeout));
 let input=open_in Sys.argv.(1)in
 try while true do
 let line=input_line input in
 match String.split_on_char '\t' line with
 |[name;mirror;width;boot;budget;growth]->
 let mirrored=int_of_string mirror and n=int_of_string width and t=int_of_string boot
 and fuel=int_of_string budget and rounds=int_of_string growth in
 if (mirrored<>0 && mirrored<>1)||n<1||n>8||t<0||t>4096||fuel<1||rounds<1 then invalid_arg "parameters";
 let base=machine name in let tm=if mirrored=1 then mirror_tm base else base in
 let status,sl=try
 active:=true;ignore(Unix.setitimer Unix.ITIMER_REAL{Unix.it_interval=0.;it_value=timeout});
 let result=match csteps tm t c0 with None->"halt",[]|Some((_,((l,_),r))as cc)->
 let a0=ng_start n cc in
 let ls,rs=ng_grow tm a0 fuel rounds(gadds(ng_seed_side n l)gempty)(gadds(ng_seed_side n r)gempty)in
 let sl=ng_explore tm ls rs fuel[]PositiveSet.empty[a0]in
 if ng_seed_ok n ls rs cc && closed_tr_b cconf_enc(ng_succs tm ls rs)sl && mem_tr cconf_enc a0 sl
 then "closed",sl else "open",[]in cleanup();result
 with Row_timeout->cleanup();"timeout",[]|Stack_overflow->cleanup();"stack_overflow",[]in
 Printf.printf "{\"machine\":\"%s\",\"status\":\"%s\",\"nodes\":[%s]}\n%!" name status(String.concat ","(List.map node sl))
 |_->invalid_arg "input row"
 done with End_of_file->close_in input
