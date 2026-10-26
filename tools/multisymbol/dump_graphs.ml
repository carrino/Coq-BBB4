open Smallbb
let codes ns s =
  let s=String.concat "" (String.split_on_char '_' s) in
  List.init (String.length s / 3) (fun i -> if s.[3*i]='-' then 6*ns else
  2*ns*(Char.code s.[3*i]-48)+(if s.[3*i+1]='R' then ns else 0)+Char.code s.[3*i+2]-65)
let si = function S0->0|S1->1|S2->2
let qi = function StA->0|StB->1|StC->2
let nums xs = "[" ^ String.concat "," (List.map string_of_int xs) ^ "]"
let node (q,((l,h),r)) = Printf.sprintf "[%d,%s,%d,%s]" (qi q) (nums(List.map si l)) (si h) (nums(List.map si r))
let () =
  let input=open_in Sys.argv.(1) in
  let ns=int_of_string Sys.argv.(2) and ms=int_of_string Sys.argv.(3)
  and n=int_of_string Sys.argv.(4) and t=int_of_string Sys.argv.(5) in
  try while true do
    let name=input_line input in let tm=machine_of_codes ns ms (codes ns name) in
    for mirrored=0 to 1 do
    let tm=if mirrored=1 then mirror_tm tm else tm in
    match csteps tm t c0 with None->() | Some ((q,((l,h),r)) as cc)->
      let a0=ng_start n cc in
      let ls,rs=ng_grow tm a0 4096 32 (gadds(ng_seed_side n l)gempty)(gadds(ng_seed_side n r)gempty) in
      let sl=ng_explore tm ls rs 4096 [] PositiveSet.empty [a0] in
      if closed_tr_b cconf_enc (ng_succs tm ls rs) sl && mem_tr cconf_enc a0 sl then (
      let index a=let rec go i=function []->failwith "edge"|b::xs->if a=b then i else go(i+1)xs in go 0 sl in
      let edges=List.map(fun a->match ng_succs tm ls rs a with Some xs->nums(List.map index xs)|None->failwith "halt")sl in
      let trans=List.init (ns*ms) (fun i->let q=if i/ms=0 then StA else if i/ms=1 then StB else StC in let s=if i mod ms=0 then S0 else if i mod ms=1 then S1 else S2 in match tm q s with None->"null"|Some tr->nums[si tr.t_write;(if tr.t_dir=DR then 1 else -1);qi tr.t_next]) in
      Printf.printf "{\"machine\":\"%s\",\"mirror\":%d,\"n\":%d,\"t\":%d,\"states\":%d,\"symbols\":%d,\"nodes\":[%s],\"edges\":[%s],\"trans\":[%s],\"ranked\":%s}\n%!" name mirrored n t ns ms (String.concat "," (List.map node sl)) (String.concat "," edges) (String.concat "," trans)
      (nums (List.filter(fun i->let tg=(if i/ms=0 then StA else if i/ms=1 then StB else StC),(if i mod ms=0 then S0 else if i mod ms=1 then S1 else S2) in not(appears_tr cinstr sl tg) || (rank_ok_tr cinstr (ng_succs tm ls rs) sl tg (compute_ranks_tr cconf_enc cinstr (ng_succs tm ls rs) sl tg)) || lex_ok_tr cinstr (ng_succs tm ls rs) sl tg (List.map (ng_comp_denote tm n) (rank_procedure tm ls rs sl tg))) (List.init(ns*ms)(fun i->i)))))
    done
  done with End_of_file->()
