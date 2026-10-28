(* Untrusted data reader for extracted weighted-tail Boolean checks.
   Output is candidate selection only; Coq replays every retained success. *)
open Weighted_tail
let () =
 if Array.length Sys.argv<>2 then failwith "usage: weighted_tail_selector DATA";
 let ic=open_in_bin Sys.argv.(1)in let text=really_input_string ic(in_channel_length ic)in close_in ic;
 let offset=ref 0 and size=String.length text in
 let space=function ' '|'\n'|'\r'|'\t'->true|_->false in
 let token()=
 while !offset<size && space text.[!offset]do incr offset done;
 if !offset=size then failwith "unexpected end of data";
 let start= !offset in while !offset<size && not(space text.[!offset])do incr offset done;
 String.sub text start(!offset-start)in
 let nat()=let v=int_of_string(token())in if v<0 then failwith "negative natural";v in
 let bool()=match token()with"0"->false|"1"->true|_->failwith "boolean"in
 let sym()=match nat()with 0->S0|1->S1|2->S2|3->S3|_->failwith "symbol"in
 let state()=match nat()with 0->StA|1->StB|_->failwith "state"in
 let list f()=let n=nat()in if n>1000000 then failwith "list budget";
 let rec loop n=if n=0 then[]else let x=f()in x::loop(n-1)in loop n in
 let word=list sym in
 let node()=let q=state()in let l=word()in let h=sym()in let r=word()in(q,((l,h),r))in
 let pos bits start=
 if start>=String.length bits||bits.[start]<>'1'then failwith "positive";
 let p=ref XH in for i=start+1 to String.length bits-1 do
 p:=(match bits.[i]with '0'->XO !p|'1'->XI !p|_->failwith "bit")done;!p in
 let z()=let bits=token()in if bits="0"then Z0 else if bits.[0]='-'then Zneg(pos bits 1)else Zpos(pos bits 0)in
 let bound=Npos(XO(XO(XO(XO(XO(XO(XO(XO(XO(XO(XO(XO XH))))))))))))in
 let templates=nat()in
 for _=1 to templates do
 let codes=list nat()in if List.length codes<>8 then failwith "table width";
 let width=nat()in let left=list word()in let right=list word()in let nodes=list node()in
 let component()=match nat()with
 |0->let values=list nat()in WRank(wc_table 0 nodes values)
 |1->
 let count()=let weight=nat()in let side=nat()in
 let kind=match nat()with 1->C1|2->C2|3->C3|_->failwith "count kind"in
 let measure=match side with 0->MAll kind|1->MLeft kind|2->MRight kind|_->failwith "side"in(weight,measure)in
 let counts=list count()in let values=list nat()in let flags=list bool()in
 WLinear(counts,wc_table 0 nodes values,wc_table false nodes flags)
 |2->let scores=Array.init 16(fun _->z())in let values=list z()in let flags=list bool()in
 let score i=wc_score scores.(i)scores.(i+1)scores.(i+2)scores.(i+3)in
 WBinary(score 0,score 4,score 8,score 12,wc_table Z0 nodes values,wc_table false nodes flags)
 |_->failwith "component kind"in
 let certs=Array.make 8 None in let count=nat()in
 for _=1 to count do
 let target=nat()in if target>=8||certs.(target)<>None then failwith "certificate target";
 let k=nat()in let guards=list word()in let inside=list node()in let components=list component()in
 certs.(target)<-Some{wc_k=k;wc_guards=guards;wc_inside=inside;wc_components=components}
 done;
 let qi=function StA->0|StB->1 and si=function S0->0|S1->1|S2->2|S3->3 in
 let tail={wt_source=machine_of_codes codes;wt_width=width;wt_left=gadds left gempty;wt_right=gadds right gempty;
 wt_nodes=nodes;wt_cert=(fun(q,s)->certs.(4*qi q+si s))}in
 let row()=let codes=list nat()in if List.length codes<>8 then failwith "row table width";
 let mirrored=bool()in let boot=nat()in{reuse_codes=codes;reuse_mirrored=mirrored;reuse_boot=boot}in
 let rows=list row()in
 List.iter(fun b->print_endline(string_of_bool b))(wt_hybrid_results bound bound tail rows)
 done;
 while !offset<size && space text.[!offset]do incr offset done;
 if !offset<>size then failwith "trailing data"
