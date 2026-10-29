(* Untrusted certificate producer. Coq rechecks every returned graph and rank. *)
open Checkers
let symbol = function '0'->S0 | '1'->S1 | '2'->S2 | '3'->S3 | _->invalid_arg "symbol"
let state = function 'A'->StA | 'B'->StB | _->invalid_arg "state"
let qi = function StA->0 | StB->1
let si = function S0->0 | S1->1 | S2->2 | S3->3
let machine text =
  let cells=Array.init 8 (fun i -> let o=3*i+(if i>=4 then 1 else 0) in
    if String.sub text o 3="---" then None else Some {t_write=symbol text.[o];
    t_dir=(if text.[o+1]='R' then DR else DL);t_next=state text.[o+2]}) in
  fun q s->cells.(4*qi q+si s)
let rec pos n = if n=1 then XH else if n land 1=0 then XO(pos(n lsr 1)) else XI(pos(n lsr 1))
let num n = if n=0 then N0 else Npos(pos n)
let rec bits = function XH->"1" | XO x->bits x ^ "0" | XI x->bits x ^ "1"
let list f xs = "[" ^ String.concat "," (List.map f xs) ^ "]"
let int = string_of_int
let syms = list (fun x->int(si x))
let item x = "[" ^ syms x.it_w ^ "," ^ int x.it_c ^ "," ^ string_of_bool x.it_cap ^ "]"
let conf (q,((((li,lb),h),rb),ri)) =
  "[" ^ int(qi q) ^ "," ^ list item li ^ "," ^ syms lb ^ "," ^ int(si h) ^ "," ^ syms rb ^ "," ^ list item ri ^ "]"
let ck = function C1->"C1" | C2->"C2" | C3->"C3" | CN->"CN"
let meas = function RwNA c->"RwNA " ^ ck c | RwNL c->"RwNL " ^ ck c | RwNR c->"RwNR " ^ ck c | RwZL->"RwZL" | RwZR->"RwZR"
let key p = "\"" ^ bits p ^ "\""
let phi = list (fun (p,n)->"[" ^ key p ^ "," ^ int n ^ "]")
let comp = function
 | RwRankE p -> "[\"rank\"," ^ phi p ^ "]"
 | RwMeasE(m,k,p,g)->"[\"meas\",\"" ^ meas m ^ "\"," ^ int k ^ "," ^ phi p ^ "," ^ list key g ^ "]"
let () =
  if Array.length Sys.argv<>7 then invalid_arg "MACHINE BOUND L T ANCHOR FUEL";
  let tm=machine Sys.argv.(1) and b=num(int_of_string Sys.argv.(2))
  and l=int_of_string Sys.argv.(3) and t=int_of_string Sys.argv.(4)
  and a=int_of_string Sys.argv.(5) and f=int_of_string Sys.argv.(6) in
  let cc=match csteps tm a c0 with Some c->c | _->failwith "prefix" in
  let seed=rw_seed l t cc in
  let sl=match close_tr rconf_enc (rw_succs tm l t) f [] PositiveSet.empty [seed] with Some s->s | _->failwith "closure" in
  let instrs=[StA,S0;StA,S1;StA,S2;StA,S3;StB,S0;StB,S1;StB,S2;StB,S3] in
  let cs=List.map (fun tg -> if List.exists (fun c -> rw_instr c = tg) sl then rw_rank_procedure tm l t sl tg else []) instrs in
  let get tg=List.nth cs (4*qi(fst tg)+si(snd tg)) in
  if not(closed_tr_b rconf_enc (rw_succs tm l t) sl && mem_tr rconf_enc seed sl &&
    prefix_gate b b tm a (tail_states(labels rw_instr sl)) (tail_instrs(labels rw_instr sl)) &&
    live_lex_ok_tr rconf_enc rw_instr (rw_succs tm l t) sl (fun tg->List.map (rw_comp_denote tm) (get tg))) then failwith "verification";
  print_endline("{\"graph\":" ^ list conf sl ^ ",\"ranks\":" ^ list (list comp) cs ^ "}")
