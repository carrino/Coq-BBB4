(* Untrusted preselection only. Every accepted row is replayed in Coq.
   Zarith is used solely to parse exact decimal integers into extracted Z. *)
module Big = Z
open Checker

let symbol = function '0'->S0 | '1'->S1 | '2'->S2 | '3'->S3
  | _ -> invalid_arg "symbol"
let state = function "A"->StA | "B"->StB | _->invalid_arg "state"
let direction = function 'L'->DL | 'R'->DR | _->invalid_arg "direction"
let state_index = function StA->0 | StB->1
let symbol_index = function S0->0 | S1->1 | S2->2 | S3->3
let nat text = let n=int_of_string text in if n<0 then invalid_arg "negative nat" else n
let sym text = if String.length text=1 then symbol text.[0] else invalid_arg "symbol"
let rec positive big =
  if Big.equal big Big.one then XH else
  let rest=positive (Big.shift_right big 1) in
  if Big.testbit big 0 then XI rest else XO rest
let z text = let n=Big.of_string text in
  match Big.sign n with 0->Z0 | 1->Zpos(positive n) | _->Zneg(positive (Big.neg n))
let n_of_int n = if n=0 then N0 else Npos(positive (Big.of_int n))
let machine text =
  if String.length text<>25 || text.[12]<>'_' then invalid_arg "machine dimensions";
  let cells=Array.init 8 (fun i ->
    let off=3*i+(if i>=4 then 1 else 0) in
    let cell=String.sub text off 3 in
    if cell="---" then None else Some {t_write=symbol cell.[0];
      t_dir=direction cell.[1];t_next=state (String.make 1 cell.[2])}) in
  fun q s -> cells.(4*state_index q+symbol_index s)
let add_unique table key value =
  if Hashtbl.mem table key then invalid_arg "duplicate field/index";
  Hashtbl.add table key value
let bindings table = List.sort (fun (a,_) (b,_) -> Stdlib.compare a b)
    (Hashtbl.fold (fun key value rest -> (key,value)::rest) table [])
let values table = List.map snd (bindings table)
type rule_data = { q:st; h:sym; left:(int,bRRunP) Hashtbl.t;
  right:(int,bRRunP) Hashtbl.t; mutable pfx:bool*bool }
exception Unsupported
let certificate path identity =
  let scalars=Hashtbl.create 16 and blocks=Hashtbl.create 16
  and left=Hashtbl.create 8 and right=Hashtbl.create 8 and rules=Hashtbl.create 8 in
  let side side l r = match side with "L"->l | "R"->r | _->invalid_arg "side" in
  let flag = function "0"->false | "1"->true | _->invalid_arg "prefix flag" in
  let input=open_in path in
  Fun.protect (fun () ->
    try while true do
      let parts=String.split_on_char ' ' (String.trim (input_line input))
                |> List.filter (fun s->s<>"") in
      match parts with
      | [] -> ()
      | ["bbbcert";_] | ["end"] -> ()
      | ["type";"irules"] -> ()
      | ["blk";id;word] ->
          add_unique blocks (nat id) (List.init (String.length word) (fun i->symbol word.[i]))
      | ["tplrun";s;i;id;a;b] ->
          add_unique (side s left right) (nat i) ((nat id,z a),z b)
      | ["rule";i;q;h;_;_] ->
          add_unique rules (nat i) {q=state q;h=sym h;left=Hashtbl.create 8;
            right=Hashtbl.create 8;pfx=(false,false)}
      | ["rulepfx";i;l;r] -> (Hashtbl.find rules (nat i)).pfx <- (flag l,flag r)
      | ["rulerun";i;s;j;id;"C";v] ->
          let rule=Hashtbl.find rules (nat i) in
          add_unique (side s rule.left rule.right) (nat j) (nat id,BC(z v))
      | ["rulerun";i;s;j;id;"V";d;lb] ->
          let rule=Hashtbl.find rules (nat i) in
          add_unique (side s rule.left rule.right) (nat j) (nat id,BV(z d,z lb))
      | ["rulerunm";i;s;j;id;d;lb;md;rs] ->
          let rule=Hashtbl.find rules (nat i) in
          add_unique (side s rule.left rule.right) (nat j) (nat id,BVm(z d,z lb,z md,z rs))
      | ("nvar"|"mmrow"|"xmin"|"x0"|"tplrunmv")::_ -> raise Unsupported
      | key::_ when String.length key>=6 && String.sub key 0 6="claim_" -> ()
      | [key;_] when List.mem key ["decided_at_step";"tpl_left";"tpl_right";"nrules"] -> ()
      | [key;value] when List.mem key ["machine";"anchor_step";"k0";"kmin";"meta_a";
             "meta_b";"tpl_state";"tpl_hsym"] ->
          add_unique scalars key value; if key="machine" then identity:=value
      | _ -> invalid_arg "unsupported certificate syntax"
    done with End_of_file -> ()) ~finally:(fun ()->close_in input);
  let get=Hashtbl.find scalars in
  let name=get "machine" in
  let tm=machine name in
  let cert={cp_anchor=nat(get "anchor_step");cp_k0=z(get "k0");cp_kmin=z(get "kmin");
    cp_a=z(get "meta_a");cp_b=z(get "meta_b");cp_st=state(get "tpl_state");
    cp_hs=sym(get "tpl_hsym");cp_blks=bindings blocks;cp_TL=values left;cp_TR=values right;
    cp_rules=List.map (fun r->{brp_st=r.q;brp_hs=r.h;brp_L=values r.left;
      brp_R=values r.right;brp_pfx=r.pfx}) (values rules)} in
  name,tm,cert

exception Row_timeout
let timed seconds f =
  ignore(Unix.setitimer Unix.ITIMER_REAL {Unix.it_interval=0.;it_value=seconds});
  Fun.protect f ~finally:(fun ()->ignore(Unix.setitimer Unix.ITIMER_REAL
    {Unix.it_interval=0.;it_value=0.}))
let () =
  if Array.length Sys.argv<>6 then begin
    prerr_endline "usage: affine_probe BOUND CFUEL FUEL TIMEOUT CERT_PATHS";exit 2
  end;
  let bound_i=nat Sys.argv.(1) and cfuel=nat Sys.argv.(2) and fuel=nat Sys.argv.(3)
  and seconds=float_of_string Sys.argv.(4) in
  if bound_i=0 || cfuel=0 || fuel=0 || seconds<=0. then invalid_arg "positive budgets required";
  let bound=n_of_int bound_i in
  Sys.set_signal Sys.sigalrm (Sys.Signal_handle (fun _->raise Row_timeout));
  let input=open_in Sys.argv.(5) in
  print_endline "certificate\tmachine\tstatus\tseconds";
  (try while true do
    let path=input_line input in
    let name=ref "" and start=Unix.gettimeofday() in
    let status=try timed seconds (fun ()->
      let m,tm,cert=certificate path name in name:=m;
      if cert.cp_anchor>bound_i then "anchor_exceeds_bound"
      else if ir_check bound bound tm cert cfuel fuel then "replay_true" else "replay_false")
      with Unsupported->"unsupported" | Row_timeout->"timeout" | Stack_overflow->"stack_overflow"
      | Invalid_argument _ | Failure _ | Not_found | Sys_error _ ->"invalid_certificate" in
    Printf.printf "%s\t%s\t%s\t%.6f\n%!" path !name status (Unix.gettimeofday()-.start)
  done with End_of_file->close_in input)
