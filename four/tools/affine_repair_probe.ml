(* Untrusted certificate search: strengthen lower bounds, remove unnecessary
   rules, or complete a block dictionary. Every success still needs Coq replay. *)
open Checker
open Affine_cert_io

let rec big_positive = function
  | XH->Big.one | XO p->Big.shift_left (big_positive p) 1
  | XI p->Big.succ (Big.shift_left (big_positive p) 1)
let big_z = function Z0->Big.zero | Zpos p->big_positive p | Zneg p->Big.neg(big_positive p)
let from_big n = match Big.sign n with 0->Z0 | 1->Zpos(positive n) | _->Zneg(positive(Big.neg n))
let sym_text = function S0->"0" | S1->"1" | S2->"2" | S3->"3"
let state_text = function StA->"A" | StB->"B"
let z_text n = Big.to_string(big_z n)
let write_cert path name c =
  let out=open_out path in
  Fun.protect (fun () ->
    Printf.fprintf out "bbbcert v7\nmachine %s\ntype irules\n" name;
    List.iter (fun (i,w)->Printf.fprintf out "blk %d %s\n" i
      (String.concat "" (List.map sym_text w))) c.cp_blks;
    Printf.fprintf out "anchor_step %d\nk0 %s\nkmin %s\nmeta_a %s\nmeta_b %s\ntpl_state %s\ntpl_hsym %s\n"
      c.cp_anchor (z_text c.cp_k0) (z_text c.cp_kmin) (z_text c.cp_a) (z_text c.cp_b)
      (state_text c.cp_st) (sym_text c.cp_hs);
    let template side runs =
      Printf.fprintf out "tpl_%s %d\n" (if side="L" then "left" else "right") (List.length runs);
      List.iteri (fun i ((s,a),b)->Printf.fprintf out "tplrun %s %d %d %s %s\n"
        side i s (z_text a) (z_text b)) runs in
    template "L" c.cp_TL; template "R" c.cp_TR;
    Printf.fprintf out "nrules %d\n" (List.length c.cp_rules);
    List.iteri (fun i r->
      Printf.fprintf out "rule %d %s %s %d %d\nrulepfx %d %d %d\n" i
        (state_text r.brp_st) (sym_text r.brp_hs) (List.length r.brp_L) (List.length r.brp_R)
        i (if fst r.brp_pfx then 1 else 0) (if snd r.brp_pfx then 1 else 0);
      let side s runs=List.iteri (fun j (id,count)->match count with
        | BC v->Printf.fprintf out "rulerun %d %s %d %d C %s\n" i s j id (z_text v)
        | BV(d,lb)->Printf.fprintf out "rulerun %d %s %d %d V %s %s\n" i s j id (z_text d) (z_text lb)
        | BVm(d,lb,md,rs)->Printf.fprintf out "rulerunm %d %s %d %d %s %s %s %s\n"
            i s j id (z_text d) (z_text lb) (z_text md) (z_text rs)) runs in
      side "L" r.brp_L;side "R" r.brp_R) c.cp_rules;
    output_string out "end\n") ~finally:(fun()->close_out out)

let minimums c =
  let lo=big_z c.cp_kmin and hi=big_z c.cp_k0 in
  let candidates=Big.succ lo::hi::List.map Big.of_int [1;2;3;4;6;8;12;16;24;32;64;128] in
  List.sort_uniq Big.compare candidates
    |> List.filter(fun k->Big.compare k lo>0 && Big.compare k hi<=0)
    |> List.map from_big
let raise_rules k rules =
  let raise_lb lb=if Big.compare(big_z lb)(big_z k)<0 then k else lb in
  let side=List.map(fun (id,c)->id,match c with
    | BC _->c | BV(d,lb)->BV(d,raise_lb lb)
    | BVm(d,lb,md,rs)->BVm(d,raise_lb lb,md,rs)) in
  List.map(fun r->{r with brp_L=side r.brp_L;brp_R=side r.brp_R}) rules
let dictionary tm c rotations =
  let seen=Hashtbl.create 128 and queue=Queue.create() and additions=ref [] in
  List.iter(fun (_,w)->if not(Hashtbl.mem seen w) then
    (Hashtbl.add seen w ();Queue.add w queue)) c.cp_blks;
  let next=ref(1+List.fold_left(fun acc (i,_)->max acc i) 3 c.cp_blks) in
  let add w =
    if List.length w>1 && List.length w<=32 && Hashtbl.length seen<128 && not(Hashtbl.mem seen w) then
      (Hashtbl.add seen w ();Queue.add w queue;additions:=(!next,w)::!additions;incr next) in
  while not(Queue.is_empty queue) do
    let w=Queue.take queue in
    (if rotations then begin
      add(List.rev w);
      let rec rotate n current = if n>0 then match current with []->()|x::xs->
        let rotated=xs@[x] in add rotated;rotate(n-1) rotated in
      rotate (List.length w-1) w
    end);
    match w with []->() | h::rest->
      List.iter(fun q->List.iter(fun direction->
        match hop_sim tm q direction 1024 q [] h rest with
        | None->() | Some(hout,_)->add(firstn(prim_root_len hout) hout)) [DL;DR]) [StA;StB]
  done;
  {c with cp_blks=c.cp_blks@List.rev !additions}

exception Found of string*bIRCertP
exception Row_timeout
let repair tm cert bound cfuel fuel mode =
  let attempt label c = if ir_check bound bound tm c cfuel fuel then raise(Found(label,c)) in
  let mins=minimums cert in
  (try
    List.iter(fun k->attempt "raise_kmin" {cert with cp_kmin=k}) mins;
    if cert.cp_rules<>[] then begin
      attempt "remove_rules" {cert with cp_rules=[]};
      List.iter(fun flags->attempt "weaken_prefix" {cert with cp_rules=
        List.map(fun r->{r with brp_pfx=flags}) cert.cp_rules}) [(false,false);(true,false);(false,true)];
      List.iter(fun k->attempt "raise_rule_bounds" {cert with cp_kmin=k;
        cp_rules=raise_rules k cert.cp_rules}) mins
    end;
    if mode="blocks" && cert.cp_blks<>[] then
      List.iter(fun rotations->
        let expanded=dictionary tm cert rotations in
        if List.length expanded.cp_blks>List.length cert.cp_blks then begin
          attempt "complete_dictionary" expanded;
          List.iter(fun k->attempt "dictionary_kmin" {expanded with cp_kmin=k}) mins;
          attempt "dictionary_no_rules" {expanded with cp_rules=[]};
          List.iter(fun flags->attempt "dictionary_prefix" {expanded with cp_rules=
            List.map(fun r->{r with brp_pfx=flags}) expanded.cp_rules}) [(false,false);(true,false);(false,true)]
        end) [false;true];
    None
  with Found(label,c)->Some(label,c))
let () =
  if Array.length Sys.argv<>8 then begin
    prerr_endline "usage: affine_repair_probe BOUND CFUEL FUEL TIMEOUT fast|blocks CERT_PATHS OUTPUT_DIR";exit 2
  end;
  let bound_i=nat Sys.argv.(1) and cfuel=nat Sys.argv.(2) and fuel=nat Sys.argv.(3)
  and seconds=float_of_string Sys.argv.(4) and mode=Sys.argv.(5) in
  if bound_i=0||cfuel=0||fuel=0||seconds<=0.||not(List.mem mode ["fast";"blocks"]) then
    invalid_arg "invalid repair budget";
  let bound=n_of_int bound_i in
  Sys.set_signal Sys.sigalrm (Sys.Signal_handle(fun _->raise Row_timeout));
  let input=open_in Sys.argv.(6) in
  print_endline "certificate\tmachine\tstatus\tstrategy\tseconds";
  (try while true do
    let path=input_line input and identity=ref "" and strategy=ref "" in
    let start=Unix.gettimeofday() in
    let status=try
      ignore(Unix.setitimer Unix.ITIMER_REAL {Unix.it_interval=0.;it_value=seconds});
      Fun.protect(fun()->
        let name,tm,c=certificate path identity in
        match repair tm c bound cfuel fuel mode with
        | None->"replay_false"
        | Some(label,repaired)->strategy:=label;
            write_cert(Filename.concat Sys.argv.(7) (name^".cert")) name repaired;"repaired_candidate")
        ~finally:(fun()->ignore(Unix.setitimer Unix.ITIMER_REAL {Unix.it_interval=0.;it_value=0.}))
      with Unsupported->"unsupported" | Row_timeout->"timeout" | Stack_overflow->"stack_overflow"
      | Invalid_argument _ | Failure _ | Not_found | Sys_error _ ->"invalid_certificate" in
    Printf.printf "%s\t%s\t%s\t%s\t%.6f\n%!" path !identity status !strategy (Unix.gettimeofday()-.start)
  done with End_of_file->close_in input)
