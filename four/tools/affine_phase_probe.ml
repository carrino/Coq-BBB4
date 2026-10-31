(* Untrusted phase search: shift an affine template along its symbolic run,
   locate the shifted template in the concrete prefix, and retry ir_check.
   Every successful certificate still needs the unchanged Coq checker. *)
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

(* Hashing only selects a candidate anchor; ir_check subsequently verifies the
   complete concrete tapes. A collision cannot create a checked certificate. *)
let prime1=1000000007 and prime2=1000000009
let mul p a b=(a*b) mod p
let rec power p a n = if n=0 then 1 else
  let half=power p a (n/2) in let square=mul p half half in
  if n mod 2=0 then square else mul p square a
let inv1=power prime1 31 (prime1-2) and inv2=power prime2 37 (prime2-2)
let digit = function S0->0|S1->1|S2->2|S3->3
let side_hash p base xs =
  fst(List.fold_left(fun (sum,weight) s->
    ((sum+mul p (digit s) weight) mod p,mul p weight base)) (0,base) xs)
let key (q,((l,h),r)) =
  q,h,(digit h+side_hash prime1 inv1 l+side_hash prime1 31 r) mod prime1,
      (digit h+side_hash prime2 inv2 l+side_hash prime2 37 r) mod prime2
let prefix tm bound =
  let table=Hashtbl.create (bound+1) in
  let tape=Array.make (2*bound+3) S0 in
  let rec loop n q head hash1 hash2 =
    let read=tape.(head) in
    let k=q,read,hash1,hash2 in
    if not(Hashtbl.mem table k) then Hashtbl.add table k n;
    if n<bound then match tm q read with
    | None->()
    | Some tr->
      let delta=digit tr.t_write-digit read in
      let hash1=(hash1+delta+prime1) mod prime1 and hash2=(hash2+delta+prime2) mod prime2 in
      tape.(head)<-tr.t_write;
      let head,b1,b2=match tr.t_dir with
        | DL->head-1,31,37 | DR->head+1,inv1,inv2 in
      loop(n+1)tr.t_next head (mul prime1 hash1 b1)(mul prime2 hash2 b2) in
  loop 0 StA (bound+1) 0 0;table
let side rs = List.map(fun (id,e)->
  let a=match e.e_cf with []->Z0 | [a]->a | _->raise Unsupported in
  ((id,a),e.e_c0)) rs
exception Found of bIRCertP*int
exception Row_timeout
let phase_search tm cert bound cfuel fuel steps =
  let tbl=mk_tbl cert.cp_blks and lo=[cert.cp_kmin] in
  match check_rulesBlkP tm tbl cert.cp_blks cfuel fuel cert.cp_rules with
  | None -> None
  | Some rules ->
    let anchors=prefix tm bound and tried=Hashtbl.create steps in
    let attempt index c =
      if not(Hashtbl.mem tried c) then begin
        Hashtbl.add tried c ();
        let shifted={cert with cp_st=c.b_st;cp_hs=c.b_hs;cp_TL=side c.b_L;cp_TR=side c.b_R} in
        let lengths rs=List.fold_left(fun sum (id,e)->
          let count=big_z(eval(fun _->cert.cp_k0)e) in
          if Big.sign count<0 || Big.compare count (Big.of_int (2*bound+1))>0 then raise Exit;
          sum+Big.to_int count*List.length(tbl id)) 0 rs in
        try
          if lengths c.b_L + lengths c.b_R>2*bound+1 then raise Exit;
          let concrete=(c.b_st,((bdside tbl (fun _->cert.cp_k0)c.b_L,c.b_hs),
                                bdside tbl (fun _->cert.cp_k0)c.b_R)) in
          let anchor=Hashtbl.find anchors (key concrete) in
          let shifted={shifted with cp_anchor=anchor} in
          if ir_check (n_of_int bound) (n_of_int bound) tm shifted cfuel fuel then
            raise(Found(shifted,index))
        with Not_found | Exit -> ()
      end in
    let rec go index c =
      if index>steps then () else begin
        if index>0 then attempt index c;
        match try_rulesBlkP lo (false,false) rules c with
        | Some(c',_) -> go (index+1) c'
        | None -> match beng_stepS tm tbl cert.cp_blks lo false false cfuel c with
          | None -> ()
          | Some(c',_) -> go (index+1) (bcanon lo tbl cert.cp_blks c')
      end in
    try go 0 (btplp_cfg cert);None with Found(c,i)->Some(c,i)

let () =
  if Array.length Sys.argv<>8 then begin
    prerr_endline "usage: affine_phase_probe BOUND CFUEL FUEL PHASES TIMEOUT CERT_PATHS OUTPUT_DIR";exit 2
  end;
  let bound=nat Sys.argv.(1) and cfuel=nat Sys.argv.(2) and fuel=nat Sys.argv.(3)
  and phases=nat Sys.argv.(4) and seconds=float_of_string Sys.argv.(5) in
  if bound=0||cfuel=0||fuel=0||phases=0||seconds<=0. then invalid_arg "invalid budget";
  Sys.set_signal Sys.sigalrm (Sys.Signal_handle(fun _->raise Row_timeout));
  let input=open_in Sys.argv.(6) in
  print_endline "certificate\tmachine\tstatus\tphase\tseconds";
  (try while true do
    let path=input_line input and identity=ref "" and phase=ref 0 in
    let start=Unix.gettimeofday() in
    let status=try
      ignore(Unix.setitimer Unix.ITIMER_REAL {Unix.it_interval=0.;it_value=seconds});
      Fun.protect(fun()->
        let name,tm,c=certificate path identity in
        match phase_search tm c bound cfuel fuel phases with
        | None->"replay_false"
        | Some(repaired,index)->phase:=index;
          write_cert(Filename.concat Sys.argv.(7)(name^".cert"))name repaired;"repaired_candidate")
        ~finally:(fun()->ignore(Unix.setitimer Unix.ITIMER_REAL {Unix.it_interval=0.;it_value=0.}))
      with Unsupported->"unsupported" | Row_timeout->"timeout" | Stack_overflow->"stack_overflow"
      | Invalid_argument _ | Failure _ | Not_found | Sys_error _ ->"invalid_certificate" in
    Printf.printf "%s\t%s\t%s\t%d\t%.6f\n%!" path !identity status !phase (Unix.gettimeofday()-.start)
  done with End_of_file->close_in input)

