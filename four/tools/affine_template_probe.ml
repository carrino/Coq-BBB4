(* Untrusted cross-machine affine template reuse. Target ir_check is the gate.
   Certificate writer and exact-prefix hash helpers follow affine_phase_probe.ml. *)
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

type snapshot = st * sym * int * int * int
let prefix tm bound =
  let anchors=Hashtbl.create (bound+1) and snapshots=ref [] in
  let tape=Array.make (2*bound+3) S0 and counts=Array.make 4 0 in
  let rec loop n q head hash1 hash2 =
    let read=tape.(head) in
    let k=q,read,hash1,hash2 in
    if not(Hashtbl.mem anchors k) then Hashtbl.add anchors k n;
    snapshots := (q,read,counts.(1),counts.(2),counts.(3)) :: !snapshots;
    if n<bound then match tm q read with
    | None->()
    | Some tr->
      let old=digit read and fresh=digit tr.t_write in
      if old>0 then counts.(old)<-counts.(old)-1;
      if fresh>0 then counts.(fresh)<-counts.(fresh)+1;
      let delta=fresh-old in
      let hash1=(hash1+delta+prime1) mod prime1 and hash2=(hash2+delta+prime2) mod prime2 in
      tape.(head)<-tr.t_write;
      let head,b1,b2=match tr.t_dir with
        | DL->head-1,31,37 | DR->head+1,inv1,inv2 in
      loop(n+1)tr.t_next head (mul prime1 hash1 b1)(mul prime2 hash2 b2) in
  loop 0 StA (bound+1) 0 0;anchors,List.rev !snapshots

let count_coefficients cert =
  let tbl=mk_tbl cert.cp_blks in
  let linear=Array.make 4 Big.zero and constant=Array.make 4 Big.zero in
  constant.(digit cert.cp_hs)<-Big.one;
  List.iter(fun ((id,a),b)->
    let counts=Array.make 4 0 in
    List.iter(fun s->let i=digit s in counts.(i)<-counts.(i)+1)(tbl id);
    for i=1 to 3 do
      let multiplicity=Big.of_int counts.(i) in
      linear.(i)<-Big.add linear.(i)(Big.mul multiplicity (big_z a));
      constant.(i)<-Big.add constant.(i)(Big.mul multiplicity (big_z b))
    done)(cert.cp_TL@cert.cp_TR);
  linear,constant

let instances cert snapshots =
  let linear,constant=count_coefficients cert in
  let pivot=ref 0 in
  for i=1 to 3 do if !pivot=0 && not(Big.equal linear.(i)Big.zero) then pivot:=i done;
  let found=Hashtbl.create 64 and minimum=big_z cert.cp_kmin in
  let add k=if Big.compare k minimum>=0 then Hashtbl.replace found (Big.to_string k) k in
  if !pivot=0 then begin
    (* Blank-only variable runs do not change nonzero-cell counts. This small
       fallback is a proposal heuristic, never a completeness assertion. *)
    for i=0 to 64 do add(Big.add minimum(Big.of_int i)) done;
    add(big_z cert.cp_k0)
  end else List.iter(fun(q,h,c1,c2,c3)->
    if q=cert.cp_st && h=cert.cp_hs then begin
      let counts=[|0;c1;c2;c3|] and i= !pivot in
      let numerator=Big.sub(Big.of_int counts.(i))constant.(i) in
      let k,remainder=Big.ediv_rem numerator linear.(i) in
      if Big.equal remainder Big.zero && Big.compare k minimum>=0 &&
         List.for_all(fun j->Big.equal (Big.of_int counts.(j))
           (Big.add(Big.mul linear.(j)k)constant.(j)))[1;2;3] then add k
    end)snapshots;
  Hashtbl.fold(fun _ k rest->k::rest)found[] |> List.sort Big.compare

exception Found of bIRCertP * string
exception Row_timeout
let search tm sources bound cfuel fuel fits checks =
  let anchors,snapshots=prefix tm bound in
  let attempt path cert k =
    incr fits;
    let tbl=mk_tbl cert.cp_blks and bound_big=Big.of_int (2*bound+1) in
    let length runs=List.fold_left(fun sum((id,a),b)->
      let count=Big.add(Big.mul(big_z a)k)(big_z b) in
      if Big.sign count<0 || Big.compare count bound_big>0 then raise Exit;
      let total=sum+Big.to_int count*List.length(tbl id) in
      if total>2*bound+1 then raise Exit;total)0 runs in
    try
      if length cert.cp_TL+length cert.cp_TR>2*bound+1 then raise Exit;
      let k0=from_big k in
      let shifted={cert with cp_k0=k0} in
      let symbolic=btplp_cfg shifted in
      let concrete=(shifted.cp_st,((bdside tbl (fun _->k0)symbolic.b_L,shifted.cp_hs),
                                  bdside tbl (fun _->k0)symbolic.b_R)) in
      let anchor=Hashtbl.find anchors(key concrete) in
      incr checks;
      let shifted={shifted with cp_anchor=anchor} in
      if ir_check (n_of_int bound)(n_of_int bound)tm shifted cfuel fuel then raise(Found(shifted,path))
    with Not_found | Exit -> () in
  try List.iter(fun(path,cert)->List.iter(attempt path cert)(instances cert snapshots))sources;None
  with Found(cert,path)->Some(cert,path)

let () =
  if Array.length Sys.argv<>7 then begin
    prerr_endline "usage: affine_template_probe BOUND CFUEL FUEL TIMEOUT INPUT_TSV OUTPUT_DIR";exit 2
  end;
  let bound=nat Sys.argv.(1) and cfuel=nat Sys.argv.(2) and fuel=nat Sys.argv.(3)
  and seconds=float_of_string Sys.argv.(4) in
  if bound=0||cfuel=0||fuel=0||seconds<=0. then invalid_arg "invalid budget";
  Sys.set_signal Sys.sigalrm(Sys.Signal_handle(fun _->raise Row_timeout));
  let cache=Hashtbl.create 4096 in
  let load path=try Hashtbl.find cache path with Not_found->
    let _,_,cert=certificate path(ref "") in Hashtbl.add cache path cert;cert in
  let input=open_in Sys.argv.(5) in
  print_endline "certificate\tmachine\tstatus\tseconds\tsource\tanchor\tk0\tinstances\tchecks";
  (try while true do
    let line=input_line input in
    match String.split_on_char '\t' line with
    | [] | [_] -> invalid_arg "expected target and template paths"
    | name::paths ->
      let destination=Filename.concat Sys.argv.(6)(name^".cert") in
      let fits=ref 0 and checks=ref 0 and source=ref "" and anchor=ref(-1) and k0=ref "" in
      let start=Unix.gettimeofday() in
      let status=try
        ignore(Unix.setitimer Unix.ITIMER_REAL {Unix.it_interval=0.;it_value=seconds});
        Fun.protect(fun()->
          let tm=machine name and templates=List.map(fun p->p,load p)paths in
          match search tm templates bound cfuel fuel fits checks with
          | None -> if !checks=0 then "no_template_match" else "replay_false"
          | Some(c,p)->write_cert destination name c;source:=p;anchor:=c.cp_anchor;k0:=z_text c.cp_k0;"replay_true")
          ~finally:(fun()->ignore(Unix.setitimer Unix.ITIMER_REAL {Unix.it_interval=0.;it_value=0.}))
        with Row_timeout->"timeout" | Unsupported->"unsupported" | Stack_overflow->"stack_overflow"
        | Invalid_argument _ | Failure _ | Sys_error _ | Not_found -> "invalid_certificate" in
      Printf.printf "%s\t%s\t%s\t%.6f\t%s\t%d\t%s\t%d\t%d\n%!"
        destination name status (Unix.gettimeofday()-.start) !source !anchor !k0 !fits !checks
  done with End_of_file->close_in input)
