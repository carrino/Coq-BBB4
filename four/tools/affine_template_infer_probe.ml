(* Target intercepts and symbolic parameter-map inference are untrusted proposals.
   Every accepted certificate passes the unchanged target ir_check. *)
(* Symbol/state/reflection variants are proposals only; target ir_check remains unchanged. *)
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

(* Hash repeated blocks in logarithmic time. Hashes only propose an anchor;
   the unchanged ir_check still compares the actual concrete target tapes. *)
let rec geometric p ratio count =
  if count=0 then 1,0 else
  let half,sum=geometric p ratio (count/2) in
  let square=mul p half half in
  let sum2=mul p sum ((1+half) mod p) in
  if count mod 2=0 then square,sum2
  else mul p square ratio,(sum2+square) mod p
let template_side_hash p base tbl parameter runs =
  let total,offset=List.fold_left(fun(total,offset)((id,a),b)->
    let count=Big.to_int(Big.add(Big.mul(big_z a)parameter)(big_z b)) in
    let word=tbl id in
    let word_hash=side_hash p base word and stride=power p base (List.length word) in
    let advance,repetitions=geometric p stride count in
    let contribution=mul p offset (mul p word_hash repetitions) in
    (total+contribution) mod p,mul p offset advance) (0,1) runs in
  ignore offset;total
let template_key cert parameter tbl =
  cert.cp_st,cert.cp_hs,
    (digit cert.cp_hs+template_side_hash prime1 inv1 tbl parameter cert.cp_TL+
      template_side_hash prime1 31 tbl parameter cert.cp_TR) mod prime1,
    (digit cert.cp_hs+template_side_hash prime2 inv2 tbl parameter cert.cp_TL+
      template_side_hash prime2 37 tbl parameter cert.cp_TR) mod prime2

exception Found of bIRCertP * string
exception Row_timeout
exception Trial_limit
let normalize_template runs =
  let merged=List.fold_left(fun acc ((id,a),b)->
    if id>=4 || Big.sign(big_z a)<0 then raise Exit;
    if a=Z0 && Big.sign(big_z b)<=0 then acc else
    match acc with
    | ((j,aa),bb)::rest when id=j -> ((id,from_big(Big.add(big_z a)(big_z aa))),
          from_big(Big.add(big_z b)(big_z bb)))::rest
    | _ -> ((id,a),b)::acc)[] runs in
  let merged=match merged with ((0,_),_)::rest->rest | rest->rest in
  List.rev merged
let rle_push symbol runs length = match runs with
  | [] when symbol=S0 -> [],0
  | (s,n)::rest when s=symbol -> (s,n+1)::rest,length
  | _ -> (symbol,1)::runs,length+1
let rle_pop runs length = match runs with
  | [] -> S0,[],0
  | (s,1)::rest -> s,rest,length-1
  | (s,n)::rest -> s,(s,n-1)::rest,length
let rec log_bucket n = if n<=1 then 0 else 1+log_bucket(n/2)
let infer_update template current =
  let expected=template.cp_TL @ template.cp_TR and actual=current.b_L @ current.b_R in
  if current.b_st<>template.cp_st || current.b_hs<>template.cp_hs ||
     List.length template.cp_TL<>List.length current.b_L ||
     List.length template.cp_TR<>List.length current.b_R then None else
  try
    let rows=List.map2(fun((id,a),b)(j,e)->
      if id<>j then raise Exit;
      let coefficient=match e.e_cf with []->Big.zero | [v]->big_z v | _->raise Exit in
      big_z a,big_z b,coefficient,big_z e.e_c0)expected actual in
    let a,b,x,y=List.find(fun(a,_,_,_)->Big.sign a>0)rows in
    let aa,ar=Big.ediv_rem x a and bb,br=Big.ediv_rem(Big.sub y b)a in
    if Big.sign aa<0 || Big.sign bb<0 || ar<>Big.zero || br<>Big.zero then None
    else if List.for_all(fun(a,b,x,y)->Big.equal x(Big.mul a aa) &&
        Big.equal y(Big.add(Big.mul a bb)b))rows then Some(from_big aa,from_big bb)
    else None
  with Exit | Not_found -> None

let infer_lap tm cert bound cfuel fuel checks =
  let tbl=mk_tbl cert.cp_blks and lo=[Z0] in
  match check_rulesBlkP tm tbl cert.cp_blks cfuel fuel cert.cp_rules with
  | None -> None
  | Some rules ->
    let seen=Hashtbl.create 32 in
    let rec go index c =
      if index>256 || Hashtbl.mem seen c then None else begin
        Hashtbl.add seen c ();
        let accepted=if index=0 then None else match infer_update cert c with
          | None -> None
          | Some(a,b)->
            let candidate={cert with cp_a=a;cp_b=b} in
            incr checks;
            if ir_check(n_of_int bound)(n_of_int bound)tm candidate cfuel fuel
            then Some candidate else None in
        match accepted with Some c->Some c | None->
        match try_rulesBlkP lo (false,false) rules c with
        | Some(c',_) -> go(index+1)c'
        | None -> match beng_stepS tm tbl cert.cp_blks lo false false cfuel c with
          | None -> None
          | Some(c',_) -> go(index+1)(bcanon lo tbl cert.cp_blks c')
      end in
    go 0(btplp_cfg cert)

let search tm sources bound cfuel fuel fits checks =
  let table=Hashtbl.create 16 and equivalent=Hashtbl.create 16 in
  List.iter(fun(path,cert)->try
    if cert.cp_blks<>[] || big_z cert.cp_a<>Big.one then raise Exit;
    let left=normalize_template cert.cp_TL and right=normalize_template cert.cp_TR in
    if not(List.exists(fun((_,a),_)->a<>Z0)(left@right)) then raise Exit;
    let slopes runs=List.map(fun((id,a),_)->id,a)runs in
    let identity=cert.cp_st,cert.cp_hs,slopes left,slopes right,cert.cp_b,cert.cp_rules in
    if not(Hashtbl.mem equivalent identity) then begin
      Hashtbl.add equivalent identity ();
      let key=cert.cp_st,cert.cp_hs,List.length left,List.length right in
      Hashtbl.add table key (path,cert,left,right)
    end
    with Exit->()) sources;
  let seen=Hashtbl.create 256 in
  let attempt n q head left right (path,cert,tl,tr) =
    let symbols_match template actual=List.for_all2(fun((id,_),_)(symbol,_)->id=digit symbol)template actual in
    if symbols_match tl left && symbols_match tr right then begin
      let pairs=List.map2(fun((_,a),_)(_,count)->big_z a,count)(tl@tr)(left@right) in
      let a,pivot_count=List.find(fun(a,_)->Big.sign a>0)pairs in
      let shift=Big.div (Big.of_int pivot_count) a in
      let offsets=List.map(fun(a,n)->Big.to_string(Big.sub(Big.of_int n)(Big.mul a shift)))pairs in
      let identity=path,offsets,log_bucket(Big.to_int shift+1) in
      if not(Hashtbl.mem seen identity) then begin
        Hashtbl.add seen identity ();incr fits;
        if !fits>=128 then raise Trial_limit;
        let template old actual=List.map2(fun((id,a),_)(_,count)->((id,a),z(string_of_int count)))old actual in
        let shifted={cert with cp_anchor=n;cp_k0=Z0;cp_kmin=Z0;
            cp_TL=template tl left;cp_TR=template tr right} in
        match infer_lap tm shifted bound cfuel fuel checks with
        | None->()
        | Some accepted->raise(Found(accepted,path))
      end
    end in
  let rec walk n q left llen head right rlen =
    List.iter(attempt n q head left right)(Hashtbl.find_all table(q,head,llen,rlen));
    if n<bound then match tm q head with
    | None->()
    | Some transition->match transition.t_dir with
      | DR->let left,llen=rle_push transition.t_write left llen in
            let head,right,rlen=rle_pop right rlen in
            walk(n+1)transition.t_next left llen head right rlen
      | DL->let right,rlen=rle_push transition.t_write right rlen in
            let head,left,llen=rle_pop left llen in
            walk(n+1)transition.t_next left llen head right rlen in
  try walk 0 StA [] 0 S0 [] 0;None with Found(cert,path)->Some(cert,path)

let transform_certificate perm mirror swap c =
  let symbol s = symbol_index s |> fun i -> symbol perm.[i] in
  let state q = if swap then (match q with StA->StB | StB->StA) else q in
  let id i = if i<4 then Char.code perm.[i]-Char.code '0' else i in
  let template xs = List.map(fun((i,a),b)->((id i,a),b))xs in
  let runs xs = List.map(fun(i,count)->id i,count)xs in
  let left,right=template c.cp_TL,template c.cp_TR in
  let left,right=if mirror then right,left else left,right in
  let rules=List.map(fun r->
    let l,rr=runs r.brp_L,runs r.brp_R in
    let l,rr,pfx=if mirror then rr,l,(snd r.brp_pfx,fst r.brp_pfx) else l,rr,r.brp_pfx in
    {brp_st=state r.brp_st;brp_hs=symbol r.brp_hs;brp_L=l;brp_R=rr;brp_pfx=pfx})c.cp_rules in
  {c with cp_st=state c.cp_st;cp_hs=symbol c.cp_hs;cp_TL=left;cp_TR=right;cp_rules=rules;
    cp_blks=List.map(fun(i,w)->i,List.map symbol w)c.cp_blks}

let () =
  if Array.length Sys.argv<>7 then begin
    prerr_endline "usage: affine_template_infer_probe BOUND CFUEL FUEL TIMEOUT INPUT_TSV OUTPUT_DIR";exit 2
  end;
  let bound=nat Sys.argv.(1) and cfuel=nat Sys.argv.(2) and fuel=nat Sys.argv.(3)
  and seconds=float_of_string Sys.argv.(4) in
  if bound=0||cfuel=0||fuel=0||seconds<=0. then invalid_arg "invalid budget";
  Sys.set_signal Sys.sigalrm(Sys.Signal_handle(fun _->raise Row_timeout));
  let cache=Hashtbl.create 4096 and originals=Hashtbl.create 4096 in
  let load token=try Hashtbl.find cache token with Not_found->
    let path,perm,mirror,swap=match String.split_on_char '|' token with
      | [p;permutation;m;s] when String.length permutation=4 && permutation.[0]='0' &&
          List.sort Stdlib.compare (List.init 4(fun i->permutation.[i]))=['0';'1';'2';'3'] &&
          List.mem m ["0";"1"] && List.mem s ["0";"1"] -> p,permutation,m="1",s="1"
      | _->invalid_arg "invalid orbit token" in
    let original=try Hashtbl.find originals path with Not_found->
      let _,_,c=certificate path(ref "") in Hashtbl.add originals path c;c in
    let cert=transform_certificate perm mirror swap original in
    Hashtbl.add cache token cert;cert in
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
        with Row_timeout->"timeout" | Trial_limit->"trial_limit" | Unsupported->"unsupported" | Stack_overflow->"stack_overflow"
        | Invalid_argument _ | Failure _ | Sys_error _ | Not_found -> "invalid_certificate" in
      Printf.printf "%s\t%s\t%s\t%.6f\t%s\t%d\t%s\t%d\t%d\n%!"
        destination name status (Unix.gettimeofday()-.start) !source !anchor !k0 !fits !checks
  done with End_of_file->close_in input)
