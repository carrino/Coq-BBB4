(* Untrusted parameter-reindexing proposals. Restrict the initial parameter
   to its residue class, and optionally combine several affine returns. The
   unchanged ir_check validates every proposal before it is emitted. *)
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

exception Found of bIRCertP * int * int * int
exception Row_timeout
let ceiling n d =
  let q,r=Big.ediv_rem n d in if Big.equal r Big.zero then q else Big.succ q
let rescale tm cert bound cfuel fuel =
  let k0=big_z cert.cp_k0 and kmin=big_z cert.cp_kmin
  and a=big_z cert.cp_a and b=big_z cert.cp_b in
  let seen=Hashtbl.create 128 in
  try
    List.iter (fun modulus ->
      let m=Big.of_int modulus in
      let _,residue=Big.ediv_rem k0 m in
      let ap=ref Big.one and bp=ref Big.zero in
      for power=1 to 4 do
        ap:=Big.mul a !ap; bp:=Big.add (Big.mul a !bp) b;
        List.iter (fun shift ->
          let r=Big.sub residue (Big.mul m (Big.of_int shift)) in
          let delta=Big.add (Big.mul (Big.sub !ap Big.one) r) !bp in
          let _,remainder=Big.ediv_rem delta m in
          if Big.equal remainder Big.zero then begin
            let j0=Big.divexact (Big.sub k0 r) m in
            let low=Big.max Big.zero (ceiling (Big.sub kmin r) m) in
            let minima=if Big.equal j0 low then [j0] else [j0;low] in
            let side runs=List.map (fun ((id,ca),cb)->
              let ca=big_z ca and cb=big_z cb in
              ((id,from_big (Big.mul ca m)),from_big (Big.add (Big.mul ca r) cb))) runs in
            List.iter (fun minimum ->
              if Big.compare minimum low>=0 && Big.compare j0 minimum>=0 then begin
                let candidate={cert with cp_k0=from_big j0;cp_kmin=from_big minimum;
                  cp_a=from_big !ap;cp_b=from_big (Big.divexact delta m);
                  cp_TL=side cert.cp_TL;cp_TR=side cert.cp_TR} in
                if not(Hashtbl.mem seen candidate) then begin
                  Hashtbl.add seen candidate ();
                  if ir_check (n_of_int bound) (n_of_int bound) tm candidate cfuel fuel then
                    raise(Found(candidate,modulus,power,shift))
                end
              end) minima
          end) [0;1]
      done) [2;3;4;5;6;8;1];
    None
  with Found(c,m,p,s)->Some(c,m,p,s)
let () =
  if Array.length Sys.argv<>7 then begin
    prerr_endline "usage: affine_residue_probe BOUND CFUEL FUEL CPU_SECONDS CERT_PATHS OUTPUT_DIR";exit 2
  end;
  let bound=nat Sys.argv.(1) and cfuel=nat Sys.argv.(2) and fuel=nat Sys.argv.(3)
  and seconds=float_of_string Sys.argv.(4) in
  if bound=0||cfuel=0||fuel=0||seconds<=0. then invalid_arg "invalid budget";
  (match classify_float seconds with FP_nan|FP_infinite->invalid_arg "nonfinite budget"|_->());
  Sys.set_signal Sys.sigprof (Sys.Signal_handle(fun _->raise Row_timeout));
  let input=open_in Sys.argv.(5) in
  print_endline "certificate\tmachine\tstatus\tmodulus\tpower\tshift\tseconds";
  (try while true do
    let path=input_line input and identity=ref "" and choice=ref(0,0,0) in
    let start=Unix.gettimeofday() in
    let status=try
      ignore(Unix.setitimer Unix.ITIMER_PROF {Unix.it_interval=0.;it_value=seconds});
      Fun.protect(fun()->
        let name,tm,c=certificate path identity in
        match rescale tm c bound cfuel fuel with
        | None->"replay_false"
        | Some(c,m,p,s)->choice:=(m,p,s);
          write_cert(Filename.concat Sys.argv.(6)(name^".cert"))name c;"repaired_candidate")
        ~finally:(fun()->ignore(Unix.setitimer Unix.ITIMER_PROF {Unix.it_interval=0.;it_value=0.}))
      with Unsupported->"unsupported" | Row_timeout->"timeout" | Stack_overflow->"stack_overflow"
      | Invalid_argument _ | Failure _ | Not_found | Sys_error _ ->"invalid_certificate" in
    let m,p,s = !choice in
    Printf.printf "%s\t%s\t%s\t%d\t%d\t%d\t%.6f\n%!" path !identity status m p s (Unix.gettimeofday()-.start)
  done with End_of_file->close_in input)
