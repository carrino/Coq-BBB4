(* Untrusted search: keep Coq positive/Z as exact inductive values. *)
open Smallbb
let codes ns s =
  let s = String.concat "" (String.split_on_char '_' s) in
  List.init (String.length s / 3) (fun i -> if s.[3*i] = '-' then 6*ns else
    2*ns * (Char.code s.[3*i] - 48) + (if s.[3*i+1] = 'R' then ns else 0) + Char.code s.[3*i+2] - 65)
let () =
  let mode=Sys.argv.(1) and input=open_in Sys.argv.(2) and output=open_out Sys.argv.(3) in
  let ns=int_of_string Sys.argv.(4) and ms=int_of_string Sys.argv.(5)
  and bs=int_of_string Sys.argv.(6) and bi=int_of_string Sys.argv.(7)
  and n=int_of_string Sys.argv.(8) and t=int_of_string Sys.argv.(9)
  and fuel=int_of_string Sys.argv.(10) and extra=int_of_string Sys.argv.(11) in
  let count=ref 0 and solved=ref 0 in
  (try while true do
    let line=input_line input in incr count;
    let tm=machine_of_codes ns ms (codes ns line) in
    let ok=match mode with "ng" -> ng_check bs bi tm n t fuel extra | "rw" -> rw_check bs bi tm n extra t fuel | "state-ng" -> ng_state_check bs tm n t fuel extra | "state-rw" -> rw_state_check bs tm n extra t fuel | "finite" -> fn_check_mode false bs bi tm n t fuel extra | "state-finite" -> fn_check_mode true bs bi tm n t fuel extra | "hist" -> hn_check_mode false bs bi tm extra n t fuel 128 | "state-hist" -> hn_check_mode true bs bi tm extra n t fuel 128 | _ -> failwith "mode" in
    if ok then incr solved else output_string output (line ^ "\n");
    if !count mod 100=0 then Printf.eprintf "%d/%d solved\n%!" !solved !count
  done with End_of_file -> ());
  close_out output;Printf.printf "solved=%d total=%d\n%!" !solved !count
