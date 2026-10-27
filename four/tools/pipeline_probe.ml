(* Untrusted search over the extracted, proved checker functions. Output rows
   are candidates, not certificates of kernel acceptance. N/Z/positive retain
   Coq's exact inductive representation. Only nat is extracted to OCaml int. *)
open Checkers

let symbol = function
  | '0' -> S0 | '1' -> S1 | '2' -> S2 | '3' -> S3
  | _ -> invalid_arg "symbol must be 0..3"
let state = function
  | 'A' -> StA | 'B' -> StB | _ -> invalid_arg "state must be A or B"
let state_index = function StA -> 0 | StB -> 1
let symbol_index = function S0 -> 0 | S1 -> 1 | S2 -> 2 | S3 -> 3
let machine text =
  if String.length text <> 25 || text.[12] <> '_' then
    invalid_arg "expected two rows of four transitions";
  let cells = Array.init 8 (fun i ->
    let off = 3 * i + if i >= 4 then 1 else 0 in
    let cell = String.sub text off 3 in
    if cell = "---" then None else
    let t_write = symbol cell.[0]
    and t_dir = match cell.[1] with
      | 'L' -> DL | 'R' -> DR | _ -> invalid_arg "direction must be L or R"
    and t_next = state cell.[2] in
    Some { t_write; t_dir; t_next }) in
  fun q s -> cells.(4 * state_index q + symbol_index s)

let rec positive_of_int n =
  if n = 1 then XH else if n land 1 = 0 then XO (positive_of_int (n lsr 1))
  else XI (positive_of_int (n lsr 1))
let n_of_int n = if n = 0 then N0 else Npos (positive_of_int n)
exception Row_timeout
let timed seconds f =
  ignore (Unix.setitimer Unix.ITIMER_REAL {Unix.it_interval=0.; it_value=seconds});
  Fun.protect f ~finally:(fun () ->
    ignore (Unix.setitimer Unix.ITIMER_REAL {Unix.it_interval=0.; it_value=0.}))

let () =
  if Array.length Sys.argv <> 9 then begin
    prerr_endline "usage: probe ng|rw BOUND N_OR_L ANCHOR FUEL ROUNDS_OR_T TIMEOUT INPUT";
    exit 2
  end;
  let mode = Sys.argv.(1) and bound_i = int_of_string Sys.argv.(2)
  and size = int_of_string Sys.argv.(3) and anchor = int_of_string Sys.argv.(4)
  and fuel = int_of_string Sys.argv.(5) and extra = int_of_string Sys.argv.(6)
  and timeout = float_of_string Sys.argv.(7) in
  if (mode <> "ng" && mode <> "rw") || bound_i < 0 || size < 1 ||
    anchor < 0 || anchor > bound_i || fuel < 1 || extra < 1 || timeout <= 0.
    then invalid_arg "invalid checker parameters";
  let bound = n_of_int bound_i in
  Sys.set_signal Sys.sigalrm (Sys.Signal_handle (fun _ -> raise Row_timeout));
  let input = open_in Sys.argv.(8) in
  (try while true do
    let line = input_line input in
    let tm = machine line in (* malformed input must fail the run *)
    let start = Unix.gettimeofday () in
    let status = try
      let accepted = timed timeout (fun () -> match mode with
        | "ng" -> ng_check bound bound tm size anchor fuel extra
        | "rw" -> rw_check bound bound tm size extra anchor fuel
        | _ -> assert false) in
      if accepted then "candidate" else "rejected"
    with Row_timeout -> "timeout" | Stack_overflow -> "stack_overflow" in
    Printf.printf "%s\t%s\t%.6f\n%!" line status (Unix.gettimeofday () -. start)
  done with End_of_file -> close_in input)
