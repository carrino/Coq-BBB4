(* Exploratory diagnostics only: describe why the extracted n-gram checker
   fails at its recorded budget. No result from this program is a proof. *)
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
    let off = 3*i + if i >= 4 then 1 else 0 in
    let cell = String.sub text off 3 in
    if cell = "---" then None else
    let t_write = symbol cell.[0]
    and t_dir = match cell.[1] with
      | 'L' -> DL | 'R' -> DR | _ -> invalid_arg "direction must be L or R"
    and t_next = state cell.[2] in
    Some {t_write; t_dir; t_next}) in
  fun q s -> cells.(4*state_index q + symbol_index s)

let rec positive_of_int n =
  if n = 1 then XH else if n land 1 = 0 then XO (positive_of_int (n lsr 1))
  else XI (positive_of_int (n lsr 1))
let n_of_int n = if n = 0 then N0 else Npos (positive_of_int n)
exception Row_timeout
(* Only the protected computation can raise an alarm exception. Blocking the
   signal outside it prevents a pending alarm from escaping during I/O; the
   active guard also covers a handler already queued by the OCaml runtime. *)
let alarm_active = ref false
let block_alarm () = ignore (Unix.sigprocmask Unix.SIG_BLOCK [Sys.sigalrm])
let cleanup_alarm () =
  alarm_active := false;
  block_alarm ();
  ignore (Unix.setitimer Unix.ITIMER_REAL {Unix.it_interval=0.; it_value=0.})
let timed seconds f =
  try
    (* Drain a pending prior alarm while raising is disabled. *)
    ignore (Unix.sigprocmask Unix.SIG_UNBLOCK [Sys.sigalrm]);
    block_alarm ();
    alarm_active := true;
    ignore (Unix.setitimer Unix.ITIMER_REAL {Unix.it_interval=0.; it_value=seconds});
    ignore (Unix.sigprocmask Unix.SIG_UNBLOCK [Sys.sigalrm]);
    let answer = f () in
    cleanup_alarm ();
    answer
  with exn -> cleanup_alarm (); raise exn

let () =
  if Array.length Sys.argv <> 8 then begin
    prerr_endline "usage: diagnose_ngram BOUND WIDTH ANCHOR FUEL ROUNDS TIMEOUT INPUT";
    exit 2
  end;
  let bound_i = int_of_string Sys.argv.(1) and width = int_of_string Sys.argv.(2)
  and anchor = int_of_string Sys.argv.(3) and fuel = int_of_string Sys.argv.(4)
  and rounds = int_of_string Sys.argv.(5) and timeout = float_of_string Sys.argv.(6) in
  if bound_i < 0 || width < 1 || anchor < 0 || anchor > bound_i || fuel < 1 ||
     rounds < 1 || timeout <= 0. then invalid_arg "invalid checker parameters";
  let bound = n_of_int bound_i in
  block_alarm ();
  Sys.set_signal Sys.sigalrm (Sys.Signal_handle (fun _ -> if !alarm_active then raise Row_timeout));
  let input = open_in Sys.argv.(7) in
  Printf.printf "machine\tstatus\tphase\tnodes\tleft_grams\tright_grams\thalt_contexts\tmissing_grams\tfrontier_edges\tseconds\tcpu_seconds\n%!";
  (try while true do
    let name = input_line input in
    let tm = machine name in
    let phase = ref "boot" and nodes = ref 0 and lgrams = ref 0 and rgrams = ref 0
    and halts = ref 0 and missing = ref 0 and frontier = ref 0 in
    let start = Unix.gettimeofday () in
    let cpu_start = Sys.time () in
    let status = try timed timeout (fun () ->
      match csteps tm anchor c0 with
      | None -> "boot_halt"
      | Some ((_,((l, _), r)) as cc) ->
        let a0 = ng_start width cc in
        phase := "grow";
        let ls, rs = ng_grow tm a0 fuel rounds
          (gadds (ng_seed_side width l) gempty) (gadds (ng_seed_side width r) gempty) in
        lgrams := PositiveSet.cardinal ls; rgrams := PositiveSet.cardinal rs;
        phase := "explore";
        let sl = ng_explore tm ls rs fuel [] PositiveSet.empty [a0] in
        nodes := List.length sl;
        phase := "seed";
        if not (ng_seed_ok width ls rs cc) then "seed_failure" else begin
          phase := "closure";
          if not (closed_tr_b cconf_enc (ng_succs tm ls rs) sl) then begin
            phase := "closure_diagnosis";
            let pool = apool_tr cconf_enc sl in
            List.iter (fun ((q,((_,head),_)) as a) ->
              match ng_succs tm ls rs a with
              | None -> (match tm q head with None -> incr halts | Some _ -> incr missing)
              | Some next -> List.iter (fun a' ->
                  if not (PositiveSet.mem (cconf_enc a') pool) then incr frontier) next) sl;
            "closure_failure"
          end else if not (mem_tr cconf_enc a0 sl) then "membership_failure"
          else if not (prefix_gate bound bound tm anchor (tail_states sl) (tail_instrs sl))
            then "prefix_failure"
          else begin
            phase := "liveness";
            if live_lex_ok_tr cconf_enc cinstr (ng_succs tm ls rs) sl
              (fun target -> List.map (ng_comp_denote tm width)
                (rank_procedure tm ls rs sl target))
            then "candidate" else "ranking_failure"
          end
        end)
      with Row_timeout -> "timeout" | Stack_overflow -> "stack_overflow" in
    Printf.printf "%s\t%s\t%s\t%d\t%d\t%d\t%d\t%d\t%d\t%.6f\t%.6f\n%!"
      name status !phase !nodes !lgrams !rgrams !halts !missing !frontier
      (Unix.gettimeofday () -. start) (Sys.time () -. cpu_start)
  done with End_of_file -> close_in input)
