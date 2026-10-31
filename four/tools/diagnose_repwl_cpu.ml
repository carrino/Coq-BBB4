(* Process-CPU timer variant. The original wall-clock driver is unchanged. *)
(* Untrusted repeated-word diagnostics and optional early size cut. A cut only
   retains a row as unresolved. Accepted rows must still replay rw_check in
   Coq without the cut. This is not a new formal checker. *)
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
let node_size (_,((((l,ls),_),rs),r)) =
  List.length l + List.length r + List.length ls + List.length rs
exception Row_timeout
(* Only the protected computation can raise an alarm exception. Blocking the
   signal outside it prevents a pending alarm from escaping during I/O; the
   active guard also covers a handler already queued by the OCaml runtime. *)
let alarm_active = ref false
let block_alarm () = ignore (Unix.sigprocmask Unix.SIG_BLOCK [Sys.sigprof])
let cleanup_alarm () =
  alarm_active := false;
  block_alarm ();
  ignore (Unix.setitimer Unix.ITIMER_PROF {Unix.it_interval=0.; it_value=0.})
let timed seconds f =
  try
    (* Drain a pending prior alarm while raising is disabled. *)
    ignore (Unix.sigprocmask Unix.SIG_UNBLOCK [Sys.sigprof]);
    block_alarm ();
    alarm_active := true;
    ignore (Unix.setitimer Unix.ITIMER_PROF {Unix.it_interval=0.; it_value=seconds});
    ignore (Unix.sigprocmask Unix.SIG_UNBLOCK [Sys.sigprof]);
    let answer = f () in
    cleanup_alarm ();
    answer
  with exn -> cleanup_alarm (); raise exn

let () =
  if Array.length Sys.argv <> 9 then begin
    prerr_endline "usage: diagnose_repwl BOUND L T ANCHOR FUEL SIZE_CAP_OR_ZERO CPU_TIMEOUT INPUT";
    exit 2
  end;
  let bound_i = int_of_string Sys.argv.(1) and width = int_of_string Sys.argv.(2)
  and threshold = int_of_string Sys.argv.(3) and anchor = int_of_string Sys.argv.(4)
  and fuel = int_of_string Sys.argv.(5) and cap = int_of_string Sys.argv.(6)
  and timeout = float_of_string Sys.argv.(7) in
  if bound_i < 0 || width < 1 || threshold < 2 || anchor < 0 || anchor > bound_i ||
     fuel < 1 || cap < 0 || timeout <= 0. then invalid_arg "invalid checker parameters";
  let bound = n_of_int bound_i in
  block_alarm ();
  Sys.set_signal Sys.sigprof (Sys.Signal_handle (fun _ -> if !alarm_active then raise Row_timeout));
  let input = open_in Sys.argv.(8) in
  Printf.printf "machine\tstatus\tphase\tnodes\texpanded_nodes\tmax_node_size\tseconds\tcpu_seconds\n%!";
  (try while true do
    let name = input_line input in
    let tm = machine name in
    let phase = ref "boot" and nodes = ref 0 and expanded = ref 0 and max_size = ref 0
    and cut_fired = ref false and blocked = ref false in
    let successors a =
      incr expanded;
      let size = node_size a in max_size := max !max_size size;
      if cap > 0 && size > cap then (cut_fired := true; None)
      else match rw_succs tm width threshold a with
        | None -> blocked := true; None
        | Some _ as next -> next in
    let start = Unix.gettimeofday () in
    let cpu_start = Sys.time () in
    let status = try timed timeout (fun () ->
      match csteps tm anchor c0 with
      | None -> "boot_halt"
      | Some cc ->
        let a0 = rw_seed width threshold cc in
        phase := "close";
        match close_tr rconf_enc successors fuel [] PositiveSet.empty [a0] with
        | None -> if !cut_fired then "node_cut" else if !blocked then "blocked" else "fuel_exhausted"
        | Some sl ->
          nodes := List.length sl;
          phase := "closure_check";
          if not (closed_tr_b rconf_enc (rw_succs tm width threshold) sl) then "closure_failure"
          else if not (mem_tr rconf_enc a0 sl) then "membership_failure"
          else let labs = labels rw_instr sl in
            if not (prefix_gate bound bound tm anchor (tail_states labs) (tail_instrs labs))
              then "prefix_failure"
            else begin
              phase := "liveness";
              if live_lex_ok_tr rconf_enc rw_instr (rw_succs tm width threshold) sl
                (fun target -> List.map (rw_comp_denote tm)
                  (rw_rank_procedure tm width threshold sl target))
              then "candidate" else "ranking_failure"
            end)
      with Row_timeout -> "timeout" | Stack_overflow -> "stack_overflow" in
    Printf.printf "%s\t%s\t%s\t%d\t%d\t%d\t%.6f\t%.6f\n%!"
      name status !phase !nodes !expanded !max_size (Unix.gettimeofday () -. start) (Sys.time () -. cpu_start)
  done with End_of_file -> close_in input)
