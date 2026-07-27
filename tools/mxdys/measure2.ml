(* Stage 0 gate-metric refinement: re-run decided machines, iterating
   hlin_layers_step manually and accumulating rule-endpoint states over the
   WHOLE derivation (Sacc), alongside the final-tower stats (Sfin).
   Sfin = states liveness gets for free from the retained proof;
   Sacc = ceiling on what rule-granularity decomposition can ever show. *)

open Inductive
module I = Inductive_inf

let rec int_of_pos = function
  | XH -> 1
  | XO p -> 2 * int_of_pos p
  | XI p -> 2 * int_of_pos p + 1

let int_of_n = function N0 -> 0 | Npos p -> int_of_pos p

let rec pos_of_int i =
  if i <= 1 then XH
  else if i land 1 = 1 then XI (pos_of_int (i / 2))
  else XO (pos_of_int (i / 2))

let n_of_int i = if i = 0 then N0 else Npos (pos_of_int i)

let rec nat_of_int i = if i <= 0 then O else S (nat_of_int (i - 1))

type acc = {
  mutable states_ms : int list;
  mutable states_all : int list;
  mutable powsum : bool;
  mutable powsum2 : bool;
  mutable mul : bool;
  mutable arith : bool;
  mutable bincnt : bool;
}

let add l x = if List.mem x l then l else x :: l

let rec scan_nat acc (e : I.nat_expr) =
  match e with
  | I.Coq_from_nat _ | I.Coq_nat_var _ | I.Coq_nat_ivar -> ()
  | I.Coq_nat_add (a, b) -> scan_nat acc a; scan_nat acc b
  | I.Coq_nat_mul (a, b) -> acc.mul <- true; scan_nat acc a; scan_nat acc b
  | I.Coq_nat_powsum (_, x) -> acc.powsum <- true; scan_nat acc x
  | I.Coq_nat_powsum2 (_, x) -> acc.powsum2 <- true; scan_nat acc x

let rec scan_seg acc (e : I.seg_expr) =
  match e with
  | I.Coq_seg_nil | I.Coq_seg_sym _ | I.Coq_seg_block _ | I.Coq_seg_var _ -> ()
  | I.Coq_seg_concat (a, b) -> scan_seg acc a; scan_seg acc b
  | I.Coq_seg_repeat (a, n) -> scan_seg acc a; scan_nat acc n
  | I.Coq_seg_arithseq (ls, n) ->
    acc.arith <- true;
    List.iter (fun ((_, _), n') -> scan_nat acc n') ls;
    scan_nat acc n

let rec scan_side acc (e : I.side_expr) =
  match e with
  | I.Coq_side_0inf | I.Coq_side_var _ -> ()
  | I.Coq_side_concat (a, b) -> scan_seg acc a; scan_side acc b
  | I.Coq_side_binary (_, n) -> acc.bincnt <- true; scan_nat acc n
  | I.Coq_side_binary_Pos (_, n) -> acc.bincnt <- true; scan_nat acc n
  | I.Coq_side_3ary_Pos (_, n) -> acc.bincnt <- true; scan_nat acc n
  | I.Coq_side_binary_dec (_, a, b, c) ->
    acc.bincnt <- true; scan_nat acc a; scan_nat acc b; scan_nat acc c
  | I.Coq_side_BL (_, n) -> acc.bincnt <- true; scan_nat acc n

let scan_config acc ~ms (c : I.config_expr) =
  let (((l, r), q), _) = c in
  let qi = int_of_n q in
  acc.states_all <- add acc.states_all qi;
  if ms then acc.states_ms <- add acc.states_ms qi;
  scan_side acc l; scan_side acc r

let scan_prop0 acc (p : I.prop0_expr) =
  match p with
  | I.Coq_nat_eq (a, b) -> scan_nat acc a; scan_nat acc b
  | I.Coq_seg_eq (a, b) | I.Coq_seg_rw (a, b) -> scan_seg acc a; scan_seg acc b
  | I.Coq_side_eq (a, b) | I.Coq_side_rw (a, b) -> scan_side acc a; scan_side acc b
  | I.Coq_config_eq (a, b) | I.Coq_config_rw (a, b) ->
    scan_config acc ~ms:false a; scan_config acc ~ms:false b
  | I.Coq_false_prop0 -> ()
  | I.Coq_multistep_expr (a, b, n) ->
    scan_config acc ~ms:true a; scan_config acc ~ms:true b; scan_nat acc n
  | I.Coq_multistep_lb_expr (a, b, n) ->
    scan_config acc ~ms:true a; scan_config acc ~ms:true b; scan_nat acc n
  | I.Coq_multistep'_expr (a, b, _) ->
    scan_config acc ~ms:true a; scan_config acc ~ms:true b

let scan_prop_expr' acc (w : I.prop_expr') =
  let ((hyps, concls), _) = w in
  List.iter (scan_prop0 acc) hyps;
  List.iter (scan_prop0 acc) concls

let fresh_acc () = { states_ms = []; states_all = []; powsum = false;
                     powsum2 = false; mul = false; arith = false; bincnt = false }

let scan_layers acc layers =
  List.iter (fun layer ->
    let (((w1_, w0_), (w1, w0)), (_, _)) = layer in
    scan_prop_expr' acc w1_; scan_prop_expr' acc w0_;
    scan_prop_expr' acc w1; scan_prop_expr' acc w0)
    layers

let show_states l =
  let l = List.sort compare l in
  String.concat "" (List.map (fun q ->
    if q < 26 then String.make 1 (Char.chr (Char.code 'A' + q))
    else "?") l)

exception Timed_out

let with_timeout secs f =
  let old = Sys.signal Sys.sigalrm (Sys.Signal_handle (fun _ -> raise Timed_out)) in
  ignore (Unix.alarm secs);
  Fun.protect ~finally:(fun () ->
    ignore (Unix.alarm 0);
    Sys.set_signal Sys.sigalrm old)
    f

let configs : (string * I.coq_Config) list = [
  ("default", I.default_config);
  ("arithseq", I.config_arithseq N0);
  ("exploop", I.config_exploop I.default_config);
  ("arith_exploop", I.config_exploop (I.config_arithseq N0));
  ("bsz2", I.config_fixed_block_size (nat_of_int 2));
  ("bsz3", I.config_fixed_block_size (nat_of_int 3));
  ("bsz2_exploop", I.config_exploop (I.config_fixed_block_size (nat_of_int 2)));
]

let find_config name = List.assoc name configs

(* Manual iteration mirroring hlin_layers_steps, scanning every state. *)
let run_instrumented tm cfg maxT a_acc =
  let init = (I.reset_hlin_layers (I.initial_steps_ex_prop tm cfg), true) in
  let rec go st i =
    let (layers, _) = st in
    scan_layers a_acc layers;
    if i >= maxT then None
    else
      match I.hlin_layers_step tm cfg st with
      | Inl st' -> go st' (i + 1)
      | Inr layers' -> scan_layers a_acc layers'; Some layers'
  in
  go init 0

(* Input: TSV lines "<tm>\tNONHALT\tcfg=<name>..." from measure.ml output. *)
let () =
  let file = Sys.argv.(1) in
  let maxT = if Array.length Sys.argv > 2 then int_of_string Sys.argv.(2) else 100000 in
  let tmo = if Array.length Sys.argv > 3 then int_of_string Sys.argv.(3) else 120 in
  let ic = open_in file in
  (try
    while true do
      let line = String.trim (input_line ic) in
      if line <> "" then begin
        match String.split_on_char '\t' line with
        | tm_str :: "NONHALT" :: rest ->
          let cfg_name =
            match List.find_opt (fun s -> String.length s > 4 && String.sub s 0 4 = "cfg=") rest with
            | Some s -> String.sub s 4 (String.length s - 4)
            | None -> "default"
          in
          let tm = tM'_from_str tm_str in
          let cfg = find_config cfg_name in
          let a_acc = fresh_acc () in
          (try
            with_timeout tmo (fun () ->
              match run_instrumented tm cfg maxT a_acc with
              | Some layers ->
                let a_fin = fresh_acc () in
                scan_layers a_fin layers;
                Printf.printf
                  "%s\tOK\tcfg=%s\tSfin=%s\tSaccMS=%s\tSaccAll=%s\tpowsum=%b\tpowsum2=%b\tmul=%b\tarith=%b\tbincnt=%b\tfin_powsum=%b\tfin_mul=%b\n%!"
                  tm_str cfg_name
                  (show_states a_fin.states_ms)
                  (show_states a_acc.states_ms) (show_states a_acc.states_all)
                  a_acc.powsum a_acc.powsum2 a_acc.mul a_acc.arith a_acc.bincnt
                  a_fin.powsum a_fin.mul
              | None -> Printf.printf "%s\tNOREPRO\tcfg=%s\n%!" tm_str cfg_name)
          with Timed_out -> Printf.printf "%s\tTIMEOUT\tcfg=%s\n%!" tm_str cfg_name)
        | _ -> ()
      end
    done
  with End_of_file -> ());
  close_in ic
