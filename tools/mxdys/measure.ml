(* Stage 0 measurement driver over the extracted Inductive decider.
   For each TM string: sweep configs; on a nonhalt verdict, walk the final
   hlin_layers and report (a) states covered by multistep rule endpoints,
   (b) states covered restricted to the w1 (acceleration) components,
   (c) whether any nat_expr uses powsum / powsum2 / mul. *)

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
  mutable states_ms : int list;   (* states at multistep rule endpoints *)
  mutable states_all : int list;  (* states in any config_expr *)
  mutable powsum : bool;
  mutable powsum2 : bool;
  mutable mul : bool;
  mutable arith : bool;           (* seg_arithseq used *)
  mutable bincnt : bool;          (* side_binary* / side_BL tape constructor used *)
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

(* Walk all layers: full accumulator + a separate accumulator restricted to
   the w1/w1_ (acceleration rule) components. *)
let analyze (layers : I.hlin_layer list) =
  let a_full = fresh_acc () in
  let a_w1 = fresh_acc () in
  List.iter (fun layer ->
    let (((w1_, w0_), (w1, w0)), (_, _)) = layer in
    scan_prop_expr' a_full w1_; scan_prop_expr' a_full w0_;
    scan_prop_expr' a_full w1; scan_prop_expr' a_full w0;
    scan_prop_expr' a_w1 w1_; scan_prop_expr' a_w1 w1)
    layers;
  (a_full, a_w1)

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

let rec take n l = if n <= 0 then [] else match l with [] -> [] | x :: r -> x :: take (n - 1) r
let rec drop n l = if n <= 0 then l else match l with [] -> [] | _ :: r -> drop (n - 1) r

let run_one tm_str maxT tmo ncfg offs =
  let tm = tM'_from_str tm_str in
  let maxT_n = n_of_int maxT in
  let rec try_cfgs = function
    | [] -> Printf.printf "%s\tFAIL\n%!" tm_str
    | (name, cfg) :: rest ->
      let result =
        try
          with_timeout tmo (fun () ->
            match I.hlin_layers_steps tm cfg maxT_n with
            | Inl _ -> None
            | Inr layers ->
              (match layers with
               | ((_, (_, w0)), _) :: _ ->
                 if I.check_nonhalt (fst w0) then Some (`Nonhalt layers)
                 else (match I.get_halts_at tm (fst w0) with
                       | Some _ -> Some `Halt
                       | None -> None)
               | [] -> None))
        with Timed_out -> None
           | Stack_overflow -> None
      in
      (match result with
       | Some (`Nonhalt layers) ->
         let (a_full, a_w1) = analyze layers in
         Printf.printf
           "%s\tNONHALT\tcfg=%s\tlayers=%d\tSms=%s\tSw1=%s\tSall=%s\tpowsum=%b\tpowsum2=%b\tmul=%b\tarith=%b\tbincnt=%b\n%!"
           tm_str name (List.length layers)
           (show_states a_full.states_ms) (show_states a_w1.states_ms)
           (show_states a_full.states_all)
           a_full.powsum a_full.powsum2 a_full.mul a_full.arith a_full.bincnt
       | Some `Halt -> Printf.printf "%s\tHALT\tcfg=%s\n%!" tm_str name
       | None -> try_cfgs rest)
  in
  try_cfgs (take ncfg (drop offs configs))

let () =
  let file = Sys.argv.(1) in
  let maxT = if Array.length Sys.argv > 2 then int_of_string Sys.argv.(2) else 100000 in
  let tmo = if Array.length Sys.argv > 3 then int_of_string Sys.argv.(3) else 30 in
  let ncfg = if Array.length Sys.argv > 4 then int_of_string Sys.argv.(4) else List.length configs in
  let offs = if Array.length Sys.argv > 5 then int_of_string Sys.argv.(5) else 0 in
  let ic = open_in file in
  (try
    while true do
      let line = String.trim (input_line ic) in
      if line <> "" then run_one line maxT tmo ncfg offs
    done
  with End_of_file -> ());
  close_in ic
