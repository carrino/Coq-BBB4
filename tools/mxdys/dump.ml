(* Diagnostic: iterate hlin_layers_step on one machine/config, printing the
   evolving layer tower, and dump the final rules in full. *)

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

let buf = Buffer.create 4096
let pr fmt = Printf.ksprintf (Buffer.add_string buf) fmt

let show_q q =
  let qi = int_of_n q in
  if qi < 26 then String.make 1 (Char.chr (Char.code 'A' + qi)) else "?"

let show_sym s = string_of_int (int_of_n s)
let show_word w = "[" ^ String.concat "" (List.map show_sym w) ^ "]"

let rec show_nat_expr (e : I.nat_expr) =
  match e with
  | I.Coq_from_nat n -> string_of_int (int_of_n n)
  | I.Coq_nat_add (a, b) -> "(" ^ show_nat_expr a ^ "+" ^ show_nat_expr b ^ ")"
  | I.Coq_nat_mul (a, b) -> "(" ^ show_nat_expr a ^ "*" ^ show_nat_expr b ^ ")"
  | I.Coq_nat_powsum (k, x) -> Printf.sprintf "powsum%d(%s)" (int_of_n k) (show_nat_expr x)
  | I.Coq_nat_powsum2 (k, x) -> Printf.sprintf "powsum2_%d(%s)" (int_of_n k) (show_nat_expr x)
  | I.Coq_nat_var i -> "n" ^ string_of_int (int_of_pos i)
  | I.Coq_nat_ivar -> "i"

let rec show_seg (e : I.seg_expr) =
  match e with
  | I.Coq_seg_nil -> "ε"
  | I.Coq_seg_sym s -> show_sym s
  | I.Coq_seg_block w -> show_word w
  | I.Coq_seg_concat (a, b) -> show_seg a ^ " " ^ show_seg b
  | I.Coq_seg_repeat (a, n) -> "(" ^ show_seg a ^ ")^" ^ show_nat_expr n
  | I.Coq_seg_arithseq (ls, n) ->
    "arith[" ^ String.concat ";" (List.map (fun ((w, z), n') ->
      Printf.sprintf "%s%+d*%s" (show_word w) (int_of_n (match z with Zpos p -> Npos p | _ -> N0)) (show_nat_expr n')) ls)
    ^ "]^" ^ show_nat_expr n
  | I.Coq_seg_var i -> "S" ^ string_of_int (int_of_pos i)

let rec show_side (e : I.side_expr) =
  match e with
  | I.Coq_side_0inf -> "0inf"
  | I.Coq_side_var i -> "X" ^ string_of_int (int_of_pos i)
  | I.Coq_side_concat (a, b) -> show_seg a ^ " " ^ show_side b
  | I.Coq_side_binary (d1, n) -> Printf.sprintf "bin%s(%s)" (show_word d1) (show_nat_expr n)
  | I.Coq_side_binary_Pos ((( d0, d1), d1a), n) ->
    Printf.sprintf "binPos%s%s%s(%s)" (show_word d0) (show_word d1) (show_word d1a) (show_nat_expr n)
  | I.Coq_side_3ary_Pos (_, n) -> Printf.sprintf "3ary(%s)" (show_nat_expr n)
  | I.Coq_side_binary_dec (_, a, b, c) ->
    Printf.sprintf "binDec(%s,%s,%s)" (show_nat_expr a) (show_nat_expr b) (show_nat_expr c)
  | I.Coq_side_BL (_, n) -> Printf.sprintf "BL(%s)" (show_nat_expr n)

let show_config (c : I.config_expr) =
  let (((l, r), q), d) = c in
  let ds = match d with L -> "<" | R -> ">" in
  Printf.sprintf "{%s  %s[%s]  %s}" (show_side l) ds (show_q q) (show_side r)

let show_prop0 (p : I.prop0_expr) =
  match p with
  | I.Coq_nat_eq (a, b) -> "nat_eq " ^ show_nat_expr a ^ " = " ^ show_nat_expr b
  | I.Coq_seg_eq (a, b) -> "seg_eq " ^ show_seg a ^ " = " ^ show_seg b
  | I.Coq_side_eq (a, b) -> "side_eq " ^ show_side a ^ " = " ^ show_side b
  | I.Coq_config_eq (a, b) -> "config_eq " ^ show_config a ^ " = " ^ show_config b
  | I.Coq_seg_rw (a, b) -> "seg_rw " ^ show_seg a ^ " ~> " ^ show_seg b
  | I.Coq_side_rw (a, b) -> "side_rw " ^ show_side a ^ " ~> " ^ show_side b
  | I.Coq_config_rw (a, b) -> "config_rw " ^ show_config a ^ " ~> " ^ show_config b
  | I.Coq_false_prop0 -> "FALSE"
  | I.Coq_multistep_expr (a, b, n) ->
    show_config a ^ " -->[" ^ show_nat_expr n ^ "] " ^ show_config b
  | I.Coq_multistep_lb_expr (a, b, n) ->
    show_config a ^ " -->lb[" ^ show_nat_expr n ^ "] " ^ show_config b
  | I.Coq_multistep'_expr (a, b, h) ->
    show_config a ^ " -->' " ^ show_config b ^ (if h then " (halt)" else "")

let show_prop_expr' tag (w : I.prop_expr') =
  let ((hyps, concls), id) = w in
  pr "  %s (id=%d):\n" tag (int_of_pos id);
  List.iter (fun p -> pr "    hyp:  %s\n" (show_prop0 p)) hyps;
  List.iter (fun p -> pr "    ccl:  %s\n" (show_prop0 p)) concls

let dump_layers layers =
  List.iteri (fun i layer ->
    let (((w1_, w0_), (w1, w0)), (l, r)) = layer in
    pr "LAYER %d  (l=%d, r=%d)\n" i (int_of_n l) (int_of_n r);
    show_prop_expr' "w1_" w1_;
    show_prop_expr' "w0_" w0_;
    show_prop_expr' "w1 " w1;
    show_prop_expr' "w0 " w0)
    layers

let () =
  let tm_str = Sys.argv.(1) in
  let cfg_name = if Array.length Sys.argv > 2 then Sys.argv.(2) else "default" in
  let maxT = if Array.length Sys.argv > 3 then int_of_string Sys.argv.(3) else 20000 in
  let every = if Array.length Sys.argv > 4 then int_of_string Sys.argv.(4) else 2000 in
  let configs = [
    ("default", I.default_config);
    ("arithseq", I.config_arithseq N0);
    ("exploop", I.config_exploop I.default_config);
    ("arith_exploop", I.config_exploop (I.config_arithseq N0));
    ("bsz2", I.config_fixed_block_size (nat_of_int 2));
    ("bsz3", I.config_fixed_block_size (nat_of_int 3));
  ] in
  let cfg = List.assoc cfg_name configs in
  let tm = tM'_from_str tm_str in
  let init = (I.reset_hlin_layers (I.initial_steps_ex_prop tm cfg), true) in
  let rec go st i =
    let (layers, _) = st in
    if i mod every = 0 then begin
      Buffer.clear buf;
      pr "=== iter %d: %d layers ===\n" i (List.length layers);
      dump_layers layers;
      print_string (Buffer.contents buf); flush stdout
    end;
    if i >= maxT then (Printf.printf "=== GAVE UP at %d iters ===\n" maxT)
    else
      match I.hlin_layers_step tm cfg st with
      | Inl st' -> go st' (i + 1)
      | Inr layers' ->
        Buffer.clear buf;
        pr "=== SOLVED at iter %d ===\n" i;
        dump_layers layers';
        print_string (Buffer.contents buf)
  in
  go init 0
