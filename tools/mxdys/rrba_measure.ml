(* Stage 0 RRBA sweep driver over the extracted decide_loop2.
   Parses the standard TM text format in OCaml and sweeps the parameter
   grid used by mxdys' RRBAv*.v proofs, cheapest first. *)

open RRBAX

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

let parse_tm s =
  let rows = String.split_on_char '_' s in
  let tbl = Hashtbl.create 16 in
  List.iteri (fun q row ->
    let nsym = String.length row / 3 in
    for sym = 0 to nsym - 1 do
      let c0 = row.[3 * sym] and c1 = row.[3 * sym + 1] and c2 = row.[3 * sym + 2] in
      if c1 = 'L' || c1 = 'R' then begin
        let w = Char.code c0 - Char.code '0' in
        let d = if c1 = 'L' then L else R in
        let q' = Char.code c2 - Char.code 'A' in
        Hashtbl.replace tbl (q, sym) (w, d, q')
      end
    done) rows;
  fun (qn, sn) ->
    let q = int_of_n qn and s = int_of_n sn in
    match Hashtbl.find_opt tbl (q, s) with
    | Some (w, d, q') -> Some ((n_of_int w, d), n_of_int q')
    | None -> None

exception Timed_out

let with_timeout secs f =
  let old = Sys.signal Sys.sigalrm (Sys.Signal_handle (fun _ -> raise Timed_out)) in
  ignore (Unix.alarm secs);
  Fun.protect ~finally:(fun () ->
    ignore (Unix.alarm 0);
    Sys.set_signal Sys.sigalrm old)
    f

(* (name, mb0, mb1, n_skip, k, maxT, loop1_as_loop2) *)
let params = [
  ("k5T1000",       0, 16, 0, 5, 1000,  false);
  ("k6T3000",       0, 16, 0, 6, 3000,  false);
  ("s1k6T10000",    0, 16, 1, 6, 10000, false);
  ("k4T8000",       0, 16, 0, 4, 8000,  false);
  ("L1s1k6T10000",  0, 16, 1, 6, 10000, true);
  ("s1k6T40000",    0, 16, 1, 6, 40000, false);
  ("s2k6T60000",    0, 16, 2, 6, 60000, false);
  ("s2k7T40000",    0, 16, 2, 7, 40000, false);
  ("mb7s1k8T40000", 7, 16, 1, 8, 40000, false);
  ("mb8s1k5T20000", 8,  8, 1, 5, 20000, false);
]

let run_one tm_str tmo nparam =
  let tm = parse_tm tm_str in
  let rec go = function
    | [] -> Printf.printf "%s\tFAIL\n%!" tm_str
    | (name, mb0, mb1, n_skip, k, maxT, l1al2) :: rest ->
      let ok =
        try
          with_timeout tmo (fun () ->
            rrba_decide tm (nat_of_int mb0) (nat_of_int mb1)
              (nat_of_int n_skip) (nat_of_int k) l1al2 (n_of_int maxT))
        with Timed_out -> false
           | Stack_overflow -> false
      in
      if ok then Printf.printf "%s\tNONHALT\tcfg=%s\n%!" tm_str name
      else go rest
  in
  let rec take n l = if n <= 0 then [] else match l with [] -> [] | x :: r -> x :: take (n - 1) r in
  go (take nparam params)

let () =
  let file = Sys.argv.(1) in
  let tmo = if Array.length Sys.argv > 2 then int_of_string Sys.argv.(2) else 60 in
  let nparam = if Array.length Sys.argv > 3 then int_of_string Sys.argv.(3) else List.length params in
  let ic = open_in file in
  (try
    while true do
      let line = String.trim (input_line ic) in
      if line <> "" then run_one line tmo nparam
    done
  with End_of_file -> ());
  close_in ic
