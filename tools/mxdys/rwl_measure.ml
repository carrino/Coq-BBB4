(* Stage 0 RWLAcc sweep driver over the extracted decide_nonhalt. *)

open RWLX

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

(* (name, bsz, bmaxT, use_acc, mnc, T) *)
let params = [
  ("b2",  2, 3200, true, 0, 10_000_000);
  ("b3",  3, 3200, true, 0, 10_000_000);
  ("b4",  4, 3200, true, 0, 10_000_000);
  ("b5",  5, 3200, true, 0, 10_000_000);
  ("b6",  6, 3200, true, 0, 10_000_000);
  ("b8",  8, 3200, true, 0, 10_000_000);
  ("b15", 15, 3200, true, 0, 10_000_000);
]

let run_one tm_str tmo nparam =
  let tm = parse_tm tm_str in
  let rec go = function
    | [] -> Printf.printf "%s\tFAIL\n%!" tm_str
    | (name, bsz, bmaxT, use_acc, mnc, tt) :: rest ->
      let ok =
        try
          with_timeout tmo (fun () ->
            rwl_decide tm (nat_of_int bsz) (nat_of_int bmaxT) use_acc
              (n_of_int mnc) (n_of_int tt))
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
  let tmo = if Array.length Sys.argv > 2 then int_of_string Sys.argv.(2) else 20 in
  let nparam = if Array.length Sys.argv > 3 then int_of_string Sys.argv.(3) else List.length params in
  let ic = open_in file in
  (try
    while true do
      let line = String.trim (input_line ic) in
      if line <> "" then run_one line tmo nparam
    done
  with End_of_file -> ());
  close_in ic
