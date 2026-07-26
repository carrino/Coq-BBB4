(* Does supplying a COUNTER HINT unlock mxdys' Inductive decider on our
   residue?

   Every config swept in wave-15's Stage 0 had ex_rules = [] -- yet the
   project README says the counter methods "require some hints from human",
   and the hint type is exactly our counter model:

     side_binary_Pos_inc_rule d0 d1 d1a qL qR QL QR :=
       (forall l r n, l <* d0 <* d1^^n <{{QL}} qL *> r -->+
                      l <* d1 <* d0^^n <* qR {{QR}}> r) /\
       (forall r n,   0inf <* d1a <* d1^^n <{{QL}} qL *> r -->+
                      0inf <* d1a <* d0 <* d0^^n <* qR {{QR}}> r)

   d1^^n is our [rep uS j]; d0 is our [uD]; d1a is the tape-edge word.  So an
   ENCDATA row IS a hint.  We have 25 of them.

   The hint is a search hint, not an axiom: Config_WF demands a PROOF of the
   rule, so anything decided this way still has to be re-proved.  This program
   only measures whether the hint makes the search succeed. *)

open Inductive
module I = Inductive_inf

let rec int_of_pos = function
  | XH -> 1 | XO p -> 2 * int_of_pos p | XI p -> 2 * int_of_pos p + 1
let int_of_n = function N0 -> 0 | Npos p -> int_of_pos p
let rec pos_of_int i =
  if i <= 1 then XH
  else if i land 1 = 1 then XI (pos_of_int (i / 2)) else XO (pos_of_int (i / 2))
let n_of_int i = if i = 0 then N0 else Npos (pos_of_int i)
let rec nat_of_int i = if i <= 0 then O else S (nat_of_int (i - 1))
let syms l = List.map n_of_int l

exception Timed_out
let with_timeout secs f =
  let old = Sys.signal Sys.sigalrm (Sys.Signal_handle (fun _ -> raise Timed_out)) in
  ignore (Unix.alarm secs);
  Fun.protect ~finally:(fun () -> ignore (Unix.alarm 0); Sys.set_signal Sys.sigalrm old) f

let decides tm cfg maxT =
  match I.hlin_layers_steps tm cfg (n_of_int maxT) with
  | Inl _ -> false
  | Inr layers ->
    (match layers with
     | ((_, (_, w0)), _) :: _ -> I.check_nonhalt (fst w0)
     | [] -> false)

(* one line: <spec> <TAB> d0 <TAB> d1 <TAB> d1a   (digit strings, e.g. 01) *)
let () =
  let file = Sys.argv.(1) in
  let maxT = if Array.length Sys.argv > 2 then int_of_string Sys.argv.(2) else 1000000 in
  let tmo  = if Array.length Sys.argv > 3 then int_of_string Sys.argv.(3) else 20 in
  let bsz  = if Array.length Sys.argv > 4 then int_of_string Sys.argv.(4) else 2 in
  let nedge = if Array.length Sys.argv > 5 then int_of_string Sys.argv.(5) else 3 in
  let digits s = List.init (String.length s) (fun i -> Char.code s.[i] - Char.code '0') in
  let ic = open_in file in
  (try while true do
    let line = String.trim (input_line ic) in
    if line <> "" then begin
      match String.split_on_char '\t' line with
      | spec :: d0s :: d1s :: d1as :: _ ->
        let tm = tM'_from_str spec in
        let d0 = syms (digits d0s) and d1 = syms (digits d1s)
        and d1a = syms (digits d1as) in
        let found = ref None in
        let edge = [[]; [n_of_int 0]; [n_of_int 1]] in
        (* T0 = initial concrete steps before the symbolic phase: a counter
           only shows its structure after the bootstrap, so 0 is wrong.
           bsz defaults to the digit length. *)
        let bsz = if bsz > 0 then bsz else List.length d1 in
        (try
          List.iter (fun t0 ->
          for ql = 0 to nedge-1 do for qr = 0 to nedge-1 do
            for cql = 0 to 3 do for cqr = 0 to 3 do
              if !found = None then begin
                let r = I.Coq_side_binary_Pos_inc_rule
                          (d0, d1, d1a, List.nth edge ql, List.nth edge qr,
                           n_of_int cql, n_of_int cqr) in
                let cfg = I.config_SBC' (n_of_int t0) (nat_of_int bsz) [r] in
                let ok = try with_timeout tmo (fun () -> decides tm cfg maxT)
                         with Timed_out -> false | Stack_overflow -> false in
                if ok then begin
                  found := Some (Printf.sprintf "T0=%d QL=%d QR=%d qL=%d qR=%d bsz=%d"
                                   t0 cql cqr ql qr bsz);
                  raise Exit
                end
              end
            done done
          done done) [0; 50; 200; 1000]
        with Exit -> ());
        (match !found with
         | Some w -> Printf.printf "%s\tHINT-DECIDED\t%s\n%!" spec w
         | None   -> Printf.printf "%s\tno\n%!" spec)
      | _ -> ()
    end
  done with End_of_file -> ());
  close_in ic
