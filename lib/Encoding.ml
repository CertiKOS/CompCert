open Maps
open RelocProgram
open Camlcoq
    
let char_of_byte i =
  if 32 <= i && i <= 126
  then Char.chr i else '.'

let rec take_drop n l =
  match n, l with
  | 0, l -> ([],l)
  | _, h::t ->
    let (l1, l2) = take_drop (n-1) t in
    (h::l1, l2)
  | _, [] -> ([],[])

let rec dump_bytes sbytes : unit =
  if sbytes = [] then ()
  else
    begin
      let (l1,l2) = take_drop 16 sbytes in
      Printf.printf "%s %s\n"
        (String.concat " " (List.map (fun i -> Printf.sprintf "%02x" i)l1))
        (String.concat "" (List.map (fun i -> Printf.sprintf "%c" (char_of_byte i))l1));
      dump_bytes l2
    end

let dump_bytes sbytes =
  let sbytes = List.map (fun b -> Camlcoq.Z.to_int (Integers.Byte.unsigned b)) sbytes in
  dump_bytes sbytes




let dump_strmap strmap : unit =
  let elts = PTree.elements strmap in
  let elts = List.map (fun (pkey, zofs) -> (Camlcoq.extern_atom pkey, Camlcoq.Z.to_int zofs)) elts in
  let elts = List.sort (fun e1 e2 -> compare (snd e1) (snd e2)) elts in
  List.iter (fun (str, ofs) -> Printf.printf "%s -> %d\n" str ofs) elts


let dump_symtable symt =
  List.iteri (fun i symt_entry ->
      let id = match symbentry_id symt_entry with
          Some x -> x
        | _ -> BinNums.Coq_xH in
      let zid = Camlcoq.P.to_int id in
      let s = extern_atom id in
      Printf.printf "%02d: %d '%s'\n" i zid s
    ) symt
