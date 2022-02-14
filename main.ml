open Api
open Parsers
module T = Kernel.Term
module B = Kernel.Basic
module _ = Typerr

let curmid = ref (B.mk_mident "")

module P = Pp.Make (struct let get_name () = !curmid end)

let run file =
  let input = Parser.input_from_file file in
  let entries = Parser.parse input in
  let _ = Env.init input in
  List.iter (fun _ -> ()
    (* match entry with
    | Entry.Def (l,id,sc,opq,tyopt,te) -> entry
    | Entry.Decl (l,id,sc,st,te) -> entry
    | _ -> failwith "not one of def or decl" *)
  ) entries

(** Polymorphic definitions are generated from these files *)
let poly_file = ref "tests/testfile.dk"
let _ =
  let usage_msg = "Usage " ^ Sys.argv.(0) ^ "[OPTION]... [FILES]..." in
  let speclist = [("-I", Arg.String Files.add_path, "Add to include path")] in
  Arg.parse speclist (fun s -> poly_file := s) usage_msg;
  ignore @@ Env.init (Parser.input_from_file !poly_file)