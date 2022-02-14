open Api
open Parsers
module T = Kernel.Term
module B = Kernel.Basic
module Typer = Typerr.Default

let curmid = ref (B.mk_mident "")

let set_debug_mode opts =
  try Env.set_debug_mode opts
  with Env.DebugFlagNotRecognized c ->
    if c = 'a' then B.Debug.enable_flag Meta.debug_flag
    else raise (Env.DebugFlagNotRecognized c)

module P = Pp.Make (struct let get_name () = !curmid end)

let run file =
  let input = Parser.input_from_file file in
  let entries = Parser.parse input in
  let env = Env.init input in
  let handle_entry = fun entry ->
    begin 
      let print_entry = P.print_entry Format.std_formatter in
      let newentry = match entry with
      | Entry.Decl (lc, id, scope, st, ty) ->
          let (ty',_) = Typer.infer (Env.get_signature env) [] ty in
          (* B.Debug.(debug d_notice) "Declaration of constant '%a'." B.pp_ident id; *)
          let en = Entry.Decl (lc, id, scope, st, ty') in
          print_entry en;
          Env.declare env lc id scope st ty';
          en
      | Entry.Def (lc, id, scope, opaque, tyopt, te) -> begin
          (* let opaque_str = if opaque then " (opaque)" else "" in
          B.Debug.(debug d_notice)
            "Definition of symbol '%a'%s." B.pp_ident id opaque_str; *)
          match tyopt with
          | Some ty -> begin
              let (ty',_) = Typer.infer (Env.get_signature env) [] ty in
              let te' = Typer.check (Env.get_signature env) [] te ty' in
              let en = Entry.Def (lc, id, scope, opaque, Some ty', te') in
              print_entry en;
              Env.define env lc id scope opaque te' (Some ty');
              en
            end
          | None ->
            begin
              let (te',ty') = Typer.infer (Env.get_signature env) [] te in
              let en = Entry.Def (lc, id, scope, opaque, Some ty', te') in
              print_entry en;
              Env.define env lc id scope opaque te' (Some ty');
              en
            end
          end
      | _ -> failwith "not able to handle entry"
      in
      ignore (newentry)
    end
  in
  List.iter handle_entry entries


(** Polymorphic definitions are generated from these files *)
let poly_file = ref "tests/testfile.dk"
let _ =
  let usage_msg = "Usage " ^ Sys.argv.(0) ^ "[OPTION]... [FILES]..." in
  let speclist = [
    ("-I", Arg.String Files.add_path, "Add to include path");
    ( "-d",
        Arg.String set_debug_mode,
        " flags enables debugging for all given flags" );] in
  Arg.parse speclist (fun s -> poly_file := s) usage_msg;
  run !poly_file