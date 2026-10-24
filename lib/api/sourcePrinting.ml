open Base
open Raven
open Ast

let word name =
  (not (String.is_empty name))
  && (Char.is_alpha name.[0] || Char.equal name.[0] '_')
  && String.for_all name ~f:(fun c ->
      Char.is_alphanum c || Char.equal c '_' || Char.equal c '\'')

let callable_operator name =
  match Stdlib.Hashtbl.find_opt Frontend.Terminals.operator_table name with
  | Some (Frontend.Parser.LT | LEQ | UNION | INTER | DIFF | COLONCOLON) -> true
  | Some _ -> false
  | None ->
      (not (String.is_empty name))
      && String.for_all name ~f:(fun c -> String.mem "+-*%.:?><=&|!" c)
      && (String.mem "+-*%<>=!&|" name.[0] || String.is_suffix name ~suffix:":")

let enumeration name =
  let rec opener i =
    if i < String.length name && String.mem "([{<" name.[i] then opener (i + 1) else i
  in
  let n = opener 0 in
  if n = 0 then false
  else
    let opening = String.prefix name n in
    List.exists [ false; true ] ~f:(fun singleton ->
        String.equal name (Expr.enumeration_name opening ~singleton))

let printable id =
  let name = Ident.name id in
  let ordinary =
    word name
    && ((not (Ast.SourceKeywords.is_keyword name)) || not (Char.is_uppercase name.[0]))
  in
  let symbolic =
    callable_operator name || enumeration name
    || List.mem
         [ "_[_]"; "_[_:=_]"; "_[_.._]"; "_[.._]"; "_[_..]" ]
         name ~equal:String.equal
  in
  if id.ident_num = 0 then ordinary || symbolic
  else ordinary && not (Char.is_uppercase name.[0])

let stem id =
  let name =
    String.map (Ident.name id) ~f:(fun c ->
        if Char.is_alphanum c || Char.equal c '_' || Char.equal c '\'' then c else '_')
  in
  if String.is_empty name then "value"
  else if Char.is_alpha name.[0] || Char.equal name.[0] '_' then name
  else "value_" ^ name

let pr ~hooks ppf program =
  let seen = ref (Set.empty (module Ident)) in
  let collect id =
    seen := Set.add !seen id;
    Ident.to_source_string id
  in
  let print names ppf =
    let printers = Rewriter.printers_of_ext_hooks ~names hooks in
    printers.pr_module_instrs ppf program.Module.mod_def
  in
  (* Collect through the same printers, including extension patterns and witness names. *)
  let sink = Stdlib.Format.make_formatter (fun _ _ _ -> ()) (fun () -> ()) in
  print { SourceNames.ident_to_string = collect } sink;
  Stdlib.Format.pp_print_flush sink ();
  let taken =
    ref
      (Set.of_list
         (module String)
         (List.map (Set.to_list !seen) ~f:Ident.to_source_string))
  in
  let rec fresh base n =
    let candidate = base ^ "_" ^ Int.to_string n in
    if Set.mem !taken candidate then fresh base (n + 1)
    else begin
      taken := Set.add !taken candidate;
      candidate
    end
  in
  let aliases =
    Set.fold !seen
      ~init:(Map.empty (module Ident))
      ~f:(fun aliases id ->
        if printable id then aliases
        else Map.set aliases ~key:id ~data:(fresh (stem id) 1))
  in
  let names =
    {
      SourceNames.ident_to_string =
        (fun id ->
          Option.value (Map.find aliases id) ~default:(Ident.to_source_string id));
    }
  in
  print names ppf
