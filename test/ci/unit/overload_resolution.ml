open Base
open Ast
open Typing.OverloadResolution

let qi name = QualIdent.from_list [ Ident.make Util.Loc.dummy name 0 ]
let formal ?(ghost = false) ?(implicit = false) type_ = { type_; ghost; implicit }
let known ?(ghost = false) tp = { type_ = Known tp; ghost }

let candidate ?(kind = Callable.Func) ?(ghost = false) ?(generics = [])
    ?(returns = Type.int) name parameters =
  { identity = qi name; kind; ghost; parameters; returns; generic_parameters = generics }

let resolve candidates args = resolve ~ghost_context:false candidates args

let selected name = function
  | Selected s -> assert (QualIdent.equal s.candidate.identity (qi name))
  | _ -> assert false

let ambiguous = function Ambiguous _ -> () | _ -> assert false
let deferred = function Deferred _ -> () | _ -> assert false
let mismatch = function Mismatch _ -> () | _ -> assert false

let () =
  let set = Type.set_typed Type.int and finite = Type.finset_typed Type.int in
  let broad = candidate "broad" [ formal set ]
  and narrow = candidate "narrow" [ formal finite ] in
  List.iter
    [ [ broad; narrow ]; [ narrow; broad ] ]
    ~f:(fun cs -> selected "narrow" (resolve cs [ known finite ]));
  selected "broad" (resolve [ narrow; broad ] [ known set ]);
  let integer = candidate "integer" [ formal Type.int ]
  and real = candidate "real" [ formal Type.real ] in
  selected "integer" (resolve [ real; integer ] [ known Type.int ]);
  selected "real" (resolve [ integer; real ] [ known Type.real ]);
  let left = candidate "left" [ formal finite; formal set ]
  and right = candidate "right" [ formal set; formal finite ] in
  ambiguous (resolve [ left; right ] [ known finite; known finite ]);
  let both = candidate "both" [ formal finite; formal finite ] in
  selected "both" (resolve [ left; right; both ] [ known finite; known finite ]);
  ambiguous
    (resolve [ integer; candidate "equal" [ formal Type.int ] ] [ known Type.int ]);
  selected "integer" (resolve [ integer; integer ] [ known Type.int ]);
  let match_ c args = match_candidate ~ghost_context:false c args in
  mismatch (match_ { integer with kind = Callable.Proc } [ known Type.int ]);
  mismatch (match_ integer []);
  mismatch (match_ integer [ known Type.int; known Type.int ]);
  let implicit =
    candidate "implicit" [ formal Type.int; formal ~implicit:true ~ghost:true Type.bool ]
  in
  selected "implicit" (resolve [ implicit ] [ known Type.int ]);
  mismatch
    (match_ (candidate "gap" [ formal ~implicit:true Type.int; formal Type.bool ]) []);
  mismatch (match_ integer [ known ~ghost:true Type.int ]);
  mismatch (match_ { integer with ghost = true } [ known Type.int ]);
  selected "ghost-formal"
    (resolve
       [ candidate "ghost-formal" [ formal ~ghost:true Type.int ] ]
       [ known ~ghost:true Type.int ]);
  let t = qi "T" in
  let generic =
    candidate ~generics:[ t ] ~returns:(Type.var t) "generic" [ formal (Type.var t) ]
  in
  selected "generic" (resolve [ generic ] [ known Type.int ]);
  let repeated =
    { generic with parameters = [ formal (Type.var t); formal (Type.var t) ] }
  in
  mismatch (match_ repeated [ known Type.int; known Type.real ]);
  deferred (resolve [ integer; generic ] [ { type_ = Unknown; ghost = false } ]);
  let empty = { type_ = Literal (Type.finset_typed Type.bot); ghost = false } in
  selected "narrow" (resolve [ broad; narrow ] [ empty ]);
  let collection =
    { generic with parameters = [ formal (Type.finset_typed (Type.var t)) ] }
  in
  deferred (resolve [ collection; narrow ] [ empty ]);
  begin match
    match_candidate ~expected:Type.int ~ghost_context:false collection [ empty ]
  with
  | Applicable s -> assert (Type.equal s.return_type Type.int)
  | _ -> assert false
  end;
  let integer = { integer with returns = Type.bool } in
  selected "integer"
    (Typing.OverloadResolution.resolve ~expected:Type.real ~ghost_context:false
       [ integer; real ]
       [ known Type.int ]);
  selected "generic"
    (Typing.OverloadResolution.resolve ~expected:Type.bool ~ghost_context:false
       [ generic ]
       [ known Type.int ]);
  let annotated = Type.mk_app ~loc:Util.Loc.dummy ~ghost:true Type.Int [] in
  selected "integer" (resolve [ integer ] [ known annotated ]);
  let finite_generic =
    { generic with parameters = [ formal (Type.set_typed (Type.var t)) ] }
  in
  selected "generic" (resolve [ finite_generic ] [ known finite ]);
  begin match
    Typing.OverloadResolution.resolve ~expected:Type.bool ~ghost_context:false [ generic ]
      [ known Type.int ]
  with
  | Selected solution ->
      assert (Type.equal solution.return_type Type.int);
      assert (List.equal Type.equal solution.parameter_types [ Type.int ])
  | _ -> assert false
  end;
  ambiguous
    (Typing.OverloadResolution.resolve ~expected:Type.real ~ghost_context:false
       [ integer; candidate ~returns:Type.real "other-result" [ formal Type.int ] ]
       [ known Type.int ]);
  begin match resolve [ integer ] [ known Type.bool ] with
  | No_match [ (identity, Argument) ] ->
      assert (QualIdent.equal identity integer.identity)
  | _ -> assert false
  end;
  begin match match_ repeated [ known Type.int; known Type.real ] with
  | Mismatch (Conflicting_binding variable) -> assert (QualIdent.equal variable t)
  | _ -> assert false
  end;
  let path names =
    QualIdent.from_list (List.map names ~f:(fun name -> QualIdent.unqualify (qi name)))
  in
  let original_t = path [ "F"; "A"; "T" ] in
  let decl =
    Callable.mk_call_decl ~kind:Func
      ~name:(QualIdent.unqualify (qi "f"))
      ~loc:Util.Loc.dummy ()
  in
  let decl =
    {
      decl with
      call_decl_formals =
        [
          Type.mk_var_decl ~ghost:true
            (QualIdent.unqualify (qi "x"))
            (Type.var original_t);
        ];
      call_decl_returns =
        [ Type.mk_var_decl (QualIdent.unqualify (qi "r")) (Type.var original_t) ];
    }
  in
  let symbol =
    ( path [ "F"; "f" ],
      Module.CallDef
        { call_decl = decl; call_def = Callable.FuncDef { func_body = None } },
      (true, false, [ (qi "F", QualIdent.to_list (qi "Instance")) ]) )
  in
  let instance_t = path [ "Instance"; "A"; "T" ] in
  begin match
    of_symbol
      ~identity:(path [ "Instance"; "f" ])
      ~generic_parameters:[ original_t ] symbol
  with
  | Some extracted ->
      assert (List.equal QualIdent.equal extracted.generic_parameters [ instance_t ]);
      assert (Type.equal extracted.returns (Type.var instance_t));
      begin match extracted.parameters with
      | [ parameter ] ->
          assert parameter.ghost;
          assert (Type.equal parameter.type_ (Type.var instance_t))
      | _ -> assert false
      end
  | None -> assert false
  end

let () =
  let unknown = { type_ = Unknown; ghost = false } in
  let integer = candidate "integer" [ formal Type.int ] in
  let real = candidate "real" [ formal Type.real ] in
  deferred (resolve [ integer; real ] [ unknown ]);
  deferred (resolve [ integer ] [ unknown ]);
  let mixed = candidate "mixed" [ formal Type.int; formal Type.bool ] in
  deferred (resolve [ mixed ] [ unknown; known Type.bool ]);
  begin match resolve [ mixed ] [ unknown; known Type.int ] with
  | No_match _ -> ()
  | _ -> assert false
  end;
  let t = qi "T" in
  let generic parameters = candidate ~generics:[ t ] "generic" parameters in
  let sets = generic [ formal (Type.set_typed (Type.var t)) ] in
  selected "integer" (resolve [ sets; integer ] [ known Type.int ]);
  begin match resolve [ sets ] [ known Type.int ] with
  | No_match _ -> ()
  | _ -> assert false
  end;
  let product =
    generic [ formal (Type.mk_prod Util.Loc.dummy [ Type.var t; Type.int ]) ]
  in
  let literal second =
    { type_ = Literal (Type.mk_prod Util.Loc.dummy [ Type.bot; second ]); ghost = false }
  in
  mismatch (match_candidate ~ghost_context:false product [ literal Type.bool ]);
  deferred (resolve [ product ] [ literal Type.int ]);
  let subtype = partial_subtype sets in
  let variable = Type.var t in
  assert (subtype (Type.map Type.real Type.int) (Type.map Type.int variable));
  assert (not (subtype (Type.map Type.int Type.bool) (Type.map Type.real variable)));
  assert (subtype (Type.finset_typed Type.real) (Type.finset_typed variable));
  assert (subtype (Type.finset_typed Type.real) (Type.set_typed variable));
  assert (not (subtype (Type.set_typed Type.real) (Type.finset_typed variable)));
  let fld tp = Type.mk_fld Util.Loc.dummy tp in
  assert (subtype (fld Type.real) (fld variable));
  assert (
    not
      (subtype
         (fld (Type.mk_prod Util.Loc.dummy [ Type.real; Type.bool ]))
         (fld (Type.mk_prod Util.Loc.dummy [ Type.int; variable ]))))
