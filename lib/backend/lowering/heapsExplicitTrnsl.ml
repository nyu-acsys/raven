open Base
open Ast
open Ast.Stmt
open Ast.Expr
open Util
open HeapNames

(** The following grammar of assertion expressions is supported:

    a := e ==> a e ? a : a a && a a2

    a2 := a2 && a2 a2' forall (x:T)* :: a2

    a2' := a2' && a2' e ==> a2' e ? a2' : a2' a1

    a1 := a1' a1 && a1 exists (x:T)* :: a1

    a1' := a1' && a1' e ==> a1' e ? a1' : a1' a0

    a0 := a0 && a0 own(e, f, v) pred_name( e* ) e *)

type inhale_exhale = Inhale | Exhale
type conditionals = Expr.t list * Expr.t list
type conditions = Expr.t list
(* Two componends in conditionals are used to keep track of conditionals given before existential quants, and ones given after existential quants *)

type universal_quants = { univ_vars : (ident * var_decl) list; triggers : expr list list }

type existential_quant_record = {
  var_decl : var_decl;
  quantified_exprs : (expr * conditionals) list;
}

type existential_quants = existential_quant_record IdentMap.t

let unsupported_expr_error (expr : Expr.t) : 'a =
  Error.error (Expr.to_loc expr)
    ("Unsupported expression under inhale/exhale: " ^ Expr.to_source_string expr)

(* The chunk value stored in a predicate/invariant's heap for one occurrence.

   For an `inv` with no return (out) args, rewrite_add_pred_utils backs PredHeapRA$P
   with the trivial one-element RA (see generate_unit_pred_ra below) instead of
   Agree, so there's no RA-level constructor to apply here: the chunk is just the
   (empty) out-args tuple itself. Unfolding an `inv` never consumes it (Agree's frame
   doesn't decrement), so this changes nothing observable.

   For a `pred` with no return args, rewrite_add_pred_utils backs PredHeapRA$P with
   `Library.Nat` instead of CountAgree[()] -- same reasoning, minus the data
   constructor, but a `pred` *is* consumed by unfolding, so the count itself has to
   stay real: it's what makes folding a pred once and then unfolding it twice a
   genuine error rather than silently accepted. The chunk is just the literal `1`
   (one more fold), with no DataConstr wrapping since Nat's `T` is already `Int`.

   A `pred`/`inv` with return args always goes through CountAgree/Agree, wrapping the
   out-args in the RA's data constructor as before. *)
let mk_pred_new_chunk ~loc (call_decl_kind : Callable.call_kind)
    (heap_elem_type : type_expr) (pred_ra_constr : qual_ident) (out_args : expr list) :
    expr =
  match call_decl_kind with
  | Invariant when List.is_empty out_args ->
      Expr.set_type (Expr.mk_tuple ~loc out_args) heap_elem_type
  | Pred when List.is_empty out_args -> Expr.set_type (Expr.mk_int ~loc 1) heap_elem_type
  | Pred ->
      Expr.mk_app ~loc ~typ:heap_elem_type (Expr.DataConstr pred_ra_constr)
        [ Expr.mk_int 1; Expr.mk_tuple out_args ]
  | Invariant ->
      Expr.mk_app ~loc ~typ:heap_elem_type (Expr.DataConstr pred_ra_constr)
        [ Expr.mk_tuple out_args ]
  | _ -> Error.internal_error loc "Expected a predicate or invariant definition"

let generate_injectivity_assertions ~loc (universal_quants : universal_quants)
    (conditions : conditions) ~env_local_var_decls (expr : expr) : Stmt.t Rewriter.t =
  (* Running example :
      Say we have:
      forall a, b :: p1(a, b) && p2(a, b) ==> f(a, b)

      universal_quants : { a, b }
      conditions : [ p1(a, b); p2(a, b) ]
      expr : f(a, b)
  *)
  let univ_quants_list = universal_quants.univ_vars in

  (* [a, b] *)
  let univ_vars = List.map univ_quants_list ~f:(fun (_, var_decl) -> var_decl) in

  (* [a', b'] *)
  let dup_vars =
    List.map univ_quants_list ~f:(fun (_, var_decl) ->
        { var_decl with var_name = Ident.fresh loc var_decl.var_name.ident_name })
  in

  let alpha_renaming_map =
    List.fold2_exn univ_vars dup_vars
      ~init:(Map.empty (module QualIdent))
      ~f:(fun map old_var_decl new_var_decl ->
        Map.add_exn map
          ~key:(QualIdent.from_ident old_var_decl.var_name)
          ~data:
            (Expr.mk_var ~typ:new_var_decl.var_type
               (QualIdent.from_ident new_var_decl.var_name)))
  in

  (* [p1(a', b'); p2(a', b')] *)
  let renamed_conditions =
    List.map conditions ~f:(fun cond -> Expr.alpha_renaming cond alpha_renaming_map)
  in

  (* f(a', b') *)
  let renamed_expr = Expr.alpha_renaming expr alpha_renaming_map in

  (* f(a, b) == f(a', b') *)
  let expr_eq = Expr.mk_eq expr renamed_expr in

  (* [a == a'; b == b']  *)
  let vars_eq_list =
    List.map2_exn univ_vars dup_vars ~f:(fun old_var_decl new_var_decl ->
        Expr.mk_eq
          (Expr.mk_var ~typ:old_var_decl.var_type
             (QualIdent.from_ident old_var_decl.var_name))
          (Expr.mk_var ~typ:new_var_decl.var_type
             (QualIdent.from_ident new_var_decl.var_name)))
  in

  (* Triggered by f(a, b) and f(a', b'), if they mention all bound variables. The
     surrounding locals are bound only if they occur. *)
  let body =
    Expr.mk_impl
      (Expr.mk_chained_and ((expr_eq :: conditions) @ renamed_conditions))
      (Expr.mk_chained_and vars_eq_list)
  in
  let occurring = Expr.symbols body in
  let env_local_var_decls =
    List.filter env_local_var_decls ~f:(fun v ->
        Set.mem occurring (QualIdent.from_ident v.Type.var_name))
  in
  let bound_vars = univ_vars @ dup_vars @ env_local_var_decls in
  let trigs =
    let mentioned = Expr.symbols ~acc:(Expr.symbols expr) renamed_expr in
    if
      List.for_all bound_vars ~f:(fun v ->
          Set.mem mentioned (QualIdent.from_ident v.var_name))
    then [ [ expr; renamed_expr ] ]
    else []
  in

  let assert_expr =
    (* forall a, b, a', b' ::
       f(a, b) == f(a', b') && p1(a, b) && p2(a, b) && p1(a', b') && p2(a', b')  ==>
        a == a' && b == b'
    *)
    Expr.mk_binder ~loc ~typ:Type.bool ~trigs Forall bound_vars body
  in

  let assert_stmt =
    let error =
      ( Error.Verification,
        loc,
        "Could not prove the injectivity of the index expression for this iterated \
         separating conjunction" )
    in

    Stmt.mk_assert_expr ~loc
      ~cmnt:
        ("Injectivity assertion: " ^ "universal quants: "
        ^ String.concat ~sep:", "
            (List.map univ_vars ~f:(fun v -> Ident.to_string v.var_name))
        ^ "; expression: " ^ Expr.to_string expr)
      ~spec_error:[ Stmt.mk_const_spec_error error ]
      assert_expr
  in

  (* An expression that holds each of a, b as a component is injective. *)
  let is_univ_var e =
    match e with
    | Expr.App (Var qi, [], _) ->
        List.exists univ_vars ~f:(fun v ->
            QualIdent.equal qi (QualIdent.from_ident v.var_name))
    | _ -> false
  in
  let components = match expr with Expr.App (Tuple, es, _) -> es | e -> [ e ] in
  let trivially_injective =
    List.for_all univ_vars ~f:(fun v ->
        List.exists components ~f:(fun e ->
            is_univ_var e && Set.mem (Expr.symbols e) (QualIdent.from_ident v.var_name)))
  in
  Rewriter.return (if trivially_injective then Stmt.mk_skip ~loc else assert_stmt)

let compute_env_local_var_decls ~loc (expr : expr) (conds : conditions)
    (universal_quants : universal_quants) : var_decl list Rewriter.t =
  let open Rewriter.Syntax in
  let symbols =
    List.fold (expr :: conds)
      ~init:(Set.empty (module QualIdent))
      ~f:(fun symbols cond -> Expr.symbols ~acc:symbols cond)
  in

  let locals =
    let locals_set =
      Set.filter symbols ~f:(fun s ->
          QualIdent.is_local s
          && not
               (List.exists universal_quants.univ_vars ~f:(fun (i, _) ->
                    Ident.(i = QualIdent.unqualify s))))
    in

    Set.to_list locals_set
  in

  let* local_var_decls =
    Rewriter.List.map locals ~f:(fun qual_ident ->
        let+ symbol = Rewriter.find_and_reify qual_ident in
        match symbol with
        | VarDef v -> v.var_decl
        | _ -> Error.internal_error loc "expected a variable declaration")
  in

  let* () =
    Rewriter.Logs.debug (fun printers m ->
        m
          "heapsExplicitTrnsl.compute_env_local_var_decls: expr: %a;\n\
          \ conds: %a;\n\
          \ universal_quants: %a;\n\
          \ OUTPUT: local_var_decls: %a"
          printers.pr_expr expr printers.pr_expr_list conds printers.pr_type_var_decl_list
          (List.map ~f:snd universal_quants.univ_vars)
          printers.pr_type_var_decl_list local_var_decls)
  in
  Rewriter.return local_var_decls

(* Dead code, retained for potential future reuse -- not called anywhere.

   [generate_inv_function] below states the ISC inverse function's "left-inverse"
   axiom (what it currently calls [postcond2]) and proves the injectivity it relies on
   *unconditionally* -- i.e. for all values of the quantified variable(s), not just
   those satisfying the ISC's own guard/condition ([conds]). That's a strictly
   stronger (and in general unsound) statement: it's only valid when the ISC's index
   expression is injective on its whole domain, not merely within the guard.

   It was made unconditional deliberately, after measuring a real problem with the
   guarded form: when the guard *doesn't* hold, the guarded axiom's implication is
   vacuously true, giving Z3 no equality to close off a matching loop between this
   axiom and the "right-inverse" axiom ([postcond1]) -- each instantiation re-creates a
   fresh application of the other's trigger, so E-matching can keep re-firing both
   without bound. Dropping the guard turns every instantiation into a genuine unit
   equality, which collapses the loop via congruence closure immediately. Measured on
   the array benchmarks in `test/arrays`: Z3 quantifier instantiations dropped from ~98,551
   (guarded) to ~41,945 (unconditional, below even the ~51,956 baseline from before
   this ISC-sharing machinery existed at all); `test/ext/prophecy/dist_counter.rav`
   went from ~45s (and documented flakiness) to a stable ~2s. The entire `dune runtest`
   suite verifies identically either way, i.e. every ISC index expression in the
   current codebase happens to be unconditionally injective -- but that's an empirical
   observation about today's tests, not a property the compiler checks or guarantees
   for arbitrary future Raven programs. A program whose ISC genuinely relies on its
   guard for injectivity will simply fail to verify (the injectivity assertion is a
   real, checked proof obligation either way -- this can't produce a silent unsoundness,
   only a spurious verification failure).

   To revive guard-dependent handling: in [generate_inv_function], replace the
   [postcond2] block's body with [GuardedIscInvAxioms.postcond2 ~loc ~inv_fn_qual_ident
   ~ret_type inv_expr env_local_var_decls universal_quants conds], and change the
   [generate_injectivity_assertions] call a few lines below back to passing [conds]
   instead of [[]] (so the proof obligation matches what this weaker axiom needs).

   A cheaper middle ground than reverting wholesale: a syntactic check for
   unconditional injectivity (e.g. recognizing index expressions built from injective
   constructors/free functions independent of any bound), falling back to this guarded
   form only where that check fails. Deliberately not implemented speculatively --
   nothing so far demonstrates it's needed in practice. *)
module GuardedIscInvAxioms = struct
  let postcond2 ~loc ~(inv_fn_qual_ident : qual_ident) ~(ret_type : Type.t)
      (inv_expr : expr) (env_local_var_decls : var_decl list)
      (universal_quants : universal_quants) (conds : conditions) : Stmt.spec =
    let inverted_expr_with_inv_expr =
      Expr.mk_app ~loc ~typ:ret_type (Var inv_fn_qual_ident)
        (inv_expr :: List.map env_local_var_decls ~f:Expr.from_var_decl)
    in
    let spec_expr2 =
      let ret_var_decls =
        List.map universal_quants.univ_vars ~f:(fun (_, vd) ->
            Type.mk_var_decl ~const:true (Ident.fresh loc "$ret") ~loc vd.var_type)
      in
      (* x ~> ret0;; y ~> ret1 *)
      let ret_renam_map =
        List.fold2_exn universal_quants.univ_vars ret_var_decls
          ~init:(Map.empty (module QualIdent))
          ~f:(fun mp (_, vd) ret_vd ->
            Map.add_exn mp
              ~key:(QualIdent.from_ident vd.var_name)
              ~data:(Expr.from_var_decl ret_vd))
      in
      Expr.mk_binder Forall ~loc
        (ret_var_decls @ env_local_var_decls)
        ~trigs:[ [ Expr.alpha_renaming inverted_expr_with_inv_expr ret_renam_map ] ]
        (Expr.mk_impl ~loc
           (Expr.mk_chained_and ~loc
              (List.map conds ~f:(fun e -> Expr.alpha_renaming e ret_renam_map)))
           (Expr.mk_eq ~loc
              (Expr.mk_tuple ~loc
                 (List.map ret_var_decls ~f:(fun ret_vd -> Expr.from_var_decl ret_vd)))
              (Expr.alpha_renaming inverted_expr_with_inv_expr ret_renam_map)))
    in
    let error =
      ( Error.Verification,
        loc,
        "This iterated separating conjunction may not be injective on the quantified \
         variable(s) within its guard" )
    in
    Stmt.mk_spec ~spec_error:[ (fun _ _ -> error) ] spec_expr2
end

let generate_inv_function ~loc (universal_quants : universal_quants) (conds : conditions)
    (inv_expr : expr) ~(arg_expr : expr) : expr Rewriter.t =
  (* Logs.debug (fun m -> m "heapsExplicitTrnsl.generate_inv_function: Generating inv function for %a" Expr.pr inv_expr);
     Logs.debug (fun m -> m "arg_expr: %a" Expr.pr arg_expr);
     Logs.debug (fun m -> m "inv_expr_type: %a; arg_expr_type: %a" Type.pr (Expr.to_type inv_expr) Type.pr (Expr.to_type arg_expr)); *)
  let open Rewriter.Syntax in
  let* tp1 = !Rewriter.expand_type_expr_ref (Expr.to_type inv_expr)
  and* tp2 = !Rewriter.expand_type_expr_ref (Expr.to_type arg_expr) in

  (* [inv_expr] and [arg_expr] need not be *exactly* the same type anymore now that
     `FinSet[T] <: Set[T]` exists: e.g. `inv_expr` can be `{||}` (typed `FinSet[K]`,
     since set enumerations always prefer the tightest available type) while
     `arg_expr` is a universally-quantified variable genuinely ranging over `Set[K]`.
     Subtype-comparable is enough; below, [arg_type] uses [Type.join tp1 tp2] (not
     bare [tp1]) as the synthesized function's formal parameter type specifically so
     that it stays a supertype of whichever of the two is narrower, keeping the
     [arg_expr] passed as the actual argument sound to accept. *)
  assert (Type.(subtype_of tp1 tp2 || subtype_of tp2 tp1));

  if List.is_empty universal_quants.univ_vars then Rewriter.return inv_expr
  else begin
    let inv_fn_ident =
      Ident.fresh loc ("$inv_" ^ ProgUtils.serialize (Expr.to_string inv_expr))
    in

    let* env_local_var_decls =
      compute_env_local_var_decls ~loc inv_expr conds universal_quants
    in

    let arg_type = Type.join tp1 tp2 in

    let arg_var_decl =
      let arg_ident = Ident.fresh loc "res" in
      {
        Type.var_name = arg_ident;
        var_loc = loc;
        var_type = arg_type |> Type.set_ghost false;
        var_const = true;
        var_ghost = false;
        var_implicit = false;
      }
    in

    let formal_var_decls = arg_var_decl :: env_local_var_decls in

    let ret_type =
      Type.mk_prod loc
        (List.map universal_quants.univ_vars ~f:(fun (_, var_decl) -> var_decl.var_type))
    in

    let ret_var_decl =
      {
        Type.var_name = Ident.fresh loc "$ret";
        var_loc = loc;
        var_type = ret_type |> Type.set_ghost false;
        var_const = true;
        var_ghost = false;
        var_implicit = false;
      }
    in

    let call_decl =
      Callable.mk_call_decl ~kind:Func ~name:inv_fn_ident ~loc ~formals:formal_var_decls
        ~returns:[ ret_var_decl ] ~needs_mask:[] ~grants_mask:[] ()
    in

    let* inv_fn_qual_ident =
      let+ module_qual_ident = Rewriter.current_module_name in

      QualIdent.append module_qual_ident inv_fn_ident
    in

    let inv_fn_def =
      Module.CallDef Callable.{ call_decl; call_def = FuncDef { func_body = None } }
    in

    let inverted_expr =
      Expr.mk_app ~loc ~typ:ret_type (Var inv_fn_qual_ident)
        (arg_expr :: List.map env_local_var_decls ~f:Expr.from_var_decl)
    in

    (*  inhale forall x: Int, y: Bool :: p(x, y, env2) ==> own( l(x, y, env1), f, v(x, y, env3) )
     *
     *  ~~>
     *
     *  func inv(res: Ref, env1: T1, env2: T2) returns (ret: (Int, Bool))
     *
     *  auto lemma inverse_func_valid()
     *    ensures forall 
     *        res: Ref, env1: T1, env2: T2 :: 
     *          {inv(res, env1, env2)} 
     *      p( inv(res, env1, env2)#0, inv(res, env1, env2)#1, env2 ) ==> 
     *        l( inv(res, env1, env2)#0, inv(res, env1, env2)#1, env1 ) == res
     *
     *    ensures forall 
     *        ret: (Int, Bool), env1: T1, env2: T2 :: 
     *          {l(ret#0, ret#1, env1)} 
     *      p(ret#0, ret#1, env2) ==> inv(l(ret#0, ret#1, env1), env1, env2) == ret
     *  {
     *    assert forall 
     *        x1: Int, y1: Bool, x2: Int, y2: Bool, env1: T1, env2: T2 :: 
     *
     *        ( l(x1, y1, env1) == l(x2, y2, env1) && 
     *           p(x1, y1, env2) && p(x2, y2, env2) ) 
     *        ==> x1 == x2 && y1 == y2;
     *
     *    assume false;
     *  } 
     *)
    let* inv_fn_auto_lemma_def =
      let inv_fn_lemma_ident =
        Ident.fresh loc ("inverse_func_valid$" ^ Ident.to_string inv_fn_ident)
      in

      let preconds, postconds =
        let postcond1 =
          (* inv(res, env1, env2) *)
          let inverted_expr_with_res =
            Expr.mk_app ~loc ~typ:ret_type (Var inv_fn_qual_ident)
              (List.map formal_var_decls ~f:Expr.from_var_decl)
          in
          let spec_expr1 =
            (* x ~> inv(res, env1, env2)#0;; y ~> inv(res, env1, env2)#1 *)
            let inv_renam_map =
              if Int.(List.length universal_quants.univ_vars = 1) then
                match List.hd_exn universal_quants.univ_vars with
                | _, vd ->
                    Map.singleton
                      (module QualIdent)
                      (QualIdent.from_ident vd.var_name)
                      inverted_expr_with_res
              else
                List.foldi universal_quants.univ_vars
                  ~init:(Map.empty (module QualIdent))
                  ~f:(fun i mp (_, vd) ->
                    Map.add_exn mp
                      ~key:(QualIdent.from_ident vd.var_name)
                      ~data:(Expr.mk_tuple_lookup ~loc inverted_expr_with_res i))
            in

            Expr.mk_binder Forall ~loc formal_var_decls
              ~trigs:
                [
                  [
                    Expr.mk_app ~loc ~typ:ret_type (Var inv_fn_qual_ident)
                      (List.map formal_var_decls ~f:Expr.from_var_decl);
                  ];
                ]
              (Expr.mk_impl ~loc
                 (Expr.mk_chained_and ~loc
                    (List.map conds ~f:(fun e -> Expr.alpha_renaming e inv_renam_map)))
                 (Expr.mk_eq ~loc
                    (Expr.from_var_decl arg_var_decl)
                    (Expr.alpha_renaming inv_expr inv_renam_map)))
          in
          let error =
            ( Error.Verification,
              loc,
              "This iterated separating conjunction may not be injective on the \
               quantified variable(s)" )
          in
          Stmt.mk_spec ~spec_error:[ (fun _ _ -> error) ] spec_expr1
        in

        let postcond2 =
          (* inv(l(x, y, env1), env1, env2) *)
          let inverted_expr_with_inv_expr =
            Expr.mk_app ~loc ~typ:ret_type (Var inv_fn_qual_ident)
              (inv_expr :: List.map env_local_var_decls ~f:Expr.from_var_decl)
          in
          let spec_expr2 =
            let ret_var_decls =
              List.map universal_quants.univ_vars ~f:(fun (_, vd) ->
                  Type.mk_var_decl ~const:true (Ident.fresh loc "$ret") ~loc vd.var_type)
            in

            (* x ~> ret0;; y ~> ret1 *)
            let ret_renam_map =
              List.fold2_exn universal_quants.univ_vars ret_var_decls
                ~init:(Map.empty (module QualIdent))
                ~f:(fun mp (_, vd) ret_vd ->
                  Map.add_exn mp
                    ~key:(QualIdent.from_ident vd.var_name)
                    ~data:(Expr.from_var_decl ret_vd))
            in

            (* Unconditional -- no [conds] guard. See [GuardedIscInvAxioms] above for
               the guarded form this was weakened from, and why. *)
            Expr.mk_binder Forall ~loc
              (ret_var_decls @ env_local_var_decls)
              ~trigs:[ [ Expr.alpha_renaming inverted_expr_with_inv_expr ret_renam_map ] ]
              (Expr.mk_eq ~loc
                 (Expr.mk_tuple ~loc
                    (List.map ret_var_decls ~f:(fun ret_vd -> Expr.from_var_decl ret_vd)))
                 (Expr.alpha_renaming inverted_expr_with_inv_expr ret_renam_map))
          in
          let error =
            ( Error.Verification,
              loc,
              "This iterated separating conjunction may not be injective on the \
               quantified variable(s)" )
          in
          Stmt.mk_spec ~spec_error:[ (fun _ _ -> error) ] spec_expr2
        in

        ([], [ postcond1; postcond2 ])
      in

      let+ injectivity_assertion =
        (* [] rather than [conds]: proves injectivity of [inv_expr] unconditionally,
           matching postcond2's now-unconditional axiom above. See
           [GuardedIscInvAxioms] for the guarded pairing ([conds] passed here) this was
           weakened from. *)
        generate_injectivity_assertions ~loc universal_quants [] ~env_local_var_decls
          inv_expr
      in

      let call_decl =
        Callable.mk_call_decl ~kind:Lemma ~name:inv_fn_lemma_ident ~loc ~precond:preconds
          ~postcond:postconds ~is_auto:true ~needs_mask:[] ~grants_mask:[] ()
      in

      let lemma_body =
        Stmt.mk_block_stmt ~loc
          [ injectivity_assertion; Stmt.mk_assume_expr ~loc (Expr.mk_bool ~loc false) ]
      in

      let call_def =
        Module.CallDef
          Callable.{ call_decl; call_def = ProcDef { proc_body = Some lemma_body } }
      in

      call_def
    in

    let* _ = Rewriter.introduce_symbol inv_fn_def in
    let+ _ =
      Rewriter.introduce_typecheck_symbol ~loc ~f:Typing.check_symbol
        inv_fn_auto_lemma_def
    in

    inverted_expr
  end

(* `forall v :: heap[v] == id`: [heap] is the unit [id] everywhere. *)
let empty_heap (heap : var_decl) (v : var_decl) (id : expr) : expr =
  let entry = Expr.mk_maplookup (Expr.from_var_decl heap) (Expr.from_var_decl v) in
  Expr.mk_binder Forall [ v ] (Expr.mk_eq entry id)

(* This function generates a module which roughly looks like the following:
 *     module f$utils {
 *       type T = f.field_type.T;
 *   
 *       var id : T = f.field_type.id;
 *   
 *       func f$heapValid(h: Map[Ref, T]) returns (ret:Bool) {
 *         forall l: Ref :: T.valid(h[l])
 *       }
 *   
 *       func f$heapChunkComp(x1: T, x2: T) returns (ret: T) {
 *         T.comp(x1, x2)
 *       }
 *   
 *       func f$heapChunkFrame(x1: T, x2: T) returns (ret: T) {
 *         T.frame(x1, x2)
 *       }
 *   
 *       func f$heapchunk_compare(x1: T, x2: T) returns (ret: Bool) {
 *         T.valid(f$heapSubChunk(x1, x2))
 *       }
 *     }
 *)
let generate_utils_module ~(is_field : bool) ?(is_frac_field = false) (mod_ident : ident)
    (ra_qual_ident : qual_ident) ?(in_arg_typ = Type.ref) (loc : location) :
    Module.symbol Rewriter.t =
  assert ((not is_field) || (is_field && Type.equal in_arg_typ Type.ref));

  let open Rewriter.Syntax in
  let fld_elem_type = ProgUtils.get_ra_rep_type ra_qual_ident in

  let mod_decl =
    {
      Module.mod_decl_name = mod_ident;
      mod_decl_formals = [];
      mod_decl_returns = [];
      mod_decl_is_sealed = false;
      mod_decl_interfaces = Set.empty (module QualIdent);
      mod_decl_rep = None;
      mod_decl_is_ra = false;
      mod_decl_is_interface = false;
      mod_decl_status = NotFree;
      mod_decl_loc = loc;
    }
  in

  let* mod_def =
    let type_ident = ProgUtils.heap_utils_rep_type_ident loc in
    let type_tp_expr = Type.mk_var (QualIdent.from_ident type_ident) in

    let type_def =
      {
        Module.type_def_name = type_ident;
        type_def_expr = Some fld_elem_type;
        type_def_rep = true;
        type_def_is_free = false;
        type_def_loc = loc;
      }
    in

    let var_def =
      {
        Stmt.var_decl =
          Type.mk_var_decl ~loc ~const:true ~ghost:true
            (ProgUtils.heap_utils_id_ident loc)
            type_tp_expr;
        var_init =
          Some (Expr.mk_var ~typ:fld_elem_type (ProgUtils.get_ra_id ra_qual_ident));
        var_is_free = NotFree;
      }
    in

    let heap_formal_arg =
      Type.mk_var_decl ~loc ~const:true
        (*~ghost:true*) (Ident.fresh loc "h")
        (Type.mk_map loc in_arg_typ type_tp_expr)
    in
    let heap_valid_fn_decl =
      Callable.mk_call_decl ~kind:Func
        ~name:(ProgUtils.heap_utils_valid_ident loc)
        ~loc ~formals:[ heap_formal_arg ]
        ~returns:[ Type.mk_var_decl ~loc ~const:true (Ident.fresh loc "ret") Type.bool ]
        ~status:MachineFree ~needs_mask:[] ~grants_mask:[] ()
    in

    let l_var_decl = Type.mk_var_decl ~loc ~const:true (Ident.fresh loc "l") in_arg_typ in

    let ra_valid_fn_qual_ident = ProgUtils.get_ra_valid_fn_qual_ident ra_qual_ident in

    let heap_valid_fn_body =
      let heap_map_lookup_l =
        Expr.mk_maplookup ~loc
          (Expr.from_var_decl heap_formal_arg)
          (Expr.from_var_decl l_var_decl)
      in

      Expr.mk_binder ~loc ~typ:Type.bool Forall [ l_var_decl ]
        ~trigs:[ [ heap_map_lookup_l ] ]
        (Expr.mk_app ~loc ~typ:Type.bool (Expr.Var ra_valid_fn_qual_ident)
           [ heap_map_lookup_l ])
    in

    let heap_valid_fn =
      {
        Callable.call_decl = heap_valid_fn_decl;
        call_def = FuncDef { func_body = Some heap_valid_fn_body };
      }
    in

    let heap_valid_inhale_fn_decl =
      {
        heap_valid_fn_decl with
        (* Callable.call_decl_kind = Func; *)
        call_decl_name = ProgUtils.heap_utils_valid_inhale_ident loc;
      }
    in

    let heap_valid_fn_expr =
      Expr.mk_app ~loc ~typ:Type.bool
        (Var (QualIdent.from_ident heap_valid_fn_decl.call_decl_name))
        [ Expr.from_var_decl heap_formal_arg ]
    in

    let heap_valid_inhale_fn =
      {
        Callable.call_decl = heap_valid_inhale_fn_decl;
        call_def =
          FuncDef
            {
              func_body =
                Some
                  (if is_frac_field then
                     let null_id_check =
                       Expr.mk_eq ~loc
                         (Expr.mk_maplookup ~loc
                            (Expr.from_var_decl heap_formal_arg)
                            (Expr.mk_null ()))
                         (Expr.mk_var ~typ:type_tp_expr
                            (ProgUtils.get_ra_id ra_qual_ident))
                     in

                     Expr.mk_and [ heap_valid_fn_expr; null_id_check ]
                   else heap_valid_fn_expr);
            };
      }
    in

    let heap_add_chunk_fn_decl =
      Callable.mk_call_decl ~kind:Func
        ~name:(ProgUtils.heap_utils_comp_chunk_ident loc)
        ~loc
        ~formals:
          [
            Type.mk_var_decl ~loc ~const:true (Ident.fresh loc "x1") type_tp_expr;
            Type.mk_var_decl ~loc ~const:true (Ident.fresh loc "x2") type_tp_expr;
          ]
        ~returns:
          [ Type.mk_var_decl ~loc ~const:true (Ident.fresh loc "ret") type_tp_expr ]
        ~status:MachineFree ~needs_mask:[] ~grants_mask:[] ()
    in

    let heap_add_chunk_fn =
      {
        Callable.call_decl = heap_add_chunk_fn_decl;
        call_def =
          FuncDef
            {
              func_body =
                Some
                  (Expr.mk_app ~loc ~typ:type_tp_expr
                     (Expr.Var (ProgUtils.get_ra_comp_fn_qual_ident ra_qual_ident))
                     [
                       Expr.from_var_decl
                         (List.hd_exn heap_add_chunk_fn_decl.call_decl_formals);
                       Expr.from_var_decl
                         (List.nth_exn heap_add_chunk_fn_decl.call_decl_formals 1);
                     ]);
            };
      }
    in

    let heap_sub_chunk_fn_decl =
      Callable.mk_call_decl ~kind:Func
        ~name:(ProgUtils.heap_utils_frame_chunk_ident loc)
        ~loc
        ~formals:
          [
            Type.mk_var_decl ~loc ~const:true (Ident.fresh loc "x1") type_tp_expr;
            Type.mk_var_decl ~loc ~const:true (Ident.fresh loc "x2") type_tp_expr;
          ]
        ~returns:
          [ Type.mk_var_decl ~loc ~const:true (Ident.fresh loc "ret") type_tp_expr ]
        ~status:MachineFree ~needs_mask:[] ~grants_mask:[] ()
    in

    let heap_sub_chunk_fn =
      {
        Callable.call_decl = heap_sub_chunk_fn_decl;
        call_def =
          FuncDef
            {
              func_body =
                Some
                  (Expr.mk_app ~loc ~typ:type_tp_expr
                     (Expr.Var (ProgUtils.get_ra_frame_fn_qual_ident ra_qual_ident))
                     [
                       Expr.from_var_decl
                         (List.hd_exn heap_sub_chunk_fn_decl.call_decl_formals);
                       Expr.from_var_decl
                         (List.nth_exn heap_sub_chunk_fn_decl.call_decl_formals 1);
                     ]);
            };
      }
    in

    let heapchunk_compare_fn_decl =
      Callable.mk_call_decl ~kind:Func
        ~name:(ProgUtils.heap_utils_heapchunk_compare_ident loc)
        ~loc
        ~formals:
          [
            Type.mk_var_decl ~loc ~const:true (Ident.fresh loc "x1") type_tp_expr;
            Type.mk_var_decl ~loc ~const:true (Ident.fresh loc "x2") type_tp_expr;
          ]
        ~returns:[ Type.mk_var_decl ~loc ~const:true (Ident.fresh loc "ret") Type.bool ]
        ~status:MachineFree ~needs_mask:[] ~grants_mask:[] ()
    in

    let heapchunk_compare_fn =
      {
        Callable.call_decl = heapchunk_compare_fn_decl;
        call_def =
          FuncDef
            {
              func_body =
                Some
                  (Expr.mk_app ~loc ~typ:type_tp_expr (Expr.Var ra_valid_fn_qual_ident)
                     [
                       Expr.mk_app ~loc ~typ:type_tp_expr
                         (Expr.Var
                            (QualIdent.from_ident heap_sub_chunk_fn_decl.call_decl_name))
                         [
                           Expr.from_var_decl
                             (List.hd_exn heapchunk_compare_fn_decl.call_decl_formals);
                           Expr.from_var_decl
                             (List.nth_exn heapchunk_compare_fn_decl.call_decl_formals 1);
                         ];
                     ]);
            };
      }
    in

    Rewriter.return
      [
        Module.SymbolDef (Module.TypeDef type_def);
        SymbolDef (Module.VarDef var_def);
        SymbolDef (Module.CallDef heap_valid_fn);
        SymbolDef (Module.CallDef heap_valid_inhale_fn);
        SymbolDef (Module.CallDef heap_add_chunk_fn);
        SymbolDef (Module.CallDef heap_sub_chunk_fn);
        SymbolDef (Module.CallDef heapchunk_compare_fn);
      ]
  in

  Rewriter.return (Module.ModDef { mod_decl; mod_def })

let rewrite_add_field_utils (symbol : Module.symbol) : Module.symbol Rewriter.t =
  let open Rewriter.Syntax in
  match symbol with
  (* A manifest field shares the target's heap and utils module; generating a
     second set keyed on the alias would defeat the point. *)
  | FieldDef { field_alias = Some _; _ } -> Rewriter.return symbol
  | FieldDef f ->
      let* printers = Rewriter.current_printers in
      let* utils_module =
        let is_field_def_real_heap = ProgUtils.is_field_def_real_heap ~printers f in
        let ra_qual_ident = ProgUtils.field_get_ra_qual_iden f in
        let mod_ident = ProgUtils.field_utils_module_ident f.field_name in
        generate_utils_module ~is_field:true ~is_frac_field:is_field_def_real_heap
          mod_ident ra_qual_ident f.field_loc
      in

      let* _ =
        Rewriter.introduce_typecheck_symbol ~loc:f.field_loc ~f:Typing.check_symbol
          utils_module
      in

      Rewriter.return symbol
  | _ -> Rewriter.return symbol

(* An `inv` with no return (out) args owns nothing but the bare fact that it currently
   holds -- there's no data for two copies to agree or disagree on, so agreement is
   trivially satisfied. (Not done for `pred`: see mk_pred_new_chunk above for why that
   would be unsound, not just a missed optimization.) Rather than instantiate Agree
   (whose rep type is a 3-constructor datatype, and whose defining/auto-lemma axioms
   cost real datatype case-splitting in the backend once an ISC accumulates a few
   fold/unfold occurrences of the same invariant -- each occurrence mints fresh
   ground terms of that datatype that Z3 has to re-derive those facts against), build
   PredHeapRA$P directly as the one-element resource algebra: `T = ()`, with `valid`,
   `comp`, `frame`, `fpuAllowed` all constant. Nothing downstream needs it to come
   from a generic-functor instantiation -- `generate_utils_module` below only ever
   references it by qual_ident-based naming convention (`<ra>.valid`, `<ra>.T`, ...),
   so a hand-built concrete module works exactly the same way a `ModInst` would. *)
let generate_unit_pred_ra ~loc (mod_ident : ident) : Module.symbol Rewriter.t =
  let t_ident = ProgUtils.heap_utils_rep_type_ident loc in
  let t_type_expr = Type.mk_var (QualIdent.from_ident t_ident) in
  let unit_expr = Expr.set_type (Expr.mk_tuple ~loc []) t_type_expr in

  let type_def =
    {
      Module.type_def_name = t_ident;
      type_def_expr = Some (Type.mk_prod loc []);
      type_def_rep = true;
      type_def_is_free = false;
      type_def_loc = loc;
    }
  in

  let id_def =
    {
      Stmt.var_decl =
        Type.mk_var_decl ~loc ~const:true ~ghost:true
          (ProgUtils.heap_utils_id_ident loc)
          t_type_expr;
      var_init = Some unit_expr;
      var_is_free = NotFree;
    }
  in

  let mk_fn ~name ~num_formals ~ret_type ~body =
    let formals =
      List.init num_formals ~f:(fun i ->
          Type.mk_var_decl ~loc ~const:true
            (Ident.fresh loc (Printf.sprintf "x%d" i))
            t_type_expr)
    in
    {
      Callable.call_decl =
        Callable.mk_call_decl ~kind:Func ~name:(Ident.make loc name 0) ~loc ~formals
          ~returns:[ Type.mk_var_decl ~loc ~const:true (Ident.fresh loc "ret") ret_type ]
          ~status:MachineFree ~needs_mask:[] ~grants_mask:[] ();
      call_def = FuncDef { func_body = Some body };
    }
  in

  let valid_fn =
    mk_fn ~name:"valid" ~num_formals:1 ~ret_type:Type.bool ~body:(Expr.mk_bool ~loc true)
  in
  let comp_fn = mk_fn ~name:"comp" ~num_formals:2 ~ret_type:t_type_expr ~body:unit_expr in
  let frame_fn =
    mk_fn ~name:"frame" ~num_formals:2 ~ret_type:t_type_expr ~body:unit_expr
  in
  let fpu_allowed_fn =
    mk_fn ~name:"fpuAllowed" ~num_formals:2 ~ret_type:Type.bool
      ~body:(Expr.mk_bool ~loc true)
  in

  let mod_decl =
    {
      Module.mod_decl_name = mod_ident;
      mod_decl_formals = [];
      mod_decl_returns = [];
      mod_decl_is_sealed = false;
      mod_decl_interfaces = Set.empty (module QualIdent);
      mod_decl_rep = None;
      mod_decl_is_ra = false;
      mod_decl_is_interface = false;
      mod_decl_status = NotFree;
      mod_decl_loc = loc;
    }
  in

  let mod_def =
    [
      Module.SymbolDef (Module.TypeDef type_def);
      Module.SymbolDef (Module.VarDef id_def);
      Module.SymbolDef (Module.CallDef valid_fn);
      Module.SymbolDef (Module.CallDef comp_fn);
      Module.SymbolDef (Module.CallDef frame_fn);
      Module.SymbolDef (Module.CallDef fpu_allowed_fn);
    ]
  in

  Rewriter.return (Module.ModDef { mod_decl; mod_def })

let rewrite_add_pred_utils (c : Callable.t) : Callable.t Rewriter.t =
  let open Rewriter.Syntax in
  match c.call_decl.call_decl_kind with
  | Pred | Invariant ->
      let loc = c.call_decl.call_decl_loc in

      let* pred_heap_ra =
        if
          Poly.(c.call_decl.call_decl_kind = Invariant)
          && List.is_empty c.call_decl.call_decl_returns
        then
          let* unit_pred_ra =
            generate_unit_pred_ra ~loc
              (ProgUtils.pred_to_ra_mod_ident ~loc c.call_decl.call_decl_name)
          in
          Rewriter.introduce_typecheck_symbol ~loc ~f:Typing.check_symbol unit_pred_ra
        else if
          Poly.(c.call_decl.call_decl_kind = Pred)
          && List.is_empty c.call_decl.call_decl_returns
        then
          (* Unlike Invariant above, a no-return-arg Pred still needs real counting
             (see mk_pred_new_chunk's doc comment for why folding it can't be made
             idempotent), just not CountAgree's data-constructor wrapping around a
             value that's always (): `Library.Nat` -- rep type plain Int, no datatype
             at all -- is exactly CountAgree[()] with that wrapping stripped off:
             its comp/frame/valid are literally CountAgree's, specialized to a value
             that always agrees with itself. Nat takes no type argument. *)
          let instantiated_pred_heap_ra =
            Module.ModInst
              {
                mod_inst_name =
                  ProgUtils.pred_to_ra_mod_ident ~loc c.call_decl.call_decl_name;
                mod_inst_type = Predefs.lib_cancellative_ra_mod_qual_ident;
                mod_inst_def = Some (Predefs.lib_nat_mod_qual_ident, []);
                mod_inst_is_interface = false;
                mod_inst_is_sealed = false;
                mod_inst_is_free = false;
                mod_inst_loc = loc;
              }
          in
          Rewriter.introduce_typecheck_symbol ~loc ~f:Typing.check_symbol
            instantiated_pred_heap_ra
        else
          let pred_ret_type =
            Type.mk_prod c.call_decl.call_decl_loc
              (List.map c.call_decl.call_decl_returns ~f:(fun var_decl ->
                   var_decl.var_type))
          in

          let* pred_ret_type_module =
            ProgUtils.intros_type_module ~loc:c.call_decl.call_decl_loc
              ~f:Typing.check_symbol pred_ret_type
          in

          let mod_inst_type, mod_inst_def_ra =
            match c.call_decl.call_decl_kind with
            | Pred ->
                ( Predefs.lib_cancellative_ra_mod_qual_ident,
                  Predefs.lib_countAgreeRA_mod_qual_ident )
            | Invariant ->
                (Predefs.lib_lattice_ra_mod_qual_ident, Predefs.lib_agree_mod_qual_ident)
            | _ -> Error.internal_error loc "Expected a predicate or invariant"
          in

          let instantiated_pred_heap_ra =
            Module.ModInst
              {
                mod_inst_name =
                  ProgUtils.pred_to_ra_mod_ident ~loc c.call_decl.call_decl_name;
                mod_inst_type;
                mod_inst_def =
                  Some (mod_inst_def_ra, [ Module.ModArg pred_ret_type_module ]);
                mod_inst_is_interface = false;
                mod_inst_is_sealed = false;
                mod_inst_is_free = false;
                mod_inst_loc = loc;
              }
          in

          Rewriter.introduce_typecheck_symbol ~loc ~f:Typing.check_symbol
            instantiated_pred_heap_ra
      in
      let* () =
        Rewriter.Logs.debug (fun printers m ->
            m "Generated pred heap RA module: %a" QualIdent.pr pred_heap_ra)
      in

      let in_arg_typ =
        Type.mk_prod c.call_decl.call_decl_loc
          (List.map c.call_decl.call_decl_formals ~f:(fun var_decl -> var_decl.var_type))
      in

      let* utils_module =
        generate_utils_module ~is_field:false
          (ProgUtils.pred_utils_module_ident c.call_decl.call_decl_name)
          pred_heap_ra ~in_arg_typ loc
      in

      let* _ =
        Rewriter.introduce_typecheck_symbol ~loc ~f:Typing.check_symbol utils_module
      in

      Rewriter.return c
  | _ -> Rewriter.return c

let rewrite_add_atomics_utils (c : Callable.t) : Callable.t Rewriter.t =
  let open Rewriter.Syntax in
  match c.call_decl.call_decl_kind with
  | Proc ->
      if not (Callable.is_atomic c.call_decl) then Rewriter.return c
      else
        let loc = c.call_decl.call_decl_loc in

        let proc_concrete_args_typ =
          Type.mk_prod c.call_decl.call_decl_loc
            (List.filter_map c.call_decl.call_decl_formals ~f:(fun var_decl ->
                 if var_decl.var_implicit then None else Some var_decl.var_type))
        in

        let* proc_conrete_args_type_module =
          ProgUtils.intros_type_module ~loc:c.call_decl.call_decl_loc
            ~f:Typing.check_symbol proc_concrete_args_typ
        in

        let proc_ret_type =
          Type.mk_prod c.call_decl.call_decl_loc
            (List.map c.call_decl.call_decl_returns ~f:(fun var_decl -> var_decl.var_type))
        in

        let* proc_ret_type_module =
          ProgUtils.intros_type_module ~loc:c.call_decl.call_decl_loc
            ~f:Typing.check_symbol proc_ret_type
        in

        let instantiated_au_proc_heap_ra =
          Module.ModInst
            {
              mod_inst_name = ProgUtils.au_to_ra_mod_ident ~loc c.call_decl.call_decl_name;
              mod_inst_type = Predefs.lib_ra_mod_qual_ident;
              mod_inst_def =
                Some
                  ( Predefs.lib_atomic_token_ra_mod_qual_ident,
                    [
                      Module.ModArg proc_conrete_args_type_module;
                      Module.ModArg proc_ret_type_module;
                    ] );
              mod_inst_is_interface = false;
              mod_inst_is_sealed = false;
              mod_inst_is_free = false;
              mod_inst_loc = loc;
            }
        in

        let* au_proc_heap_ra =
          Rewriter.introduce_typecheck_symbol ~loc ~f:Typing.check_symbol
            instantiated_au_proc_heap_ra
        in
        let* () =
          Rewriter.Logs.debug (fun printers m ->
              m "Generated au heap RA module: %a" printers.pr_symbol
                instantiated_au_proc_heap_ra)
        in

        let in_arg_typ =
          Type.atomic_token (QualIdent.from_ident c.call_decl.call_decl_name)
        in

        let* utils_module =
          generate_utils_module ~is_field:false
            (ProgUtils.au_utils_module_ident c.call_decl.call_decl_name)
            au_proc_heap_ra ~in_arg_typ loc
        in

        let* _ =
          Rewriter.introduce_typecheck_symbol ~loc ~f:Typing.check_symbol utils_module
        in

        Rewriter.return c
  | _ -> Rewriter.return c

let introduce_heaps_in_stmts ~loc ~fields_list ~preds_list ~au_preds_list body :
    Stmt.t Rewriter.t =
  let open Rewriter.Syntax in
  (* TODO: Introduce variables of right types for predHeaps *)
  let* field_heap_var_defs =
    Rewriter.List.map fields_list ~f:(fun field_name ->
        let* field_symbol = Rewriter.find_and_reify field_name in

        let field_elem_type =
          match field_symbol with
          | FieldDef f -> (
              match f.field_type with
              | App (Fld, [ tp_expr ], _) -> tp_expr
              | _ -> Error.type_error f.field_loc "Expected field identifier.")
          | _ -> Error.internal_error Loc.dummy "expected a field_def"
        in

        (* Done so that Ident is aware of this name being used; prevents the same name from being generated again during SSA transform *)
        let _ = Ident.fresh loc (field_heap_name field_name).ident_name in

        let (heap_var_decl : var_decl) =
          {
            var_name = field_heap_name field_name;
            var_loc = loc;
            var_type = Type.mk_map loc Type.ref field_elem_type;
            var_const = false;
            var_ghost = false;
            var_implicit = false;
          }
        in

        let loc = Stmt.to_loc body in
        let* field_utils_id = ProgUtils.get_field_utils_id field_name in

        let assume_expr1 =
          let l_var =
            Type.
              {
                var_name = Ident.fresh loc "l";
                var_loc = loc;
                var_type = Type.ref;
                var_const = false;
                var_ghost = false;
                var_implicit = false;
              }
          in

          empty_heap heap_var_decl l_var field_utils_id
        in

        let _ = Ident.fresh loc (field_heap_name2 field_name).ident_name in

        let (heap_var_decl2 : var_decl) =
          {
            var_name = field_heap_name2 field_name;
            var_loc = loc;
            var_type = Type.mk_map loc Type.ref field_elem_type;
            var_const = false;
            var_ghost = false;
            var_implicit = false;
          }
        in

        let assume_expr2 =
          let l_var =
            {
              Type.var_name = Ident.fresh loc "l";
              var_loc = loc;
              var_type = Type.ref;
              var_const = false;
              var_ghost = false;
              var_implicit = false;
            }
          in

          empty_heap heap_var_decl2 l_var field_utils_id
        in

        Rewriter.return
          ( { Stmt.var_decl = heap_var_decl; var_init = None; var_is_free = NotFree },
            { Stmt.var_decl = heap_var_decl2; var_init = None; var_is_free = NotFree },
            Stmt.mk_assume_expr ~loc assume_expr1,
            Stmt.mk_assume_expr ~loc assume_expr2 ))
  in

  let* pred_heap_var_defs =
    Rewriter.List.map preds_list ~f:(fun pred_name ->
        let* pred_heap_elem_type_qual_ident =
          ProgUtils.get_pred_utils_rep_type pred_name
        in

        let pred_heap_elem_type = Type.mk_var pred_heap_elem_type_qual_ident in

        let* pred_in_types = ProgUtils.pred_in_types pred_name in

        (* Done so that Ident is aware of this name being used; prevents the same name from being generated again during SSA transform *)
        let _ = Ident.fresh loc (pred_heap_name pred_name).ident_name in

        let (heap_var_decl : var_decl) =
          {
            var_name = pred_heap_name pred_name;
            var_loc = loc;
            var_type =
              Type.mk_map loc (Type.mk_prod loc pred_in_types) pred_heap_elem_type;
            var_const = true;
            var_ghost = false;
            var_implicit = false;
          }
        in

        let loc = Stmt.to_loc body in
        let* pred_utils_id = ProgUtils.get_pred_utils_id loc pred_name in

        let assume_expr1 =
          let in_var =
            {
              Type.var_name = Ident.fresh loc "in";
              var_loc = loc;
              var_type = Type.mk_prod loc pred_in_types;
              var_const = false;
              var_ghost = false;
              var_implicit = false;
            }
          in

          empty_heap heap_var_decl in_var pred_utils_id
        in

        let _ = Ident.fresh loc (pred_heap_name2 pred_name).ident_name in

        let (heap_var_decl2 : var_decl) =
          {
            var_name = pred_heap_name2 pred_name;
            var_loc = loc;
            var_type =
              Type.mk_map loc (Type.mk_prod loc pred_in_types) pred_heap_elem_type;
            var_const = false;
            var_ghost = false;
            var_implicit = false;
          }
        in

        let loc = Stmt.to_loc body in
        let assume_expr2 =
          let in_var =
            {
              Type.var_name = Ident.fresh loc "in";
              var_loc = loc;
              var_type = Type.mk_prod loc pred_in_types;
              var_const = false;
              var_ghost = false;
              var_implicit = false;
            }
          in

          empty_heap heap_var_decl2 in_var pred_utils_id
        in

        Rewriter.return
          ( { Stmt.var_decl = heap_var_decl; var_init = None; var_is_free = NotFree },
            { Stmt.var_decl = heap_var_decl2; var_init = None; var_is_free = NotFree },
            Stmt.mk_assume_expr ~loc assume_expr1,
            Stmt.mk_assume_expr ~loc assume_expr2 ))
  in

  let* au_heap_var_defs =
    Rewriter.List.map au_preds_list ~f:(fun call_name ->
        let* au_heap_elem_type_qual_ident = ProgUtils.get_au_utils_rep_type call_name in

        let au_heap_elem_type = Type.mk_var au_heap_elem_type_qual_ident in

        (* Done so that Ident is aware of this name being used; prevents the same name from being generated again during SSA transform *)
        let _ = Ident.fresh loc (au_heap_name call_name).ident_name in

        let (heap_var_decl : var_decl) =
          {
            var_name = au_heap_name call_name;
            var_loc = loc;
            var_type = Type.mk_map loc (Type.atomic_token call_name) au_heap_elem_type;
            var_const = false;
            var_ghost = false;
            var_implicit = false;
          }
        in

        let* au_utils_id = ProgUtils.get_au_utils_id loc call_name in

        let assume_expr1 =
          let in_var =
            {
              Type.var_name = Ident.fresh loc "tok";
              var_loc = loc;
              var_type = Type.atomic_token call_name |> Type.set_ghost true;
              var_const = false;
              var_ghost = true;
              var_implicit = false;
            }
          in

          empty_heap heap_var_decl in_var au_utils_id
        in

        let _ = Ident.fresh loc (au_heap_name2 call_name).ident_name in

        let (heap_var_decl2 : var_decl) =
          {
            var_name = au_heap_name2 call_name;
            var_loc = loc;
            var_type = Type.mk_map loc (Type.atomic_token call_name) au_heap_elem_type;
            var_const = false;
            var_ghost = false;
            var_implicit = false;
          }
        in

        let assume_expr2 =
          let in_var =
            {
              Type.var_name = Ident.fresh loc "in";
              var_loc = loc;
              var_type = Type.atomic_token call_name;
              var_const = false;
              var_ghost = true;
              var_implicit = false;
            }
          in

          empty_heap heap_var_decl2 in_var au_utils_id
        in

        Rewriter.return
          ( { Stmt.var_decl = heap_var_decl; var_init = None; var_is_free = NotFree },
            { Stmt.var_decl = heap_var_decl2; var_init = None; var_is_free = NotFree },
            Stmt.mk_assume_expr ~loc assume_expr1,
            Stmt.mk_assume_expr ~loc assume_expr2 ))
  in

  let* init_assumes =
    Rewriter.List.fold_left ~init:[]
      (field_heap_var_defs @ pred_heap_var_defs @ au_heap_var_defs)
      ~f:(fun assumes (heap_var_decl, heap_var_decl2, assume_stmt1, assume_stmt2) ->
        Logs.debug (fun m ->
            m
              "HeapsExplicitTrnsl.introduce_heaps_in_stmts: heap_var_decl: %a; \
               heap_var_decl2: %a"
              Ident.pr heap_var_decl.var_decl.var_name Ident.pr
              heap_var_decl2.var_decl.var_name);
        let* _ = Rewriter.introduce_symbol (Module.VarDef heap_var_decl) in
        let+ _ = Rewriter.introduce_symbol (Module.VarDef heap_var_decl2) in
        assume_stmt1 :: assume_stmt2 :: assumes)
  in

  Rewriter.return (Stmt.mk_block_stmt ~loc (init_assumes @ [ body ]))

let rec rewrite_fpu (stmt : Stmt.t) : Stmt.t Rewriter.t =
  let open Rewriter.Syntax in
  match stmt.stmt_desc with
  | Basic (Fpu fpu_desc) ->
      let* field_symbol =
        let* symbol = Rewriter.find_and_reify fpu_desc.fpu_field in
        match symbol with
        | FieldDef f -> Rewriter.return f
        | _ -> Error.internal_error stmt.stmt_loc "expected a field_def"
      in

      let field_expr = Expr.mk_var ~typ:field_symbol.field_type fpu_desc.fpu_field in

      let fpu_allowed_qual_iden =
        let field_ra = ProgUtils.field_get_ra_qual_iden field_symbol in
        ProgUtils.get_ra_fpu_allowed_qual_ident field_ra
      in

      let* old_val =
        match fpu_desc.fpu_old_val with
        | Some expr -> Rewriter.return expr
        | None ->
            let* field_heap_symbol =
              let* symbol =
                Rewriter.find_and_reify
                  (QualIdent.from_ident (field_heap_name fpu_desc.fpu_field))
              in
              match symbol with
              | VarDef v -> Rewriter.return v.var_decl
              | _ -> Error.internal_error stmt.stmt_loc "expected a var_def"
            in

            Rewriter.return
            @@ Expr.mk_maplookup ~loc:stmt.stmt_loc
                 (Expr.from_var_decl field_heap_symbol)
                 fpu_desc.fpu_ref
      in

      let assert_stmt =
        let error =
          (Error.Verification, stmt.stmt_loc, "This update may not be frame-preserving")
        in
        Stmt.mk_assert_expr ~loc:stmt.stmt_loc
          ~cmnt:("FPU stmt: " ^ Stmt.to_string stmt)
          ~spec_error:[ Stmt.mk_const_spec_error error ]
          (Expr.mk_app ~loc:stmt.stmt_loc ~typ:Type.bool (Expr.Var fpu_allowed_qual_iden)
             [ old_val; fpu_desc.fpu_new_val ])
      in

      let exhale_stmt =
        let error =
          (Error.Verification, stmt.stmt_loc, "This update may not be frame-preserving")
        in
        Stmt.mk_exhale_expr ~loc:stmt.stmt_loc
          ~cmnt:("FPU stmt: " ^ Stmt.to_string stmt)
          ~spec_error:[ Stmt.mk_const_spec_error error ]
          (Expr.mk_app ~loc:stmt.stmt_loc ~typ:Type.perm Expr.Own
             [ fpu_desc.fpu_ref; field_expr; old_val ])
      in

      let inhale_stmt =
        Stmt.mk_inhale_expr ~loc:stmt.stmt_loc
          ~cmnt:("FPU stmt: " ^ Stmt.to_string stmt)
          (Expr.mk_app ~loc:stmt.stmt_loc ~typ:Type.perm Expr.Own
             [ fpu_desc.fpu_ref; field_expr; fpu_desc.fpu_new_val ])
      in

      let new_stmt =
        Stmt.mk_block_stmt ~loc:stmt.stmt_loc [ assert_stmt; exhale_stmt; inhale_stmt ]
      in

      Rewriter.return new_stmt
  | _ -> Rewriter.Stmt.descend stmt ~f:rewrite_fpu

let rec rewrite_binds (stmt : Stmt.t) : Stmt.t Rewriter.t =
  match stmt.stmt_desc with
  | Basic (Bind bind_desc) ->
      let open Rewriter.Syntax in
      let* bind_lhs =
        Rewriter.List.map bind_desc.bind_lhs ~f:(fun qual_ident ->
            let* qual_ident, symbol = Rewriter.resolve_and_find qual_ident in
            let+ symbol = Rewriter.Symbol.reify symbol in
            match symbol with
            | VarDef { var_decl; _ } -> Expr.mk_var ~typ:var_decl.var_type qual_ident
            | _ -> assert false)
      in

      let* () =
        Rewriter.Logs.debug (fun printers m ->
            m "HeapExplicitTrnsl.rewrite_binds: bind_lhs = %a; bind_rhs = %a"
              printers.pr_expr_list bind_lhs printers.pr_expr bind_desc.bind_rhs.spec_form)
      in

      let exis_vars =
        List.map bind_lhs ~f:(fun e ->
            let ident_name = "$bind_" ^ QualIdent.to_string (Expr.to_qual_ident e) in

            Type.mk_var_decl ~loc:stmt.stmt_loc ~ghost:true
              (Ident.fresh stmt.stmt_loc ident_name)
              (Expr.to_type e))
      in

      let alpha_renaming_map =
        List.fold2_exn bind_lhs exis_vars
          ~init:(Map.empty (module QualIdent))
          ~f:(fun renam_map e1 e2 ->
            Map.add_exn renam_map ~key:(Expr.to_qual_ident e1)
              ~data:(Expr.from_var_decl e2))
      in

      let spec_error =
        match bind_desc.bind_rhs.spec_error with
        | [] ->
            let error =
              ( Error.Verification,
                Expr.to_loc bind_desc.bind_rhs.spec_form,
                "The right-hand side of this bind statement may not hold" )
            in
            [ Stmt.mk_const_spec_error error ]
        | errors -> errors
      in
      let assert_stmt =
        Stmt.mk_assert_expr ~loc:stmt.stmt_loc
          ~cmnt:("Bind stmt: " ^ Stmt.to_string stmt)
          ~spec_error
          (Expr.mk_binder Exists ~loc:stmt.stmt_loc exis_vars
             (Expr.alpha_renaming bind_desc.bind_rhs.spec_form alpha_renaming_map))
      in

      let assume_stmt =
        Stmt.mk_assume_expr ~loc:stmt.stmt_loc
          ~cmnt:("Bind stmt: " ^ Stmt.to_string stmt)
          bind_desc.bind_rhs.spec_form
      in

      let new_stmt = Stmt.mk_block_stmt ~loc:stmt.stmt_loc [ assert_stmt; assume_stmt ] in
      Rewriter.return new_stmt
  | _ -> Rewriter.Stmt.descend stmt ~f:rewrite_binds

type expr_match = { var_decl : var_decl; expr : expr option }

let match_up_expr ~(printers : Rewriter.printers) (expr1 : expr) (expr2 : expr)
    (vars : var_decl list) : (var_decl * expr) ident_map option =
  (* expr1 is the expr with vars; expr2 is the one to be matched against. So expr1 is allowed to have more existentials than expr2. For first implementation, expr2 is not allowed to have any existentials for now *)

  (* Return value of None represents that the expressions did not match up *)

  (* Running example:
          expr1: forall a :: f(a) ==> exists b :: e(a, b)
          expr2: forall a1 :: f(a1) ==> e(a1, v)

          vars: [b]
  *)
  Logs.debug (fun m ->
      m "HeapsExplicitTrnsl.match_up_expr: expr1: %a; expr2: %a" printers.pr_expr expr1
        printers.pr_expr expr2);

  let rec match_up_expr (expr1 : expr) (expr2 : expr) (var_map : expr_match ident_map) :
      expr_match ident_map option =
    (* if Type.((Expr.to_type expr1) <> (Expr.to_type expr2)) then
         (Logs.debug (fun m -> m "HeapsExplicitTrnsl.match_up_expr: Type mismatch: %a; %a" Type.pr (Expr.to_type expr1) Type.pr (Expr.to_type expr2));
         None)
       else *)
    match (expr1, expr2) with
    | Binder (Compr, v_d1, _, e1, _), Binder (Compr, v_d2, _, e2, _)
    | Binder (Forall, v_d1, _, e1, _), Binder (Forall, v_d2, _, e2, _) ->
        if not (Int.equal (List.length v_d1) (List.length v_d2)) then None
        else
          let typ_check =
            List.for_all2_exn v_d1 v_d2 ~f:(fun vd1 vd2 ->
                Type.equal vd1.var_type vd2.var_type)
          in

          if not typ_check then None
          else
            let renaming_map =
              List.fold2_exn v_d1 v_d2
                ~init:(Map.empty (module QualIdent))
                ~f:(fun renam_map vd1 vd2 ->
                  Map.add_exn renam_map
                    ~key:(QualIdent.from_ident vd2.var_name)
                    ~data:(Expr.from_var_decl vd1))
            in

            (* renaming expr2 to use the same universal quants as expr1 *)
            let e2 = Expr.alpha_renaming e2 renaming_map in

            match_up_expr e1 e2 var_map
    | Binder (Exists, v_d1, _, e1, _), e2 ->
        let var_map =
          List.fold v_d1 ~init:var_map ~f:(fun var_map vd1 ->
              match Map.find var_map vd1.var_name with
              | Some _ -> var_map
              | None ->
                  Error.internal_error (Expr.to_loc expr1)
                    "unexpected existential quantifier in expr1; expected all \
                     existentials to be declared in var_map")
        in

        match_up_expr e1 e2 var_map
    | App (constr1, exprs1, _), App (constr2, exprs2, _) -> (
        match constr1 with
        | Var qual_ident
          when List.exists (Map.keys var_map) ~f:(fun iden ->
                   QualIdent.equal (QualIdent.from_ident iden) qual_ident) -> (
            let var_iden = QualIdent.to_ident qual_ident in

            let expr_match = Map.find_exn var_map var_iden in
            match expr_match.expr with
            | None ->
                let var_map =
                  Map.set var_map ~key:var_iden
                    ~data:{ expr_match with expr = Some expr2 }
                in

                Some var_map
            | Some e -> if Expr.alpha_equal e expr2 then Some var_map else None)
        | _ ->
            if Expr.equal_constr constr1 constr2 then
              if
                (* Logs.debug (fun m -> m "HeapsExplicitTrnsl.match_up_expr: expr1: %a; expr2: %a" Expr.pr expr1 Expr.pr expr2); *)
                List.length exprs1 <> List.length exprs2
              then None
              else
                let var_map_optn =
                  List.fold2_exn exprs1 exprs2 ~init:(Some var_map)
                    ~f:(fun var_map_optn e1 e2 ->
                      Option.flat_map var_map_optn ~f:(fun var_map ->
                          match_up_expr e1 e2 var_map))
                in

                var_map_optn
            else
              (* Logs.debug (fun m -> m "HeapsExplicitTrnsl.match_up_expr: Constructor mismatch: %a; %a" Expr.pr expr1 Expr.pr expr2); *)
              None)
    | _ -> None
  in

  let var_map_optn =
    match_up_expr expr1 expr2
      (Map.of_alist_exn
         (module Ident)
         (List.map vars ~f:(fun var_decl ->
              (var_decl.var_name, { var_decl; expr = None }))))
  in

  match var_map_optn with
  | Some var_map ->
      Some
        (Map.map var_map ~f:(fun { var_decl; expr } ->
             match expr with
             | Some e -> (var_decl, e)
             | None ->
                 Error.internal_error (Expr.to_loc expr1)
                   "expected all variables to be matched up"))
  | None -> None

(* Looks up an already-compiled inverse function for the ISC identified by
   [spec_source]/[conjunct_idx] (the [clause_idx]-th clause of the callable [decl_qi],
   [conjunct_idx]-th ISC within that clause -- see [Rewriter.state_isc_cache]), reusing it
   if the current occurrence's [(universal_quants, conds, inv_expr)] matches (via
   [match_up_expr]) the template recorded for the first occurrence seen for that key.
   Falls back to [generate_inv_function] (minting a fresh function, exactly as before)
   whenever there's no [spec_source], this is the first occurrence for the key, or -- as a
   pure safety net -- matching against a cached template unexpectedly fails.

   Returns the same [expr] [generate_inv_function] would (the inverse function applied to
   [arg_expr]), plus the "env" actual expressions to substitute for [inv_expr]'s free
   locals when a caller needs to reapply the same inverse function to [inv_expr] itself
   (e.g. for forward-trigger assertions) -- previously recomputed there via a second,
   independent [compute_env_local_var_decls] call. *)
let get_or_generate_inv_function ~loc (universal_quants : universal_quants)
    (conds : conditions) (inv_expr : expr) ~(arg_expr : expr)
    ~(spec_source : (qual_ident * int) option) ~(conjunct_idx : int) :
    (expr * expr list) Rewriter.t =
  let open Rewriter.Syntax in
  if List.is_empty universal_quants.univ_vars then Rewriter.return (inv_expr, [])
  else
    let mint_fresh () =
      let* inv_fn_expr =
        generate_inv_function ~loc universal_quants conds inv_expr ~arg_expr
      in
      let+ env_local_var_decls =
        compute_env_local_var_decls ~loc inv_expr conds universal_quants
      in
      (inv_fn_expr, env_local_var_decls)
    in
    match spec_source with
    | None ->
        let+ inv_fn_expr, env_local_var_decls = mint_fresh () in
        (inv_fn_expr, List.map env_local_var_decls ~f:Expr.from_var_decl)
    | Some (decl_qi, clause_idx) -> (
        let* isc_cache = Rewriter.current_isc_cache in
        let cache_key = (decl_qi, clause_idx, conjunct_idx) in
        match Hashtbl.find isc_cache cache_key with
        | None ->
            let* inv_fn_expr, env_local_var_decls = mint_fresh () in
            (match inv_fn_expr with
            | App (Var inv_fn_qual_ident, _, _) ->
                Hashtbl.set isc_cache ~key:cache_key
                  ~data:
                    Rewriter.
                      {
                        isc_inv_fn_qual_ident = inv_fn_qual_ident;
                        isc_univ_vars = universal_quants.univ_vars;
                        isc_conds = conds;
                        isc_inv_expr = inv_expr;
                        isc_env_var_decls = env_local_var_decls;
                      }
            | _ -> ());
            Rewriter.return
              (inv_fn_expr, List.map env_local_var_decls ~f:Expr.from_var_decl)
        | Some tmpl -> (
            let* printers = Rewriter.current_printers in
            let template_forall =
              Expr.mk_binder Forall
                (List.map tmpl.isc_univ_vars ~f:snd)
                (Expr.mk_tuple (tmpl.isc_conds @ [ tmpl.isc_inv_expr ]))
            in
            let occurrence_forall =
              Expr.mk_binder Forall
                (List.map universal_quants.univ_vars ~f:snd)
                (Expr.mk_tuple (conds @ [ inv_expr ]))
            in
            match
              match_up_expr ~printers template_forall occurrence_forall
                tmpl.isc_env_var_decls
            with
            | Some var_map ->
                let env_actual_exprs =
                  List.map tmpl.isc_env_var_decls ~f:(fun vd ->
                      snd (Map.find_exn var_map vd.var_name))
                in
                let ret_type =
                  Type.mk_prod loc
                    (List.map universal_quants.univ_vars ~f:(fun (_, vd) -> vd.var_type))
                in
                let inv_fn_expr =
                  Expr.mk_app ~loc ~typ:ret_type (Var tmpl.isc_inv_fn_qual_ident)
                    (arg_expr :: env_actual_exprs)
                in
                Rewriter.return (inv_fn_expr, env_actual_exprs)
            | None ->
                let+ inv_fn_expr, env_local_var_decls = mint_fresh () in
                (inv_fn_expr, List.map env_local_var_decls ~f:Expr.from_var_decl)))

module ParseAssertionLang = struct
  let rec parse_a ?cmnt ?spec_error ?spec_source ~loc
      ?(universal_quants : universal_quants = { univ_vars = []; triggers = [] })
      (conds : conditions) (expr : expr) ~parse_a0 : Stmt.t Rewriter.t =
    let open Rewriter.Syntax in
    let parse_a = parse_a ?cmnt ~loc ?spec_error ?spec_source ~parse_a0 in
    match expr with
    | App (Ite, [ c; e1; e2 ], expr_attr) ->
        let* stmt1 = parse_a ~universal_quants (c :: conds) e1 in

        let not_c = Expr.mk_not ~loc:(Expr.to_loc c) c in
        let* stmt2 = parse_a ~universal_quants (not_c :: conds) e2 in

        Rewriter.return (Stmt.mk_block_stmt ~loc [ stmt1; stmt2 ])
    | App (Impl, [ c; e2 ], expr_attr) -> parse_a ~universal_quants (c :: conds) e2
    | App (And, e_list, expr_attr) ->
        let* stmts_list =
          Rewriter.List.map e_list ~f:(fun e -> parse_a ~universal_quants conds e)
        in

        Rewriter.return (Stmt.mk_block_stmt ~loc stmts_list)
    | Binder (Forall, var_decls, trgs, e, expr_attr) ->
        let universal_quants =
          let new_quants =
            List.map var_decls ~f:(fun var_decl -> (var_decl.var_name, var_decl))
          in
          {
            univ_vars = universal_quants.univ_vars @ new_quants;
            triggers =
              (match universal_quants.triggers with
              | [] -> trgs
              | _ ->
                  List.concat_map universal_quants.triggers ~f:(fun trigs ->
                      List.map trgs ~f:(fun trg -> trigs @ trg)));
          }
        in

        let* stmt = parse_a ~universal_quants conds e in

        Rewriter.return stmt
    | _ -> parse_a0 ?cmnt ?spec_error ?spec_source ~loc universal_quants conds expr
end

module ScalarResource = struct
  type counted = {
    constructor : qual_ident;
    value_projection : qual_ident;
    amount_projection : qual_ident;
    value : expr;
    amount : expr;
    empty : expr;
    zero : expr;
    limit : expr option;
    amount_first : bool;
  }

  type encoding =
    | Generic
    | Lattice
    | Counted of counted
    | Counter
    | Persistent of expr
    | Unit

  type t = {
    encoding : encoding;
    cancellative : bool;
    heap : expr;
    scratch : expr;
    key : expr;
    chunk : expr;
    comp : qual_ident;
    frame : qual_ident;
    compare : qual_ident;
    valid : qual_ident;
    valid_inhale : qual_ident;
    error : string;
  }

  let decode (expr : expr) : t option Rewriter.t =
    let open Rewriter.Syntax in
    let loc = Expr.to_loc expr in
    let make ?(cancellative = false) encoding heap_name scratch_name key chunk comp frame
        compare valid valid_inhale error =
      let heap_expr name =
        let* symbol = Rewriter.find_and_reify (QualIdent.from_ident name) in
        match symbol with
        | VarDef v -> Rewriter.return (Expr.from_var_decl v.var_decl)
        | _ -> Error.internal_error loc "Expected a resource heap variable"
      in
      let* heap = heap_expr heap_name in
      let+ scratch = heap_expr scratch_name in
      Some
        {
          encoding;
          cancellative;
          heap;
          scratch;
          key;
          chunk;
          comp;
          frame;
          compare;
          valid;
          valid_inhale;
          error;
        }
    in
    match expr with
    | App (Own, [ key; field; chunk ], _) ->
        let* name = Rewriter.resolve (Expr.to_qual_ident field) in
        let* comp = ProgUtils.get_field_utils_comp name in
        let* frame = ProgUtils.get_field_utils_frame name in
        let* compare = ProgUtils.get_field_utils_heapchunk_compare name in
        let* valid = ProgUtils.get_field_utils_valid name in
        let* valid_inhale = ProgUtils.get_field_utils_valid_inhale name in
        let* field = Rewriter.find_and_reify_field name in
        let ra = ProgUtils.field_get_ra_qual_iden field in
        let* symbol = Rewriter.find ra in
        let origin, _, _ = symbol in
        let implements interface =
          Rewriter.Symbol.extract symbol ~f:(fun _ _ -> function
            | ModDef m ->
                Set.mem m.mod_decl.mod_decl_interfaces interface
                || QualIdent.(origin = interface)
            | _ -> false)
        in
        let lattice = implements Predefs.lib_lattice_ra_mod_qual_ident in
        let cancellative = implements Predefs.lib_cancellative_ra_mod_qual_ident in
        let encoding =
          match chunk with
          | App (DataConstr constructor, [ value; amount ], _)
            when QualIdent.(origin = Predefs.lib_frac_mod_qual_ident)
                 && Ident.(
                      QualIdent.unqualify constructor
                      = Predefs.lib_frac_chunk_constr_ident) ->
              Counted
                {
                  constructor;
                  value_projection =
                    QualIdent.append ra Predefs.lib_frac_chunk_destr1_ident;
                  amount_projection =
                    QualIdent.append ra Predefs.lib_frac_chunk_destr2_ident;
                  value;
                  amount;
                  empty =
                    Expr.mk_app ~loc ~typ:(Expr.to_type chunk)
                      (Var (ProgUtils.get_ra_id ra))
                      [];
                  zero = Expr.mk_real ~loc 0.;
                  limit = Some (Expr.mk_real ~loc 1.);
                  amount_first = false;
                }
          | _ -> if lattice then Lattice else Generic
        in
        make ~cancellative encoding (field_heap_name name) (field_heap_name2 name) key
          chunk comp frame compare valid valid_inhale "This own predicate may not hold"
    | App (((AUPred name | AUPredCommit name) as constr), key :: args, _) ->
        let* name = Rewriter.resolve name in
        let* rep = ProgUtils.get_au_utils_rep_type name in
        let typ = Type.mk_var rep in
        let* chunk =
          match (constr, args) with
          | AUPred _, [ args ] ->
              let+ constr = ProgUtils.au_ra_uncommitted_constr_qual_ident loc name in
              Expr.mk_app ~loc ~typ (DataConstr constr) [ args ]
          | AUPredCommit _, [ args; ret ] ->
              let+ constr = ProgUtils.au_ra_committed_constr_qual_ident loc name in
              Expr.mk_app ~loc ~typ (DataConstr constr) [ args; ret ]
          | _ -> unsupported_expr_error expr
        in
        let* comp = ProgUtils.get_au_utils_comp loc name in
        let* frame = ProgUtils.get_au_utils_frame name in
        let* compare = ProgUtils.get_au_utils_heapchunk_compare name in
        let* valid = ProgUtils.get_au_utils_valid name in
        let* valid_inhale = ProgUtils.get_au_utils_valid_inhale name in
        make Generic (au_heap_name name) (au_heap_name2 name) key chunk comp frame compare
          valid valid_inhale "This atomic update predicate may not hold"
    | App (Var name, args, _) ->
        let* symbol = Rewriter.find_and_reify name in
        begin match symbol with
        | CallDef c
          when Poly.(
                 c.call_decl.call_decl_kind = Pred
                 || c.call_decl.call_decl_kind = Invariant) ->
            let* name = Rewriter.resolve name in
            let* rep = ProgUtils.get_pred_utils_rep_type name in
            let* in_types = ProgUtils.pred_in_types name in
            let* constr = ProgUtils.pred_ra_constr_qual_ident loc name in
            let ins, outs = List.split_n args (List.length in_types) in
            let key = Expr.mk_tuple ~loc ins in
            let chunk =
              mk_pred_new_chunk ~loc c.call_decl.call_decl_kind (Type.mk_var rep) constr
                outs
            in
            let* comp = ProgUtils.get_pred_utils_comp name in
            let* frame = ProgUtils.get_pred_utils_frame name in
            let* compare = ProgUtils.get_pred_utils_heapchunk_compare name in
            let* valid = ProgUtils.get_pred_utils_valid name in
            let* valid_inhale = ProgUtils.get_pred_utils_valid_inhale loc name in
            let* ra = ProgUtils.pred_get_ra_qual_iden name in
            let* encoding =
              match (c.call_decl.call_decl_kind, outs) with
              | Invariant, [] -> Rewriter.return Unit
              | Invariant, _ ->
                  Rewriter.return
                    (Persistent
                       (Expr.mk_app ~loc ~typ:(Expr.to_type chunk)
                          (Var (ProgUtils.get_ra_id ra))
                          []))
              | Pred, [] -> Rewriter.return Counter
              | Pred, _ ->
                  let* amount_projection =
                    ProgUtils.pred_ra_count_destr_qual_ident loc name
                  in
                  let+ value_projection =
                    ProgUtils.pred_ra_val_destr_qual_ident loc name
                  in
                  Counted
                    {
                      constructor = constr;
                      value_projection;
                      amount_projection;
                      value = Expr.mk_tuple ~loc outs;
                      amount = Expr.mk_int ~loc 1;
                      empty =
                        Expr.mk_app ~loc ~typ:(Expr.to_type chunk)
                          (Var (ProgUtils.get_ra_id ra))
                          [];
                      zero = Expr.mk_int ~loc 0;
                      limit = None;
                      amount_first = true;
                    }
              | _ -> Rewriter.return Generic
            in
            make encoding (pred_heap_name name) (pred_heap_name2 name) key chunk comp
              frame compare valid valid_inhale "This predicate may not hold"
        | _ -> Rewriter.return None
        end
    | _ -> Rewriter.return None

  let apply ~loc fn args = Expr.mk_app ~loc ~typ:Type.bool (Var fn) args
  let arithmetic ~loc op a b = Expr.mk_app ~loc ~typ:(Expr.to_type a) op [ a; b ]
  let relation ~loc op a b = Expr.mk_app ~loc ~typ:Type.bool op [ a; b ]

  let construct ~loc c value amount =
    Expr.mk_app ~loc ~typ:(Expr.to_type c.empty) (DataConstr c.constructor)
      (if c.amount_first then [ amount; value ] else [ value; amount ])

  let projections ~loc c entry =
    ( Expr.mk_app ~loc ~typ:(Expr.to_type c.value) (DataDestr c.value_projection) [ entry ],
      Expr.mk_app ~loc ~typ:(Expr.to_type c.amount) (DataDestr c.amount_projection)
        [ entry ] )

  let amount_valid ~loc c amount =
    Expr.mk_and ~loc
      (relation ~loc Gt amount c.zero
      :: Option.to_list
           (Option.map c.limit ~f:(fun limit -> relation ~loc Leq amount limit)))

  let consumption ~loc r entry =
    match r.encoding with
    | Generic | Lattice ->
        (* Abstract lattice proofs need the frameCompInv trigger. *)
        apply ~loc r.compare [ entry; r.chunk ]
    | Unit -> Expr.mk_bool ~loc true
    | Persistent _ -> Expr.mk_eq ~loc entry r.chunk
    | Counter ->
        Expr.mk_and ~loc
          [
            relation ~loc Geq entry r.chunk;
            relation ~loc Geq r.chunk (Expr.mk_int ~loc 0);
          ]
    | Counted c ->
        let value, amount = projections ~loc c entry in
        Expr.mk_and ~loc
          [
            Expr.mk_eq ~loc entry (construct ~loc c value amount);
            amount_valid ~loc c amount;
            amount_valid ~loc c c.amount;
            Expr.mk_eq ~loc value c.value;
            relation ~loc Geq amount c.amount;
          ]

  let remainder ~loc r entry =
    match r.encoding with
    | Generic ->
        Expr.mk_app ~loc ~typ:(Expr.to_type entry) (Var r.frame) [ entry; r.chunk ]
    | Lattice | Persistent _ | Unit -> entry
    | Counter -> arithmetic ~loc Minus entry r.chunk
    | Counted c ->
        let value, amount = projections ~loc c entry in
        Expr.mk_ite ~loc
          (Expr.mk_eq ~loc amount c.amount)
          c.empty
          (construct ~loc c value (arithmetic ~loc Minus amount c.amount))

  let composition ~loc r entry =
    match r.encoding with
    | Generic | Lattice ->
        ( Expr.mk_bool ~loc true,
          Expr.mk_app ~loc ~typ:(Expr.to_type entry) (Var r.comp) [ entry; r.chunk ] )
    | Unit -> (Expr.mk_bool ~loc true, entry)
    | Persistent empty ->
        ( Expr.mk_or ~loc [ Expr.mk_eq ~loc entry empty; Expr.mk_eq ~loc entry r.chunk ],
          r.chunk )
    | Counter ->
        ( Expr.mk_and ~loc
            [
              relation ~loc Geq entry (Expr.mk_int ~loc 0);
              relation ~loc Geq r.chunk (Expr.mk_int ~loc 0);
            ],
          arithmetic ~loc Plus entry r.chunk )
    | Counted c ->
        let value, amount = projections ~loc c entry in
        let empty = Expr.mk_eq ~loc entry c.empty in
        let total =
          arithmetic ~loc Plus (Expr.mk_ite ~loc empty c.zero amount) c.amount
        in
        ( Expr.mk_and ~loc
            [
              amount_valid ~loc c c.amount;
              amount_valid ~loc c total;
              Expr.mk_or ~loc
                [
                  empty;
                  Expr.mk_and ~loc
                    [
                      Expr.mk_eq ~loc entry (construct ~loc c value amount);
                      amount_valid ~loc c amount;
                      Expr.mk_eq ~loc value c.value;
                    ];
                ];
            ],
          construct ~loc c c.value total )

  let assign_entry ~loc r guard chunk =
    Stmt.mk_assign ~loc
      [ Expr.to_qual_ident r.heap ]
      (Expr.mk_ite ~loc guard (Expr.mk_mapupdate ~loc r.heap r.key chunk) r.heap)

  let update ~loc r guard op =
    let chunk =
      Expr.mk_app ~loc
        ~typ:(Type.map_codom (Expr.to_type r.heap))
        (Var op)
        [ Expr.mk_maplookup ~loc r.heap r.key; r.chunk ]
    in
    Expr.mk_ite ~loc guard (Expr.mk_mapupdate ~loc r.heap r.key chunk) r.heap

  let errors r expr spec_error =
    spec_error
    @ [ Stmt.mk_const_spec_error (Error.RelatedLoc, Expr.to_loc expr, r.error) ]

  let translate_generic ?cmnt ?(spec_error = []) ?spec_source ~loc kind conds expr r =
    let guard = Expr.mk_and ~loc conds in
    let op, validity =
      match kind with Inhale -> (r.comp, r.valid_inhale) | Exhale -> (r.frame, r.valid)
    in
    let comment =
      Option.value cmnt ~default:"" ^ "\n"
      ^ (match kind with Inhale -> "inhale: " | Exhale -> "exhale: ")
      ^ Expr.to_string expr
    in
    let check = apply ~loc validity [ r.heap ] in
    let check_stmt =
      match kind with
      | Inhale -> Stmt.mk_assume_expr ~loc ?spec_source check
      | Exhale ->
          Stmt.mk_assert_expr ~loc ?spec_source ~spec_error:(errors r expr spec_error)
            check
    in
    Stmt.mk_block_stmt ~loc
      [
        Stmt.mk_havoc ~loc (Expr.to_qual_ident r.scratch);
        Stmt.mk_assume_expr ~loc ~cmnt:comment
          (Expr.mk_eq ~loc r.scratch (update ~loc r guard op));
        Stmt.mk_assign ~loc [ Expr.to_qual_ident r.heap ] r.scratch;
        check_stmt;
      ]

  let translate ?cmnt ?(spec_error = []) ?spec_source ~loc kind conds expr r =
    match r.encoding with
    | Generic -> translate_generic ?cmnt ~spec_error ?spec_source ~loc kind conds expr r
    | Lattice | Counted _ | Counter | Persistent _ | Unit ->
        let guard = Expr.mk_and ~loc conds in
        let entry = Expr.mk_maplookup ~loc r.heap r.key in
        let updates chunk =
          match (r.encoding, kind) with
          | Unit, _ | (Lattice | Persistent _), Exhale -> []
          | _ -> [ assign_entry ~loc r guard chunk ]
        in
        let statements =
          match kind with
          | Exhale ->
              let check = Expr.mk_impl ~loc guard (consumption ~loc r entry) in
              Stmt.mk_assert_expr ~loc ?cmnt ?spec_source
                ~spec_error:(errors r expr spec_error) check
              :: updates (remainder ~loc r entry)
          | Inhale ->
              let check, chunk = composition ~loc r entry in
              Stmt.mk_assume_expr ~loc ?cmnt ?spec_source (Expr.mk_impl ~loc guard check)
              :: updates chunk
              @ [
                  Stmt.mk_assume_expr ~loc ?spec_source
                    (apply ~loc r.valid_inhale [ r.heap ]);
                ]
        in
        Stmt.mk_block_stmt ~loc statements

  let rec stable = function
    | App ((Read | Own | AUPred _ | AUPredCommit _ | ExprExt _), _, _) | Binder _ -> false
    | App (Var name, args, _) ->
        let ident = QualIdent.unqualify name in
        (* FPU lowering can expose a heap lookup directly in a chunk. *)
        (not
           (String.is_suffix ident.ident_name ~suffix:"$Heap"
           || String.is_suffix ident.ident_name ~suffix:"$Heap2"))
        && List.for_all args ~f:stable
    | App (_, args, _) -> List.for_all args ~f:stable

  let rec guarded conds = function
    | App (Impl, [ guard; body ], _) -> guarded (guard :: conds) body
    | App (Ite, [ guard; body; App (Bool true, [], _) ], _) ->
        guarded (guard :: conds) body
    | App (Ite, [ guard; App (Bool true, [], _); body ], _) ->
        guarded (Expr.mk_not guard :: conds) body
    | expr -> (Expr.mk_and (List.rev conds), expr)

  let fuse_inhale_exhale inhale spec guard r =
    let loc = inhale.stmt_loc in
    let lookup = Expr.mk_maplookup ~loc r.heap r.key in
    let condition, composed = composition ~loc r lookup in
    let intermediate =
      match r.encoding with
      | Unit -> r.heap
      | _ -> Expr.mk_ite ~loc guard (Expr.mk_mapupdate ~loc r.heap r.key composed) r.heap
    in
    let assumptions =
      [
        Stmt.mk_assume_expr ~loc ?spec_source:spec.spec_source
          ~cmnt:"Fused inhale/exhale: composition check"
          (Expr.mk_impl ~loc guard condition);
        Stmt.mk_assume_expr ~loc ?spec_source:spec.spec_source
          ~cmnt:"Fused inhale/exhale: inhale validity"
          (apply ~loc r.valid_inhale [ intermediate ]);
      ]
    in
    (* weak_frameCompInv discharges consumption after a valid composition. *)
    let updates =
      match r.encoding with
      | Counted _ | Counter | Unit -> []
      | Generic when r.cancellative -> []
      | Generic | Lattice | Persistent _ ->
          [ assign_entry ~loc r guard (remainder ~loc r composed) ]
    in
    Stmt.mk_block_stmt ~loc (assumptions @ updates)

  let fuse ~reverse first second pre post =
    let open Rewriter.Syntax in
    let guard_out, atom_out = guarded [] pre.spec_form in
    let guard_in, atom_in = guarded [] post.spec_form in
    let* out_resource = decode atom_out in
    let* in_resource = decode atom_in in
    match (out_resource, in_resource) with
    | Some r, Some s
      when Expr.alpha_equal r.heap s.heap
           && Expr.alpha_equal r.key s.key
           && Expr.alpha_equal guard_out guard_in
           && List.for_all
                [ guard_out; guard_in; r.key; s.key; r.chunk; s.chunk ]
                ~f:stable ->
        if reverse then
          if Expr.alpha_equal r.chunk s.chunk then
            Rewriter.return (Some (fuse_inhale_exhale first pre guard_out r))
          else Rewriter.return None
        else
          let exhale, inhale = (first, second) in
          let loc = exhale.stmt_loc in
          let lookup = Expr.mk_maplookup ~loc r.heap r.key in
          let check = Expr.mk_impl ~loc guard_out (consumption ~loc r lookup) in
          let check_stmt =
            Stmt.mk_assert_expr ~loc
              ~spec_error:(errors r atom_out pre.spec_error)
              ?spec_source:pre.spec_source ~cmnt:"Fused exhale/inhale: consumption check"
              check
          in
          let update_stmts =
            if Expr.alpha_equal r.chunk s.chunk then []
            else
              let loc = inhale.stmt_loc in
              let rest = remainder ~loc r lookup in
              let condition, chunk =
                match (r.encoding, s.encoding) with
                | Counted old, Counted incoming ->
                    (* A changed value must agree with any unconsumed chunk. *)
                    let value, amount = projections ~loc old lookup in
                    let total =
                      if Expr.alpha_equal old.amount incoming.amount then amount
                      else
                        arithmetic ~loc Plus
                          (arithmetic ~loc Minus amount old.amount)
                          incoming.amount
                    in
                    ( Expr.mk_and ~loc
                        [
                          amount_valid ~loc incoming incoming.amount;
                          amount_valid ~loc incoming total;
                          Expr.mk_or ~loc
                            [
                              Expr.mk_eq ~loc amount old.amount;
                              Expr.mk_eq ~loc value incoming.value;
                            ];
                        ],
                      construct ~loc incoming incoming.value total )
                | Persistent _, Persistent _ -> (Expr.mk_eq ~loc r.chunk s.chunk, lookup)
                | _ -> composition ~loc s rest
              in
              let assumptions =
                [
                  Stmt.mk_assume_expr ~loc ?spec_source:post.spec_source
                    (Expr.mk_impl ~loc guard_in condition);
                ]
              in
              match (r.encoding, s.encoding) with
              | Persistent _, Persistent _ | Unit, Unit -> assumptions
              | _ -> assumptions @ [ assign_entry ~loc r guard_in chunk ]
          in
          let assume_stmt =
            Stmt.mk_assume_expr ~loc:inhale.stmt_loc ?spec_source:post.spec_source
              ~cmnt:"Fused exhale/inhale: inhale validity"
              (apply ~loc:inhale.stmt_loc s.valid_inhale [ s.heap ])
          in
          Rewriter.return
            (Some
               (Stmt.mk_block_stmt ~loc ((check_stmt :: update_stmts) @ [ assume_stmt ])))
    | _ -> Rewriter.return None
end

module TrnslInhale = struct
  (* Counts ISC (own/AU-token/predicate-application) occurrences seen so far while
     translating the *current* top-level spec, left-to-right -- reset by
     [trnsl_inhale_expr] before each such translation, incremented by
     [trnsl_inhale_a0] at each of its three ISC-detection branches. Local, single-purpose
     mutable state (not part of the [Rewriter] monad, never read/written outside this
     module): [trnsl_inhale_a0] is handed to [ParseAssertionLang.parse_a] as a plain
     callback, whose signature can't carry an extra threaded accumulator, and the
     resulting [conjunct_idx] only needs to agree, position-for-position, between the
     original declaration's clause and any of its substituted occurrences -- both walked
     by this same left-to-right recursion -- for [get_or_generate_inv_function]'s cache
     key to line up. *)
  let conjunct_counter = ref 0

  let next_conjunct_idx () =
    let idx = !conjunct_counter in
    conjunct_counter := idx + 1;
    idx

  let rec skolemize_inhale_expr (universal_quants : universal_quants)
      (subst : expr qual_ident_map) (expr : expr) : expr Rewriter.t =
    let open Rewriter.Syntax in
    (* Inhales use arbitrary variables/maps; WitnessComputation constrains exhale functions. *)
    let generate_skolem_function_inhale (universal_quants : universal_quants)
        (var_decl : var_decl) : expr Rewriter.t =
      let univ_quants_list = universal_quants.univ_vars in
      (* univ_quants_list computed here to keep the ordering on keys constant for the construction *)
      if List.is_empty univ_quants_list then
        let var_decl =
          {
            var_decl with
            var_name = Ident.fresh var_decl.var_loc var_decl.var_name.ident_name;
          }
        in
        let symbol =
          Module.VarDef { var_decl; var_init = None; var_is_free = MachineFree }
        in
        let* _ = Rewriter.introduce_symbol symbol in

        Rewriter.return
          (Expr.mk_var ~typ:var_decl.var_type (QualIdent.from_ident var_decl.var_name))
      else
        let map_dom_type =
          Type.mk_prod var_decl.var_loc
            (List.map univ_quants_list ~f:(fun (_, v_d) -> v_d.var_type))
        in
        let var_type = Type.mk_map var_decl.var_loc map_dom_type var_decl.var_type in

        let var_decl =
          {
            var_decl with
            var_name =
              Ident.fresh var_decl.var_loc ("skolem_" ^ var_decl.var_name.ident_name);
            var_type;
          }
        in
        let symbol =
          Module.VarDef { var_decl; var_init = None; var_is_free = MachineFree }
        in
        let* _ = Rewriter.introduce_symbol symbol in

        let tuple_expr =
          Expr.mk_tuple
            (List.map univ_quants_list ~f:(fun (_, v_d) ->
                 Expr.mk_var ~typ:v_d.var_type (QualIdent.from_ident v_d.var_name)))
        in

        Rewriter.return
          (Expr.mk_maplookup
             (Expr.mk_var ~typ:var_decl.var_type (QualIdent.from_ident var_decl.var_name))
             tuple_expr)
    in

    match expr with
    | Binder (Forall, var_decls, trgs, e, e_attr) ->
        let universal_quants =
          let new_quants =
            List.map var_decls ~f:(fun var_decl -> (var_decl.var_name, var_decl))
          in
          { universal_quants with univ_vars = universal_quants.univ_vars @ new_quants }
        in

        let* e = skolemize_inhale_expr universal_quants subst e in

        Rewriter.return Expr.(Binder (Forall, var_decls, trgs, e, e_attr))
    | Binder (Exists, var_decls, trgs, e, e_attr) ->
        let* subst =
          Rewriter.List.fold_left var_decls ~init:subst ~f:(fun map var_decl ->
              let* (new_expr : expr) =
                generate_skolem_function_inhale universal_quants var_decl
              in
              Rewriter.return
                (Map.add_exn map
                   ~key:(QualIdent.from_ident var_decl.var_name)
                   ~data:new_expr))
        in

        let* e = skolemize_inhale_expr universal_quants subst e in

        let* () =
          Rewriter.Logs.debug (fun printers m ->
              m
                "HeapsExplicitTrnsl.TrnslInhale.skolemize_inhale_expr: found \
                 existentials:  e: %a"
                printers.pr_expr e)
        in
        Rewriter.return e
    | _ ->
        let* expr =
          Rewriter.Expr.descend expr ~f:(skolemize_inhale_expr universal_quants subst)
        in

        let expr = Expr.alpha_renaming expr subst in

        (* This will cause the renaming to be done at each step of descend, but renaming should be idempotent, so that should be okay *)
        let* () =
          Rewriter.Logs.debug (fun printers m ->
              m "HeapsExplicitTrnsl.TrnslInhale.skolemize_inhale_expr: e: %a"
                printers.pr_expr expr)
        in
        Rewriter.return expr

  let rec rewriter_skolemize_inhale_stmts (stmt : Stmt.t) : Stmt.t Rewriter.t =
    let open Rewriter.Syntax in
    match stmt.stmt_desc with
    | Basic (Spec (spec_kind, spec)) -> (
        match spec_kind with
        | Inhale ->
            let* e =
              skolemize_inhale_expr
                { univ_vars = []; triggers = [] }
                (Map.empty (module QualIdent))
                spec.spec_form
            in

            let spec = { spec with spec_form = e } in

            Rewriter.return { stmt with stmt_desc = Basic (Spec (spec_kind, spec)) }
        | _ -> Rewriter.return stmt)
    | _ -> Rewriter.Stmt.descend stmt ~f:rewriter_skolemize_inhale_stmts

  let rec rewriter_skolemize_assume_stmts (stmt : Stmt.t) : Stmt.t Rewriter.t =
    let open Rewriter.Syntax in
    match stmt.stmt_desc with
    | Basic (Spec (spec_kind, spec)) -> (
        match spec_kind with
        | Assume ->
            let* e =
              skolemize_inhale_expr
                { univ_vars = []; triggers = [] }
                (Map.empty (module QualIdent))
                spec.spec_form
            in

            let spec = { spec with spec_form = e } in

            Rewriter.return { stmt with stmt_desc = Basic (Spec (spec_kind, spec)) }
        | _ -> Rewriter.return stmt)
    | _ -> Rewriter.Stmt.descend stmt ~f:rewriter_skolemize_assume_stmts

  let rec rewriter_eliminate_binds_for_inhale (stmt : Stmt.t) :
      (Stmt.t, expr option) Rewriter.t_ext =
    let open Rewriter.Syntax in
    match stmt.stmt_desc with
    | Basic (Spec (Inhale, spec)) ->
        let* () = Rewriter.set_user_state (Some spec.spec_form) in
        Rewriter.return stmt
    | Basic (Spec (Assert, spec)) ->
        let* () = Rewriter.set_user_state (Some spec.spec_form) in
        Rewriter.return stmt
    | Basic (Bind bind_desc) -> (
        let* prev_expr = Rewriter.current_user_state in
        let* () = Rewriter.set_user_state None in

        match prev_expr with
        | None -> Rewriter.return stmt
        | Some prev_expr -> (
            let* printers = Rewriter.current_printers in
            Logs.debug (fun m ->
                m
                  "HeapsExplicitTrnsl.TrnslInhale.rewriter_eliminate_binds_for_inhale: \
                   bind_desc: %a; prev_expr: %a"
                  printers.pr_stmt stmt printers.pr_expr prev_expr);

            let* bind_lhs_var_decls =
              Rewriter.List.map bind_desc.bind_lhs ~f:(fun qual_ident ->
                  let+ var_def = Rewriter.find_and_reify_var qual_ident in
                  var_def.var_decl)
            in

            match
              match_up_expr ~printers bind_desc.bind_rhs.spec_form prev_expr
                bind_lhs_var_decls
            with
            | None ->
                Logs.debug (fun m ->
                    m
                      "HeapsExplicitTrnsl.TrnslInhale.rewriter_eliminate_binds_for_inhale: \
                       Could not match up expressions");
                Rewriter.return stmt
            | Some var_map ->
                Logs.debug (fun m ->
                    m
                      "HeapsExplicitTrnsl.TrnslInhale.rewriter_eliminate_binds_for_inhale: \
                       var_map: %a"
                      (Util.Print.pr_map ~key:Ident.pr ~value:printers.pr_type_var_decl)
                      (Map.map ~f:Stdlib.fst var_map));
                let assign_stmts =
                  List.map bind_lhs_var_decls ~f:(fun var_decl ->
                      let _, rhs = Map.find_exn var_map var_decl.var_name in

                      Stmt.mk_assign
                        ~loc:(Expr.to_loc bind_desc.bind_rhs.spec_form)
                        [ var_decl.var_name |> QualIdent.from_ident ]
                        rhs)
                in

                Rewriter.return
                  (Stmt.mk_block_stmt
                     ~loc:(Expr.to_loc bind_desc.bind_rhs.spec_form)
                     assign_stmts)))
    | _ ->
        let* () = Rewriter.set_user_state None in
        Rewriter.Stmt.descend stmt ~f:rewriter_eliminate_binds_for_inhale

  let rec trnsl_inhale_expr ?cmnt ?spec_error ?spec_source ~loc (expr : expr) :
      Stmt.t Rewriter.t =
    conjunct_counter := 0;
    ParseAssertionLang.parse_a ?cmnt ?spec_error ?spec_source ~loc [] expr
      ~parse_a0:trnsl_inhale_a0

  and trnsl_inhale_a0 ?cmnt ?spec_error ?spec_source ~loc
      (universal_quants : universal_quants) (conds : conditions) (expr : expr) :
      Stmt.t Rewriter.t =
    let open Rewriter.Syntax in
    let* resource =
      if List.is_empty universal_quants.univ_vars then ScalarResource.decode expr
      else Rewriter.return None
    in
    match resource with
    | Some resource ->
        ignore (next_conjunct_idx ());
        Rewriter.return
          (ScalarResource.translate ?cmnt ?spec_error ?spec_source ~loc Inhale conds expr
             resource)
    | None ->
        trnsl_inhale_a0_general ?cmnt ?spec_error ?spec_source ~loc universal_quants conds
          expr

  and trnsl_inhale_a0_general ?cmnt ?spec_error ?spec_source ~loc
      (universal_quants : universal_quants) (conds : conditions) (expr : expr) :
      Stmt.t Rewriter.t =
    let open Rewriter.Syntax in
    let univ_quants_list = universal_quants.univ_vars in
    let univ_vars_list = List.map univ_quants_list ~f:(fun (var, var_decl) -> var_decl) in
    match expr with
    | App (Own, [ e1; e2; e3 ], _) ->
        (* forall a, b, c :: m1(a, b, c) ==> own(f1(a, b, c), field, f2(a, b, c))

           ===>

           // asserting injectivity of functions
           assert forall a, b, c, a', b', c' :: m1(a, b, c) && m1(a', b', c') ==> f1(a, b, c) == f1(a', b', c') ==> (a == a' && b == b' && c == c')

           havoc(field$Heap2);

           assert forall l: Ref ::
             m1(inv(l)#0, inv(l)#1, inv(l)#2) && l == f1(inv(l)#0, inv(l)#1, inv(l)#2) ?
               field$Heap2[l] == field.comp( field$Heap[l], f2(inv(l)#0, inv(l)#1, inv(l)#2) ) :
             field$Heap2[l] == field$Heap[l]

           field$Heap := field$Heap2
           assume field.valid(field$Heap)
        *)
        let field_type =
          match Expr.to_type e2 with
          | App (Fld, [ tp_expr ], _) -> tp_expr
          | _ -> Error.type_error (Expr.to_loc e2) "Expected field identifier."
        in

        (* Resolve before deriving the heap's name: a callee's contract arrives
           here with the instantiation substitution already applied
           syntactically, so a manifest field would otherwise get a heap beside
           the alias rather than beside the field it stands for. *)
        let* field_name = Rewriter.resolve (Expr.to_qual_ident e2) in
        let field_heap_name = field_heap_name field_name in
        let field_heap_qual_ident = QualIdent.from_ident field_heap_name in
        let field_heap_expr =
          Expr.mk_var
            ~typ:(Type.mk_map (Expr.to_loc e2) Type.ref field_type)
            field_heap_qual_ident
        in

        let field_heap2_name = field_heap_name2 field_name in
        let field_heap2_qual_ident = QualIdent.from_ident field_heap2_name in
        let field_heap2_expr =
          Expr.mk_var
            ~typ:(Type.mk_map (Expr.to_loc e2) Type.ref field_type)
            field_heap2_qual_ident
        in

        let* (field_heapchunk_operator : qual_ident) =
          ProgUtils.get_field_utils_comp field_name
        in

        let* (field_heap_valid_fn : qual_ident) =
          ProgUtils.get_field_utils_valid field_name
        in

        let* (field_heap_valid_inhale_fn : qual_ident) =
          ProgUtils.get_field_utils_valid_inhale field_name
        in

        let l_var =
          Type.
            {
              var_name = Ident.fresh (Expr.to_loc expr) "l";
              var_loc = Expr.to_loc expr;
              var_type = Type.ref;
              var_const = false;
              var_ghost = false;
              var_implicit = false;
            }
        in

        let l_expr =
          Expr.mk_var ~typ:l_var.var_type (QualIdent.from_ident l_var.var_name)
        in

        let conjunct_idx = next_conjunct_idx () in
        let* inv_fn_expr, env_actual_exprs =
          get_or_generate_inv_function ~loc universal_quants conds e1 ~arg_expr:l_expr
            ~spec_source ~conjunct_idx
        in

        let inv_exprs =
          List.mapi univ_vars_list ~f:(fun index _var_decl ->
              if Int.(List.length univ_vars_list = 1) then inv_fn_expr
              else Expr.mk_tuple_lookup inv_fn_expr index)
        in

        (* inhale forall i, j :: { v(i,j) } own(f(i, j), fld, v(i, j))
         *   ~~>
         * forall i, j :: { v(i,j) }
         *  v[
         *      i <- inv(f(i, j), i, j)#0,
         *      j <- inv(f(i, j), i, j)#1
         *  ] (var substitution)
         *    =
         *  v(i, j) *)
        let* forward_trigger_assertions =
          let inv_fn_qi_opt =
            match inv_fn_expr with
            | App (Expr.Var inv_fn_qi, args, _) -> Some inv_fn_qi
            | _ -> None
          in

          begin match inv_fn_qi_opt with
          | None -> Rewriter.return []
          | Some inv_fn_qi ->
              let inv_expr =
                Expr.mk_app ~loc
                  ~typ:
                    (Type.mk_prod loc
                       (List.map univ_vars_list ~f:(fun var_decl -> var_decl.var_type)))
                  (Expr.Var inv_fn_qi) (e1 :: env_actual_exprs)
              in

              (* i ~> inv(f(i, j), i, j)#0
               * j ~> inv(f(i, j), i, j)#1*)
              let renaming_map =
                List.foldi univ_vars_list
                  ~init:(Map.empty (module QualIdent))
                  ~f:(fun index map var_decl ->
                    Map.set map
                      ~key:(QualIdent.from_ident var_decl.var_name)
                      ~data:
                        (if Int.(List.length univ_vars_list = 1) then inv_expr
                         else Expr.mk_tuple_lookup ~loc inv_expr index))
              in

              Rewriter.return
                (List.map (List.concat universal_quants.triggers) ~f:(fun trg_term ->
                     let new_trg_term = Expr.alpha_renaming trg_term renaming_map in

                     Stmt.mk_assume_expr ~loc ~cmnt:"forward_trigger_assertion"
                       (Expr.mk_binder ~trigs:universal_quants.triggers ~loc
                          ~typ:Type.bool Forall univ_vars_list
                          (Expr.mk_impl (Expr.mk_and conds)
                             (Expr.mk_eq ~loc trg_term new_trg_term)))))
          end
        in

        let alpha_renaming_map =
          List.fold2_exn univ_vars_list inv_exprs
            ~init:(Map.empty (module QualIdent))
            ~f:(fun map var_decl expr ->
              Map.set map ~key:(QualIdent.from_ident var_decl.var_name) ~data:expr)
        in

        let e1_subst = Expr.alpha_renaming e1 alpha_renaming_map in
        let e3_subst = Expr.alpha_renaming e3 alpha_renaming_map in
        let conds_subst =
          List.map conds ~f:(fun e -> Expr.alpha_renaming e alpha_renaming_map)
        in
        let new_trigs =
          List.map universal_quants.triggers ~f:(fun trgs ->
              List.map trgs ~f:(fun trg -> Expr.alpha_renaming trg alpha_renaming_map))
        in

        let havoc_stmt = Stmt.mk_havoc ~loc field_heap2_qual_ident in
        let assume_stmt =
          let l_eq_e1_expr = Expr.mk_eq l_expr e1_subst in

          Stmt.mk_assume_expr ~loc
            ~cmnt:
              ((match cmnt with None -> "" | Some cmnt -> cmnt ^ "\n")
              ^ "inhale: "
              ^ Stdlib.Format.asprintf "%a" Expr.pr
                  (Expr.mk_binder Forall univ_vars_list
                     (Expr.mk_impl (Expr.mk_and conds) expr)))
            (match univ_vars_list with
            | [] ->
                Expr.mk_eq ~loc field_heap2_expr
                  (Expr.mk_ite ~loc
                     (Expr.mk_and ~loc conds_subst)
                     (Expr.mk_mapupdate ~loc field_heap_expr e1_subst
                        (Expr.mk_app ~loc ~typ:field_type
                           (Expr.Var field_heapchunk_operator)
                           [ Expr.mk_maplookup ~loc field_heap_expr e1_subst; e3_subst ]))
                     field_heap_expr)
            | _ ->
                Expr.mk_binder
                  ~trigs:
                    ([
                       [ Expr.mk_maplookup ~loc field_heap2_expr l_expr ];
                       [ Expr.mk_maplookup ~loc field_heap_expr l_expr ];
                     ]
                    @ new_trigs)
                  ~loc ~typ:Type.bool Forall [ l_var ]
                  (Expr.mk_app ~loc ~typ:Type.bool Expr.Ite
                     [
                       (* m1(a,b,c) && l == f1(a, b, c) *)
                       Expr.mk_and ~loc (l_eq_e1_expr :: conds_subst);
                       (* field$Heap2[l] == field.comp( field$Heap[l], f2(a, b, c) ) *)
                       Expr.mk_eq ~loc
                         (Expr.mk_maplookup ~loc field_heap2_expr e1_subst)
                         (Expr.mk_app ~loc ~typ:field_type
                            (Expr.Var field_heapchunk_operator)
                            [ Expr.mk_maplookup ~loc field_heap_expr l_expr; e3_subst ]);
                       (* field$Heap2[l] == field$Heap[l] *)
                       Expr.mk_eq ~loc
                         (Expr.mk_maplookup ~loc field_heap2_expr l_expr)
                         (Expr.mk_maplookup ~loc field_heap_expr l_expr);
                     ]))
        in

        (* field$Heap := field$Heap2 *)
        let eq_stmt =
          Stmt.mk_assign ~loc [ field_heap_expr |> Expr.to_qual_ident ] field_heap2_expr
        in

        let assume_heap_valid =
          Stmt.mk_assume_expr ~loc
            (Expr.mk_app ~loc ~typ:Type.bool (Expr.Var field_heap_valid_inhale_fn)
               [ field_heap_expr ])
        in

        let stmts_list =
          [ havoc_stmt; assume_stmt ] @ forward_trigger_assertions
          @ [ eq_stmt; assume_heap_valid ]
        in

        let stmt = Stmt.mk_block_stmt ~loc stmts_list in

        Rewriter.return stmt
    | App ((AUPred call_qual_ident as constr), token :: au_args, _)
    | App ((AUPredCommit call_qual_ident as constr), token :: au_args, _) ->
        let args =
          match (constr, au_args) with
          | AUPred _, [ args_tuple ] -> Expr.unfold_tuple args_tuple
          | AUPredCommit _, [ args_tuple; ret_tuple ] ->
              Expr.unfold_tuple args_tuple @ [ ret_tuple ]
          | _ -> unsupported_expr_error expr
        in
        let* heap_elem_type_qual_iden = ProgUtils.get_au_utils_rep_type call_qual_ident in

        let heap_elem_type = Type.mk_var heap_elem_type_qual_iden in

        let call_name = call_qual_ident in
        let au_heap_name = au_heap_name call_name in
        let au_heap_qual_ident = QualIdent.from_ident au_heap_name in
        let au_heap_expr =
          Expr.mk_var ~typ:(Type.mk_map loc Type.ref heap_elem_type) au_heap_qual_ident
        in

        let au_heap2_name = au_heap_name2 call_name in
        let au_heap2_qual_ident = QualIdent.from_ident au_heap2_name in
        let au_heap2_expr =
          Expr.mk_var ~typ:(Type.mk_map loc Type.ref heap_elem_type) au_heap2_qual_ident
        in

        let* (au_heapchunk_operator : qual_ident) =
          ProgUtils.get_au_utils_comp loc call_name
        in

        let* (au_heap_valid_fn : qual_ident) = ProgUtils.get_au_utils_valid call_name in

        let* (au_heap_valid_inhale_fn : qual_ident) =
          ProgUtils.get_au_utils_valid_inhale call_name
        in

        let* au_ra_uncommitted_constr =
          ProgUtils.au_ra_uncommitted_constr_qual_ident loc call_qual_ident
        in
        let* au_ra_committed_constr =
          ProgUtils.au_ra_committed_constr_qual_ident loc call_qual_ident
        in

        let havoc_stmt = Stmt.mk_havoc ~loc au_heap2_qual_ident in

        let new_token_var =
          {
            Type.var_name = Ident.fresh loc "tok";
            var_loc = loc;
            var_type = Type.atomic_token call_name;
            var_const = false;
            var_ghost = true;
            var_implicit = false;
          }
        in

        let new_token_expr = Expr.from_var_decl new_token_var in

        let conjunct_idx = next_conjunct_idx () in
        let* inv_fn_expr, env_actual_exprs =
          get_or_generate_inv_function ~loc universal_quants conds token
            ~arg_expr:new_token_expr ~spec_source ~conjunct_idx
        in

        let inv_exprs =
          List.mapi univ_vars_list ~f:(fun index var_decl ->
              if Int.(List.length univ_vars_list = 1) then inv_fn_expr
              else Expr.mk_tuple_lookup inv_fn_expr index)
        in

        (* inhale forall i, j :: { v(i,j) } AUPred(proc, gamma(i,j), (a_1, ... a_k)(i, j))
         *   ~~>
         * forall i, j :: { v(i,j) }
         *  (a_1, ... a_k)[
         *      i <- inv(f(i, j), i, j)#0,
         *      j <- inv(f(i, j), i, j)#1
         *  ] (var substitution)
         *    =
         *  (a_1, ... a_k)(i, j) *)
        let* forward_trigger_assertions =
          let inv_fn_qi_opt =
            match inv_fn_expr with
            | App (Expr.Var inv_fn_qi, args, _) -> Some inv_fn_qi
            | _ -> None
          in

          begin match inv_fn_qi_opt with
          | None -> Rewriter.return []
          | Some inv_fn_qi ->
              let inv_expr =
                Expr.mk_app ~loc
                  ~typ:
                    (Type.mk_prod loc
                       (List.map univ_vars_list ~f:(fun var_decl -> var_decl.var_type)))
                  (Expr.Var inv_fn_qi) (token :: env_actual_exprs)
              in

              (* i ~> inv(f(i, j), i, j)#0
               * j ~> inv(f(i, j), i, j)#1*)
              let renaming_map =
                List.foldi univ_vars_list
                  ~init:(Map.empty (module QualIdent))
                  ~f:(fun index map var_decl ->
                    Map.set map
                      ~key:(QualIdent.from_ident var_decl.var_name)
                      ~data:
                        (if Int.(List.length univ_vars_list = 1) then inv_expr
                         else Expr.mk_tuple_lookup ~loc inv_expr index))
              in

              Rewriter.return
                (List.map (List.concat universal_quants.triggers) ~f:(fun trg_term ->
                     let new_trg_term = Expr.alpha_renaming trg_term renaming_map in

                     Stmt.mk_assume_expr ~loc ~cmnt:"forward_trigger_assertion"
                       (Expr.mk_binder ~trigs:universal_quants.triggers ~loc
                          ~typ:Type.bool Forall univ_vars_list
                          (Expr.mk_impl (Expr.mk_and conds)
                             (Expr.mk_eq ~loc trg_term new_trg_term)))))
          end
        in

        let alpha_renaming_map =
          List.fold2_exn univ_vars_list inv_exprs
            ~init:(Map.empty (module QualIdent))
            ~f:(fun map var_decl expr ->
              Map.set map ~key:(QualIdent.from_ident var_decl.var_name) ~data:expr)
        in

        let token_subst = Expr.alpha_renaming token alpha_renaming_map in
        let args_subst =
          List.map args ~f:(fun e -> Expr.alpha_renaming e alpha_renaming_map)
        in
        let conds_subst =
          List.map conds ~f:(fun e -> Expr.alpha_renaming e alpha_renaming_map)
        in
        let new_trigs =
          List.map universal_quants.triggers ~f:(fun trgs ->
              List.map trgs ~f:(fun trg -> Expr.alpha_renaming trg alpha_renaming_map))
        in

        let assume_stmt =
          let token_var_eq_given_token = Expr.mk_eq new_token_expr token_subst in

          let new_chunk =
            match constr with
            | AUPred _ ->
                Expr.mk_app ~loc ~typ:heap_elem_type
                  (Expr.DataConstr au_ra_uncommitted_constr)
                  [ Expr.mk_tuple args_subst ]
            | AUPredCommit _ ->
                let ret_val = List.last_exn args_subst in
                let call_args = List.drop_last_exn args_subst in

                Expr.mk_app ~loc ~typ:heap_elem_type
                  (Expr.DataConstr au_ra_committed_constr)
                  [ Expr.mk_tuple call_args; ret_val ]
            | _ ->
                Error.internal_error loc
                  "expected an atomic-update predicate expression (AUPred or \
                   AUPredCommit)"
          in

          Stmt.mk_assume_expr ~loc
            ~cmnt:
              ((match cmnt with None -> "" | Some cmnt -> cmnt)
              ^ "\ninhale: "
              ^ Stdlib.Format.asprintf "%a" Expr.pr
                  (Expr.mk_binder Forall univ_vars_list
                     (Expr.mk_impl (Expr.mk_and conds) expr)))
            (match univ_vars_list with
            | [] ->
                Expr.mk_eq ~loc au_heap2_expr
                  (Expr.mk_ite ~loc
                     (Expr.mk_and ~loc conds_subst)
                     (Expr.mk_mapupdate ~loc au_heap_expr token_subst
                        (Expr.mk_app ~loc ~typ:heap_elem_type
                           (Expr.Var au_heapchunk_operator)
                           [ Expr.mk_maplookup ~loc au_heap_expr token_subst; new_chunk ]))
                     au_heap_expr)
            | _ ->
                Expr.mk_binder
                  ~trigs:
                    ([
                       [ Expr.mk_maplookup ~loc au_heap2_expr new_token_expr ];
                       [ Expr.mk_maplookup ~loc au_heap_expr new_token_expr ];
                     ]
                    @ new_trigs)
                  ~loc ~typ:Type.bool Forall [ new_token_var ]
                  (Expr.mk_app ~loc ~typ:Type.bool Expr.Ite
                     [
                       (* m1(a,b,c) && l == f1(a, b, c) *)
                       Expr.mk_and ~loc (token_var_eq_given_token :: conds_subst);
                       (* au$Heap2[l] == field.comp( field$Heap[l], f2(a, b, c) ) *)
                       Expr.mk_eq ~loc
                         (Expr.mk_maplookup ~loc au_heap2_expr token_subst)
                         (Expr.mk_app ~loc ~typ:heap_elem_type
                            (Expr.Var au_heapchunk_operator)
                            [
                              Expr.mk_maplookup ~loc au_heap_expr new_token_expr;
                              new_chunk;
                            ]);
                       (* au$Heap2[l] == au$Heap[l] *)
                       Expr.mk_eq ~loc
                         (Expr.mk_maplookup ~loc au_heap2_expr new_token_expr)
                         (Expr.mk_maplookup ~loc au_heap_expr new_token_expr);
                     ]))
        in

        (* au$Heap := au$Heap2 *)
        let eq_stmt =
          Stmt.mk_assign ~loc [ au_heap_expr |> Expr.to_qual_ident ] au_heap2_expr
        in

        let assume_heap_valid =
          Stmt.mk_assume_expr ~loc
            (Expr.mk_app ~loc ~typ:Type.bool (Expr.Var au_heap_valid_inhale_fn)
               [ au_heap_expr ])
        in

        (* let* injectivity_assertion =
          generate_injectivity_assertions ~loc universal_quants conds token
        in *)
        let stmts_list =
          match univ_quants_list with [] -> [] | _ -> [ (* injectivity_assertion *) ]
        in

        let stmts_list =
          stmts_list @ [ havoc_stmt; assume_stmt ] @ forward_trigger_assertions
          @ [ eq_stmt; assume_heap_valid ]
        in

        let stmt = Stmt.mk_block_stmt ~loc stmts_list in

        Rewriter.return stmt
    | e -> (
        let* is_e_pure = ProgUtils.is_expr_pure e in
        if is_e_pure then
          let body_expr =
            match conds with [] -> e | _ -> Expr.mk_impl (Expr.mk_and conds) e
          in
          let assume_expr =
            Expr.mk_binder ~loc ~typ:Type.bool ~trigs:universal_quants.triggers Forall
              (List.map univ_quants_list ~f:(fun (_, v_d) -> v_d))
              body_expr
          in
          Rewriter.return
            (Stmt.mk_assume_expr ~loc
               ~cmnt:
                 ((match cmnt with None -> "" | Some cmnt -> cmnt)
                 ^ "\ninhale: "
                 ^ Stdlib.Format.asprintf "%a" Expr.pr
                     (Expr.mk_binder Forall univ_vars_list
                        (Expr.mk_impl (Expr.mk_and conds) expr)))
               assume_expr)
        else
          match e with
          | App (Var qual_ident, args, _) -> (
              let* symbol = Rewriter.find_and_reify qual_ident in
              match symbol with
              | CallDef c
                when Poly.(
                       c.call_decl.call_decl_kind = Pred
                       || c.call_decl.call_decl_kind = Invariant) ->
                  let* heap_elem_type_qual_iden =
                    ProgUtils.get_pred_utils_rep_type qual_ident
                  in

                  let heap_elem_type = Type.mk_var heap_elem_type_qual_iden in

                  let pred_name = qual_ident in
                  let pred_heap_name = pred_heap_name pred_name in
                  let pred_heap_qual_ident = QualIdent.from_ident pred_heap_name in
                  let pred_heap_expr =
                    Expr.mk_var
                      ~typ:(Type.mk_map loc Type.ref heap_elem_type)
                      pred_heap_qual_ident
                  in

                  let pred_heap2_name = pred_heap_name2 pred_name in
                  let pred_heap2_qual_ident = QualIdent.from_ident pred_heap2_name in
                  let pred_heap2_expr =
                    Expr.mk_var
                      ~typ:(Type.mk_map loc Type.ref heap_elem_type)
                      pred_heap2_qual_ident
                  in

                  let* (pred_heapchunk_operator : qual_ident) =
                    ProgUtils.get_pred_utils_comp pred_name
                  in

                  let* (pred_heap_valid_fn : qual_ident) =
                    ProgUtils.get_pred_utils_valid pred_name
                  in

                  let* (pred_heap_valid_inhale_fn : qual_ident) =
                    ProgUtils.get_pred_utils_valid_inhale loc pred_name
                  in

                  let* pred_in_types = ProgUtils.pred_in_types qual_ident in

                  let* pred_out_types = ProgUtils.pred_out_types qual_ident in

                  let* pred_ra_constr =
                    ProgUtils.pred_ra_constr_qual_ident loc qual_ident
                  in

                  let in_vars =
                    List.map pred_in_types ~f:(fun tp ->
                        {
                          Type.var_name = Ident.fresh loc "in";
                          var_loc = Expr.to_loc e;
                          var_type = tp |> Type.set_ghost false;
                          var_const = false;
                          var_ghost = false;
                          var_implicit = false;
                        })
                  in

                  let in_vars_exprs =
                    List.map in_vars ~f:(fun v -> Expr.from_var_decl v)
                  in
                  let in_vars_tuple = Expr.mk_tuple in_vars_exprs in

                  let actual_arg_in_exprs = List.take args (List.length pred_in_types) in
                  let actual_arg_out_exprs = List.drop args (List.length pred_in_types) in

                  let conjunct_idx = next_conjunct_idx () in
                  let* inv_fn_expr, env_actual_exprs =
                    get_or_generate_inv_function ~loc universal_quants conds
                      (Expr.mk_tuple actual_arg_in_exprs)
                      ~arg_expr:in_vars_tuple ~spec_source ~conjunct_idx
                  in

                  let inv_exprs =
                    List.mapi univ_vars_list ~f:(fun index var_decl ->
                        if Int.(List.length univ_vars_list = 1) then inv_fn_expr
                        else Expr.mk_tuple_lookup inv_fn_expr index)
                  in

                  (* inhale forall i, j :: { v(i,j) } pred(ins(i, j); outs(i, j))
                   *   ~~>
                   * forall i, j :: { v(i,j) }
                   *  outs[
                   *      i <- inv(f(i, j), i, j)#0,
                   *      j <- inv(f(i, j), i, j)#1
                   *  ] (var substitution)
                   *    =
                   *  outs(i, j) *)
                  let* forward_trigger_assertions =
                    let inv_fn_qi_opt =
                      match inv_fn_expr with
                      | App (Expr.Var inv_fn_qi, args, _) -> Some inv_fn_qi
                      | _ -> None
                    in

                    begin match inv_fn_qi_opt with
                    | None -> Rewriter.return []
                    | Some inv_fn_qi ->
                        let inv_expr =
                          Expr.mk_app ~loc
                            ~typ:
                              (Type.mk_prod loc
                                 (List.map univ_vars_list ~f:(fun var_decl ->
                                      var_decl.var_type)))
                            (Expr.Var inv_fn_qi)
                            (Expr.mk_tuple actual_arg_in_exprs :: env_actual_exprs)
                        in

                        (* i ~> inv(f(i, j), i, j)#0
                         * j ~> inv(f(i, j), i, j)#1*)
                        let renaming_map =
                          List.foldi univ_vars_list
                            ~init:(Map.empty (module QualIdent))
                            ~f:(fun index map var_decl ->
                              Map.set map
                                ~key:(QualIdent.from_ident var_decl.var_name)
                                ~data:
                                  (if Int.(List.length univ_vars_list = 1) then inv_expr
                                   else Expr.mk_tuple_lookup ~loc inv_expr index))
                        in

                        Rewriter.return
                          (List.map (List.concat universal_quants.triggers)
                             ~f:(fun trg_term ->
                               let new_trg_term =
                                 Expr.alpha_renaming trg_term renaming_map
                               in

                               Stmt.mk_assume_expr ~loc ~cmnt:"forward_trigger_assertion"
                                 (Expr.mk_binder ~trigs:universal_quants.triggers ~loc
                                    ~typ:Type.bool Forall univ_vars_list
                                    (Expr.mk_impl (Expr.mk_and conds)
                                       (Expr.mk_eq ~loc trg_term new_trg_term)))))
                    end
                  in

                  let alpha_renaming_map =
                    List.fold2_exn univ_vars_list inv_exprs
                      ~init:(Map.empty (module QualIdent))
                      ~f:(fun map var_decl expr ->
                        Map.set map
                          ~key:(QualIdent.from_ident var_decl.var_name)
                          ~data:expr)
                  in

                  let actual_arg_in_exprs_subst =
                    List.map actual_arg_in_exprs ~f:(fun e ->
                        Expr.alpha_renaming e alpha_renaming_map)
                  in
                  let actual_arg_in_exprs_subst_tuple =
                    Expr.mk_tuple actual_arg_in_exprs_subst
                  in
                  let actual_arg_out_exprs_subst =
                    List.map actual_arg_out_exprs ~f:(fun e ->
                        Expr.alpha_renaming e alpha_renaming_map)
                  in
                  let conds_subst =
                    List.map conds ~f:(fun e -> Expr.alpha_renaming e alpha_renaming_map)
                  in
                  let new_trigs =
                    List.map universal_quants.triggers ~f:(fun trgs ->
                        List.map trgs ~f:(fun trg ->
                            Expr.alpha_renaming trg alpha_renaming_map))
                  in

                  let havoc_stmt = Stmt.mk_havoc ~loc pred_heap2_qual_ident in

                  let assume_stmt =
                    let in_vars_eq_args =
                      Expr.mk_eq in_vars_tuple actual_arg_in_exprs_subst_tuple
                    in

                    let new_chunk =
                      mk_pred_new_chunk ~loc c.call_decl.call_decl_kind heap_elem_type
                        pred_ra_constr actual_arg_out_exprs_subst
                    in

                    Stmt.mk_assume_expr ~loc
                      ~cmnt:
                        ((match cmnt with None -> "" | Some cmnt -> cmnt)
                        ^ "\ninhale: "
                        ^ Stdlib.Format.asprintf "%a" Expr.pr
                            (Expr.mk_binder Forall univ_vars_list
                               (Expr.mk_impl (Expr.mk_and conds) expr)))
                      (match univ_vars_list with
                      | [] ->
                          Expr.mk_eq ~loc pred_heap2_expr
                            (Expr.mk_ite ~loc
                               (Expr.mk_and ~loc conds_subst)
                               (Expr.mk_mapupdate ~loc pred_heap_expr
                                  actual_arg_in_exprs_subst_tuple
                                  (Expr.mk_app ~loc ~typ:heap_elem_type
                                     (Expr.Var pred_heapchunk_operator)
                                     [
                                       Expr.mk_maplookup ~loc pred_heap_expr
                                         actual_arg_in_exprs_subst_tuple;
                                       new_chunk;
                                     ]))
                               pred_heap_expr)
                      | _ ->
                          Expr.mk_binder
                            ~trigs:
                              ([
                                 [ Expr.mk_maplookup ~loc pred_heap2_expr in_vars_tuple ];
                                 [ Expr.mk_maplookup ~loc pred_heap_expr in_vars_tuple ];
                               ]
                              @ new_trigs)
                            ~loc ~typ:Type.bool Forall in_vars
                            (Expr.mk_app ~loc ~typ:Type.bool Expr.Ite
                               [
                                 (* m1(a,b,c) && l == f1(a, b, c) *)
                                 Expr.mk_and ~loc (in_vars_eq_args :: conds_subst);
                                 (* pred$Heap2[l] == field.comp( field$Heap[l], f2(a, b, c) ) *)
                                 Expr.mk_eq ~loc
                                   (Expr.mk_maplookup ~loc pred_heap2_expr
                                      actual_arg_in_exprs_subst_tuple)
                                   (Expr.mk_app ~loc ~typ:heap_elem_type
                                      (Expr.Var pred_heapchunk_operator)
                                      [
                                        Expr.mk_maplookup ~loc pred_heap_expr
                                          in_vars_tuple;
                                        new_chunk;
                                      ]);
                                 (* pred$Heap2[l] == pred$Heap[l] *)
                                 Expr.mk_eq ~loc
                                   (Expr.mk_maplookup ~loc pred_heap2_expr in_vars_tuple)
                                   (Expr.mk_maplookup ~loc pred_heap_expr in_vars_tuple);
                               ]))
                  in

                  (* pred$Heap := pred$Heap2 *)
                  let eq_stmt =
                    Stmt.mk_assign ~loc
                      [ pred_heap_expr |> Expr.to_qual_ident ]
                      pred_heap2_expr
                  in

                  let assume_heap_valid =
                    Stmt.mk_assume_expr ~loc
                      (Expr.mk_app ~loc ~typ:Type.bool
                         (Expr.Var pred_heap_valid_inhale_fn) [ pred_heap_expr ])
                  in

                  (* let* injectivity_assertion =
                    generate_injectivity_assertions ~loc universal_quants conds
                      (Expr.mk_tuple actual_arg_in_exprs)
                  in *)
                  let stmts_list =
                    match univ_quants_list with
                    | [] -> []
                    | _ -> [ (* injectivity_assertion *) ]
                  in

                  let stmts_list =
                    stmts_list @ [ havoc_stmt; assume_stmt ] @ forward_trigger_assertions
                    @ [ eq_stmt; assume_heap_valid ]
                  in

                  let stmt = Stmt.mk_block_stmt ~loc stmts_list in

                  Rewriter.return stmt
              | _ -> Error.internal_error loc "expected a predicate definition")
          | _ ->
              (* Logs.debug (fun m -> m "TrnslInhale.trnsl_inhale_a0: unknown inhale expr"); *)
              unsupported_expr_error expr)

  let rec trnsl_assume_expr ?cmnt ?spec_error ?spec_source ~loc (expr : expr) :
      Stmt.t Rewriter.t =
    ParseAssertionLang.parse_a ?cmnt ?spec_error ?spec_source ~loc [] expr
      ~parse_a0:trnsl_assume_a0
  (* trnsl_assume_a ?cmnt ~loc [] expr *)

  and trnsl_assume_a0 ?cmnt ?spec_error ?spec_source ~loc
      (universal_quants : universal_quants) (conds : conditions) (expr : expr) :
      Stmt.t Rewriter.t =
    let open Rewriter.Syntax in
    let univ_quants_list = universal_quants.univ_vars in
    let univ_vars_list = List.map univ_quants_list ~f:(fun (var, var_decl) -> var_decl) in
    let* is_pure = ProgUtils.is_expr_pure expr in
    match expr with
    | App (Own, [ e1; e2; e3 ], _) ->
        (* forall a, b, c :: m1(a, b, c) ==> own(f1(a, b, c), field, f2(a, b, c))

           ===>

           assert forall a, b, c :: m1(a,b,c) ==>
                 heapChunkCompare ( field$Heap[l], f2(a, b, c) )
        *)
        let field_type =
          match Expr.to_type e2 with
          | App (Fld, [ tp_expr ], _) -> tp_expr
          | _ -> Error.type_error (Expr.to_loc e2) "Expected field identifier."
        in

        (* Resolve before deriving the heap's name: a callee's contract arrives
           here with the instantiation substitution already applied
           syntactically, so a manifest field would otherwise get a heap beside
           the alias rather than beside the field it stands for. *)
        let* field_name = Rewriter.resolve (Expr.to_qual_ident e2) in
        let field_heap_name = field_heap_name field_name in
        let field_heap_qual_ident = QualIdent.from_ident field_heap_name in
        let field_heap_expr =
          Expr.mk_var
            ~typ:(Type.mk_map (Expr.to_loc e2) Type.ref field_type)
            field_heap_qual_ident
        in

        let* (field_heapchunk_operator : qual_ident) =
          ProgUtils.get_field_utils_heapchunk_compare field_name
        in

        let* (field_heap_valid_fn : qual_ident) =
          ProgUtils.get_field_utils_valid field_name
        in

        let assume_stmt =
          Stmt.mk_assume_expr ~loc
            ~cmnt:
              ((match cmnt with None -> "" | Some cmnt -> cmnt ^ "\n")
              ^ "assume: "
              ^ Stdlib.Format.asprintf "%a" Expr.pr
                  (Expr.mk_binder Forall univ_vars_list
                     (Expr.mk_impl (Expr.mk_and conds) expr)))
            (Expr.mk_binder ~loc ~typ:Type.bool Forall univ_vars_list
               (Expr.mk_impl ~loc (Expr.mk_and ~loc conds)
                  (Expr.mk_app ~loc ~typ:Type.bool (Expr.Var field_heapchunk_operator)
                     [ Expr.mk_maplookup ~loc field_heap_expr e1; e3 ])))
        in

        Rewriter.return assume_stmt
    | App ((AUPred call_qual_ident as constr), token :: au_args, _)
    | App ((AUPredCommit call_qual_ident as constr), token :: au_args, _) ->
        let args =
          match (constr, au_args) with
          | AUPred _, [ args_tuple ] -> Expr.unfold_tuple args_tuple
          | AUPredCommit _, [ args_tuple; ret_tuple ] ->
              Expr.unfold_tuple args_tuple @ [ ret_tuple ]
          | _ ->
              (* Logs.debug(fun m -> m "TrnslInhale.trnsl_assume_a0: could not compute args"); *)
              unsupported_expr_error expr
        in
        let* () =
          Rewriter.Logs.debug (fun printers m ->
              m "HeapsExplicitTrnsl.Trnslassume.trnsl_assume_a0: expr: %a"
                printers.pr_expr expr)
        in
        let loc = Expr.to_loc expr in
        let* heap_elem_type_qual_iden = ProgUtils.get_au_utils_rep_type call_qual_ident in

        let heap_elem_type = Type.mk_var heap_elem_type_qual_iden in

        let call_name = call_qual_ident in
        let au_heap_name = au_heap_name call_name in
        let au_heap_qual_ident = QualIdent.from_ident au_heap_name in
        let au_heap_expr =
          Expr.mk_var ~typ:(Type.mk_map loc Type.ref heap_elem_type) au_heap_qual_ident
        in

        let* (au_heapchunk_operator : qual_ident) =
          ProgUtils.get_au_utils_heapchunk_compare call_name
        in

        let* au_ra_uncommitted_constr =
          ProgUtils.au_ra_uncommitted_constr_qual_ident loc call_qual_ident
        in
        let* au_ra_committed_constr =
          ProgUtils.au_ra_committed_constr_qual_ident loc call_qual_ident
        in

        let assume_stmt =
          let new_chunk =
            match constr with
            | AUPred _ ->
                Expr.mk_app ~loc ~typ:heap_elem_type
                  (Expr.DataConstr au_ra_uncommitted_constr)
                  [ Expr.mk_tuple args ]
            | AUPredCommit _ ->
                let ret_val = List.last_exn args in
                let call_args = List.drop_last_exn args in

                Expr.mk_app ~loc ~typ:heap_elem_type
                  (Expr.DataConstr au_ra_committed_constr)
                  [ Expr.mk_tuple call_args; ret_val ]
            | _ ->
                Error.internal_error loc
                  "expected an atomic-update predicate expression (AUPred or \
                   AUPredCommit)"
          in

          Stmt.mk_assume_expr ~loc
            ~cmnt:
              ((match cmnt with None -> "" | Some cmnt -> cmnt)
              ^ "\nassume: "
              ^ Stdlib.Format.asprintf "%a" Expr.pr
                  (Expr.mk_binder Forall univ_vars_list
                     (Expr.mk_impl (Expr.mk_and conds) expr)))
            (Expr.mk_binder ~loc ~typ:Type.bool Forall univ_vars_list
               (Expr.mk_impl ~loc (Expr.mk_and ~loc conds)
                  (Expr.mk_app ~loc ~typ:Type.bool (Expr.Var au_heapchunk_operator)
                     [ Expr.mk_maplookup ~loc au_heap_expr token; new_chunk ])))
        in

        Rewriter.return assume_stmt
    | e when is_pure ->
        let body_expr =
          match conds with [] -> e | _ -> Expr.mk_impl (Expr.mk_and conds) e
        in
        let assume_expr =
          Expr.mk_binder ~loc ~typ:Type.bool ~trigs:universal_quants.triggers Forall
            (List.map univ_quants_list ~f:(fun (_, v_d) -> v_d))
            body_expr
        in
        Rewriter.return
          (Stmt.mk_assume_expr ~loc
             ~cmnt:
               ((match cmnt with None -> "" | Some cmnt -> cmnt)
               ^ "\nassume: "
               ^ Stdlib.Format.asprintf "%a" Expr.pr
                   (Expr.mk_binder Forall univ_vars_list
                      (Expr.mk_impl (Expr.mk_and conds) expr)))
             assume_expr)
    | App (Var qual_ident, args, _) ->
        let* c = Rewriter.find_and_reify_callable qual_ident in
        let* heap_elem_type_qual_iden = ProgUtils.get_pred_utils_rep_type qual_ident in

        let heap_elem_type = Type.mk_var heap_elem_type_qual_iden in

        let pred_name = qual_ident in
        let pred_heap_name = pred_heap_name pred_name in
        let pred_heap_qual_ident = QualIdent.from_ident pred_heap_name in
        let pred_heap_expr =
          Expr.mk_var ~typ:(Type.mk_map loc Type.ref heap_elem_type) pred_heap_qual_ident
        in

        let* (pred_heapchunk_operator : qual_ident) =
          ProgUtils.get_pred_utils_heapchunk_compare pred_name
        in

        let* pred_in_types = ProgUtils.pred_in_types qual_ident in

        let* pred_out_types = ProgUtils.pred_out_types qual_ident in

        let* pred_ra_constr = ProgUtils.pred_ra_constr_qual_ident loc qual_ident in

        let assume_stmt =
          let new_chunk =
            mk_pred_new_chunk ~loc c.call_decl.call_decl_kind heap_elem_type
              pred_ra_constr
              (List.drop args (List.length pred_in_types))
          in

          Stmt.mk_assume_expr ~loc
            ~cmnt:
              ((match cmnt with None -> "" | Some cmnt -> cmnt)
              ^ "\nassume: "
              ^ Stdlib.Format.asprintf "%a" Expr.pr
                  (Expr.mk_binder Forall univ_vars_list
                     (Expr.mk_impl (Expr.mk_and conds) expr)))
            (Expr.mk_binder ~loc ~typ:Type.bool Forall univ_vars_list
               (Expr.mk_impl ~loc
                  (* m1(a,b,c) && l == f1(a, b, c) *)
                  (Expr.mk_and ~loc conds)
                  (* pred$Heap2[l] == field.comp( field$Heap[l], f2(a, b, c) ) *)
                  (Expr.mk_app ~loc ~typ:Type.bool (Expr.Var pred_heapchunk_operator)
                     [
                       Expr.mk_maplookup ~loc pred_heap_expr
                         (Expr.mk_tuple (List.take args (List.length pred_in_types)));
                       new_chunk;
                     ])))
        in
        Rewriter.return assume_stmt
    | _ ->
        (* Logs.debug(fun m -> m "TrnslInhale.trnsl_assume_a0: unknown expr"); *)
        unsupported_expr_error expr
end

module TrnslExhale = struct
  (* See [TrnslInhale.conjunct_counter]: same purpose, own counter, reset by
     [trnsl_exhale_expr]. *)
  let conjunct_counter = ref 0

  let next_conjunct_idx () =
    let idx = !conjunct_counter in
    conjunct_counter := idx + 1;
    idx

  let rec rewriter_user_annot_elim_exists_from_exhales (stmt : Stmt.t) :
      (Stmt.t, expr option) Rewriter.t_ext =
    let open Rewriter.Syntax in
    let rec find_existentials (expr : expr) : var_decl list =
      match expr with
      | Binder (Exists, var_decls, trgs, e, _) -> var_decls @ find_existentials e
      | Binder (_, var_decls, trgs, e, _) -> find_existentials e
      | App (_, exprs, _) -> List.concat_map exprs ~f:find_existentials
    in

    let subst_existentials (expr : expr) (subst_map : expr qual_ident_map) : expr =
      let rec elim_exists (expr : expr) subst_map : expr =
        match expr with
        | Binder (Exists, var_decls, trgs, e, _) ->
            let all_existentials_exist =
              List.for_all var_decls ~f:(fun var_decl ->
                  Map.mem subst_map (QualIdent.from_ident var_decl.var_name))
            in

            if not all_existentials_exist then
              Error.internal_error (Expr.to_loc expr)
                "Expected all existentials to be matched up"
            else e
        | Binder (b, var_decls, trgs, e, expr_attr) ->
            let e = elim_exists e subst_map in
            Binder (b, var_decls, trgs, e, expr_attr)
        | App (constr, exprs, expr_attr) ->
            let exprs = List.map exprs ~f:(fun e -> elim_exists e subst_map) in
            App (constr, exprs, expr_attr)
      in

      let expr = Expr.alpha_renaming expr subst_map in
      elim_exists expr subst_map
    in

    match stmt.stmt_desc with
    | Basic (Spec (Exhale, spec)) -> (
        let* prev_expr = Rewriter.current_user_state in
        let* () = Rewriter.set_user_state None in
        let* printers = Rewriter.current_printers in

        Logs.debug (fun m ->
            m
              "HeapsExplicitTrnsl.TrnslExhale.rewriter_user_annot_elim_exists_from_exhales: \
               prev_expr: %a; exhale_expr: %a"
              (Util.Print.pr_option printers.pr_expr)
              prev_expr printers.pr_expr spec.spec_form);

        let exhale_expr = spec.spec_form in
        match prev_expr with
        | None -> Rewriter.return stmt
        | Some prev_expr -> (
            Logs.debug (fun m ->
                m
                  "HeapsExplicitTrnsl.TrnslExhale.rewriter_user_annot_elim_exists_from_exhales: \
                   prev_expr: %a; exhale_expr: %a"
                  printers.pr_expr prev_expr printers.pr_expr exhale_expr);
            let existential_vars = find_existentials exhale_expr in

            match match_up_expr ~printers spec.spec_form prev_expr existential_vars with
            | None -> Rewriter.return stmt
            | Some var_map ->
                let subst_map = Map.map var_map ~f:(fun (var_decl, expr) -> expr) in
                let subst_map =
                  (Map.map_keys_exn (module QualIdent)) subst_map ~f:(fun ident ->
                      QualIdent.from_ident ident)
                in
                let spec_form = subst_existentials exhale_expr subst_map in

                let spec = { spec with spec_form } in

                Rewriter.return { stmt with stmt_desc = Basic (Spec (Exhale, spec)) }))
    | Basic (Spec (Assert, spec)) -> (
        let* prev_expr = Rewriter.current_user_state in

        let* () = Rewriter.set_user_state (Some spec.spec_form) in
        let* printers = Rewriter.current_printers in

        let assert_expr = spec.spec_form in
        match prev_expr with
        | None -> Rewriter.return stmt
        | Some prev_expr -> (
            Logs.debug (fun m ->
                m
                  "HeapsExplicitTrnsl.TrnslExhale.rewriter_user_annot_elim_exists_from_exhales \
                   (assert): prev_expr: %a; assert_expr: %a"
                  printers.pr_expr prev_expr printers.pr_expr assert_expr);
            let existential_vars = find_existentials assert_expr in

            match match_up_expr ~printers spec.spec_form prev_expr existential_vars with
            | None ->
                Logs.debug (fun m ->
                    m
                      "HeapsExplicitTrnsl.TrnslExhale.rewriter_user_annot_elim_exists_from_exhales \
                       (assert): No match up");
                Rewriter.return stmt
            | Some var_map ->
                let subst_map = Map.map var_map ~f:(fun (var_decl, expr) -> expr) in
                let subst_map =
                  (Map.map_keys_exn (module QualIdent)) subst_map ~f:(fun ident ->
                      QualIdent.from_ident ident)
                in
                let spec_form = subst_existentials assert_expr subst_map in

                Logs.debug (fun m ->
                    m
                      "HeapsExplicitTrnsl.TrnslExhale.rewriter_user_annot_elim_exists_from_exhales \
                       (assert): spec_form: %a"
                      printers.pr_expr spec_form);

                let spec = { spec with spec_form } in

                Rewriter.return { stmt with stmt_desc = Basic (Spec (Assert, spec)) }))
    | Basic _ ->
        let* () = Rewriter.set_user_state None in
        Rewriter.return stmt
    | _ ->
        (* let* () = Rewriter.set_user_state None in *)
        Rewriter.Stmt.descend stmt ~f:rewriter_user_annot_elim_exists_from_exhales

  let rec trnsl_exhale_expr ?cmnt ?spec_error ?spec_source ~loc (expr : expr) :
      Stmt.t Rewriter.t =
    conjunct_counter := 0;
    ParseAssertionLang.parse_a ?cmnt ?spec_error ?spec_source ~loc [] expr
      ~parse_a0:trnsl_exhale_a0

  and trnsl_exhale_a0 ?cmnt ?(spec_error = []) ?spec_source ~loc
      (universal_quants : universal_quants) (conds : conditions) (expr : expr) :
      Stmt.t Rewriter.t =
    let open Rewriter.Syntax in
    let* resource =
      if List.is_empty universal_quants.univ_vars then ScalarResource.decode expr
      else Rewriter.return None
    in
    match resource with
    | Some resource ->
        ignore (next_conjunct_idx ());
        Rewriter.return
          (ScalarResource.translate ?cmnt ~spec_error ?spec_source ~loc Exhale conds expr
             resource)
    | None ->
        trnsl_exhale_a0_general ?cmnt ~spec_error ?spec_source ~loc universal_quants conds
          expr

  and trnsl_exhale_a0_general ?cmnt ?(spec_error = []) ?spec_source ~loc
      (universal_quants : universal_quants) (conds : conditions) (expr : expr) :
      Stmt.t Rewriter.t =
    let open Rewriter.Syntax in
    let univ_quants_list = universal_quants.univ_vars in
    let univ_vars_list = List.map univ_quants_list ~f:(fun (var, var_decl) -> var_decl) in

    match expr with
    | App (Own, [ e1; e2; e3 ], _) ->
        (* forall a, b, c :: m1(a, b, c) ==> own(f1(a, b, c), field, f2(a, b, c))

           ===>

           // asserting injectivity of functions
           assert forall a, b, c, a', b', c' :: m1(a, b, c) && m1(a', b', c') ==> f1(a, b, c) == f1(a', b', c') ==> (a == a' && b == b' && c == c')

           havoc(field$Heap2);

           assert forall l: Ref ::
             m1(inv(l)#0, inv(l)#1, inv(l)#2) && l == f1(inv(l)#0, inv(l)#1, inv(l)#2) ?
                 field$Heap2[l] == field.frame( field$Heap[l], f2(a, b, c) ) :
               field$Heap2[l] == field$Heap[l]

           field$Heap := field$Heap2
           assert field.valid(field$Heap)
        *)
        let field_type =
          match Expr.to_type e2 with
          | App (Fld, [ tp_expr ], _) -> tp_expr
          | _ -> Error.type_error (Expr.to_loc e2) "Expected field identifier."
        in

        (* Resolve before deriving the heap's name: a callee's contract arrives
           here with the instantiation substitution already applied
           syntactically, so a manifest field would otherwise get a heap beside
           the alias rather than beside the field it stands for. *)
        let* field_name = Rewriter.resolve (Expr.to_qual_ident e2) in
        let field_heap_name = field_heap_name field_name in
        let field_heap_qual_ident = QualIdent.from_ident field_heap_name in
        let field_heap_expr =
          Expr.mk_var
            ~typ:(Type.mk_map (Expr.to_loc e2) Type.ref field_type)
            field_heap_qual_ident
        in

        let field_heap2_name = field_heap_name2 field_name in
        let field_heap2_qual_ident = QualIdent.from_ident field_heap2_name in
        let field_heap2_expr =
          Expr.mk_var
            ~typ:(Type.mk_map (Expr.to_loc e2) Type.ref field_type)
            field_heap2_qual_ident
        in

        let* (field_heapchunk_operator : qual_ident) =
          ProgUtils.get_field_utils_frame field_name
        in

        let* (field_heap_valid_fn : qual_ident) =
          ProgUtils.get_field_utils_valid field_name
        in

        let l_var =
          Type.
            {
              var_name = Ident.fresh (Expr.to_loc expr) "l";
              var_loc = Expr.to_loc expr;
              var_type = Type.ref;
              var_const = false;
              var_ghost = false;
              var_implicit = false;
            }
        in

        let l_expr =
          Expr.mk_var ~typ:l_var.var_type (QualIdent.from_ident l_var.var_name)
        in

        let conjunct_idx = next_conjunct_idx () in
        let* inv_fn_expr, env_actual_exprs =
          get_or_generate_inv_function ~loc universal_quants conds e1 ~arg_expr:l_expr
            ~spec_source ~conjunct_idx
        in

        let inv_exprs =
          List.mapi univ_vars_list ~f:(fun index var_decl ->
              if Int.(List.length univ_vars_list = 1) then inv_fn_expr
              else Expr.mk_tuple_lookup inv_fn_expr index)
        in

        (* exhale forall i, j :: { v(i,j) } own(f(i, j), fld, v(i, j))
         *   ~~>
         * forall i, j :: { v(i,j) }
         *  v[
         *      i <- inv(f(i, j), i, j)#0,
         *      j <- inv(f(i, j), i, j)#1
         *  ] (var substitution)
         *    =
         *  v(i, j) *)
        let* forward_trigger_assertions =
          let inv_fn_qi_opt =
            match inv_fn_expr with
            | App (Expr.Var inv_fn_qi, args, _) -> Some inv_fn_qi
            | _ -> None
          in

          begin match inv_fn_qi_opt with
          | None -> Rewriter.return []
          | Some inv_fn_qi ->
              let inv_expr =
                Expr.mk_app ~loc
                  ~typ:
                    (Type.mk_prod loc
                       (List.map univ_vars_list ~f:(fun var_decl -> var_decl.var_type)))
                  (Expr.Var inv_fn_qi) (e1 :: env_actual_exprs)
              in

              (* i ~> inv(f(i, j), i, j)#0
               * j ~> inv(f(i, j), i, j)#1*)
              let renaming_map =
                List.foldi univ_vars_list
                  ~init:(Map.empty (module QualIdent))
                  ~f:(fun index map var_decl ->
                    Map.set map
                      ~key:(QualIdent.from_ident var_decl.var_name)
                      ~data:
                        (if Int.(List.length univ_vars_list = 1) then inv_expr
                         else Expr.mk_tuple_lookup ~loc inv_expr index))
              in

              Rewriter.return
                (List.map (List.concat universal_quants.triggers) ~f:(fun trg_term ->
                     let new_trg_term = Expr.alpha_renaming trg_term renaming_map in

                     Stmt.mk_assume_expr ~loc ~cmnt:"forward_trigger_assertion"
                       (Expr.mk_binder ~trigs:universal_quants.triggers ~loc
                          ~typ:Type.bool Forall univ_vars_list
                          (Expr.mk_impl (Expr.mk_and conds)
                             (Expr.mk_eq ~loc trg_term new_trg_term)))))
          end
        in

        let alpha_renaming_map =
          List.fold2_exn univ_vars_list inv_exprs
            ~init:(Map.empty (module QualIdent))
            ~f:(fun map var_decl expr ->
              Map.set map ~key:(QualIdent.from_ident var_decl.var_name) ~data:expr)
        in

        let e1_subst = Expr.alpha_renaming e1 alpha_renaming_map in
        let e3_subst = Expr.alpha_renaming e3 alpha_renaming_map in
        let conds_subst =
          List.map conds ~f:(fun e -> Expr.alpha_renaming e alpha_renaming_map)
        in
        let new_trigs =
          List.map universal_quants.triggers ~f:(fun trgs ->
              List.map trgs ~f:(fun trg -> Expr.alpha_renaming trg alpha_renaming_map))
        in

        let havoc_stmt = Stmt.mk_havoc ~loc field_heap2_qual_ident in
        let assume_stmt =
          let l_eq_e1_expr = Expr.mk_eq l_expr e1_subst in

          Stmt.mk_assume_expr ~loc
            ~cmnt:
              ((match cmnt with None -> "" | Some cmnt -> cmnt ^ "\n")
              ^ "exhale: "
              ^ Stdlib.Format.asprintf "%a" Expr.pr
                  (Expr.mk_binder Forall univ_vars_list
                     (Expr.mk_impl (Expr.mk_and conds) expr)))
            (match univ_vars_list with
            | [] ->
                Expr.mk_eq ~loc field_heap2_expr
                  (Expr.mk_ite ~loc
                     (Expr.mk_and ~loc conds_subst)
                     (* field$Heap2[l] == field.comp( field$Heap[l], f2(a, b, c) ) *)
                     (Expr.mk_mapupdate ~loc field_heap_expr e1_subst
                        (Expr.mk_app ~loc ~typ:field_type
                           (Expr.Var field_heapchunk_operator)
                           [ Expr.mk_maplookup ~loc field_heap_expr e1_subst; e3_subst ]))
                     field_heap_expr)
            | _ ->
                Expr.mk_binder
                  ~trigs:
                    ([
                       [ Expr.mk_maplookup ~loc field_heap2_expr l_expr ];
                       [ Expr.mk_maplookup ~loc field_heap_expr l_expr ];
                     ]
                    @ new_trigs)
                  ~loc ~typ:Type.bool Forall [ l_var ]
                  (Expr.mk_app ~loc ~typ:Type.bool Expr.Ite
                     [
                       (* m1(a,b,c) && l == f1(a, b, c) *)
                       Expr.mk_and ~loc (l_eq_e1_expr :: conds_subst);
                       (* field$Heap2[l] == field.comp( field$Heap[l], f2(a, b, c) ) *)
                       Expr.mk_eq ~loc
                         (Expr.mk_maplookup ~loc field_heap2_expr e1_subst)
                         (Expr.mk_app ~loc ~typ:field_type
                            (Expr.Var field_heapchunk_operator)
                            [ Expr.mk_maplookup ~loc field_heap_expr l_expr; e3_subst ]);
                       (* field$Heap2[l] == field$Heap[l] *)
                       Expr.mk_eq ~loc
                         (Expr.mk_maplookup ~loc field_heap2_expr l_expr)
                         (Expr.mk_maplookup ~loc field_heap_expr l_expr);
                     ]))
        in

        (* field$Heap := field$Heap2 *)
        let eq_stmt =
          Stmt.mk_assign ~loc [ field_heap_expr |> Expr.to_qual_ident ] field_heap2_expr
        in

        let assert_heap_valid =
          Stmt.mk_assert_expr ~loc
            ~spec_error:
              (spec_error
              @ [
                  Stmt.mk_const_spec_error
                    (Error.RelatedLoc, Expr.to_loc expr, "This own predicate may not hold");
                ])
            (Expr.mk_app ~loc ~typ:Type.bool (Expr.Var field_heap_valid_fn)
               [ field_heap_expr ])
        in

        let stmts_list =
          [ havoc_stmt; assume_stmt ] @ forward_trigger_assertions
          @ [ eq_stmt; assert_heap_valid ]
        in

        let stmt = Stmt.mk_block_stmt ~loc stmts_list in

        Rewriter.return stmt
    | App ((AUPred call_qual_ident as constr), token :: au_args, _)
    | App ((AUPredCommit call_qual_ident as constr), token :: au_args, _) ->
        let args =
          match (constr, au_args) with
          | AUPred _, [ args_tuple ] -> Expr.unfold_tuple args_tuple
          | AUPredCommit _, [ args_tuple; ret_tuple ] ->
              Expr.unfold_tuple args_tuple @ [ ret_tuple ]
          | _ ->
              (* Logs.debug(fun m -> m "TrnslInhale.trnsl_exhale_a0: could not compute args"); *)
              unsupported_expr_error expr
        in
        let* heap_elem_type_qual_iden = ProgUtils.get_au_utils_rep_type call_qual_ident in

        let heap_elem_type = Type.mk_var heap_elem_type_qual_iden in

        let call_name = call_qual_ident in
        let au_heap_name = au_heap_name call_name in
        let au_heap_qual_ident = QualIdent.from_ident au_heap_name in
        let au_heap_expr =
          Expr.mk_var ~typ:(Type.mk_map loc Type.ref heap_elem_type) au_heap_qual_ident
        in

        let au_heap2_name = au_heap_name2 call_name in
        let au_heap2_qual_ident = QualIdent.from_ident au_heap2_name in
        let au_heap2_expr =
          Expr.mk_var ~typ:(Type.mk_map loc Type.ref heap_elem_type) au_heap2_qual_ident
        in

        let* (au_heapchunk_operator : qual_ident) =
          ProgUtils.get_au_utils_frame call_name
        in

        let* (au_heap_valid_fn : qual_ident) = ProgUtils.get_au_utils_valid call_name in

        let* au_ra_uncommitted_constr =
          ProgUtils.au_ra_uncommitted_constr_qual_ident loc call_qual_ident
        in
        let* au_ra_committed_constr =
          ProgUtils.au_ra_committed_constr_qual_ident loc call_qual_ident
        in

        let havoc_stmt = Stmt.mk_havoc ~loc au_heap2_qual_ident in

        let new_token_var =
          {
            Type.var_name = Ident.fresh loc "tok";
            var_loc = loc;
            var_type = Type.atomic_token call_name;
            var_const = false;
            var_ghost = true;
            var_implicit = false;
          }
        in

        let new_token_expr = Expr.from_var_decl new_token_var in

        let conjunct_idx = next_conjunct_idx () in
        let* inv_fn_expr, env_actual_exprs =
          get_or_generate_inv_function ~loc universal_quants conds token
            ~arg_expr:new_token_expr ~spec_source ~conjunct_idx
        in

        let inv_exprs =
          List.mapi univ_vars_list ~f:(fun index var_decl ->
              if Int.(List.length univ_vars_list = 1) then inv_fn_expr
              else Expr.mk_tuple_lookup inv_fn_expr index)
        in

        (* exhale forall i, j :: { v(i,j) } AUPred(proc, gamma(i,j), (a_1, ... a_k)(i, j))
         *   ~~>
         * forall i, j :: { v(i,j) }
         *  (a_1, ... a_k)[
         *      i <- inv(f(i, j), i, j)#0,
         *      j <- inv(f(i, j), i, j)#1
         *  ] (var substitution)
         *    =
         *  (a_1, ... a_k)(i, j) *)
        let* forward_trigger_assertions =
          let inv_fn_qi_opt =
            match inv_fn_expr with
            | App (Expr.Var inv_fn_qi, args, _) -> Some inv_fn_qi
            | _ -> None
          in

          begin match inv_fn_qi_opt with
          | None -> Rewriter.return []
          | Some inv_fn_qi ->
              let inv_expr =
                Expr.mk_app ~loc
                  ~typ:
                    (Type.mk_prod loc
                       (List.map univ_vars_list ~f:(fun var_decl -> var_decl.var_type)))
                  (Expr.Var inv_fn_qi) (token :: env_actual_exprs)
              in

              (* i ~> inv(f(i, j), i, j)#0
               * j ~> inv(f(i, j), i, j)#1*)
              let renaming_map =
                List.foldi univ_vars_list
                  ~init:(Map.empty (module QualIdent))
                  ~f:(fun index map var_decl ->
                    Map.set map
                      ~key:(QualIdent.from_ident var_decl.var_name)
                      ~data:
                        (if Int.(List.length univ_vars_list = 1) then inv_expr
                         else Expr.mk_tuple_lookup ~loc inv_expr index))
              in

              Rewriter.return
                (List.map (List.concat universal_quants.triggers) ~f:(fun trg_term ->
                     let new_trg_term = Expr.alpha_renaming trg_term renaming_map in

                     Stmt.mk_assume_expr ~loc ~cmnt:"forward_trigger_assertion"
                       (Expr.mk_binder ~trigs:universal_quants.triggers ~loc
                          ~typ:Type.bool Forall univ_vars_list
                          (Expr.mk_impl (Expr.mk_and conds)
                             (Expr.mk_eq ~loc trg_term new_trg_term)))))
          end
        in

        let alpha_renaming_map =
          List.fold2_exn univ_vars_list inv_exprs
            ~init:(Map.empty (module QualIdent))
            ~f:(fun map var_decl expr ->
              Map.set map ~key:(QualIdent.from_ident var_decl.var_name) ~data:expr)
        in

        let token_subst = Expr.alpha_renaming token alpha_renaming_map in
        let args_subst =
          List.map args ~f:(fun e -> Expr.alpha_renaming e alpha_renaming_map)
        in
        let conds_subst =
          List.map conds ~f:(fun e -> Expr.alpha_renaming e alpha_renaming_map)
        in
        let new_trigs =
          List.map universal_quants.triggers ~f:(fun trgs ->
              List.map trgs ~f:(fun trg -> Expr.alpha_renaming trg alpha_renaming_map))
        in

        let assume_stmt =
          let token_var_eq_given_token = Expr.mk_eq new_token_expr token_subst in

          let new_chunk =
            match constr with
            | AUPred _ ->
                Expr.mk_app ~loc ~typ:heap_elem_type
                  (Expr.DataConstr au_ra_uncommitted_constr)
                  [ Expr.mk_tuple args_subst ]
            | AUPredCommit _ ->
                let ret_val = List.last_exn args_subst in
                let call_args = List.drop_last_exn args_subst in

                Expr.mk_app ~loc ~typ:heap_elem_type
                  (Expr.DataConstr au_ra_committed_constr)
                  [ Expr.mk_tuple call_args; ret_val ]
            | _ ->
                Error.internal_error loc
                  "expected an atomic-update predicate expression (AUPred or \
                   AUPredCommit)"
          in

          Stmt.mk_assume_expr ~loc
            ~cmnt:
              ((match cmnt with None -> "" | Some cmnt -> cmnt)
              ^ "\nexhale: "
              ^ Stdlib.Format.asprintf "%a" Expr.pr
                  (Expr.mk_binder Forall univ_vars_list
                     (Expr.mk_impl (Expr.mk_and conds) expr)))
            (match univ_vars_list with
            | [] ->
                Expr.mk_eq ~loc au_heap2_expr
                  (Expr.mk_ite ~loc
                     (Expr.mk_and ~loc conds_subst)
                     (Expr.mk_mapupdate ~loc au_heap_expr token_subst
                        (Expr.mk_app ~loc ~typ:heap_elem_type
                           (Expr.Var au_heapchunk_operator)
                           [ Expr.mk_maplookup ~loc au_heap_expr token_subst; new_chunk ]))
                     au_heap_expr)
            | _ ->
                Expr.mk_binder
                  ~trigs:
                    ([
                       [ Expr.mk_maplookup ~loc au_heap2_expr new_token_expr ];
                       [ Expr.mk_maplookup ~loc au_heap_expr new_token_expr ];
                     ]
                    @ new_trigs)
                  ~loc ~typ:Type.bool Forall [ new_token_var ]
                  (Expr.mk_binder ~loc ~typ:Type.bool Forall univ_vars_list
                     (Expr.mk_app ~loc ~typ:Type.bool Expr.Ite
                        [
                          (* m1(a,b,c) && l == f1(a, b, c) *)
                          Expr.mk_and ~loc (token_var_eq_given_token :: conds_subst);
                          (* au$Heap2[l] == field.comp( field$Heap[l], f2(a, b, c) ) *)
                          Expr.mk_eq ~loc
                            (Expr.mk_maplookup ~loc au_heap2_expr token_subst)
                            (Expr.mk_app ~loc ~typ:heap_elem_type
                               (Expr.Var au_heapchunk_operator)
                               [
                                 Expr.mk_maplookup ~loc au_heap_expr new_token_expr;
                                 new_chunk;
                               ]);
                          (* pred$Heap2[l] == pred$Heap[l] *)
                          Expr.mk_eq ~loc
                            (Expr.mk_maplookup ~loc au_heap2_expr new_token_expr)
                            (Expr.mk_maplookup ~loc au_heap_expr new_token_expr);
                        ])))
        in

        (* pred$Heap := pred$Heap2 *)
        let eq_stmt =
          Stmt.mk_assign ~loc [ au_heap_expr |> Expr.to_qual_ident ] au_heap2_expr
        in

        (* Logs.debug (fun m -> m "heapsExplicitTrnsl.trnsl_exhale_a0: Found auPred/auPredCommit; loc=%s expr=%a; Length of spec_error: %i; errors=%a" 
          (Loc.to_string_simple loc)
          Expr.pr expr 
          (List.length spec_error) 
          (Util.Print.pr_list_nl Format.pp_print_string) (List.map spec_error ~f:(fun err -> err call_qual_ident  loc |> Error.to_string))
        ); *)
        let assert_heap_valid =
          Stmt.mk_assert_expr ~loc
            ~spec_error:
              (spec_error
              @ [
                  Stmt.mk_const_spec_error
                    ( Error.RelatedLoc,
                      Expr.to_loc expr,
                      "This atomic update predicate may not hold" );
                ])
            (Expr.mk_app ~loc ~typ:Type.bool (Expr.Var au_heap_valid_fn) [ au_heap_expr ])
        in

        (* let* injectivity_assertion =
          generate_injectivity_assertions ~loc universal_quants conds token
        in *)
        let stmts_list =
          match univ_quants_list with [] -> [] | _ -> [ (* injectivity_assertion *) ]
        in

        let stmts_list =
          stmts_list @ [ havoc_stmt; assume_stmt ] @ forward_trigger_assertions
          @ [ eq_stmt; assert_heap_valid ]
        in

        let stmt = Stmt.mk_block_stmt ~loc stmts_list in

        Rewriter.return stmt
    | e -> (
        let* is_e_pure = ProgUtils.is_expr_pure e in
        if is_e_pure then
          let assert_expr =
            Expr.mk_binder ~loc ~typ:Type.bool ~trigs:universal_quants.triggers Forall
              (List.map univ_quants_list ~f:(fun (_, v_d) -> v_d))
              (Expr.mk_impl (Expr.mk_and conds) e)
          in

          let assert_stmt =
            Stmt.mk_assert_expr ~loc
              ~cmnt:
                ((match cmnt with None -> "" | Some cmnt -> cmnt)
                ^ "\nexhale: "
                ^ Stdlib.Format.asprintf "%a" Expr.pr
                    (Expr.mk_binder Forall univ_vars_list
                       (Expr.mk_impl (Expr.mk_and conds) expr)))
              ~spec_error:
                (spec_error
                @ [
                    Stmt.mk_const_spec_error
                      (Error.RelatedLoc, Expr.to_loc e, "This assertion may not hold");
                  ])
              assert_expr
          in
          (* let assume_stmt = (Stmt.mk_assume_expr ~loc assert_expr) in *)
          (* Rewriter.return (Stmt.mk_block_stmt ~loc [assume_stmt; assert_stmt]) *)
          Rewriter.return assert_stmt
        else
          match e with
          | App (Var qual_ident, args, _) -> (
              let* symbol = Rewriter.find_and_reify qual_ident in
              match symbol with
              | CallDef c
                when Poly.(
                       c.call_decl.call_decl_kind = Pred
                       || c.call_decl.call_decl_kind = Invariant) ->
                  let* heap_elem_type_qual_iden =
                    ProgUtils.get_pred_utils_rep_type qual_ident
                  in

                  let heap_elem_type = Type.mk_var heap_elem_type_qual_iden in

                  let pred_name = qual_ident in
                  let pred_heap_name = pred_heap_name pred_name in
                  let pred_heap_qual_ident = QualIdent.from_ident pred_heap_name in
                  let pred_heap_expr =
                    Expr.mk_var
                      ~typ:(Type.mk_map loc Type.ref heap_elem_type)
                      pred_heap_qual_ident
                  in

                  let pred_heap2_name = pred_heap_name2 pred_name in
                  let pred_heap2_qual_ident = QualIdent.from_ident pred_heap2_name in
                  let pred_heap2_expr =
                    Expr.mk_var
                      ~typ:(Type.mk_map loc Type.ref heap_elem_type)
                      pred_heap2_qual_ident
                  in

                  let* (pred_heapchunk_operator : qual_ident) =
                    ProgUtils.get_pred_utils_frame pred_name
                  in

                  let* (pred_heap_valid_fn : qual_ident) =
                    ProgUtils.get_pred_utils_valid pred_name
                  in

                  let* pred_in_types = ProgUtils.pred_in_types qual_ident in

                  let* pred_out_types = ProgUtils.pred_out_types qual_ident in

                  let* pred_ra_constr =
                    ProgUtils.pred_ra_constr_qual_ident loc qual_ident
                  in

                  let in_vars =
                    List.map pred_in_types ~f:(fun tp ->
                        {
                          Type.var_name = Ident.fresh loc "in";
                          var_loc = Expr.to_loc e;
                          var_type = tp |> Type.set_ghost false;
                          var_const = false;
                          var_ghost = false;
                          var_implicit = false;
                        })
                  in

                  let in_vars_exprs =
                    List.map in_vars ~f:(fun v -> Expr.from_var_decl v)
                  in
                  let in_vars_tuple = Expr.mk_tuple in_vars_exprs in

                  let actual_arg_in_exprs = List.take args (List.length pred_in_types) in
                  let actual_arg_out_exprs = List.drop args (List.length pred_in_types) in

                  let conjunct_idx = next_conjunct_idx () in
                  let* inv_fn_expr, env_actual_exprs =
                    get_or_generate_inv_function ~loc universal_quants conds
                      (Expr.mk_tuple actual_arg_in_exprs)
                      ~arg_expr:in_vars_tuple ~spec_source ~conjunct_idx
                  in

                  let inv_exprs =
                    List.mapi univ_vars_list ~f:(fun index var_decl ->
                        if Int.(List.length univ_vars_list = 1) then inv_fn_expr
                        else Expr.mk_tuple_lookup inv_fn_expr index)
                  in

                  (* exhale forall i, j :: { v(i,j) } pred(ins(i, j); outs(i, j))
                   *   ~~>
                   * forall i, j :: { v(i,j) }
                   *  outs[
                   *      i <- inv(f(i, j), i, j)#0,
                   *      j <- inv(f(i, j), i, j)#1
                   *  ] (var substitution)
                   *    =
                   *  outs(i, j) *)
                  let* forward_trigger_assertions =
                    let inv_fn_qi_opt =
                      match inv_fn_expr with
                      | App (Expr.Var inv_fn_qi, args, _) -> Some inv_fn_qi
                      | _ -> None
                    in

                    begin match inv_fn_qi_opt with
                    | None -> Rewriter.return []
                    | Some inv_fn_qi ->
                        let inv_expr =
                          Expr.mk_app ~loc
                            ~typ:
                              (Type.mk_prod loc
                                 (List.map univ_vars_list ~f:(fun var_decl ->
                                      var_decl.var_type)))
                            (Expr.Var inv_fn_qi)
                            (Expr.mk_tuple actual_arg_in_exprs :: env_actual_exprs)
                        in

                        (* i ~> inv(f(i, j), i, j)#0
                         * j ~> inv(f(i, j), i, j)#1*)
                        let renaming_map =
                          List.foldi univ_vars_list
                            ~init:(Map.empty (module QualIdent))
                            ~f:(fun index map var_decl ->
                              Map.set map
                                ~key:(QualIdent.from_ident var_decl.var_name)
                                ~data:
                                  (if Int.(List.length univ_vars_list = 1) then inv_expr
                                   else Expr.mk_tuple_lookup ~loc inv_expr index))
                        in

                        Rewriter.return
                          (List.map (List.concat universal_quants.triggers)
                             ~f:(fun trg_term ->
                               let new_trg_term =
                                 Expr.alpha_renaming trg_term renaming_map
                               in

                               Stmt.mk_assume_expr ~loc ~cmnt:"forward_trigger_assertion"
                                 (Expr.mk_binder ~trigs:universal_quants.triggers ~loc
                                    ~typ:Type.bool Forall univ_vars_list
                                    (Expr.mk_impl (Expr.mk_and conds)
                                       (Expr.mk_eq ~loc trg_term new_trg_term)))))
                    end
                  in

                  let alpha_renaming_map =
                    List.fold2_exn univ_vars_list inv_exprs
                      ~init:(Map.empty (module QualIdent))
                      ~f:(fun map var_decl expr ->
                        Map.set map
                          ~key:(QualIdent.from_ident var_decl.var_name)
                          ~data:expr)
                  in

                  let actual_arg_in_exprs_subst =
                    List.map actual_arg_in_exprs ~f:(fun e ->
                        Expr.alpha_renaming e alpha_renaming_map)
                  in
                  let actual_arg_in_exprs_subst_tuple =
                    Expr.mk_tuple actual_arg_in_exprs_subst
                  in
                  let actual_arg_out_exprs_subst =
                    List.map actual_arg_out_exprs ~f:(fun e ->
                        Expr.alpha_renaming e alpha_renaming_map)
                  in
                  let conds_subst =
                    List.map conds ~f:(fun e -> Expr.alpha_renaming e alpha_renaming_map)
                  in
                  let new_trigs =
                    List.map universal_quants.triggers ~f:(fun trgs ->
                        List.map trgs ~f:(fun trg ->
                            Expr.alpha_renaming trg alpha_renaming_map))
                  in

                  let havoc_stmt = Stmt.mk_havoc ~loc pred_heap2_qual_ident in

                  let assume_stmt =
                    let in_vars_eq_args =
                      Expr.mk_eq in_vars_tuple actual_arg_in_exprs_subst_tuple
                      (* List.map2_exn in_vars actual_arg_in_exprs_subst ~f:(fun var_decl arg ->
                           Expr.mk_eq (Expr.from_var_decl var_decl) arg
                         ) *)
                    in

                    let new_chunk =
                      mk_pred_new_chunk ~loc c.call_decl.call_decl_kind heap_elem_type
                        pred_ra_constr actual_arg_out_exprs_subst
                    in

                    Stmt.mk_assume_expr ~loc
                      ~cmnt:
                        ((match cmnt with None -> "" | Some cmnt -> cmnt)
                        ^ "\nexhale: "
                        ^ Stdlib.Format.asprintf "%a" Expr.pr
                            (Expr.mk_binder Forall univ_vars_list
                               (Expr.mk_impl (Expr.mk_and conds) expr)))
                      (match univ_vars_list with
                      | [] ->
                          Expr.mk_eq ~loc pred_heap2_expr
                            (Expr.mk_ite ~loc
                               (Expr.mk_and ~loc conds_subst)
                               (Expr.mk_mapupdate ~loc pred_heap_expr
                                  actual_arg_in_exprs_subst_tuple
                                  (Expr.mk_app ~loc ~typ:heap_elem_type
                                     (Expr.Var pred_heapchunk_operator)
                                     [
                                       Expr.mk_maplookup ~loc pred_heap_expr
                                         actual_arg_in_exprs_subst_tuple;
                                       new_chunk;
                                     ]))
                               pred_heap_expr)
                      | _ ->
                          Expr.mk_binder
                            ~trigs:
                              ([
                                 [ Expr.mk_maplookup ~loc pred_heap2_expr in_vars_tuple ];
                                 [ Expr.mk_maplookup ~loc pred_heap_expr in_vars_tuple ];
                               ]
                              @ new_trigs)
                            ~loc ~typ:Type.bool Forall in_vars
                            (Expr.mk_app ~loc ~typ:Type.bool Expr.Ite
                               [
                                 (* m1(a,b,c) && l == f1(a, b, c) *)
                                 Expr.mk_and ~loc (in_vars_eq_args :: conds_subst);
                                 (* pred$Heap2[l] == field.comp( field$Heap[l], f2(a, b, c) ) *)
                                 Expr.mk_eq ~loc
                                   (Expr.mk_maplookup ~loc pred_heap2_expr
                                      actual_arg_in_exprs_subst_tuple)
                                   (Expr.mk_app ~loc ~typ:heap_elem_type
                                      (Expr.Var pred_heapchunk_operator)
                                      [
                                        Expr.mk_maplookup ~loc pred_heap_expr
                                          in_vars_tuple;
                                        new_chunk;
                                      ]);
                                 (* pred$Heap2[l] == pred$Heap[l] *)
                                 Expr.mk_eq ~loc
                                   (Expr.mk_maplookup ~loc pred_heap2_expr in_vars_tuple)
                                   (Expr.mk_maplookup ~loc pred_heap_expr in_vars_tuple);
                               ]))
                  in

                  (* pred$Heap := pred$Heap2 *)
                  let eq_stmt =
                    Stmt.mk_assign ~loc
                      [ pred_heap_expr |> Expr.to_qual_ident ]
                      pred_heap2_expr
                  in

                  (* Logs.debug (fun m -> m "heapsExplicitTrnsl.trnsl_exhale_a0: Found pred/inv; loc=%s expr=%a; Length of spec_error: %i; errors=%a" 
                    (Loc.to_string_simple loc)
                    Expr.pr expr 
                    (List.length spec_error) 
                    (Util.Print.pr_list_nl Format.pp_print_string) (List.map spec_error ~f:(fun err -> err qual_ident  loc |> Error.to_string))
                  ); *)
                  let assert_heap_valid =
                    Stmt.mk_assert_expr ~loc
                      ~spec_error:
                        (spec_error
                        @ [
                            Stmt.mk_const_spec_error
                              ( Error.RelatedLoc,
                                Expr.to_loc e,
                                "This predicate may not hold" );
                          ])
                      (Expr.mk_app ~loc ~typ:Type.bool (Expr.Var pred_heap_valid_fn)
                         [ pred_heap_expr ])
                  in

                  (* let* injectivity_assertion =
                    generate_injectivity_assertions ~loc universal_quants conds
                      (Expr.mk_tuple actual_arg_in_exprs)
                  in *)
                  let stmts_list =
                    match univ_quants_list with
                    | [] -> []
                    | _ -> [ (* injectivity_assertion *) ]
                  in

                  let stmts_list =
                    stmts_list @ [ havoc_stmt; assume_stmt ] @ forward_trigger_assertions
                    @ [ eq_stmt; assert_heap_valid ]
                  in

                  let stmt = Stmt.mk_block_stmt ~loc stmts_list in

                  Rewriter.return stmt
              | _ -> Error.internal_error loc "expected a predicate definition")
          | _ ->
              (* Logs.debug(fun m -> m "TrnslInhale.trnsl_exhale_a0: unknown expr"); *)
              unsupported_expr_error expr)
end

let flatten_resource_blocks stmts =
  let rec transparent stmt =
    match stmt.stmt_desc with
    | Basic (VarDef _) -> false
    | Block { block_kind = Regular; block_body } -> List.for_all block_body ~f:transparent
    | Block _ -> false
    | _ -> true
  in
  let rec flatten pending acc =
    match pending with
    | [] -> List.rev acc
    | [] :: rest -> flatten rest acc
    | (stmt :: rest) :: remaining ->
        begin match stmt.stmt_desc with
        | Block { block_kind = Regular; block_body } when transparent stmt ->
            flatten (block_body :: rest :: remaining) acc
        | _ -> flatten (rest :: remaining) (stmt :: acc)
        end
  in
  flatten [ stmts ] []

let rec inherit_spec_name name stmt =
  let open Rewriter.Syntax in
  let+ stmt = Rewriter.Stmt.descend stmt ~f:(inherit_spec_name name) in
  match stmt.stmt_desc with
  | Basic (Spec (kind, spec)) when Option.is_none spec.spec_name ->
      { stmt with stmt_desc = Basic (Spec (kind, { spec with spec_name = Some name })) }
  | _ -> stmt

let rec rewrite_make_heaps_explicit (s : Stmt.t) : Stmt.t Rewriter.t =
  let open Rewriter.Syntax in
  match s.stmt_desc with
  | Stmt.Block block ->
      let* _ = Rewriter.enter_block block in
      let* block_body =
        translate_resource_sequence [] (flatten_resource_blocks block.block_body)
      in
      let+ () = Rewriter.exit_block in
      { s with stmt_desc = Block { block with block_body } }
  | Stmt.Basic basic_stmt ->
      begin match basic_stmt with
      | VarDef _ | Use _ | New _ | Assign _ | Bind _ | Havoc _ | Return _ | AUAction _
      | Fpu _ | Call _ | BasicStmtExt _ ->
          Rewriter.return s
      | Spec (spec_kind, spec) ->
          let* translated =
            match spec_kind with
            | Inhale ->
                let expr = spec.spec_form in

                let* stmt =
                  TrnslInhale.trnsl_inhale_expr ?cmnt:spec.spec_comment
                    ~spec_error:spec.spec_error ?spec_source:spec.spec_source
                    ~loc:s.stmt_loc expr
                in
                Rewriter.return stmt
            | Exhale ->
                let expr = spec.spec_form in

                let* stmt =
                  TrnslExhale.trnsl_exhale_expr ?cmnt:spec.spec_comment
                    ~spec_error:spec.spec_error ?spec_source:spec.spec_source
                    ~loc:s.stmt_loc expr
                in
                Rewriter.return stmt
            | Assume ->
                let expr = spec.spec_form in

                let* stmt =
                  TrnslInhale.trnsl_assume_expr ?cmnt:spec.spec_comment
                    ~spec_error:spec.spec_error ~loc:s.stmt_loc expr
                in
                Rewriter.return stmt
            | Assert ->
                let* is_e_pure = ProgUtils.is_expr_pure spec.spec_form in
                if is_e_pure then
                  (* let assume_stmt = Stmt.mk_assume_expr ~loc:s.stmt_loc spec.spec_form in *)
                  (* Rewriter.return (Stmt.mk_block_stmt ~loc:s.stmt_loc [s; assume_stmt]) *)
                  (* The corresponding assume stmt is being added in backend/checker.ml *)
                  Rewriter.return s
                else
                  let loc = Stmt.to_loc s in
                  let nondet_var =
                    Type.
                      {
                        var_name = Ident.fresh loc "$nondet";
                        var_loc = loc;
                        var_type = Type.bool;
                        var_const = true;
                        var_ghost = false;
                        var_implicit = false;
                      }
                  in

                  let (nondet_var_def : Module.symbol) =
                    VarDef
                      { var_decl = nondet_var; var_init = None; var_is_free = NotFree }
                  in

                  let* _ = Rewriter.introduce_symbol nondet_var_def in

                  let* exhale_stmt =
                    TrnslExhale.trnsl_exhale_expr
                      ?cmnt:
                        (Some (Option.value ~default:(Stmt.to_string s) spec.spec_comment))
                      ~spec_error:spec.spec_error ~loc spec.spec_form
                  in
                  let assume_false_stmt = Stmt.mk_assume_expr ~loc (Expr.mk_bool false) in

                  let cond_stmt =
                    Stmt.Cond
                      {
                        cond_test = Some (Expr.from_var_decl nondet_var);
                        cond_then =
                          Stmt.mk_block_stmt ~loc [ exhale_stmt; assume_false_stmt ];
                        cond_else = Stmt.mk_block_stmt ~loc [];
                        cond_if_assumes_false = true;
                      }
                  in

                  let nondet_false_stmt =
                    Stmt.mk_assume_expr ~loc (Expr.mk_not (Expr.from_var_decl nondet_var))
                  in

                  let* assume_stmt =
                    TrnslInhale.trnsl_assume_expr ?cmnt:spec.spec_comment
                      ~spec_error:spec.spec_error ~loc:s.stmt_loc spec.spec_form
                  in

                  let new_stmt =
                    Stmt.mk_block_stmt ~loc
                      [
                        Stmt.{ stmt_desc = cond_stmt; stmt_loc = loc };
                        nondet_false_stmt;
                        assume_stmt;
                      ]
                  in

                  Rewriter.return new_stmt
          in
          begin match spec.spec_name with
          | Some name -> inherit_spec_name name translated
          | None -> Rewriter.return translated
          end
      | FieldRead fr_desc ->
          let* lhs_var = Rewriter.find_and_reify fr_desc.field_read_lhs in
          let lhs_var =
            match lhs_var with
            | VarDef var_symbol -> var_symbol.var_decl
            | _ -> Error.type_error s.stmt_loc "Expected a variable definition."
          in

          let field_name = fr_desc.field_read_field in
          let field_loc = fr_desc.field_read_field |> QualIdent.to_loc in
          let* field_symbol = Rewriter.find_and_reify field_name in

          let field_symbol =
            match field_symbol with
            | FieldDef field_symbol -> field_symbol
            | _ -> Error.type_error field_loc "Expected a field definition."
          in

          let field_ra = ProgUtils.field_get_ra_qual_iden field_symbol in
          let field_read_ref_loc = fr_desc.field_read_ref |> Expr.to_loc in
          let loc = Loc.merge field_loc field_read_ref_loc in

          let* orig_ra_name, ra_def, _ = Rewriter.find field_ra in

          if QualIdent.(orig_ra_name = Predefs.lib_frac_mod_qual_ident) then
            let field_ra_type = ProgUtils.get_ra_rep_type field_ra in

            let field_heap_name = field_heap_name field_name in
            let field_heap_expr =
              Expr.mk_var
                ~typ:(Type.mk_map s.stmt_loc Type.ref field_ra_type)
                (QualIdent.from_ident field_heap_name)
            in

            let field_val_destr =
              QualIdent.append field_ra Predefs.lib_frac_chunk_destr1_ident
            in
            let field_frac_destr =
              QualIdent.append field_ra Predefs.lib_frac_chunk_destr2_ident
            in

            let assert_expr =
              Expr.mk_app ~loc:s.stmt_loc ~typ:Type.bool Expr.Gt
                [
                  Expr.mk_app ~typ:Type.real (DataDestr field_frac_destr)
                    [ Expr.mk_maplookup field_heap_expr fr_desc.field_read_ref ];
                  Expr.mk_real 0.;
                ]
            in

            let assert_stmt =
              let error =
                ( Error.Verification,
                  loc,
                  "Could not assert sufficient permissions to access this field" )
              in
              Stmt.mk_assert_expr ~loc:s.stmt_loc
                ~spec_error:[ Stmt.mk_const_spec_error error ]
                assert_expr
            in

            let assign_stmt =
              Stmt.mk_assign ~loc:s.stmt_loc ~is_init:fr_desc.field_read_is_init
                [ fr_desc.field_read_lhs ]
                (Expr.mk_app ~typ:lhs_var.var_type (DataDestr field_val_destr)
                   [ Expr.mk_maplookup field_heap_expr fr_desc.field_read_ref ])
            in

            Rewriter.return
              (Stmt.mk_block_stmt ~loc:s.stmt_loc [ assert_stmt; assign_stmt ])
          else Error.type_error s.stmt_loc "Expected a FracRA type."
      | FieldWrite
          {
            field_write_ref = ref_expr;
            field_write_field = field_name;
            field_write_val = assign_rhs;
          } ->
          let* field_symbol = Rewriter.find_and_reify field_name in

          let field_symbol =
            match field_symbol with
            | FieldDef field_symbol -> field_symbol
            | _ -> Error.type_error s.stmt_loc "Expected a field definition."
          in

          let field_ra = ProgUtils.field_get_ra_qual_iden field_symbol in

          let* orig_ra_name, ra_def, _ = Rewriter.find field_ra in

          if QualIdent.(orig_ra_name = Predefs.lib_frac_mod_qual_ident) then
            let field_ra_type = ProgUtils.get_ra_rep_type field_ra in

            let field_heap_name = field_heap_name field_name in
            let field_heap_expr =
              Expr.mk_var
                ~typ:(Type.mk_map s.stmt_loc Type.ref field_ra_type)
                (QualIdent.from_ident field_heap_name)
            in

            let field_frac_destr =
              QualIdent.append field_ra Predefs.lib_frac_chunk_destr2_ident
            in
            let field_frac_constr =
              QualIdent.append field_ra Predefs.lib_frac_chunk_constr_ident
            in

            let assert_expr =
              Expr.mk_app ~loc:s.stmt_loc ~typ:Type.bool Expr.Geq
                [
                  Expr.mk_app ~typ:Type.real (DataDestr field_frac_destr)
                    [ Expr.mk_maplookup field_heap_expr ref_expr ];
                  Expr.mk_real 1.;
                ]
            in

            let new_val =
              Expr.mk_app ~typ:field_ra_type (DataConstr field_frac_constr)
                [ assign_rhs; Expr.mk_real 1. ]
            in

            let assert_stmt =
              let error =
                ( Error.Verification,
                  s.stmt_loc,
                  "Could not assert sufficient permissions to assign this field" )
              in
              Stmt.mk_assert_expr ~loc:s.stmt_loc
                ~spec_error:[ Stmt.mk_const_spec_error error ]
                assert_expr
            in
            let assign_stmt =
              Stmt.mk_assign ~loc:s.stmt_loc
                [ field_heap_expr |> Expr.to_qual_ident ]
                (Expr.mk_app
                   ~typ:(Type.mk_map s.stmt_loc Type.ref field_ra_type)
                   MapUpdate
                   [ field_heap_expr; ref_expr; new_val ])
            in

            Rewriter.return
              (Stmt.mk_block_stmt ~loc:s.stmt_loc [ assert_stmt; assign_stmt ])
          else Error.type_error s.stmt_loc "Expected a FracRA type."
      end
  | _ ->
      let* s = Rewriter.Stmt.descend s ~f:rewrite_make_heaps_explicit in

      Rewriter.return s

and translate_resource_sequence acc = function
  | ({ stmt_desc = Basic (Spec ((Exhale as kind), pre)); _ } as first)
    :: ({ stmt_desc = Basic (Spec (Inhale, post)); _ } as second)
    :: rest
  | ({ stmt_desc = Basic (Spec ((Inhale as kind), pre)); _ } as first)
    :: ({ stmt_desc = Basic (Spec (Exhale, post)); _ } as second)
    :: rest ->
      let open Rewriter.Syntax in
      (* Prefer an existing forward fusion when the pairs overlap. *)
      let* forward =
        match (kind, rest) with
        | Inhale, ({ stmt_desc = Basic (Spec (Inhale, third)); _ } as next) :: tail ->
            let+ fused = ScalarResource.fuse ~reverse:false second next post third in
            Option.map fused ~f:(fun stmt -> (stmt, tail))
        | _ -> Rewriter.return None
      in
      begin match forward with
      | Some (stmt, tail) ->
          let* first = rewrite_make_heaps_explicit first in
          let* stmt = rewrite_make_heaps_explicit stmt in
          translate_resource_sequence (stmt :: first :: acc) tail
      | None ->
          let* fused =
            ScalarResource.fuse
              ~reverse:(match kind with Inhale -> true | _ -> false)
              first second pre post
          in
          begin match fused with
          | Some stmt ->
              let* stmt = rewrite_make_heaps_explicit stmt in
              translate_resource_sequence (stmt :: acc) rest
          | None ->
              let* first = rewrite_make_heaps_explicit first in
              translate_resource_sequence (first :: acc) (second :: rest)
          end
      end
  | stmt :: rest ->
      let open Rewriter.Syntax in
      let* stmt = rewrite_make_heaps_explicit stmt in
      translate_resource_sequence (stmt :: acc) rest
  | [] -> Rewriter.return (List.rev acc)
