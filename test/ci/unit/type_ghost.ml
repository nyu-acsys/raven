open Raven

let () =
  let plain = Ast.Type.mk_app ~loc:Util.Loc.dummy Bool [] in
  let ghost = Ast.Type.mk_app ~loc:Util.Loc.dummy ~ghost:true Bool [] in
  assert (not (Ast.Type.is_ghost plain));
  assert (Ast.Type.is_ghost ghost)
