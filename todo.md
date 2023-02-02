1. ghost fields
2. import (qualIdents)
3. bind existentials using assert , or `:|`?
4. Do we need Rep types any more?
5. How to tie single-node.rav to Resource_algebra.rav
6. Add MemImport support in parser
7. Add support for TypeExpressions with qualified idents in parser.
8. Figure out where to use Type.join and where Type.meet in process_expr
9. Process implicit callable args appropriately.
10. Add spawn/join functions. Add process identifier types, etc.
11. Do obligations checks, in terms of type checking for now.
12. Treat types and modules as the same (for instance Modules can accept types or modules as args)


Questions:
1. What type to assign to callable expressions which return multiple things?
2. Would it be better for Own expr to take three args instead of two? Presently difficult to distinguish an `x.f` expr from `x` expr.
3. What is the purpose of Stmt.spec.spec_error? The parser sets them all to None initially.
4. What exactly to do with Data types? How do their variant_decls need to be added to the Typing_env? Need to sketch this out.

Archive:
1. Module.import_directive can be `ModImport of type_expr` or `MemImport of qual_ident`. MemImport is not used in the parser. What is it for?
Ans: To allow for importing modules and import specific members from modules respectively.