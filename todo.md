1. ghost fields
1. bind existentials using assert , or `:|`?
1. How to tie single-node.rav to Resource_algebra.rav
1. Process implicit callable args appropriately.
1. Add spawn/join functions. Add process identifier types, etc.
1. Do obligations checks, in terms of type checking for now.


Questions:
2. Would it be better for Own expr to take three args instead of two? Presently difficult to distinguish an `x.f` expr from `x` expr.
3. What is the purpose of Stmt.spec.spec_error? The parser sets them all to None initially.

