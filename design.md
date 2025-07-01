# Rust Verification in Raven

# Overview
Raven-Rust (r^2) is a verification algorithm and tool, allowing for the first time annotated,
concurrent Rust code to be verified using custom resource algebra and modules.

# Invoking Raven
```
raven file.rs
# OR
cargo raven # (run Raven on whole Rust crate)
```
This way of invoking raven will either verify `file.rs` (in the first case) by translating it to
`compiled-file.rav`, including `file.rav` if it exists, and then verifying `compiled-file.rav`, or it will
verify the crate at the current subdirectory (in the second case), placing the results in the `target/` directory.

# Translation Process
Translation happens in multiple steps: parsing Rust files, parsing Raven files, and compiling Rust files to raven files.

1. The Rust libraries included by `file.rs` (in the first case) or included in the crate (in the second case) are located

2. Then, each is parsed, and converted to a raven module.

3. Finally, all of these modules, along with their `rav` counterparts, are merged into a single module and verified.

## Translation of the Rust Files
then, the following steps are taken:

### Translation of Structs
1. First, for each struct `Struct` annotated with
`#[rr::refined_by(("x1", "x2", .., "xn") : ("Type1" * "Type2" * ... * "Typen"))]`,
the type is added as a case `isStruct()` to `RustValue`, and a predicate
`isTypedByStruct` is added. The types `Int`, `Bool`, `Array`, `RawPointer`,
and `MaybeUninit` are available by default.

2. Second, the `#[rr::exists("x" : "Type")]` and `#[rr::invariant("P")]` clauses are then included in the relevant `isTypedByStruct` definition.

3. Finally, for each struct `Struct`, the type ``

### Translation of Functions
1. Third, for each function, `#[rr::params("x1" : "Type", ..., "xn" : "Type")]` along with
   `#[rr::args(SHAPE)]` are parsed, where SHAPE is a list of tuples of variables from `x1` through `xn`,
   each tuple representing some struct.
2. Then, the function's arguments and return types are parsed into the arguments and `returns` clause, respectively, of the Raven function.
3. The function's `#[rr::exists("x" : "Type")]` clauses are attached to the function as `implicit ghost` variables.
4. Then, the function's `#[rr::requires(P)]` and `#[rr::ensures(Q)]` clauses are attached to the function.
5. Each intermediate variable of the function `intermediate_i` is translated into the variable `ℓintermediate_i`.
6. Each mid-level intermediate instruction is translated to a Raven method call.
7. Finally, with the help of annotations, there will be method calls that will manipulate the ghost state.

