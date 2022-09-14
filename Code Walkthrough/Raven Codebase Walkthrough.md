## [[Raven Codebase Walkthrough]]
[[Raven]]


### Layout:
- bin/raven.ml: Entry-point.
- [[Raven AST|lib/ast/ast.ml]]: Defines Abstract Syntax Tree.
- lib/config: stores version and other config stuff. Currently mostly empty.
- lib/frontend:
	- [[Raven Lexer|lexer.mll]]
	- [[Raven Parser|parser.mly]]
	- [[Raven Resolve Namespaces|resolve_namespaces.ml]]
	- [[Raven Type Checker|type_checker.ml]]
- lib/util:
	- error.ml
	- loc.ml
	- print.ml

### Overview
1. bin/raven.ml is the entry point. Raven accepts a source code files as a cmd argument. 
2. It then calls [[Raven Lexer]] to generate a stream of tokens. 
3. This stream is then parsed by [[Raven Parser]] to generate an AST.
   
   [[Raven Questions]] Implement rewriting at this step to ensure every expression is pure etc?
   
4. At this stage, the AST is very barebones (ie many data fields have not been populated yet). We make an initial pass over the AST by calling `Resolve_namespaces.start_disambiguate`. This does a few things:
	- Rewrite variable names etc to make every identifier globally unique. This allows us to not worry about scopes for variable names. This is done by keeping a stack of maps which remember the original name in input file and new name.
	  %% #RavenToDos, [[Raven Questions]] : Store this mapping for later? Will need for debugging etc purposes perhaps? Also, not clear how to deal with rep types vs module name overloading. I think currently just treating every usage as rep type.%%
	  
	- Go over every function and method to collect metadata for each object, things like local variables for callables, and members for modules etc.
	  
	- Replacing module rep types with fully quantified types.
	- Making sure each callable and constructor is called with right number of arguments
	  %% #RavenToDos : Check that this is actually being done, and that it is being done properly.%%
	
	- Potentially also expand import directives here? #RavenToDos, [[Raven Questions]]

5. Call a basic type checker which ensures all types work, operations are being done on objects of the right types etc.
   Currently very loose with `Any` types (verify this). Need to make it strict.
