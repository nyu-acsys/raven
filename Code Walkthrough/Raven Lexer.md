/lib/frontend/lexer.mll
Consists of list of recognized keywords.

Some notable things:
- The lexer differentiates between identifiers which start with a lowercase char (`ident`) and identifiers which start with an uppercase char (`mod_ident`). This distinction is made here to enforce the naming convention that types and modules will be named with a capitalized name, whereas methods, functions, variables will be named with an uncapitalized name.
  
  Note that after the first letter, upper and lowercase characters can be freely mixed in both idents.

[[Raven Questions]]: should module names also allow like `Lock#1` input from users? Right now `mod_ident` doesn't.

- Comments are C-style `/* */` 
- `{!` and `!}` is used to denote ghost blocks.
- `{|` and `|}` denote sets.
- `[|` and `\]` denote...what exactly? [[Raven Questions]]