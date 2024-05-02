Type-checking:
  - Ensure that return variables are not allowed in pre-conditions
  - Check that openAU, commitAU having right number of arguments
  - Check that assertion expressions having the right format -- conditionals in ternary expr being pure, etc
  - Ensure that return variables of functions are not used in the function body
  - Ensure that predicates don't have implicit ghost args

- Implement mask computation to check interface <-> module compatibility
- Improve expression matching algorithm
- Revamp witness computation code
- Extend module system to allow parametrised modules as return types / parameters
