%{

open Ext.DecreasesExtInstance

%}

%token DECREASES

%%

%public contract_ext:
| DECREASES; es = separated_nonempty_list(COMMA, expr) {
  Decreases (List.map Stmt.mk_spec es)
}
