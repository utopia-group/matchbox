%{
    open Core
    open Gpl
    open Semantics
    open BaseLogic
%}


%token <int> INT
%token <string> ID
%token <string> BV
%token MATCHSTICK
%token ARROW
%token FDARROW
%token SEMICOLON
%token COLON
%token TIMES
%token ELSE
%token COMPOSE
%token KEY
%token DATA
%token ACTION
%token TO
%token DOT
%token ASSIGN
%token EOF
%token BAR
%token LSQUARE
%token RSQUARE
%token LPAREN
%token RPAREN
%token LBRACE
%token RBRACE
%token DELETE
%token IGNORE
%token EQ
%token AND
%token OR
%token IMP
%token TRUE
%token FALSE
%token FILTER
%token COMMA
%token RENAME
%token ADD
%token TCAM
%token LPM
%token CAM
%token LIMIT
%token ROWS
%token ASSUME
%token FORALL
%token GHOST

%left COMPOSE SEMICOLON

%left TIMES

/* AND binds tighter than or */
%nonassoc OR 
%nonassoc AND


%start <ParserContext.t> matchstix
%%

matchstix :
| ms = list(tmatchstick); EOF { ParserContext.concat ms }

tmatchstick : m = terminated(matchstick, DOT) { m }

matchstick :
| LIMIT; table = ID; TO; n = INT; option(ROWS);
    { ParserContext.(empty |> add_resource_limit table n) }
| ASSUME; table = ID; COLON; LBRACE; source = typed_vars; BAR; phi = formula; RBRACE; FDARROW; target = delimited(LBRACE, typed_vars, RBRACE);
    {   let open ParserContext in
        let typ = FDBaseChecker.DepFunDep.{refine = phi; source; target} in
        add_assumption table typ empty
    }
| ghost = option(GHOST); hw = hardware; table = ID; 
    keys = delimited(LPAREN, typed_vars, RPAREN);
    COLON;
    data = delimited(LBRACE, typed_vars, RBRACE);
    action_list = delimited(LSQUARE, nonempty_list(action), RSQUARE);
    clause = option(preceded(MATCHSTICK, algebra));
    {   let open ParserContext in
        let defined = Symbol.make table [] (-1) in
        let actions = Type.ActionSet.of_list action_list in
        let typ = Type.{is_ghost = Option.is_some ghost; hw; keys; actions; data} in
        empty
        |> add_type table typ
        |> opt_add_def defined (complete_clause clause table typ)
        |> update_stats clause
    }

hardware :
| LPM { Hardware.LPM } 
| TCAM { Hardware.TCAM }
| CAM { Hardware.CAM }

typed_vars :
| xs = separated_list(COMMA, typed_var)
  { String.Map.of_alist_exn xs }

typed_var :
| x = ID; COLON; w = INT 
    { (x, w) }

decl :
| x = ID; ASSIGN; f = ID; LPAREN; w = INT; RPAREN
    { (x, f, w) }

algebra :
| BAR; keys = separated_list(COMMA, BV); ARROW; action = ID; LPAREN; data = separated_list(COMMA, BV); RPAREN; BAR
    { ParserContext.create_table keys action data }
| FORALL; decls = separated_nonempty_list(COMMA, decl); COLON; BAR; keys = separated_nonempty_list(COMMA, ID); ARROW; action = ID; LPAREN; data = separated_list(COMMA, ID); RPAREN; BAR
    { ParserContext.bulk_create_table decls keys action data }
| name = ID 
    { Clause.id (Symbol.make name [] (-1)) }
| c1 = algebra; TIMES; c2 = algebra 
    { Clause.(c1 * c2) } 
| c1 = algebra; COMPOSE; c2 = algebra
    { Clause.(c1 >>> c2) }
| LPAREN; c = algebra; RPAREN
    { c }
| c = algebra; COMPOSE; KEY; x = var; ASSIGN; e = expr 
    { Clause.(MatchTfx.SetTo (x, e) <<| c) }
| c = algebra; COMPOSE; DELETE; KEY; x = var
    { Clause.(MatchTfx.Del (x) <<| c) }
| c = algebra; COMPOSE; IGNORE; KEY; x = var
    { Clause.(MatchTfx.WildCard x <<| c)  }
| c = algebra; COMPOSE; FILTER; b = formula 
    { Clause.(MatchTfx.Filter (b) <<| c) }
| c = algebra; COMPOSE; DATA; x = var; ASSIGN; e = expr
    { Clause.(c |>> OutTfx.SetTo(x, e))}
| c = algebra; COMPOSE; DELETE; DATA; x = var
    { Clause.(c |>> OutTfx.Del (x) )}
| c = algebra; COMPOSE; RENAME; old_name = action; TO; new_name = action
    { Clause.(c |>> OutTfx.Rename (old_name, new_name))  }
| c = algebra; COMPOSE; ADD; name = action
    { Clause.(c |>> OutTfx.Add name)  }

var : 
| x = ID; 
    { Var.make x (-1) }

expr :
| w = INT; v = delimited(LSQUARE, INT, RSQUARE)
    { Expr.bvi v w }
| x = var; 
    { Expr.var x }
| LPAREN; e = expr; RPAREN
    { e }

formula :
| TRUE 
    { BExpr.true_ }
| FALSE 
    { BExpr.false_ }
| e1 = expr; EQ; e2 = expr
    { BExpr.(e1 == e2) }
| phi = formula; AND; psi = formula 
    { BExpr.and_ phi psi }
| phi = formula; OR; psi = formula
    { BExpr.ors [phi; psi] }
| LPAREN; phi = formula; RPAREN 
    { phi }

action :
| name = ID 
    { Semantics.MagmaAction.make name }
| a1 = action; SEMICOLON; a2 = action 
    { Semantics.MagmaAction.(a1 @ a2) }
| LPAREN; a = action; RPAREN
    { a }