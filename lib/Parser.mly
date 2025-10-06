%{
    open Core
    open Gpl
    open BaseLogic
%}


%token <int> INT
%token <string> ID
%token MATCHSTICK
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
%token TCAM
%token LPM
%token CAM

%left COMPOSE SEMICOLON

%left TIMES

/* AND binds tighter than or */
%nonassoc OR 
%nonassoc AND


%start <(unit, t) Either.t list> matchstix
%%

matchstix :
| ms = list(tmatchstick); EOF { ms }

tmatchstick : m = terminated(matchstick, DOT) { m }

matchstick :
| hardware; table = ID; 
    keys = delimited(LPAREN, typed_vars, RPAREN);
    COLON;
    delimited(LBRACE, typed_vars, RBRACE);
    delimited(LSQUARE, nonempty_list(action), RSQUARE);
    clause = option(preceded(MATCHSTICK, algebra));
    {   
        let defined = Symbol.make table (List.map ~f:snd keys) (-1) in
        match clause with 
        | None -> 
            Base.Either.First ()
        | Some clause -> 
            Base.Either.Second { defined; definition = clause} 
}

hardware :
| LPM { } 
| TCAM { }
| CAM { }

typed_vars :
| xs = separated_nonempty_list(COMMA, typed_var)
  { xs }

typed_var :
| x = ID; COLON; w = INT 
    { (x, w) }

algebra :
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
| c = algebra; COMPOSE; RENAME; old_name = action; TO new_name = action
    { Clause.(c |>> OutTfx.Rename (old_name, new_name))  }

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