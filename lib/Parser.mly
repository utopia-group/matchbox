%{
    open Core
    open Gpl
    open Semantics
    open BaseLogic
%}


%token <int> INT
%token <string> ID
%token <string> BP
%token MATCHSTICK
%token ARROW
%token FDARROW
%token SEMICOLON
%token COLON
%token TIMES
%token ELSE
%token COMPOSE
%token OVERRIDE
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
%token BAND
%token OR
%token IMP
%token TRUE
%token FALSE
%token CUBE_FILTER
%token FILTER
%token COMMA
%token RENAME
%token TCAM
%token LPM
%token CAM
// %token LIMIT
%token ROWS
%token ASSUME
%token ASSERT
%token ACTIONVAR
%token FORALL
%token PRIVATE

%left COMPOSE SEMICOLON

%left TIMES

/* AND binds tighter than OR */
%left OR
%left AND
%left BAND

%start <ParserContext.t> matchstix
%%

matchstix :
| ms = list(tmatchstick); EOF { ParserContext.concat ms }

tmatchstick : m = terminated(matchstick, DOT) { m }

matchstick :
// | LIMIT; table = ID; TO; n = INT; option(ROWS);
//     { ParserContext.(empty |> add_resource_limit table n) }
| ASSUME; table = ID; COLON;
  LBRACE; source = typed_vars; BAR; phi = formula; RBRACE; FDARROW;
  target = delimited(LBRACE, typed_vars, RBRACE);
    {   let open ParserContext in
        let typ = FDBaseChecker.DepFunDep.{refine = phi; source; target} in
        {empty with
         gfds = Map.add_multi empty.gfds ~key:table ~data:typ;
         stats =
         {empty.stats with
          num_fds = empty.stats.num_fds + 1;
          size_fds = empty.stats.size_fds + BExpr.size phi
         }
        }
    }
| ASSERT; table = ID; COLON;
  LBRACE; source = typed_vars; BAR; phi = formula; RBRACE; FDARROW;
  target = delimited(LBRACE, typed_vars, RBRACE);
    {   let open ParserContext in
        let typ = FDBaseChecker.DepFunDep.{refine = phi; source; target} in
        add_assertion table typ empty
    }
| ASSERT; table = ID; COLON;
  LBRACE; pre = formula; RBRACE; IMP;
  LBRACE; g = post_guarantee; RBRACE;
    {   let open ParserContext in
        add_property Property.{table; pre; post = [g]} empty
    }
| private_ = option(PRIVATE); hw = hardware; table = ID;
  keys = delimited(LPAREN, typed_vars, RPAREN);
  COLON;
  data = delimited(LBRACE, typed_vars, RBRACE);
  action_list = delimited(LSQUARE, nonempty_list(action), RSQUARE);
  clause = option(preceded(MATCHSTICK, algebra));
    {   let open ParserContext in
        let defined = Symbol.make table [] (-1) in
        let actions = Type.ActionSet.of_list action_list in
        let typ = Type.{is_private = Option.is_some private_; hw; keys; actions; data} in
        empty
        |> add_vars keys
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

row :
| BAR;
    keys = separated_list(COMMA, BP); ARROW;
    action = ID; LPAREN; data = separated_list(COMMA, BP); RPAREN;
  BAR
    { (keys, action, data) }

mapping :
| key = ID; ARROW; w = INT; v = delimited(LSQUARE, INT, RSQUARE)
    { (key, w, v) }

algebra :
| rows = separated_nonempty_list(COMMA, row)
    { ParserContext.create_table rows }
| FORALL; decls = separated_nonempty_list(COMMA, decl); COLON;
    BAR;
      keys = separated_nonempty_list(COMMA, ID); ARROW;
      action = ID; LPAREN; data = separated_list(COMMA, ID); RPAREN;
    BAR
    { ParserContext.bulk_create_table decls keys action data }
| name = ID 
    { Clause.id (Symbol.make name [] (-1)) }
| c1 = algebra; TIMES; c2 = algebra 
    { Clause.(c1 * c2) } 
| c1 = algebra; COMPOSE; c2 = algebra
    { Clause.(c1 >>> c2) }
| c1 = algebra; OVERRIDE; c2 = algebra
    { Clause.override c1 c2 }
| LPAREN; c = algebra; RPAREN
    { c }
| c = algebra; COMPOSE; KEY; x = var; ASSIGN; e = expr 
    { Clause.(MatchTfx.SetTo (x, e) <<| c) }
| c = algebra; COMPOSE; DELETE; KEY; x = var
    { Clause.(MatchTfx.Del x <<| c) }
| c = algebra; COMPOSE; IGNORE; KEY; x = var
    { Clause.(MatchTfx.WildCard x <<| c)  }
| c = algebra; COMPOSE; CUBE_FILTER;
  mappings = delimited(LBRACE, separated_list(COMMA, mapping), RBRACE)
    {   mappings
        |> List.map ~f:(fun (k, w, i) -> (k, Match.Exact (Bit.Vector.of_int ~width:w i)))
        |> Map.of_alist_exn (module String)
        |> MatchTfx.CubeFilter
        |> Fn.flip Clause.(<<|) c }
| c = algebra; COMPOSE; FILTER; b = formula 
    { Clause.(MatchTfx.Filter b <<| c) }
| c = algebra; COMPOSE; DATA; x = var; ASSIGN; e = expr
    { Clause.(c |>> OutTfx.SetTo(x, e))}
| c = algebra; COMPOSE; DELETE; DATA; x = var
    { Clause.(c |>> OutTfx.Del x )}
| c = algebra; COMPOSE; RENAME; old_name = action; TO; new_name = action
    { Clause.(c |>> OutTfx.Rename (old_name, new_name))  }

var : 
| x = ID; 
    { Var.make x (-1) }

expr :
| w = INT; v = delimited(LSQUARE, INT, RSQUARE)
    { Expr.bvi v w }
| x = var; 
    { Expr.var x }
| e1 = expr; BAND; e2 = expr 
    { Expr.BinOp (BAnd, e1, e2) }
| e1 = expr; BAR; e2 = expr 
    { Expr.BinOp (BOr, e1, e2) }
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
    { BExpr.and_ psi phi }
| phi = formula; OR; psi = formula
    { BExpr.ors [phi; psi] }
| LPAREN; phi = formula; RPAREN
    { phi }

post_guarantee :
| ACTIONVAR; EQ; a = action
    { Property.ActionEq a }
| phi = formula
    { Property.Pred phi }

action :
| name = ID 
    { MagmaAction.make name }
| a1 = action; SEMICOLON; a2 = action 
    { MagmaAction.(a1 @ a2) }
| LPAREN; a = action; RPAREN
    { a }