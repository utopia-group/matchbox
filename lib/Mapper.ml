

type location = String.t * int

type t = {
  abs_config : Config.t;
  tgt_ config : Config.t;
  spec : DSLv2.t;
}

let gen_rules (ctx :t) (row : MatchAction.t) (position : t) =
  let ctx = insert_abs ctx position in 
  let phi, provenance = symb_ex ctx insert in 
  