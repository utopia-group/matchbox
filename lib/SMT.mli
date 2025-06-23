type sort 
val s_to_string : sort -> string

type expr
val e_to_string : expr -> string

type command
val c_to_string : command -> string

type tactical
val t_to_string : tactical -> string

type program = command list
val p_to_string : program -> string

val var : string -> expr

val bv_sort : int -> sort
val bv : int -> int -> expr
val bv' : Bit.Vector.t -> expr

val int_sort : sort
val int : int -> expr

val real_sort : sort
val real : float -> expr

val check_sat : command
val check_sat_using : tactical -> command
val get_model : command
val declare_const : string -> sort -> command
val get_value : string list -> command
val assert_ : expr -> command
val minimize : expr -> command
val maximize : expr -> command
val exit : command

val tactic : string -> tactical
val then_ : tactical list -> tactical
val par_then : tactical list -> tactical
val par_or : tactical list -> tactical
val or_else : tactical list -> tactical
val repeat : tactical -> tactical
val repeat' : tactical -> int -> tactical
val try_for : tactical -> float -> tactical
val using_params : tactical -> (string * expr) list -> tactical

val symb : string -> expr list -> expr

val true_ : expr
val false_ : expr
val and_ : expr list -> expr
val iff : expr list -> expr
val or_ : expr list -> expr
val implies : expr list -> expr
val forall : (string * sort) list -> expr -> expr
val exists : (string * sort) list -> expr -> expr
val not : expr -> expr
val ite : expr -> expr -> expr -> expr

val ( + ) : expr list -> expr
val ( - ) : expr list -> expr
val ( * ) : expr list -> expr
val ( mod ) : expr list -> expr
val div : expr list -> expr
val ( = ) : expr list -> expr
val ( < ) : expr list -> expr
val ( > ) : expr list -> expr
val ( <= ) : expr list -> expr
val ( >= ) : expr list -> expr
val distinct : expr list -> expr
val modeq : expr -> expr -> expr -> expr

val int2bv : int -> expr -> expr

val bvadd : expr list -> expr
val bvmul : expr list -> expr
val bvsub : expr list -> expr

val concat : expr list -> expr
val extract : hi:int -> lo:int -> expr list -> expr

val bvand : expr list -> expr 
val bvor : expr list -> expr

val bvult : expr list -> expr
val bvule : expr list -> expr
val bvugt : expr list -> expr
val bvuge : expr list -> expr
val bvsle : expr list -> expr
val bvslt : expr list -> expr
val bvsgt : expr list -> expr
val bvsge : expr list -> expr

module Model : sig
    type 'a t = 'a Core.String.Map.t 
    val parse : string -> string t 
    val map : 'a t -> f:('a -> 'b) -> 'b t
    val find_exn : 'a t -> string -> 'a
    val find : 'a t -> string -> 'a option
end 

type response 

val run : Runner.t -> program -> response
val check : response -> string Model.t option

