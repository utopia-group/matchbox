(* Named GPL --- We are going to produce a GPL with Names *)
open Core

module NamedTablePipe = struct
  open Primitives 
  type t = 
    | Active of Active.t
    | Table of string
    [@@deriving eq]

  let assert_ phi = Active (Active.assert_ phi)
  let assume phi = Active (Active.assume phi)

  let to_smtlib = function 
  | Active a -> Active.to_smtlib a
  | Table name -> 
    Printf.sprintf "%s.apply()" name

end

module NGPL = Cmd.Make (NamedTablePipe)

module Declarations = struct
  type t = 
    | Table of Primitives.Table.t
    | CodeBlock of { name : string; body : NGPL.t}
    | Main of string list
    | Seq of t * t

  let well_formed () = failwith "TODO"
  let interp () = failwith "TODO"
  let inline  () = failwith "TODO"
end
