open Lattice
open Language.Ast
open Apron
open Query

(* Signature of VALUE Abstract Domain *)
module type VALUE = sig
  include LATTICE
  val top : var list -> t
  val bot : var list -> t
  (* Forward Over-approximating assignment*)
  val fo_assign : t -> ichan ->  ochan -> aExp -> aExp -> t * ichan *  ochan
  val filter : t ->  ichan ->  ochan -> bExp -> t * ichan *  ochan
  (* Backward Over-approximating assignment*)
  val bo_assign : t -> ichan ->  ochan -> aExp -> aExp -> t * ichan *  ochan
  val print : Format.formatter -> t -> unit
  (*val bo_assign : t -> aExp -> aExp -> t 
    val fu_assign: t -> t -> t
    val bo_assign: t -> t -> t
    val bu_assign: t -> t -> t
    val print : Format.formatter -> t -> unit
    val output_json :  t ->  Yojson.Safe.t*)
end
(* val fo_assign: t -> t -> t
   val fu_assign: t -> t -> t
   val bo_assign: t -> t -> t
   val bu_assign: t -> t -> t
   val filter: t -> t -> t
   val fu_filter: t -> t -> t
   val bo_filter: t -> t -> t
   val bu_filter: t -> t -> t *)
