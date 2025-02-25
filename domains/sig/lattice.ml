
(** Signature of a lattice *)
open Query
module type LATTICE = sig
  type t
  val bot : t
  val is_bottom : t -> bool
  val is_top : t -> bool
  val is_leq : t -> t -> bool
  val join : t -> t -> t
  val meet : t -> t -> t
  val widen : t -> t -> t
end
