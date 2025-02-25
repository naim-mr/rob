open Apron

(* Type of apron manager *)
type 'a man = 'a Manager.t

(* An apron abstract domain is defined by its abstract type and its manager *)
module type APRON_DOM = sig
  type t

  val man : t man
end
