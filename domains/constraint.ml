(*   
             ********* (Linear) Constraints ************
   Copyright (C) 2012-2014 by Caterina Urban. All rights reserved.
*)

(* 
module type CONSTRAINT =
sig

  type t = Lincons1.t
  val env : t -> Environment.t
  val linexpr : t -> Linexpr1.t

  val isBot : t -> bool
  val compare : t -> t -> int (* -1: c1 < c2, 0: c1 = c2, 1: c1 > c2 *)
  val isEq : t -> t -> bool
  val isLeq : t -> t -> bool
  val similar : t -> t -> bool (* constraints differing only for the constant *)
  val var : var -> t -> bool
  (* val variant : t -> t -> bool (* widening *) *)

  val negate : t -> t
  val expand : t -> t * t
  (* val widen : t -> t -> t (* widening *) *)

  val print : var list -> Format.formatter -> t -> unit

end *)

open Language.Ast
open Sig.Value
open Apron

module Constraint =
struct

  type t = Lincons1.t

  let env c = Lincons1.get_env c

  let linexpr c = Lincons1.get_linexpr1 c

  let is_bottom c = Lincons1.is_unsat c

  let compare_coeff c1 c2 =
    match c1,c2 with
    | Coeff.Interval c1,Coeff.Interval c2 ->
      let inf = Scalar.cmp c1.Interval.inf c2.Interval.inf in
      let sup = Scalar.cmp c1.Interval.sup c2.Interval.sup in
      if (inf = 0)
      then
        if (sup = 0)
        then 0
        else sup
      else inf
    | Coeff.Interval c1,Coeff.Scalar c2 ->
      let inf = Scalar.cmp c1.Interval.inf c2 in
      let sup = Scalar.cmp c1.Interval.sup c2 in
      if (inf = 0)
      then
        if (sup = 0)
        then 0
        else sup
      else inf
    | Coeff.Scalar c1,Coeff.Interval c2 ->
      let inf = Scalar.cmp c1 c2.Interval.inf in
      let sup = Scalar.cmp c1 c2.Interval.sup in
      if (inf = 0)
      then
        if (sup = 0)
        then 0
        else sup
      else inf
    | Coeff.Scalar c1,Coeff.Scalar c2 -> Scalar.cmp c1 c2

  let compare_typ t1 t2 =
    match t1,t2 with
    | Lincons1.EQ,_ | _,Lincons1.EQ -> raise (Invalid_argument "isEqTyp:EQ")
    | Lincons1.SUPEQ,Lincons1.SUPEQ -> 0
    | Lincons1.SUP,_ | _,Lincons1.SUP -> raise (Invalid_argument "isEqTyp:SUP")
    | Lincons1.DISEQ,_ | _,Lincons1.DISEQ -> raise (Invalid_argument "isEqTyp:DISEQ")
    | (Lincons1.EQMOD _),_ | _,(Lincons1.EQMOD _) -> raise (Invalid_argument "isEqTyp:EQMOD")

  let compare c1 c2 =
    let rec aux l1 l2 =
      match l1,l2 with
      | [],[] -> 
        let c = compare_coeff (Lincons1.get_cst c1) (Lincons1.get_cst c2) in
        if (c = 0)
        then compare_typ (Lincons1.get_typ c1) (Lincons1.get_typ c2)
        else c
      | [],(x2,v2)::l2s ->
        let c = compare_coeff (Coeff.s_of_int 0) v2 in
        if (c = 0) then aux l1 l2s else c
      | (x1,v1)::l1s,[] ->
        let c = compare_coeff v1 (Coeff.s_of_int 0) in
        if (c = 0) then aux l1s l2 else c
      | (x1,v1)::l1s,(x2,v2)::l2s when (Var.compare x1 x2) < 0 ->
        let c = compare_coeff v1 (Coeff.s_of_int 0) in
        if (c = 0) then aux l1s l2 else c
      | (x1,v1)::l1s,(x2,v2)::l2s when (Var.compare x1 x2) = 0 ->
        let c = compare_coeff v1 v2 in
        if (c = 0) then aux l1s l2s else c
      | (x1,v1)::l1s,(x2,v2)::l2s (*when (Var.compare x1 x2) > 0*) ->
        let c = compare_coeff (Coeff.s_of_int 0) v2 in
        if (c = 0) then aux l1 l2s else c
    in
    let l1 = ref [] and l2 = ref [] in
    Lincons1.iter (fun v x -> l1 := (x,v)::!l1) c1; 
    Lincons1.iter (fun v x -> l2 := (x,v)::!l2) c2;
    aux (List.rev !l1) (List.rev !l2)

  let is_eq c1 c2 = (compare c1 c2) = 0

  let is_leq c1 c2 = (compare c1 c2) <= 0

  let similar c1 c2 = 
    let rec aux l1 l2 =
      match l1,l2 with
      | [],[] -> 0
      | [],(x2,v2)::l2s ->
        let c = compare_coeff (Coeff.s_of_int 0) v2 in
        if (c = 0) then aux l1 l2s else c
      | (x1,v1)::l1s,[] ->
        let c = compare_coeff v1 (Coeff.s_of_int 0) in
        if (c = 0) then aux l1s l2 else c
      | (x1,v1)::l1s,(x2,v2)::l2s when (Var.compare x1 x2) < 0 ->
        let c = compare_coeff v1 (Coeff.s_of_int 0) in
        if (c = 0) then aux l1s l2 else c
      | (x1,v1)::l1s,(x2,v2)::l2s when (Var.compare x1 x2) = 0 ->
        let c = compare_coeff v1 v2 in
        if (c = 0) then aux l1s l2s else c
      | (x1,v1)::l1s,(x2,v2)::l2s (*when (Var.compare x1 x2) > 0*) ->
        let c = compare_coeff (Coeff.s_of_int 0) v2 in
        if (c = 0) then aux l1 l2s else c
    in
    let t1 = Lincons1.get_typ c1 and t2 = Lincons1.get_typ c2 in
    match t1,t2 with
    | Lincons1.SUPEQ,Lincons1.SUPEQ ->
      let l1 = ref [] and l2 = ref [] in
      Lincons1.iter (fun v x -> l1 := (x,v)::!l1) c1; 
      Lincons1.iter (fun v x -> l2 := (x,v)::!l2) c2;
      (aux !l1 !l2 = 0)
    | _ -> false

  let var v c =		
    let v = Var.of_string v.varId in
    let c = Lincons1.get_coeff c v in
    (compare_coeff c (Coeff.s_of_int 0)) != 0
  let add_scalar c1 c2 =
    match c1,c2 with
    | Scalar.Float c1,Scalar.Float c2 -> Scalar.Float (c1 +. c2)
    | Scalar.Float c1,Scalar.Mpqf c2 -> Scalar.Float (c1 +. (Mpqf.to_float c2))
    | Scalar.Float c1,Scalar.Mpfrf c2 -> Scalar.Float (c1 +. (Mpfrf.to_float c2))
    | Scalar.Mpqf c1,Scalar.Float c2 -> Scalar.Float ((Mpqf.to_float c1) +. c2)
    | Scalar.Mpqf c1,Scalar.Mpqf c2 -> Scalar.Mpqf (Mpqf.add c1 c2)
    | Scalar.Mpqf c1,Scalar.Mpfrf c2 -> Scalar.Mpqf (Mpqf.add c1 (Mpfrf.to_mpqf c2))
    | Scalar.Mpfrf c1,Scalar.Float c2 -> Scalar.Float ((Mpfrf.to_float c1) +. c2)
    | Scalar.Mpfrf c1,Scalar.Mpqf c2 -> Scalar.Mpqf (Mpqf.add (Mpfrf.to_mpqf c1) c2)
    | Scalar.Mpfrf c1,Scalar.Mpfrf c2 -> Scalar.Mpfrf (Mpfrf.add c1 c2 Mpfr.Zero)

  let add_coeff c1 c2 = 
    match c1,c2 with
    | Coeff.Scalar c1,Coeff.Scalar c2 -> Coeff.Scalar (add_scalar c1 c2)
    | Coeff.Scalar c1,Coeff.Interval c2 ->
      Coeff.reduce (Coeff.i_of_scalar (add_scalar c1 c2.Interval.inf) (add_scalar c1 c2.Interval.sup))
    | Coeff.Interval c1,Coeff.Scalar c2 ->
      Coeff.reduce (Coeff.i_of_scalar (add_scalar c1.Interval.inf c2) (add_scalar c1.Interval.sup c2))
    | Coeff.Interval c1,Coeff.Interval c2 ->
      Coeff.reduce (Coeff.i_of_scalar (add_scalar c1.Interval.inf c2.Interval.inf) (add_scalar c1.Interval.sup c2.Interval.sup))

  let negate c =
    let n = Lincons1.copy c in
    let t = Lincons1.get_typ n in
    match t with
    | Lincons1.EQ -> raise (Invalid_argument "negate:EQ")
    | Lincons1.SUPEQ ->
      Lincons1.iter (fun v x -> Lincons1.set_coeff n x (Coeff.neg v)) n;
      Lincons1.set_cst n (Coeff.neg (add_coeff (Lincons1.get_cst n) (Coeff.s_of_int 1))); n
    | Lincons1.SUP -> raise (Invalid_argument "negate:SUP")
    | Lincons1.DISEQ -> raise (Invalid_argument "negate:DISEQ")
    | Lincons1.EQMOD _ -> raise (Invalid_argument "negate:EQMOD")

  let expand c =
    let t = Lincons1.get_typ c in
    match t with
    | Lincons1.EQ ->
      let c1 = Lincons1.copy c in
      let c2 = Lincons1.copy c in
      Lincons1.set_typ c1 Lincons1.SUPEQ;
      Lincons1.iter (fun v x -> Lincons1.set_coeff c2 x (Coeff.neg v)) c2;
      Lincons1.set_cst c2 (Coeff.neg (Lincons1.get_cst c2));
      Lincons1.set_typ c2 Lincons1.SUPEQ; (c1,c2)
    | Lincons1.SUPEQ -> raise (Invalid_argument "SUPEQ")
    | Lincons1.SUP -> raise (Invalid_argument "SUP")
    | Lincons1.DISEQ -> raise (Invalid_argument "DISEQ")
    | Lincons1.EQMOD _ -> raise (Invalid_argument "EQMOD") 

  let print vars fmt c =
    let first = ref true in
    let rec aux c v =
      match c with
      | Coeff.Scalar s -> 
        if v <> "" && Scalar.sgn s = 0 then () else (
          if Scalar.sgn s < 0 then 
            if v <> "" && Scalar.equal_int s (-1) then Format.fprintf fmt "-" else
              Format.fprintf fmt "-%s" (Scalar.to_string (Scalar.neg s))
          else if !first then 
            if v <> "" && Scalar.equal_int s 1 then () else
              Format.fprintf fmt "%s" (Scalar.to_string s)
          else 
          if v <> "" && Scalar.equal_int s 1 then Format.fprintf fmt "+" else
            Format.fprintf fmt "+%s" (Scalar.to_string s);
          if v <> "" then Format.fprintf fmt "%s" v;
          first := false
        )
      | Coeff.Interval i ->
        if Scalar.equal i.Interval.inf i.Interval.sup then
          aux (Coeff.Scalar i.Interval.inf) v
        else (
          if not !first then Format.fprintf fmt "+";
          Format.fprintf fmt "[%s,%s]" (Scalar.to_string i.Interval.inf) (Scalar.to_string i.Interval.sup);
          if v <> "" then Format.fprintf fmt "%s" v
        );
        first := false
    in
    Lincons1.iter (fun v x -> 
        try 
          let x = List.find (fun y -> String.compare (Var.to_string x) y.varId = 0) vars in
          Format.fprintf Format.str_formatter "%s{%s}" x.varId x.varName;
          aux v (Format.flush_str_formatter ())
        with Not_found -> ()
      ) c;
    let k = Coeff.neg (Lincons1.get_cst c) in
    if !first then Format.fprintf fmt "0";
    first := true;
    (match Lincons1.get_typ c with
     | Lincons1.EQ -> Format.fprintf fmt " == "; aux k ""
     | Lincons1.SUPEQ -> Format.fprintf fmt " >= "; aux k ""
     | Lincons1.SUP -> Format.fprintf fmt " > "; aux k ""
     | Lincons1.DISEQ -> raise (Invalid_argument "print:DISEQ")
     | Lincons1.EQMOD s -> raise (Invalid_argument "print:EQMOD"))

end

