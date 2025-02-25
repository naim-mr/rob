open Language.Ast
open Utils
open Sig.Value
open InvMap

(* Forward Iterator: take a value domain and compute the abstract analysis on a C program*)
module Make (V : VALUE) = struct
  module VarSet = Setext.Make (struct
    type t = var

    let compare = compare
  end)

  type t = { inv : V.t; num_inv : V.t InvMap.t }

  let add_inv t lab inv = { t with num_inv = InvMap.add lab inv t.num_inv }

  let bot vars =
    { inv = V.bot vars; num_inv = InvMap.empty }

  let top vars =
    { inv = V.top vars; num_inv = InvMap.empty}

  let join t1 t2 =
    {
      inv = V.join t1.inv t2.inv;
      num_inv =
        InvMap.merge
          (fun l i1 i2 ->
            match (i1, i2) with
            | Some x, None | None, Some x -> Some x
            | Some x, Some y when x = y -> Some x
            | _, _ -> failwith "impossible")
          t1.num_inv t2.num_inv;
    }

  let filter t b = { t with inv = V.filter t.inv b }
  let fo_assign t x e = { t with inv = V.fo_assign t.inv x e }

  let print fmt t =
    InvMap.iter
      (fun l tn -> Format.fprintf fmt "%d:%a\n" l V.print tn)
      t.num_inv

  let exec main vars =
    let rec stmt t s =
      match s with
      | A_label _ -> t
      | A_assign ((lval, _), (exp, _)) ->
          let inv = V.fo_assign t.inv lval exp in
          { t with inv }
      | A_if ((b, ba), s1, s2) ->
          let t1 = block { t with inv = V.filter t.inv b } s1 in
          let t2 =
            block { t with inv = V.filter t.inv (fst (negBExp (b, ba))) } s2
          in
          join t1 t2
      | A_while (l, (b, ba), s) ->
          let rec aux is im n =
            let i = join t im in
            if V.is_leq i.inv is.inv then is
            else
              let is =
                if n <= !Config.joinfwd then i
                else { i with inv = V.widen is.inv i.inv }
              in
              aux is (block { t with inv = V.filter is.inv b } s) (n + 1)
          in
          let is = bot vars in
          let im = block { t with inv = V.filter t.inv b } s in
          let res = aux is im 1 in
          let res = add_inv res l res.inv in
          filter res (fst (negBExp (b, ba)))
      | _ -> failwith "nyi"
    and block t b =
      match b with
      | A_empty l -> add_inv t l t.inv
      | A_block (l, (s, _), b) ->
          let t = add_inv t l t.inv in
          block (stmt t s) b
    in
    let t = block (top vars) main in
    t
end
