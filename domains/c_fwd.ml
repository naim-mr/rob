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
  let bot vars = { inv = V.bot vars; num_inv = InvMap.empty }
  let top vars = { inv = V.top vars; num_inv = InvMap.empty }

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

  let filter t ic oc b =
    let inv, ic, oc = V.filter t.inv ic oc b in
    ({ t with inv }, ic, oc)

  let fo_assign t x ic oc e =
    let inv, ic, oc = V.fo_assign t.inv ic oc x e in
    ({ t with inv }, ic, oc)

  let print fmt t =
    InvMap.iter
      (fun l tn -> Format.fprintf fmt "%d:%a\n" l V.print tn)
      t.num_inv

  let exec main vars ic oc =
    let rec stmt t ic oc s =
      match s with
      | A_label _ -> (t, ic, oc)
      | A_assign ((lval, _), (exp, _)) -> fo_assign t lval ic oc exp
      | A_if ((b, ba), s1, s2) ->
          let t1, _, _ = filter t ic oc b in
          let t1, ic', oc' = block t1 ic oc s1 in
          let t2, _, _ = filter t ic oc (fst (negBExp (b, ba))) in
          let t2, _, _ = block t2 ic oc s2 in
          (join t1 t2, ic', oc')
      | A_while (l, (b, ba), s) ->
          let rec aux is im ic oc n =
            let i = join t im in
            if V.is_leq i.inv is.inv then (is, ic, oc)
            else
              let is =
                if n <= !Config.joinfwd then i
                else { i with inv = V.widen is.inv i.inv }
              in
              let t, ic, i =
                let inv, _, _ = V.filter is.inv ic oc b in
                block { t with inv } ic oc s
              in
              aux is t ic oc (n + 1)
          in
          let is = bot vars in
          let t, _, _ = filter t ic oc b in
          let im,ic,oc = block t ic oc s in
          let res,ic,oc = aux is im ic oc 1 in
          let res = add_inv res l res.inv in
          filter res ic oc (fst (negBExp (b, ba)))
      | _ -> failwith "nyi"
    and block t ic oc b =
      match b with
      | A_empty l -> (add_inv t l t.inv, ic, oc)
      | A_block (l, (s, _), b) ->
          let t = add_inv t l t.inv in
          let t, ic, oc = stmt t ic oc s in
          block t ic oc b
    in
    let t = block (top vars) ic oc main  in
    t
end
