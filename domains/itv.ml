open Sig.Value
open Apron 
open Language.Ast
open Sig.Apron_dom
(* Boxes Abstract Domain (strict)*)
module Box_AP : APRON_DOM = (
  struct
    type t = Box.t

    let man : t Manager.t = Box.manager_alloc ()
  end :
    APRON_DOM)


(* Build a Value abstract domain from an apron numerical abstract domain *)
module Make: VALUE = struct
  module A = Box_AP
  type t = { abs : A.t Abstract1.t; env : Environment.t; vars : var list }

  let rec make_env xs env =
    match xs with
    | [] -> env
    | x :: xs ->
        make_env xs (Environment.add env [| Var.of_string x.varId |] [||])

  let bot vars =
    let env = make_env vars (Environment.make [||] [||]) in
    let abs = Abstract1.bottom A.man env in
    { abs; env; vars }

  let top vars =
    let env = make_env vars (Environment.make [||] [||]) in
    let abs = Abstract1.top A.man env in
    { abs; env; vars }

  let is_bottom t = Abstract1.is_bottom A.man t.abs
  let is_top t = Abstract1.is_top A.man t.abs
  let is_leq t1 t2 = Abstract1.is_leq A.man t1.abs t2.abs
  let join t1 t2 = { t1 with abs = Abstract1.join A.man t1.abs t2.abs }
  let meet t1 t2 = { t1 with abs = Abstract1.meet A.man t1.abs t2.abs }
  let widen t1 t2 = { t1 with abs = Abstract1.widening A.man t1.abs t2.abs }

  let fo_assign t ic oc x exp =
    match x with
    | A_var x ->
        let env = t.env in
        let e = Texpr1.of_expr env (aExp_to_apron exp) in
        let abs =
          Abstract1.assign_texpr A.man t.abs (Var.of_string x.varId) e None
        in
        ({ t with abs }, ic, oc)
    | _ -> raise (Invalid_argument "fo_assign: unexpected lvalue")

  let bo_assign t ic oc x exp =
    match x with
    | A_var x ->
        let env = t.env in
        let e = Texpr1.of_expr env (aExp_to_apron exp) in
        let b =
          Abstract1.substitute_texpr A.man t.abs (Var.of_string x.varId) e None
        in
        ({ t with abs = b }, ic, oc)
    | _ -> raise (Invalid_argument "bwdAssign: unexpected lvalue")

  let print fmt t = Abstract1.print fmt t.abs

  let rec filter t ic oc e =
    let t =
      match e with
      | A_TRUE -> t
      | A_MAYBE -> t
      | A_FALSE -> bot t.vars
      | A_bunary (o, e) -> (
          match o with
          | A_NOT ->
              let e, _ = negBExp e in
              let t,_,_ = (filter t ic oc e) in t)
      | A_bbinary (o, (e1, _), (e2, _)) -> (
          let t1, _, _ = filter t ic oc e1 and t2, _, _ = filter t ic oc e2 in
          match o with A_AND -> meet t1 t2 | A_OR -> join t1 t2)
      | A_rbinary (o, e1, e2) ->
          let env = t.env in
          let c =
            match o with
            | A_LESS ->
                Tcons1.make
                  (Texpr1.of_expr env
                     (aExp_to_apron (A_abinary (A_MINUS, e2, e1))))
                  Tcons1.SUP
            | A_LESS_EQUAL ->
                Tcons1.make
                  (Texpr1.of_expr env
                     (aExp_to_apron (A_abinary (A_MINUS, e2, e1))))
                  Tcons1.SUPEQ
            | A_GREATER ->
                Tcons1.make
                  (Texpr1.of_expr env
                     (aExp_to_apron (A_abinary (A_MINUS, e1, e2))))
                  Tcons1.SUP
            | A_GREATER_EQUAL ->
                Tcons1.make
                  (Texpr1.of_expr env
                     (aExp_to_apron (A_abinary (A_MINUS, e1, e2))))
                  Tcons1.SUPEQ
          in
          let a = Tcons1.array_make env 1 in
          Tcons1.array_set a 0 c;
          { t with abs = Abstract1.meet_tcons_array A.man t.abs a }
    in
    (t, ic, oc)
end
