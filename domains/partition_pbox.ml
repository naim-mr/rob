(***************************************************)
(*                                                 *)
(*   Ranking Function Numerical Domain Partition   *)
(*                                                 *)
(*                  Caterina Urban                 *)
(*     École Normale Supérieure, Paris, France     *)
(*                   2012 - 2015                   *)
(*                                                 *)
(***************************************************)

open Constraint
open Apron_numeric
open Sig.Value
open Apron
open Language.Ast

module Make (N : APRON_DOM) : VALUE = struct
  module C = Constraint
  (** Linear constraints used to represent the partition. *)

  type t = {
    constraints : C.t list; (* representation as list of constraints *)
    env : Environment.t; (* APRON environment *)
    vars : var list (* list of variables in the APRON environment *);
  }
  (** An element of the numerical abstract domain. *)

  type apron_t = N.t Abstract1.t

  (** The current representation as list of linear constraints. *)
  let constraints b : C.t list =
    List.fold_right
      (fun c cs ->
        (* warning: fold_left impacts speed and result of the analysis *)
        try
          (* equality constraints are turned into pairs of inequalities *)
          let c1, c2 = C.expand c in
          c1 :: c2 :: cs
        with Invalid_argument _ -> c :: cs)
      b.constraints []

  (** The current APRON environment. *)
  let env b = b.env

  (** The current list of variables in the APRON environment. *)
  let vars b = b.vars

  (** Creates an APRON man depending on the numerical abstract domain. *)

  let man = N.man

  (**)

  let rec make_env xs env =
    match xs with
    | [] -> env
    | x :: xs ->
        make_env xs (Environment.add env [| Var.of_string x.varId |] [||])

  let bot vs =
    let e = make_env vs (Environment.make [||] [||]) in
    { constraints = [ Lincons1.make_unsat e ]; env = e; vars = vs }

  let inner e vs cs = { constraints = cs; env = e; vars = vs }

  let top vs =
    {
      constraints = [];
      env = make_env vs (Environment.make [||] [||]);
      vars = vs;
    }

  let print fmt b =
    let vars = b.vars in
    let a = Lincons1.array_make b.env (List.length b.constraints) in
    let i = ref 0 in
    List.iter
      (fun c ->
        Lincons1.array_set a !i c;
        i := !i + 1)
      b.constraints;
    let b = Abstract1.of_lincons_array man b.env a in
    let a = Abstract1.to_lincons_array man b in
    let cs = ref [] in
    for i = 0 to Lincons1.array_length a - 1 do
      cs := Lincons1.array_get a i :: !cs
    done;
    match !cs with
    | [] -> Format.fprintf fmt "top"
    | x :: _ ->
        if C.is_bottom x then Format.fprintf fmt "bottom"
        else
          let i = ref 1 and l = List.length !cs in
          List.iter
            (fun c ->
              C.print vars fmt c;
              if !i = l then () else Format.fprintf fmt " && ";
              i := !i + 1)
            !cs
  (**)

  let is_bottom b =
    let a = Lincons1.array_make b.env (List.length b.constraints) in
    let i = ref 0 in
    List.iter
      (fun c ->
        Lincons1.array_set a !i c;
        i := !i + 1)
      b.constraints;
    let b = Abstract1.of_lincons_array man b.env a in
    Abstract1.is_bottom man b

  let is_top b =
    let a = Lincons1.array_make b.env (List.length b.constraints) in
    let i = ref 0 in
    List.iter
      (fun c ->
        Lincons1.array_set a !i c;
        i := !i + 1)
      b.constraints;
    let b = Abstract1.of_lincons_array man b.env a in
    Abstract1.is_top man b

  let is_leq b1 b2 =
    let env = b1.env in
    let a1 = Lincons1.array_make env (List.length b1.constraints) in
    let i = ref 0 in
    List.iter
      (fun c ->
        Lincons1.array_set a1 !i c;
        i := !i + 1)
      b1.constraints;
    let b1 = Abstract1.of_lincons_array man env a1 in
    let a2 = Lincons1.array_make env (List.length b2.constraints) in
    let j = ref 0 in
    List.iter
      (fun c ->
        Lincons1.array_set a2 !j c;
        j := !j + 1)
      b2.constraints;
    let b2 = Abstract1.of_lincons_array man env a2 in
    Abstract1.is_leq man b1 b2

  (**)

  let to_apron_t (t : t) : apron_t =
    let env = t.env in
    let a = Lincons1.array_make env (List.length t.constraints) in
    let i = ref 0 in
    List.iter
      (fun c ->
        Lincons1.array_set a !i c;
        i := !i + 1)
      t.constraints;
    Abstract1.of_lincons_array man env a

  let of_apron_t env vars (a : apron_t) : t =
    let a = Abstract1.to_lincons_array man a in
    let cs = ref [] in
    for i = 0 to Lincons1.array_length a - 1 do
      cs := Lincons1.array_get a i :: !cs (*TODO: normalization *)
    done;
    { constraints = !cs; env; vars }

  let rec assume ?(pow = 5.) b =
    let add_scalar c1 c2 =
      match (c1, c2) with
      | Scalar.Float c1, Scalar.Float c2 -> Scalar.Float (c1 +. c2)
      | Scalar.Float c1, Scalar.Mpqf c2 -> Scalar.Float (c1 +. Mpqf.to_float c2)
      | Scalar.Float c1, Scalar.Mpfrf c2 ->
          Scalar.Float (c1 +. Mpfrf.to_float c2)
      | Scalar.Mpqf c1, Scalar.Float c2 -> Scalar.Float (Mpqf.to_float c1 +. c2)
      | Scalar.Mpqf c1, Scalar.Mpqf c2 -> Scalar.Mpqf (Mpqf.add c1 c2)
      | Scalar.Mpqf c1, Scalar.Mpfrf c2 ->
          Scalar.Mpqf (Mpqf.add c1 (Mpfrf.to_mpqf c2))
      | Scalar.Mpfrf c1, Scalar.Float c2 ->
          Scalar.Float (Mpfrf.to_float c1 +. c2)
      | Scalar.Mpfrf c1, Scalar.Mpqf c2 ->
          Scalar.Mpqf (Mpqf.add (Mpfrf.to_mpqf c1) c2)
      | Scalar.Mpfrf c1, Scalar.Mpfrf c2 ->
          Scalar.Mpfrf (Mpfrf.add c1 c2 Mpfr.Zero)
    in
    let mul_scalar c1 c2 =
      match (c1, c2) with
      | Scalar.Float c1, Scalar.Float c2 -> Scalar.Float (c1 *. c2)
      | Scalar.Float c1, Scalar.Mpqf c2 -> Scalar.Float (c1 *. Mpqf.to_float c2)
      | Scalar.Float c1, Scalar.Mpfrf c2 ->
          Scalar.Float (c1 *. Mpfrf.to_float c2)
      | Scalar.Mpqf c1, Scalar.Float c2 -> Scalar.Float (Mpqf.to_float c1 *. c2)
      | Scalar.Mpqf c1, Scalar.Mpqf c2 -> Scalar.Mpqf (Mpqf.mul c1 c2)
      | Scalar.Mpqf c1, Scalar.Mpfrf c2 ->
          Scalar.Mpqf (Mpqf.mul c1 (Mpfrf.to_mpqf c2))
      | Scalar.Mpfrf c1, Scalar.Float c2 ->
          Scalar.Float (Mpfrf.to_float c1 *. c2)
      | Scalar.Mpfrf c1, Scalar.Mpqf c2 ->
          Scalar.Mpqf (Mpqf.mul (Mpfrf.to_mpqf c1) c2)
      | Scalar.Mpfrf c1, Scalar.Mpfrf c2 ->
          Scalar.Mpfrf (Mpfrf.mul c1 c2 Mpfr.Zero)
    in
    let div_scalar c1 c2 =
      match (c1, c2) with
      | Scalar.Float c1, Scalar.Float c2 -> Scalar.Float (c1 /. c2)
      | Scalar.Float c1, Scalar.Mpqf c2 -> Scalar.Float (c1 /. Mpqf.to_float c2)
      | Scalar.Float c1, Scalar.Mpfrf c2 ->
          Scalar.Float (c1 /. Mpfrf.to_float c2)
      | Scalar.Mpqf c1, Scalar.Float c2 -> Scalar.Float (Mpqf.to_float c1 /. c2)
      | Scalar.Mpqf c1, Scalar.Mpqf c2 -> Scalar.Mpqf (Mpqf.div c1 c2)
      | Scalar.Mpqf c1, Scalar.Mpfrf c2 ->
          Scalar.Mpqf (Mpqf.div c1 (Mpfrf.to_mpqf c2))
      | Scalar.Mpfrf c1, Scalar.Float c2 ->
          Scalar.Float (Mpfrf.to_float c1 /. c2)
      | Scalar.Mpfrf c1, Scalar.Mpqf c2 ->
          Scalar.Mpqf (Mpqf.div (Mpfrf.to_mpqf c1) c2)
      | Scalar.Mpfrf c1, Scalar.Mpfrf c2 ->
          Scalar.Mpfrf (Mpfrf.div c1 c2 Mpfr.Zero)
    in
    let env = b.env in
    let vars = b.vars in
    (* count occurrences of variables within the polyhedral constraints *)
    let blookup =
      let filter_equality =
        List.filter
          (fun c -> not (Lincons1.get_typ c = Lincons1.EQ))
          b.constraints
      in
      match filter_equality with
      | [] -> b
      | _ -> { b with constraints = filter_equality }
    in
    let occ =
      List.map
        (fun x ->
          let o =
            List.fold_left
              (fun ao c -> if C.var x c then ao + 1 else ao)
              0 blookup.constraints
          in
          (x, o))
        vars
    in
    (* selecting the variable with less occurrences *)
    let x =
      fst
        (List.hd
           (List.sort
              (fun (x1, o1) (x2, o2) ->
                if x1.varName = x1.varId && x2.varName != x2.varId then 1
                else if x1.varName != x1.varId && x2.varName = x2.varId then -1
                else compare o1 o2)
              occ))
    in
    (* creating an APRON variable *)
    let v = Var.of_string x.varId in
    (* creating an APRON polyhedra *)
    let a = Lincons1.array_make env (List.length b.constraints) in
    let i = ref 0 in
    List.iter
      (fun c ->
        Lincons1.array_set a !i c;
        i := !i + 1)
      b.constraints;
    let p = Abstract1.of_lincons_array man env a in
    (* creating an APRON polyhedra *)
    (* getting the interval of variation of the variable in the polyhedra *)
    let i = Abstract1.bound_variable man p v in
    (* splitting the interval making assumtions *)
    let inf = i.Interval.inf in
    let sup = i.Interval.sup in
    if 1 = Scalar.is_infty sup then (
      if -1 = Scalar.is_infty inf then (
        (* infinite domain: for -inf <= v <= +oo*)
        let e = Linexpr1.make env in
        Linexpr1.set_coeff e v (Coeff.s_of_int 1);
        Linexpr1.set_cst e (Coeff.s_of_int (-1));
        let c = Lincons1.make e Lincons1.SUPEQ in
        (* split on : c = v >= -1 *)
        assert (not (is_bottom { constraints = c :: b.constraints; env; vars }));
        assert (
          not
            (is_bottom { constraints = C.negate c :: b.constraints; env; vars }));
        ( { constraints = c :: b.constraints; env; vars },
          { constraints = C.negate c :: b.constraints; env; vars } ))
      else if (*  m <= v <= +oo *)
              pow > 30. then (
        assert (not (is_bottom { constraints = b.constraints; env; vars }));
        ( { constraints = b.constraints; env; vars },
          { constraints = b.constraints; env; vars } ))
      else
        let p2 = 2. ** pow in
        if Scalar.cmp inf (Scalar.of_float p2) > 0 then
          assume ~pow:(2. ** (pow +. 1.)) b
        else
          let mid = int_of_float p2 in
          let e = Linexpr1.make env in
          Linexpr1.set_coeff e v (Coeff.s_of_int 1);
          Linexpr1.set_cst e
            (Coeff.Scalar (mul_scalar (Scalar.of_int (-1)) inf));
          let c = Lincons1.make e Lincons1.SUPEQ in
          (*  c =  v  >= m  *)
          let e1 = Linexpr1.make env in
          Linexpr1.set_coeff e1 v (Coeff.s_of_int (-1));
          Linexpr1.set_cst e1 (Coeff.s_of_int mid);
          let c1 = Lincons1.make e1 Lincons1.SUPEQ in
          let e3 = Linexpr1.make env in
          Linexpr1.set_coeff e3 v (Coeff.s_of_int 1);
          Linexpr1.set_cst e3 (Coeff.s_of_int (-mid));
          let c3 = Lincons1.make e3 Lincons1.SUPEQ in
          (* c3 =  v >= 2 ^ n *)
          (* split on:
             a- c && c1 ==  m <= v <= 2^n
             b- c3      ==  2^n <= v <= +oo
          *)
          assert (
            not
              (is_bottom { constraints = c :: c1 :: b.constraints; env; vars }));
          assert (
            not (is_bottom { constraints = c3 :: b.constraints; env; vars }));
          ( { constraints = c :: c1 :: b.constraints; env; vars },
            { constraints = c3 :: b.constraints; env; vars } ))
    else if -1 = Scalar.is_infty inf then (
      (* -oo <= v <= M*)
      let mid =
        if Scalar.cmp sup (Scalar.of_int 0) >= 0 then
          div_scalar sup (Scalar.of_int 2)
        else mul_scalar sup (Scalar.of_int 2)
      in
      let e = Linexpr1.make env in
      Linexpr1.set_coeff e v (Coeff.s_of_int (-1));
      Linexpr1.set_cst e (Coeff.Scalar sup);
      let c = Lincons1.make e Lincons1.SUPEQ in
      (* c ==  v <= (M ) *)
      let e1 = Linexpr1.make env in
      Linexpr1.set_coeff e1 v (Coeff.s_of_int 1);
      Linexpr1.set_cst e1 (Coeff.Scalar (Scalar.neg mid));
      let c1 = Lincons1.make e1 Lincons1.SUPEQ in
      (* c1 ==  v >= M/2 *)
      let e2 = Linexpr1.make env in
      Linexpr1.set_coeff e2 v (Coeff.s_of_int (-1));
      Linexpr1.set_cst e2 (Coeff.Scalar mid);
      let c2 = Lincons1.make e2 Lincons1.SUPEQ in
      (* c2 ==   M/2 >= v   *)
      (* split on:
           a- c1 && c2 ==  M/2 <= v <= M -1
           b- c        ==  -oo<= v <= M/2
      *)
      assert (
        not (is_bottom { constraints = c :: c1 :: b.constraints; env; vars }));
      assert (not (is_bottom { constraints = c2 :: b.constraints; env; vars }));
      ( { constraints = c :: c1 :: b.constraints; env; vars },
        { constraints = c2 :: b.constraints; env; vars } ))
    else if Scalar.equal inf sup then (
      (* -m <= v <= m : v == m *)
      (* let e = Linexpr1.make env in
         Linexpr1.set_coeff e v (Coeff.s_of_int 1) ;
         Linexpr1.set_cst e (Coeff.Scalar (mul_scalar (Scalar.of_int (-1)) inf));
         let c = Lincons1.make e Lincons1.SUPEQ in *)
      (* split on:
           c == v >= m && v<=m
      *)
      assert (not (is_bottom { constraints = b.constraints; env; vars }));
      assert (not (is_bottom { constraints = b.constraints; env; vars }));
      ( { constraints = b.constraints; env; vars },
        { constraints = b.constraints; env; vars } ))
    else
      (* m <= v <= M *)
      let e = Linexpr1.make env in
      Linexpr1.set_coeff e v (Coeff.s_of_int 1);
      let s = add_scalar sup inf in
      let s = div_scalar s (Scalar.of_int 2) in
      (* s = ((m + M) / 2 *)
      Linexpr1.set_cst e (Coeff.Scalar (Scalar.neg s));
      let c = Lincons1.make e Lincons1.SUPEQ in
      (* c = x >= ((m + M) / 2)   *)
      let e2 = Linexpr1.make env in
      Linexpr1.set_coeff e2 v (Coeff.s_of_int (-1));
      Linexpr1.set_cst e2 (Coeff.Scalar sup);
      let c2 = Lincons1.make e2 Lincons1.SUPEQ in
      (* c2 = x <= M *)
      let e3 = Linexpr1.make env in
      Linexpr1.set_coeff e3 v (Coeff.s_of_int (-1));
      Linexpr1.set_cst e3 (Coeff.Scalar s);
      let c3 = Lincons1.make e3 Lincons1.SUPEQ in
      (* c3 = x <= ((m + M / 2) + 1) *)
      let e4 = Linexpr1.make env in
      Linexpr1.set_coeff e4 v (Coeff.s_of_int 1);
      Linexpr1.set_cst e4 (Coeff.Scalar inf);
      let c4 = Lincons1.make e2 Lincons1.SUPEQ in
      (* c4 = x >= m *)
      (* split on:
           a- c && c2   == ((m + M / 2) + 1) <= v <= M
           b- c3 && c4  ==  m <= v <= ((m + M / 2) )
      *)
      assert (
        not (is_bottom { constraints = c :: c2 :: b.constraints; env; vars }));
      assert (
        not (is_bottom { constraints = c3 :: c4 :: b.constraints; env; vars }));
      ( { constraints = c :: c2 :: b.constraints; env; vars },
        { constraints = c3 :: c4 :: b.constraints; env; vars } )

  let join b1 b2 =
    let env = b1.env in
    let vars = b1.vars in
    let a1 = Lincons1.array_make env (List.length b1.constraints) in
    let i = ref 0 in
    List.iter
      (fun c ->
        Lincons1.array_set a1 !i c;
        i := !i + 1)
      b1.constraints;
    let b1 = Abstract1.of_lincons_array man env a1 in
    let a2 = Lincons1.array_make env (List.length b2.constraints) in
    let j = ref 0 in
    List.iter
      (fun c ->
        Lincons1.array_set a2 !j c;
        j := !j + 1)
      b2.constraints;
    let b2 = Abstract1.of_lincons_array man env a2 in
    let b = Abstract1.join man b1 b2 in
    let a = Abstract1.to_lincons_array man b in
    let cs = ref [] in
    for i = 0 to Lincons1.array_length a - 1 do
      cs := Lincons1.array_get a i :: !cs (*TODO: normalization *)
    done;
    { constraints = !cs; env; vars }

  let widen b1 b2 =
    let env = b1.env in
    let vars = b1.vars in
    let a1 = Lincons1.array_make env (List.length b1.constraints) in
    let i = ref 0 in
    List.iter
      (fun c ->
        Lincons1.array_set a1 !i c;
        i := !i + 1)
      b1.constraints;
    let b1 = Abstract1.of_lincons_array man env a1 in
    let a2 = Lincons1.array_make env (List.length b2.constraints) in
    let j = ref 0 in
    List.iter
      (fun c ->
        Lincons1.array_set a2 !j c;
        j := !j + 1)
      b2.constraints;
    let b2 = Abstract1.of_lincons_array man env a2 in
    let b = Abstract1.widening man b1 b2 in
    let a = Abstract1.to_lincons_array man b in
    let cs = ref [] in
    for i = 0 to Lincons1.array_length a - 1 do
      cs := Lincons1.array_get a i :: !cs (*TODO: normalization *)
    done;
    { constraints = !cs; env; vars }

  let meet b1 b2 =
    let env = b1.env in
    let vars = b1.vars in
    let a1 = Lincons1.array_make env (List.length b1.constraints) in
    let i = ref 0 in
    List.iter
      (fun c ->
        Lincons1.array_set a1 !i c;
        i := !i + 1)
      b1.constraints;
    let b1 = Abstract1.of_lincons_array man env a1 in
    let a2 = Lincons1.array_make env (List.length b2.constraints) in
    let j = ref 0 in
    List.iter
      (fun c ->
        Lincons1.array_set a2 !j c;
        j := !j + 1)
      b2.constraints;
    let b2 = Abstract1.of_lincons_array man env a2 in
    let b = Abstract1.meet man b1 b2 in
    let a = Abstract1.to_lincons_array man b in
    let cs = ref [] in
    for i = 0 to Lincons1.array_length a - 1 do
      cs := Lincons1.array_get a i :: !cs (*TODO: normalization *)
    done;
    { constraints = !cs; env; vars }

  (**)

  let fo_assign b x e =
    match x with
    | A_var x ->
        let env = b.env in
        let vars = b.vars in
        let e = Texpr1.of_expr env (aExp_to_apron e) in
        let a = Lincons1.array_make env (List.length b.constraints) in
        let i = ref 0 in
        List.iter
          (fun c ->
            Lincons1.array_set a !i c;
            i := !i + 1)
          b.constraints;
        let b = Abstract1.of_lincons_array man env a in
        let b = Abstract1.assign_texpr man b (Var.of_string x.varId) e None in
        let a = Abstract1.to_lincons_array man b in
        let cs = ref [] in
        for i = 0 to Lincons1.array_length a - 1 do
          cs := Lincons1.array_get a i :: !cs (*TODO: normalization *)
        done;
        { constraints = !cs; env; vars }
    | _ -> raise (Invalid_argument "fo_assign: unexpected lvalue")

  (* let bwdAssign_underapprox (t:t) ((x,e): aExp * aExp) : t = match x with
     | A_var x ->
       if not N.supports_underapproximation then
         raise (Invalid_argument "Underapproximation not supported by this abstract domain, use polyhedra instead");
       let env = t.env in
       let vars = t.vars in
       let at = to_apron_t t in
       let top = Abstract1.top man (Abstract1.env at) in
       let pre = top in (* use top as pre environment *)
       let assignDest = Banal_domain.STRONG (Function_banal_converter.var_to_banal x) in
       let assignValue = Function_banal_converter.of_aExp e in
       let assigned = BanalApron.bwd_assign at () assignDest assignValue pre in
       of_apron_t env vars assigned
     | _ -> raise (Invalid_argument "bwdAssign_underapprox: unexpected lvalue")
  *)
  let bo_assign b x e =
    match x with
    | A_var x ->
        let f manager b (x, e) : t =
          let env = b.env in
          let vars = b.vars in
          let e = Texpr1.of_expr env (aExp_to_apron e) in
          let a = Lincons1.array_make env (List.length b.constraints) in
          let i = ref 0 in
          List.iter
            (fun c ->
              Lincons1.array_set a !i c;
              i := !i + 1)
            b.constraints;
          let b = Abstract1.of_lincons_array manager env a in
          let b =
            Abstract1.substitute_texpr manager b (Var.of_string x.varId) e None
          in
          let a = Abstract1.to_lincons_array manager b in
          let cs = ref [] in
          for i = 0 to Lincons1.array_length a - 1 do
            cs := Lincons1.array_get a i :: !cs (*TODO: normalization *)
          done;
          { constraints = !cs; env; vars }
        in
        let b1 = f man b (x, e) in
        let b2 = f (Box.manager_alloc ()) b (x, e) in
        { b1 with constraints = b1.constraints @ b2.constraints }
    | _ -> raise (Invalid_argument "bwdAssign: unexpected lvalue")

  (* let filter_underapprox (t:t) (e:bExp) : t =
     if not N.supports_underapproximation then
       raise (Invalid_argument "Underapproximation not supported by this abstract domain, use octagons or polyhedra instead");
     let env = t.env in
     let vars = t.vars in
     let expr = Function_banal_converter.of_bExp e in
     let at = to_apron_t t in
     let top = Abstract1.top man (Abstract1.env at) in
     let bot = Abstract1.bottom man (Abstract1.env at) in
     let pre = top in (* use top as pre environment *)
     let filtered = BanalApron.bwd_filter at bot () expr () pre in
     let result = of_apron_t env vars filtered in
     result *)

  let rec filter b e =
    let f man b e =
      match e with
      | A_TRUE -> b
      | A_MAYBE -> b
      | A_FALSE -> bot b.vars
      | A_bunary (o, e) -> (
          match o with
          | A_NOT ->
              let e, _ = negBExp e in
              filter b e)
      | A_bbinary (o, (e1, _), (e2, _)) -> (
          let b1 = filter b e1 and b2 = filter b e2 in
          match o with A_AND -> meet b1 b2 | A_OR -> join b1 b2)
      | A_rbinary (o, e1, e2) -> (
          let env = b.env in
          let vars = b.vars in
          let a = Lincons1.array_make env (List.length b.constraints) in
          let i = ref 0 in
          List.iter
            (fun c ->
              Lincons1.array_set a !i c;
              i := !i + 1)
            b.constraints;
          let b = Abstract1.of_lincons_array man env a in
          match o with
          | A_LESS ->
              let e =
                Texpr1.of_expr env (aExp_to_apron (A_abinary (A_MINUS, e2, e1)))
              in
              let c = Tcons1.make e Tcons1.SUP in
              let a = Tcons1.array_make env 1 in
              Tcons1.array_set a 0 c;
              let b = Abstract1.meet_tcons_array man b a in
              let a = Abstract1.to_lincons_array man b in
              let cs = ref [] in
              for i = 0 to Lincons1.array_length a - 1 do
                cs := Lincons1.array_get a i :: !cs (*TODO: normalization *)
              done;
              { constraints = !cs; env; vars }
          | A_LESS_EQUAL ->
              let e =
                Texpr1.of_expr env (aExp_to_apron (A_abinary (A_MINUS, e2, e1)))
              in
              let c = Tcons1.make e Tcons1.SUPEQ in
              let a = Tcons1.array_make env 1 in
              Tcons1.array_set a 0 c;
              let b = Abstract1.meet_tcons_array man b a in
              let a = Abstract1.to_lincons_array man b in
              let cs = ref [] in
              for i = 0 to Lincons1.array_length a - 1 do
                cs := Lincons1.array_get a i :: !cs (*TODO: normalization *)
              done;
              { constraints = !cs; env; vars }
          | A_GREATER ->
              let e =
                Texpr1.of_expr env (aExp_to_apron (A_abinary (A_MINUS, e1, e2)))
              in
              let c = Tcons1.make e Tcons1.SUP in
              let a = Tcons1.array_make env 1 in
              Tcons1.array_set a 0 c;
              let b = Abstract1.meet_tcons_array man b a in
              let a = Abstract1.to_lincons_array man b in
              let cs = ref [] in
              for i = 0 to Lincons1.array_length a - 1 do
                cs := Lincons1.array_get a i :: !cs (*TODO: normalization *)
              done;
              { constraints = !cs; env; vars }
          | A_GREATER_EQUAL ->
              let e =
                Texpr1.of_expr env (aExp_to_apron (A_abinary (A_MINUS, e1, e2)))
              in
              let c = Tcons1.make e Tcons1.SUPEQ in
              let a = Tcons1.array_make env 1 in
              Tcons1.array_set a 0 c;
              let b = Abstract1.meet_tcons_array man b a in
              let a = Abstract1.to_lincons_array man b in
              let cs = ref [] in
              for i = 0 to Lincons1.array_length a - 1 do
                cs := Lincons1.array_get a i :: !cs (*TODO: normalization *)
              done;
              { constraints = !cs; env; vars })
    in
    let b1 = f man b e in
    let b2 = f (Box.manager_alloc ()) b e in
    { b1 with constraints = b1.constraints @ b2.constraints }

  (**)
end
