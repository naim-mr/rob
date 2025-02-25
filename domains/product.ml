open Sig.Value
open Apron
module Make(A:VALUE) (B:VALUE):VALUE = struct
  type t = {
    t_left : A.t;
    t_right: B.t;
  }

  let bot vars = {
    t_left = A.bot vars;
    t_right = B.bot vars;
  }
  let top vars = {
    t_left = A.top vars;
    t_right = B.top vars;
  }

  let lift2_l f t1 t2 =  f t1.t_left t2.t_left
  let lift2_r f t1 t2 =  f t1.t_right t2.t_right
  let is_bottom t = A.is_bottom t.t_left || B.is_bottom t.t_right

  let is_top t = A.is_top t.t_left && B.is_top t.t_right

  let is_leq t1 t2 = A.is_leq t1.t_left t2.t_left && B.is_leq t1.t_right t2.t_right

  let join t1 t2 = {t_left = lift2_l A.join t1 t2; t_right = lift2_r B.join t1 t2}

  let meet t1 t2 = {t_left = lift2_l A.meet t1 t2; t_right = lift2_r B.meet t1 t2}

  let widen t1 t2 = {t_left = lift2_l A.widen t1 t2; t_right = lift2_r B.widen t1 t2}

  let fo_assign t x exp = { t_left = A.fo_assign t.t_left x exp; t_right = B.fo_assign t.t_right x exp}

  let filter t exp = { t_left = A.filter t.t_left exp; t_right = B.filter t.t_right exp}

  let bo_assign t x exp = { t_left = A.bo_assign t.t_left x exp; t_right = B.bo_assign t.t_right x exp}
  let print fmt t = Format.fprintf fmt "@[Product: (%a,%a) @]"  A.print t.t_left  B.print  t.t_right

  let fo_assign_man (man:'a Manager.t) t x exp = failwith "nyi"

end