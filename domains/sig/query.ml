open Language.Ast

type 'a with_bottom = Val of 'a | Bot
type ochan = {
  is_equal: var -> var -> bool option;
  is_odd: var -> bool option;
  is_even: var -> bool option;
}

type bnd = Z.t
 
type i_data = Interval of var * Z.t * Z.t | Odd of var | Even of var

type ichan = {
  refine_under: i_data list;
  refine_all: i_data list
}

let empty_ochan =
  let is_equal = fun x -> fun y -> None in 
  let is_odd =  fun x -> None in 
  let is_even = fun x -> None in 
  {
  is_equal = is_equal;
  is_odd = is_odd;
  is_even = is_even
}
let empty_ichan = {refine_under = []; refine_all = []}