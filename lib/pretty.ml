
open Syntax
open Bindlib

let string_of_term_in (_ : ctxt) = function
  | TVar x -> name_of x
  | TTerm -> "<tterm>"
  | TMetavar _ -> "<tmetavar>"

let rec string_of_staged_spec_in (ctxt : ctxt) = function
  | Return t ->
      let t_str = string_of_term_in ctxt t in
      Format.sprintf "ret %s" t_str
  | Ensures _ ->
      "ens <state>"
  | Bind (s, b) ->
      let s_str = string_of_staged_spec_in ctxt s in
      let x, b, ctxt = unbind_in ctxt b in
      let x_str = name_of x in
      let b_str = string_of_staged_spec_in ctxt b in
      Format.sprintf "(%s; %s. %s)" s_str x_str b_str
  | Apply (f, t) ->
      let f_str = string_of_term_in ctxt f in
      let t_str = string_of_term_in ctxt t in
      Format.sprintf "%s %s" f_str t_str
  | Disjunct _ -> assert false
  | Exists _ -> assert false
  | Reset _ -> assert false
  | Shift _ -> assert false
  | SMetavar _ -> assert false

let string_of_staged_spec = string_of_staged_spec_in empty_ctxt
