
open Syntax
open Bindlib

let rec string_of_term_in (ctxt : ctxt) = function
  | TVar x ->
      name_of x
  | TUnit ->
      "()"
  | TBool b ->
      string_of_bool b
  | TInt i ->
      string_of_int i
  | TLambda b ->
      let b_str = string_of_staged_spec_binder_in ctxt b in
      Format.sprintf "\\%s" b_str
  | TMetavar _ ->
      "<tmetavar>"

and string_of_state_in (_ctxt : ctxt) = function
  | STState ->
      "<ststate>"
  | STMetavar _ ->
      "<stmetavar>"

and string_of_staged_spec_in (ctxt : ctxt) = function
  | Return t ->
      let t_str = string_of_term_in ctxt t in
      Format.sprintf "return %s" t_str
  | Ensures st ->
      let st_str = string_of_state_in ctxt st in
      Format.sprintf "ensures %s" st_str
  | Bind (s, b) ->
      let s_str = string_of_staged_spec_in ctxt s in
      let b_str = string_of_staged_spec_binder_in ctxt b in
      Format.sprintf "(%s; %s)" s_str b_str
  | Apply (f, t) ->
      let f_str = string_of_term_in ctxt f in
      let t_str = string_of_term_in ctxt t in
      Format.sprintf "%s %s" f_str t_str
  | Disjunct (s1, s2) ->
      let s1_str = string_of_staged_spec_in ctxt s1 in
      let s2_str = string_of_staged_spec_in ctxt s2 in
      Format.sprintf "(%s \\/ %s)" s1_str s2_str
  | Exists b ->
      let b_str = string_of_staged_spec_binder_in ctxt b in
      Format.sprintf "(exists %s)" b_str
  | Shift b ->
      let b_str = string_of_staged_spec_binder_in ctxt b in
      Format.sprintf "(shift %s)" b_str
  | Reset s ->
      let s_str = string_of_staged_spec_in ctxt s in
      Format.sprintf "reset (%s)" s_str
  | Dollar (s, cont) ->
      let s_str = string_of_staged_spec_in ctxt s in
      let cont_str = string_of_staged_spec_binder_in ctxt cont in
      Format.sprintf "dollar (%s, %s)" s_str cont_str
  | SMetavar _ ->
      "<smetavar>"

and string_of_staged_spec_binder_in (ctxt : ctxt) = function
  | Binder b ->
      let x, b, ctxt = unbind_in ctxt b in
      let x_str = name_of x in
      let b_str = string_of_staged_spec_in ctxt b in
      Format.sprintf "%s. %s" x_str b_str
  | SBMetavar _ ->
      "<sbmetavar>"

let string_of_staged_spec = string_of_staged_spec_in empty_ctxt
