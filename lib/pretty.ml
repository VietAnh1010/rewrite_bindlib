
open Syntax
open Bindlib

let rec string_of_term_in (ctxt : ctxt) = function
  | TVar x ->
      name_of x
  | TSymbol s ->
      s.s_name
  | TUnit ->
      "()"
  | TBool b ->
      string_of_bool b
  | TInt i ->
      string_of_int i
  | TPair (t1, t2) ->
      let t1_str = string_of_term_in ctxt t1 in
      let t2_str = string_of_term_in ctxt t2 in
      Format.sprintf "(%s, %s)" t1_str t2_str
  | TFun b ->
      let b_str = string_of_staged_spec_binder_in ctxt b in
      Format.sprintf "(\\%s)" b_str
  | TMetavar _ ->
      "<tmetavar>"

and string_of_state_in (_ctxt : ctxt) = function
  | StState ->
      "<ststate>"
  | StMetavar _ ->
      "<stmetavar>"

and string_of_staged_spec_in (ctxt : ctxt) = function
  | Return t ->
      let t_str = string_of_term_in ctxt t in
      Format.sprintf "return %s" t_str
  | Ensures st ->
      let st_str = string_of_state_in ctxt st in
      Format.sprintf "ensures %s" st_str
  | Sequence (s1, s2) ->
      let s1_str = string_of_staged_spec_in ctxt s1 in
      let s2_str = string_of_staged_spec_in ctxt s2 in
      Format.sprintf "(%s; %s)" s1_str s2_str
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
  | Dollar (s, k) ->
      let s_str = string_of_staged_spec_in ctxt s in
      let k_str = string_of_staged_spec_binder_in ctxt k in
      Format.sprintf "dollar (%s, %s)" s_str k_str
  | SMetavar _ ->
      "<smetavar>"

and string_of_staged_spec_binder_in (ctxt : ctxt) = function
  | Ignore s ->
      let s_str = string_of_staged_spec_in ctxt s in
      Format.sprintf "_. %s" s_str
  | Binder b ->
      let x, s, ctxt = unbind_in ctxt b in
      let x_str = name_of x in
      let s_str = string_of_staged_spec_in ctxt s in
      Format.sprintf "%s. %s" x_str s_str
  | SBMetavar _ ->
      "<sbmetavar>"

let string_of_staged_spec = string_of_staged_spec_in empty_ctxt
let string_of_staged_spec_binder = string_of_staged_spec_binder_in empty_ctxt
