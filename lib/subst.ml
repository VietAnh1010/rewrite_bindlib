open Bindlib
open Syntax
open Constructors
open Util
open Uobj

type subst = uobj MetavarMap.t

let empty = MetavarMap.empty
let add = MetavarMap.add
let find_opt = MetavarMap.find_opt
let adds f mv t = add mv (f t)
let find_opts f mv sigma = Option.map f (find_opt mv sigma)
let add_term = adds uobj_of_term
let add_state = adds uobj_of_state
let add_staged_spec = adds uobj_of_staged_spec
let add_staged_spec_binder = adds uobj_of_staged_spec_binder
let find_term_opt = find_opts term_of_uobj
let find_state_opt = find_opts state_of_uobj
let find_staged_spec_opt = find_opts staged_spec_of_uobj
let find_staged_spec_binder_opt = find_opts staged_spec_binder_of_uobj
let string_of_subst _sigma = Format.sprintf "%s" "[]"

exception Substitution_failure

let rec subst_term (sigma : subst) (t : term) =
  match t with
  | TVar _ -> t
  | TSymbol _ -> t
  | TUnit -> t
  | TBool _ -> t
  | TInt _ -> t
  | TPair (t1, t2) ->
      let t1 = subst_term sigma t1 in
      let t2 = subst_term sigma t2 in
      TPair (t1, t2)
  | TFun b ->
      let b = subst_staged_spec_binder sigma b in
      TFun b
  | TMetavar mv -> begin
      match find_term_opt mv sigma with
      | None -> raise Substitution_failure
      | Some t -> t
    end

and subst_state (sigma : subst) (st : state) =
  match st with
  | StState -> st
  | StMetavar mv -> begin
      match find_state_opt mv sigma with
      | None -> raise Substitution_failure
      | Some st -> st
    end

and subst_staged_spec (sigma : subst) (s : staged_spec) =
  match s with
  | Return t ->
      let t = subst_term sigma t in
      Return t
  | Ensures st ->
      let st = subst_state sigma st in
      Ensures st
  | Sequence (s1, s2) ->
      let s1 = subst_staged_spec sigma s1 in
      let s2 = subst_staged_spec sigma s2 in
      Sequence (s1, s2)
  | Bind (s, b) ->
      let s = subst_staged_spec sigma s in
      let b = subst_staged_spec_binder sigma b in
      Bind (s, b)
  | Apply (f, t) ->
      let f = subst_term sigma f in
      let t = subst_term sigma t in
      Apply (f, t)
  | Disjunct (s1, s2) ->
      let s1 = subst_staged_spec sigma s1 in
      let s2 = subst_staged_spec sigma s2 in
      Sequence (s1, s2)
  | Exists b ->
      let b = subst_staged_spec_binder sigma b in
      Exists b
  | Shift b ->
      let b = subst_staged_spec_binder sigma b in
      Shift b
  | Reset s ->
      let s = subst_staged_spec sigma s in
      Reset s
  | Dollar (s, k) ->
      let s = subst_staged_spec sigma s in
      let k = subst_staged_spec_binder sigma k in
      Dollar (s, k)
  | SMetavar mv -> begin
      match find_staged_spec_opt mv sigma with
      | None -> raise Substitution_failure
      | Some s -> s
    end

and subst_staged_spec_binder (sigma : subst) (b : staged_spec_binder) =
  match b with
  | Binder b ->
      let x, s = unbind b in
      let s = subst_staged_spec sigma s in
      let b = unbox (bind_var x (box_staged_spec s)) in
      Binder b
  | Ignore s ->
      let s = subst_staged_spec sigma s in
      Ignore s
  | SBMetavar mv -> begin
      match find_staged_spec_binder_opt mv sigma with
      | None -> raise Substitution_failure
      | Some b -> b
    end
