open Bindlib

type meta =
  { m_name : string }

type symbol =
  { s_name : string }

type term =
  | TVar of term var
  | TSymbol of symbol
  | TUnit
  | TBool of bool
  | TInt of int
  | TPair of term * term
  | TFun of staged_spec_binder
  | TMetavar of meta

and state =
  | StState
  | StMetavar of meta

and staged_spec =
  | Return of term
  | Ensures of state
  | Sequence of staged_spec * staged_spec
  | Bind of staged_spec * staged_spec_binder
  | Apply of term * term
  | Disjunct of staged_spec * staged_spec
  | Exists of staged_spec_binder
  | Shift of staged_spec_binder
  | Reset of staged_spec
  | Dollar of staged_spec * staged_spec_binder
  | SMetavar of meta

and staged_spec_binder =
  | Ignore of staged_spec
  | Binder of (term, staged_spec) binder
  | SBMetavar of meta

type sort =
  | Term
  | State
  | StagedSpec
  | StagedSpecBinder

module Constructors = struct
  let new_tvar = new_var (fun v -> TVar v)

  let mk_tvar = box_var
  let mk_tsymbol s = box (TSymbol s)
  let mk_tunit = box TUnit
  let mk_tbool b = box (TBool b)
  let mk_tint i = box (TInt i)
  let mk_tpair = box_apply2 (fun t1 t2 -> TPair (t1, t2))
  let mk_tfun = box_apply (fun b -> TFun b)
  let mk_tmetavar m = box (TMetavar m)

  let mk_ststate = box StState
  let mk_stmetavar m = box (StMetavar m)

  let mk_return = box_apply (fun t -> Return t)
  let mk_ensures = box_apply (fun st -> Ensures st)
  let mk_sequence = box_apply2 (fun s1 s2 -> Sequence (s1, s2))
  let mk_bind = box_apply2 (fun s b -> Bind (s, b))
  let mk_apply = box_apply2 (fun f t -> Apply (f, t))
  let mk_disjunct = box_apply2 (fun s1 s2 -> Disjunct (s1, s2))
  let mk_exists = box_apply (fun b -> Exists b)
  let mk_shift = box_apply (fun b -> Shift b)
  let mk_reset = box_apply (fun s -> Reset s)
  let mk_dollar = box_apply2 (fun s k -> Dollar (s, k))
  let mk_smetavar m = box (SMetavar m)

  let mk_ignore = box_apply (fun s -> Ignore s)
  let mk_binder = box_apply (fun b -> Binder b)
  let mk_sbmetavar m = box (SBMetavar m)

  let rec box_term = function
    | TVar x -> mk_tvar x
    | TSymbol s -> mk_tsymbol s
    | TUnit -> mk_tunit
    | TBool b -> mk_tbool b
    | TInt i -> mk_tint i
    | TPair (t1, t2) -> mk_tpair (box_term t1) (box_term t2)
    | TFun b -> mk_tfun (box_staged_spec_binder b)
    | TMetavar m -> mk_tmetavar m

  and box_state = function
    | StState -> mk_ststate
    | StMetavar m -> mk_stmetavar m

  and box_staged_spec = function
    | Return t -> mk_return (box_term t)
    | Ensures st -> mk_ensures (box_state st)
    | Sequence (s1, s2) -> mk_sequence (box_staged_spec s1) (box_staged_spec s2)
    | Bind (s, b) -> mk_bind (box_staged_spec s) (box_staged_spec_binder b)
    | Apply (f, t) -> mk_apply (box_term f) (box_term t)
    | Disjunct (s1, s2) -> mk_disjunct (box_staged_spec s1) (box_staged_spec s2)
    | Exists b -> mk_exists (box_staged_spec_binder b)
    | Shift b -> mk_shift (box_staged_spec_binder b)
    | Reset s -> mk_reset (box_staged_spec s)
    | Dollar (s, k) -> mk_dollar (box_staged_spec s) (box_staged_spec_binder k)
    | SMetavar m -> mk_smetavar m

  and box_staged_spec_binder = function
    | Ignore s -> mk_ignore (box_staged_spec s)
    | Binder b -> mk_binder (box_binder box_staged_spec b)
    | SBMetavar m -> mk_sbmetavar m
end

module StagedSpecBinder = struct
  let subst (b : staged_spec_binder) (t : term) : staged_spec =
    match b with
    | Ignore s -> s
    | Binder b -> subst b t
    | SBMetavar _ -> assert false

  let prepend ~(delimited : bool) (b : staged_spec_binder) (s : staged_spec) : staged_spec =
    if delimited then
      Dollar (s, b)
    else
      match b with
      | Ignore s' -> Sequence (s, s')
      | Binder _ -> Bind (s, b)
      | SBMetavar _ -> assert false
end

module Meta = struct
  type t = meta
  let equal (m1 : t) (m2 : t) = String.equal m1.m_name m2.m_name
  let compare (m1 : t) (m2 : t) = String.compare m1.m_name m2.m_name
  let hash (m : t) = String.hash m.m_name
end

module Symbol = struct
  type t = symbol
  let equal (s1 : t) (s2 : t) = String.equal s1.s_name s2.s_name
  let compare (s1 : t) (s2 : t) = String.compare s1.s_name s2.s_name
  let hash (s : t) = String.hash s.s_name
end

module Sort = struct
  exception Invalid_sort of string

  let invalid_sort msg = raise (Invalid_sort msg)
end
