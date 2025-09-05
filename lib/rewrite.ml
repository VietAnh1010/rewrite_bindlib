open Bindlib
open Syntax
open Pretty
open Sort
open Util

type rule =
  | RTerm of term rule_desc
  | RState of state rule_desc
  | RStagedSpec of staged_spec rule_desc
  | RStagedSpecBinder of staged_spec_binder rule_desc

and 'a rule_desc =
  { lhs : 'a; rhs : 'a rule_desc_rhs }

and 'a rule_desc_rhs =
  | Static of 'a
  | Dynamic of unit

module Subst = struct

  type uobj =
    | UTerm of term
    | UState of state
    | UStagedSpec of staged_spec
    | UStagedSpecBinder of staged_spec_binder

  let sort_of_uobj = function
    | UTerm _ -> Term
    | UState _ -> State
    | UStagedSpec _ -> StagedSpec
    | UStagedSpecBinder _ -> StagedSpecBinder

  let string_of_uobj_sort obj = string_of_sort (sort_of_uobj obj)

  let invalid_uobj_sort ~expected obj =
    invalid_sort (Format.sprintf "expected sort %s, got %s" (string_of_sort expected) (string_of_uobj_sort obj))

  let term_of_uobj = function
    | UTerm t -> t
    | obj -> invalid_uobj_sort ~expected:Term obj

  let state_of_uobj = function
    | UState st -> st
    | obj -> invalid_uobj_sort ~expected:State obj

  let staged_spec_of_uobj = function
    | UStagedSpec s -> s
    | obj -> invalid_uobj_sort ~expected:StagedSpec obj

  let staged_spec_binder_of_uobj = function
    | UStagedSpecBinder b -> b
    | obj -> invalid_uobj_sort ~expected:StagedSpecBinder obj

  type t = uobj MetaMap.t

  let empty = MetaMap.empty

  let add = MetaMap.add
  let add_term m t = add m (UTerm t)
  let add_state m st = add m (UState st)
  let add_staged_spec m s = add m (UStagedSpec s)
  let add_staged_spec_binder m b = add m (UStagedSpecBinder b)

  let find_opt = MetaMap.find_opt
  let find_term_opt m sigma = Option.map term_of_uobj (find_opt m sigma)
  let find_state_opt m sigma = Option.map state_of_uobj (find_opt m sigma)
  let find_staged_spec_opt m sigma = Option.map staged_spec_of_uobj (find_opt m sigma)
  let find_staged_spec_binder_opt m sigma = Option.map staged_spec_binder_of_uobj (find_opt m sigma)

  let to_string _sigma = Format.sprintf "%s" "[]"
end

exception Unification_failure

let rec unify_term (t1 : term) (t2 : term) (sigma : Subst.t) : Subst.t =
  match t1, t2 with
  | TVar x1, TVar x2 when eq_vars x1 x2 ->
      sigma
  | TSymbol s1, TSymbol s2 when Symbol.equal s1 s2 ->
      sigma
  | TUnit, TUnit ->
      sigma
  | TBool b1, TBool b2 when b1 = b2 ->
      sigma
  | TInt i1, TInt i2 when i1 = i2 ->
      sigma
  | TPair (t11, t12), TPair (t21, t22) ->
      let sigma = unify_term t11 t21 sigma in
      let sigma = unify_term t12 t22 sigma in
      sigma
  | TFun b1, TFun b2 ->
      unify_staged_spec_binder b1 b2 sigma
  | TMetavar _, TMetavar _ ->
      raise Unification_failure
  | TMetavar m, t
  | t, TMetavar m ->
      begin
        match Subst.find_term_opt m sigma with
        | None -> Subst.add_term m t sigma
        | Some t' -> unify_term t t' sigma
      end
  | _, _ ->
      raise Unification_failure

and unify_state (st1 : state) (st2 : state) (sigma : Subst.t) : Subst.t =
  match st1, st2 with
  | StState, StState ->
      sigma
  | StMetavar _, StMetavar _ ->
      raise Unification_failure
  | StMetavar m, st
  | st, StMetavar m ->
      begin
        match Subst.find_state_opt m sigma with
        | None -> Subst.add_state m st sigma
        | Some st' -> unify_state st st' sigma
      end

and unify_staged_spec (s1 : staged_spec) (s2 : staged_spec) (sigma : Subst.t) : Subst.t =
  match s1, s2 with
  | Return t1, Return t2 ->
      unify_term t1 t2 sigma
  | Ensures st1, Ensures st2 ->
      unify_state st1 st2 sigma
  | Sequence (s11, s12), Sequence (s21, s22) ->
      let sigma = unify_staged_spec s11 s21 sigma in
      let sigma = unify_staged_spec s12 s22 sigma in
      sigma
  | Bind (s1, b1), Bind (s2, b2) ->
      let sigma = unify_staged_spec s1 s2 sigma in
      let sigma = unify_staged_spec_binder b1 b2 sigma in
      sigma
  | Apply (t11, t12), Apply (t21, t22) ->
      let sigma = unify_term t11 t21 sigma in
      let sigma = unify_term t12 t22 sigma in
      sigma
  | Disjunct (s11, s12), Disjunct (s21, s22) ->
      let sigma = unify_staged_spec s11 s21 sigma in
      let sigma = unify_staged_spec s12 s22 sigma in
      sigma
  | Exists b1, Exists b2 ->
      unify_staged_spec_binder b1 b2 sigma
  | Shift b1, Shift b2 ->
      unify_staged_spec_binder b1 b2 sigma
  | Reset s1, Reset s2 ->
      unify_staged_spec s1 s2 sigma
  | Dollar (s1, k1), Dollar (s2, k2) ->
      let sigma = unify_staged_spec s1 s2 sigma in
      let sigma = unify_staged_spec_binder k1 k2 sigma in
      sigma
  | SMetavar _, SMetavar _ ->
      raise Unification_failure
  | SMetavar m, s
  | s, SMetavar m ->
      begin
        match Subst.find_staged_spec_opt m sigma with
        | None -> Subst.add_staged_spec m s sigma
        | Some s' -> unify_staged_spec s s' sigma
      end
  | _, _ ->
      raise Unification_failure

and unify_staged_spec_binder (b1 : staged_spec_binder) (b2 : staged_spec_binder) (sigma : Subst.t) : Subst.t =
  match b1, b2 with
  | Ignore s1, Ignore s2 ->
      unify_staged_spec s1 s2 sigma
  | Binder b1, Binder b2 ->
      let _, s1, s2 = unbind2 b1 b2 in
      unify_staged_spec s1 s2 sigma
  | SBMetavar _, SBMetavar _ ->
      raise Unification_failure
  | SBMetavar m, b
  | b, SBMetavar m ->
      begin
        match Subst.find_staged_spec_binder_opt m sigma with
        | None -> Subst.add_staged_spec_binder m b sigma
        | Some b' -> unify_staged_spec_binder b b' sigma
      end
  | _, _ ->
      raise Unification_failure
