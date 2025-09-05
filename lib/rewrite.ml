open Bindlib
open Syntax
open Pretty
open Sort
open Util
open Constructors

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

  type t = uobj MetavarMap.t

  let empty = MetavarMap.empty

  let add = MetavarMap.add
  let adds f mv t = add mv (f t)
  let add_term = adds (fun t -> UTerm t)
  let add_state = adds (fun st -> UState st)
  let add_staged_spec = adds (fun s -> UStagedSpec s)
  let add_staged_spec_binder = adds (fun b -> UStagedSpecBinder b)

  let find_opt = MetavarMap.find_opt
  let find_opts f mv sigma = Option.map f (find_opt mv sigma)
  let find_term_opt = find_opts term_of_uobj
  let find_state_opt = find_opts state_of_uobj
  let find_staged_spec_opt = find_opts staged_spec_of_uobj
  let find_staged_spec_binder_opt = find_opts staged_spec_binder_of_uobj

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
  | TMetavar mv, t
  | t, TMetavar mv ->
      begin
        match Subst.find_term_opt mv sigma with
        | None -> Subst.add_term mv t sigma
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
  | StMetavar mv, st
  | st, StMetavar mv ->
      begin
        match Subst.find_state_opt mv sigma with
        | None -> Subst.add_state mv st sigma
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
  | SMetavar mv, s
  | s, SMetavar mv ->
      begin
        match Subst.find_staged_spec_opt mv sigma with
        | None -> Subst.add_staged_spec mv s sigma
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
  | SBMetavar mv, b
  | b, SBMetavar mv ->
      begin
        match Subst.find_staged_spec_binder_opt mv sigma with
        | None -> Subst.add_staged_spec_binder mv b sigma
        | Some b' -> unify_staged_spec_binder b b' sigma
      end
  | _, _ ->
      raise Unification_failure

exception Substitution_failure

let rec subst_term (sigma : Subst.t) (t : term) =
  match t with
  | TVar _ ->
      t
  | TSymbol _ ->
      t
  | TUnit ->
      t
  | TBool _ ->
      t
  | TInt _ ->
      t
  | TPair (t1, t2) ->
      let t1 = subst_term sigma t1 in
      let t2 = subst_term sigma t2 in
      TPair (t1, t2)
  | TFun b ->
      let b = subst_staged_spec_binder sigma b in
      TFun b
  | TMetavar mv ->
      begin
        match Subst.find_term_opt mv sigma with
        | None -> raise Substitution_failure
        | Some t -> t
      end

and subst_state (sigma : Subst.t) (st : state) =
  match st with
  | StState ->
      st
  | StMetavar mv ->
      begin
        match Subst.find_state_opt mv sigma with
        | None -> raise Substitution_failure
        | Some st -> st
      end

and subst_staged_spec (sigma : Subst.t) (s : staged_spec) =
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
  | SMetavar mv ->
      begin
        match Subst.find_staged_spec_opt mv sigma with
        | None -> raise Substitution_failure
        | Some s -> s
      end

and subst_staged_spec_binder (sigma : Subst.t) (b : staged_spec_binder) =
  match b with
  | Ignore s ->
      let s = subst_staged_spec sigma s in
      Ignore s
  | Binder b ->
      let x, s = unbind b in
      let s = subst_staged_spec sigma s in
      let b = unbox (bind_var x (box_staged_spec s)) in
      Binder b
  | SBMetavar mv ->
      begin
        match Subst.find_staged_spec_binder_opt mv sigma with
        | None -> raise Substitution_failure
        | Some b -> b
      end
