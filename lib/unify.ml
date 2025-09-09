open Bindlib
open Syntax
open Subst

exception Unification_failure

let rec unify_term_aux (sigma : subst) (t1 : term) (t2 : term) : subst =
  match t1, t2 with
  | TVar x1, TVar x2 when eq_vars x1 x2 -> sigma
  | TSymbol s1, TSymbol s2 when Symbol.equal s1 s2 -> sigma
  | TUnit, TUnit -> sigma
  | TBool b1, TBool b2 when b1 = b2 -> sigma
  | TInt i1, TInt i2 when i1 = i2 -> sigma
  | TPair (t11, t12), TPair (t21, t22) ->
      let sigma = unify_term_aux sigma t11 t21 in
      let sigma = unify_term_aux sigma t12 t22 in
      sigma
  | TFun b1, TFun b2 -> unify_staged_spec_binder_aux sigma b1 b2
  | TMetavar _, TMetavar _ -> raise Unification_failure
  | TMetavar mv, t | t, TMetavar mv -> begin
      match find_term_opt mv sigma with
      | None -> add_term mv t sigma
      | Some t' -> unify_term_aux sigma t t'
    end
  | _, _ -> raise Unification_failure

and unify_state_aux (sigma : subst) (st1 : state) (st2 : state) : subst =
  match st1, st2 with
  | StState, StState -> sigma
  | StMetavar _, StMetavar _ -> raise Unification_failure
  | StMetavar mv, st | st, StMetavar mv -> begin
      match find_state_opt mv sigma with
      | None -> add_state mv st sigma
      | Some st' -> unify_state_aux sigma st st'
    end

and unify_staged_spec_aux (sigma : subst) (s1 : staged_spec) (s2 : staged_spec)
    : subst =
  match s1, s2 with
  | Return t1, Return t2 -> unify_term_aux sigma t1 t2
  | Ensures st1, Ensures st2 -> unify_state_aux sigma st1 st2
  | Sequence (s11, s12), Sequence (s21, s22) ->
      let sigma = unify_staged_spec_aux sigma s11 s21 in
      let sigma = unify_staged_spec_aux sigma s12 s22 in
      sigma
  | Bind (s1, b1), Bind (s2, b2) ->
      let sigma = unify_staged_spec_aux sigma s1 s2 in
      let sigma = unify_staged_spec_binder_aux sigma b1 b2 in
      sigma
  | Apply (t11, t12), Apply (t21, t22) ->
      let sigma = unify_term_aux sigma t11 t21 in
      let sigma = unify_term_aux sigma t12 t22 in
      sigma
  | Disjunct (s11, s12), Disjunct (s21, s22) ->
      let sigma = unify_staged_spec_aux sigma s11 s21 in
      let sigma = unify_staged_spec_aux sigma s12 s22 in
      sigma
  | Exists b1, Exists b2 -> unify_staged_spec_binder_aux sigma b1 b2
  | Shift b1, Shift b2 -> unify_staged_spec_binder_aux sigma b1 b2
  | Reset s1, Reset s2 -> unify_staged_spec_aux sigma s1 s2
  | Dollar (s1, k1), Dollar (s2, k2) ->
      let sigma = unify_staged_spec_aux sigma s1 s2 in
      let sigma = unify_staged_spec_binder_aux sigma k1 k2 in
      sigma
  | SMetavar _, SMetavar _ -> raise Unification_failure
  | SMetavar mv, s | s, SMetavar mv -> begin
      match find_staged_spec_opt mv sigma with
      | None -> add_staged_spec mv s sigma
      | Some s' -> unify_staged_spec_aux sigma s s'
    end
  | _, _ -> raise Unification_failure

and unify_staged_spec_binder_aux (sigma : subst) (b1 : staged_spec_binder)
    (b2 : staged_spec_binder) : subst =
  match b1, b2 with
  | Binder b1, Binder b2 ->
      let _, s1, s2 = unbind2 b1 b2 in
      unify_staged_spec_aux sigma s1 s2
  | Ignore s1, Ignore s2 -> unify_staged_spec_aux sigma s1 s2
  | SBMetavar _, SBMetavar _ -> raise Unification_failure
  | SBMetavar mv, b | b, SBMetavar mv -> begin
      match find_staged_spec_binder_opt mv sigma with
      | None -> add_staged_spec_binder mv b sigma
      | Some b' -> unify_staged_spec_binder_aux sigma b b'
    end
  | _, _ -> raise Unification_failure

let unify_term = unify_term_aux empty
let unify_state = unify_state_aux empty
let unify_staged_spec = unify_staged_spec_aux empty
let unify_staged_spec_binder = unify_staged_spec_binder_aux empty
