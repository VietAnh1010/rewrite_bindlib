open Bindlib
open Syntax
open Pretty
open Sort
open Util
open Constructors

type uobj =
  | UOTerm of term
  | UOState of state
  | UOStagedSpec of staged_spec
  | UOStagedSpecBinder of staged_spec_binder

let sort_of_uobj = function
  | UOTerm _ -> Term
  | UOState _ -> State
  | UOStagedSpec _ -> StagedSpec
  | UOStagedSpecBinder _ -> StagedSpecBinder

let string_of_uobj_sort uobj = string_of_sort (sort_of_uobj uobj)

let invalid_uobj_sort ~expected uobj =
  invalid_sort
    (Format.sprintf "expected sort %s, got %s" (string_of_sort expected)
       (string_of_uobj_sort uobj))

let uobj_of_term t = UOTerm t
let uobj_of_state st = UOState st
let uobj_of_staged_spec s = UOStagedSpec s
let uobj_of_staged_spec_binder b = UOStagedSpecBinder b

let term_of_uobj = function
  | UOTerm t -> t
  | uobj -> invalid_uobj_sort ~expected:Term uobj

let state_of_uobj = function
  | UOState st -> st
  | uobj -> invalid_uobj_sort ~expected:State uobj

let staged_spec_of_uobj = function
  | UOStagedSpec s -> s
  | uobj -> invalid_uobj_sort ~expected:StagedSpec uobj

let staged_spec_binder_of_uobj = function
  | UOStagedSpecBinder b -> b
  | uobj -> invalid_uobj_sort ~expected:StagedSpecBinder uobj

module Subst = struct
  type t = uobj MetavarMap.t

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
  let to_string _sigma = Format.sprintf "%s" "[]"
end

exception Unification_failure

let rec unify_term_aux (sigma : Subst.t) (t1 : term) (t2 : term) : Subst.t =
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
      match Subst.find_term_opt mv sigma with
      | None -> Subst.add_term mv t sigma
      | Some t' -> unify_term_aux sigma t t'
    end
  | _, _ -> raise Unification_failure

and unify_state_aux (sigma : Subst.t) (st1 : state) (st2 : state) : Subst.t =
  match st1, st2 with
  | StState, StState -> sigma
  | StMetavar _, StMetavar _ -> raise Unification_failure
  | StMetavar mv, st | st, StMetavar mv -> begin
      match Subst.find_state_opt mv sigma with
      | None -> Subst.add_state mv st sigma
      | Some st' -> unify_state_aux sigma st st'
    end

and unify_staged_spec_aux (sigma : Subst.t) (s1 : staged_spec)
    (s2 : staged_spec) : Subst.t =
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
      match Subst.find_staged_spec_opt mv sigma with
      | None -> Subst.add_staged_spec mv s sigma
      | Some s' -> unify_staged_spec_aux sigma s s'
    end
  | _, _ -> raise Unification_failure

and unify_staged_spec_binder_aux (sigma : Subst.t) (b1 : staged_spec_binder)
    (b2 : staged_spec_binder) : Subst.t =
  match b1, b2 with
  | Binder b1, Binder b2 ->
      let _, s1, s2 = unbind2 b1 b2 in
      unify_staged_spec_aux sigma s1 s2
  | Ignore s1, Ignore s2 -> unify_staged_spec_aux sigma s1 s2
  | SBMetavar _, SBMetavar _ -> raise Unification_failure
  | SBMetavar mv, b | b, SBMetavar mv -> begin
      match Subst.find_staged_spec_binder_opt mv sigma with
      | None -> Subst.add_staged_spec_binder mv b sigma
      | Some b' -> unify_staged_spec_binder_aux sigma b b'
    end
  | _, _ -> raise Unification_failure

let unify_term = unify_term_aux Subst.empty
let unify_state = unify_state_aux Subst.empty
let unify_staged_spec = unify_staged_spec_aux Subst.empty
let unify_staged_spec_binder = unify_staged_spec_binder_aux Subst.empty

exception Substitution_failure

let rec subst_term (sigma : Subst.t) (t : term) =
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
      match Subst.find_term_opt mv sigma with
      | None -> raise Substitution_failure
      | Some t -> t
    end

and subst_state (sigma : Subst.t) (st : state) =
  match st with
  | StState -> st
  | StMetavar mv -> begin
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
  | SMetavar mv -> begin
      match Subst.find_staged_spec_opt mv sigma with
      | None -> raise Substitution_failure
      | Some s -> s
    end

and subst_staged_spec_binder (sigma : Subst.t) (b : staged_spec_binder) =
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
      match Subst.find_staged_spec_binder_opt mv sigma with
      | None -> raise Substitution_failure
      | Some b -> b
    end

type ('ctxt, 'a) rule_rhs = Static of 'a | Dynamic of (Subst.t -> 'ctxt -> 'a)
type ('ctxt, 'a) rule = {lhs : 'a; rhs : ('ctxt, 'a) rule_rhs}

let string_of_rule_rhs to_string = function
  | Static rhs -> to_string rhs
  | Dynamic _ -> "<dynamic>"

let string_of_rule to_string {lhs; rhs} =
  Format.sprintf "{lhs = %s; rhs = %s}" (to_string lhs)
    (string_of_rule_rhs to_string rhs)

type 'ctxt urule =
  | URTerm of ('ctxt, term) rule
  | URState of ('ctxt, state) rule
  | URStagedSpec of ('ctxt, staged_spec) rule
  | URStagedSpecBinder of ('ctxt, staged_spec_binder) rule

let sort_of_urule = function
  | URTerm _ -> Term
  | URState _ -> State
  | URStagedSpec _ -> StagedSpec
  | URStagedSpecBinder _ -> StagedSpecBinder

let string_of_urule_sort rule = string_of_sort (sort_of_urule rule)

exception Rewrite_failure of exn

let rewrite_failure exn = raise (Rewrite_failure exn)

module RewriteExact = struct
  let rewrite_with unify subst {lhs; rhs} ctxt target =
    try
      let sigma = unify lhs target in
      match rhs with
      | Static rhs -> subst sigma rhs
      | Dynamic rhs -> rhs sigma ctxt
    with exn -> rewrite_failure exn

  let rewrite_term rule = rewrite_with unify_term subst_term rule
  let rewrite_state rule = rewrite_with unify_state subst_state rule

  let rewrite_staged_spec rule =
    rewrite_with unify_staged_spec subst_staged_spec rule

  let rewrite_staged_spec_binder rule =
    rewrite_with unify_staged_spec_binder subst_staged_spec_binder rule
end

module RewriteAll = struct
  open RewriteExact

  type ('ctxt, 'a) rewriter = {
    rw_term : ('ctxt, 'a, term) rewriter_method;
    rw_state : ('ctxt, 'a, state) rewriter_method;
    rw_staged_spec : ('ctxt, 'a, staged_spec) rewriter_method;
    rw_staged_spec_binder : ('ctxt, 'a, staged_spec_binder) rewriter_method;
  }

  and ('ctxt, 'a, 'b) rewriter_method =
    ('ctxt, 'a) rewriter -> ('ctxt, 'a) rule -> 'ctxt -> 'b -> 'b

  let rw_with rewrite rw self rule ctxt target =
    try rewrite rule ctxt target
    with Rewrite_failure _ -> rw self rule ctxt target

  module AbstractRewriter = struct
    let rw_term self rule ctxt t =
      match t with
      | TVar _ -> t
      | TSymbol _ -> t
      | TUnit -> t
      | TBool _ -> t
      | TInt _ -> t
      | TPair (t1, t2) ->
          let t1 = self.rw_term self rule ctxt t1 in
          let t2 = self.rw_term self rule ctxt t2 in
          TPair (t1, t2)
      | TFun b ->
          let b = self.rw_staged_spec_binder self rule ctxt b in
          TFun b
      | TMetavar _ -> t

    let rw_state _ _ _ st =
      match st with
      | StState -> st
      | StMetavar _ -> st

    let rw_staged_spec self rule ctxt s =
      match s with
      | Return t ->
          let t = self.rw_term self rule ctxt t in
          Return t
      | Ensures st ->
          let st = self.rw_state self rule ctxt st in
          Ensures st
      | Sequence (s1, s2) ->
          let s1 = self.rw_staged_spec self rule ctxt s1 in
          let s2 = self.rw_staged_spec self rule ctxt s2 in
          Sequence (s1, s2)
      | Bind (s, b) ->
          let s = self.rw_staged_spec self rule ctxt s in
          let b = self.rw_staged_spec_binder self rule ctxt b in
          Bind (s, b)
      | Apply (f, t) ->
          let f = self.rw_term self rule ctxt f in
          let t = self.rw_term self rule ctxt t in
          Apply (f, t)
      | Disjunct (s1, s2) ->
          let s1 = self.rw_staged_spec self rule ctxt s1 in
          let s2 = self.rw_staged_spec self rule ctxt s2 in
          Disjunct (s1, s2)
      | Exists b ->
          let b = self.rw_staged_spec_binder self rule ctxt b in
          Exists b
      | Shift b ->
          let b = self.rw_staged_spec_binder self rule ctxt b in
          Shift b
      | Reset s ->
          let s = self.rw_staged_spec self rule ctxt s in
          Reset s
      | Dollar (s, k) ->
          let s = self.rw_staged_spec self rule ctxt s in
          let k = self.rw_staged_spec_binder self rule ctxt k in
          Dollar (s, k)
      | SMetavar _ -> s

    let rw_staged_spec_binder self rule ctxt b =
      match b with
      | Binder b ->
          let x, s = unbind b in
          let s = self.rw_staged_spec self rule ctxt s in
          let b = unbox (bind_var x (box_staged_spec s)) in
          Binder b
      | Ignore s ->
          let s = self.rw_staged_spec self rule ctxt s in
          Ignore s
      | SBMetavar _ -> b

    let rewriter = {rw_term; rw_state; rw_staged_spec; rw_staged_spec_binder}
  end

  module type ConcreteRewriter = sig
    type t

    val rw_term : ('ctxt, t, term) rewriter_method
    val rw_state : ('ctxt, t, state) rewriter_method
    val rw_staged_spec : ('ctxt, t, staged_spec) rewriter_method
    val rw_staged_spec_binder : ('ctxt, t, staged_spec_binder) rewriter_method
    val rewriter : ('ctxt, t) rewriter
  end

  module TermRewriter = struct
    include AbstractRewriter

    type t = term

    let rw_term self = rw_with rewrite_term rw_term self
    let rewriter = {rewriter with rw_term}
  end

  module StateRewriter = struct
    include AbstractRewriter

    type t = state

    let rw_state self = rw_with rewrite_state rw_state self
    let rewriter = {rewriter with rw_state}
  end

  module StagedSpecRewriter = struct
    include AbstractRewriter

    type t = staged_spec

    let rw_staged_spec self = rw_with rewrite_staged_spec rw_staged_spec self
    let rewriter = {rewriter with rw_staged_spec}
  end

  module StagedSpecBinderRewriter = struct
    include AbstractRewriter

    type t = staged_spec_binder

    let rw_staged_spec_binder self =
      rw_with rewrite_staged_spec_binder rw_staged_spec_binder self

    let rewriter = {rewriter with rw_staged_spec_binder}
  end

  module Make (T : ConcreteRewriter) = struct
    type t = T.t

    open T

    let rewrite_term rule = rw_term rewriter rule
    let rewrite_state rule = rw_state rewriter rule
    let rewrite_staged_spec rule = rw_staged_spec rewriter rule
    let rewrite_staged_spec_binder rule = rw_staged_spec_binder rewriter rule
  end

  module Term = Make (TermRewriter)
  module State = Make (StateRewriter)
  module StagedSpec = Make (StagedSpecRewriter)
  module StagedSpecBinder = Make (StagedSpecBinderRewriter)
end
