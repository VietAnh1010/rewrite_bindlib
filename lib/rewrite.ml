open Bindlib
open Syntax
open Pretty
open Constructors
open Subst
open Unify

type ('ctxt, 'a) rule_rhs = Static of 'a | Dynamic of (subst -> 'ctxt -> 'a)
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

exception Rewrite_failure

(* let rewrite_failure exn = raise (Rewrite_failure exn) *)

module RewriteExact = struct
  let rewrite_with unify subst {lhs; rhs} ctxt target =
    try
      let sigma = unify lhs target in
      match rhs with
      | Static rhs -> subst sigma rhs
      | Dynamic rhs -> rhs sigma ctxt
    with _ -> raise Rewrite_failure

  let rewrite_term rule = rewrite_with unify_term subst_term rule
  let rewrite_state rule = rewrite_with unify_state subst_state rule

  let rewrite_staged_spec rule =
    rewrite_with unify_staged_spec subst_staged_spec rule

  let rewrite_staged_spec_binder rule =
    rewrite_with unify_staged_spec_binder subst_staged_spec_binder rule
end

module type Core = sig
  module M : Monad.S

  module Transformer : sig
    val lift_rewrite :
      ('rule -> 'ctxt -> 'a -> 'a) -> 'rule -> 'ctxt -> 'a -> 'a M.t

    val wrap_rw :
      ('self -> 'rule -> 'ctxt -> 'a -> 'a M.t) ->
      'self ->
      'rule ->
      'ctxt ->
      'a ->
      'a M.t

    val wrap_rewrite :
      ('rule -> 'ctxt -> 'a -> 'a M.t) -> 'rule -> 'ctxt -> 'a -> 'a
  end
end

module Make (C : Core) = struct
  include C

  type ('ctxt, 'a) rewriter = {
    rw_term : ('ctxt, 'a, term) rewriter_method;
    rw_state : ('ctxt, 'a, state) rewriter_method;
    rw_staged_spec : ('ctxt, 'a, staged_spec) rewriter_method;
    rw_staged_spec_binder : ('ctxt, 'a, staged_spec_binder) rewriter_method;
  }

  and ('ctxt, 'a, 'b) rewriter_method =
    ('ctxt, 'a) rewriter -> ('ctxt, 'a) rule -> 'ctxt -> 'b -> 'b M.t

  module Transformer = struct
    include Transformer

    let rw_with rewrite rw self rule ctxt target =
      try lift_rewrite rewrite rule ctxt target
      with Rewrite_failure -> rw self rule ctxt target
  end

  module Visitor = struct
    open M
    open LetSyntax

    let rw_term self rule ctxt t =
      match t with
      | TVar _ -> return t
      | TSymbol _ -> return t
      | TUnit -> return t
      | TBool _ -> return t
      | TInt _ -> return t
      | TPair (t1, t2) ->
          let+ t1 = self.rw_term self rule ctxt t1
          and+ t2 = self.rw_term self rule ctxt t2 in
          TPair (t1, t2)
      | TFun b ->
          let+ b = self.rw_staged_spec_binder self rule ctxt b in
          TFun b
      | TMetavar _ -> return t

    let rw_state _ _ _ st =
      match st with
      | StState -> return st
      | StMetavar _ -> return st

    let rw_staged_spec self rule ctxt s =
      match s with
      | Return t ->
          let+ t = self.rw_term self rule ctxt t in
          Return t
      | Ensures st ->
          let+ st = self.rw_state self rule ctxt st in
          Ensures st
      | Sequence (s1, s2) ->
          let+ s1 = self.rw_staged_spec self rule ctxt s1
          and+ s2 = self.rw_staged_spec self rule ctxt s2 in
          Sequence (s1, s2)
      | Bind (s, b) ->
          let+ s = self.rw_staged_spec self rule ctxt s
          and+ b = self.rw_staged_spec_binder self rule ctxt b in
          Bind (s, b)
      | Apply (f, t) ->
          let+ f = self.rw_term self rule ctxt f
          and+ t = self.rw_term self rule ctxt t in
          Apply (f, t)
      | Disjunct (s1, s2) ->
          let+ s1 = self.rw_staged_spec self rule ctxt s1
          and+ s2 = self.rw_staged_spec self rule ctxt s2 in
          Disjunct (s1, s2)
      | Exists b ->
          let+ b = self.rw_staged_spec_binder self rule ctxt b in
          Exists b
      | Shift b ->
          let+ b = self.rw_staged_spec_binder self rule ctxt b in
          Shift b
      | Reset s ->
          let+ s = self.rw_staged_spec self rule ctxt s in
          Reset s
      | Dollar (s, k) ->
          let+ s = self.rw_staged_spec self rule ctxt s
          and+ k = self.rw_staged_spec_binder self rule ctxt k in
          Dollar (s, k)
      | SMetavar _ -> return s

    let rw_staged_spec_binder self rule ctxt b =
      match b with
      | Binder b ->
          let x, s = unbind b in
          let+ s = self.rw_staged_spec self rule ctxt s in
          let b = unbox (bind_var x (box_staged_spec s)) in
          Binder b
      | Ignore s ->
          let+ s = self.rw_staged_spec self rule ctxt s in
          Ignore s
      | SBMetavar _ -> return b
  end

  open Transformer
  open Visitor
  open RewriteExact

  module BaseRewriter = struct
    let rw_term self = wrap_rw rw_term self
    let rw_state self = wrap_rw rw_state self
    let rw_staged_spec self = wrap_rw rw_staged_spec self
    let rw_staged_spec_binder self = wrap_rw rw_staged_spec_binder self
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
    include BaseRewriter

    type t = term

    let rw_term self = wrap_rw (rw_with rewrite_term Visitor.rw_term) self
    let rewriter = {rewriter with rw_term}
  end

  module StateRewriter = struct
    include BaseRewriter

    type t = state

    let rw_state self = wrap_rw (rw_with rewrite_state Visitor.rw_state) self
    let rewriter = {rewriter with rw_state}
  end

  module StagedSpecRewriter = struct
    include BaseRewriter

    type t = staged_spec

    let rw_staged_spec self =
      wrap_rw (rw_with rewrite_staged_spec Visitor.rw_staged_spec) self

    let rewriter = {rewriter with rw_staged_spec}
  end

  module StagedSpecBinderRewriter = struct
    include BaseRewriter

    type t = staged_spec_binder

    let rw_staged_spec_binder self =
      wrap_rw
        (rw_with rewrite_staged_spec_binder Visitor.rw_staged_spec_binder)
        self

    let rewriter = {rewriter with rw_staged_spec_binder}
  end

  module Tie (R : ConcreteRewriter) = struct
    open R
    open Transformer

    let rewrite_term rule = wrap_rewrite (rw_term rewriter) rule
    let rewrite_state rule = wrap_rewrite (rw_state rewriter) rule
    let rewrite_staged_spec rule = wrap_rewrite (rw_staged_spec rewriter) rule

    let rewrite_staged_spec_binder rule =
      wrap_rewrite (rw_staged_spec_binder rewriter) rule
  end

  module Term = Tie (TermRewriter)
  module State = Tie (StateRewriter)
  module StagedSpec = Tie (StagedSpecRewriter)
  module StagedSpecBinder = Tie (StagedSpecBinderRewriter)
end

module RewriteAll = Make (struct
  module M = Monad.Identity

  module Transformer = struct
    let wrap_rw rw = rw

    let lift_rewrite rewrite rule ctxt target =
      M.return (rewrite rule ctxt target)

    let wrap_rewrite rewrite rule ctxt target = M.run (rewrite rule ctxt target)
  end
end)

module RewriteFirst = Make (struct
  module M = Monad.State (Bool)

  module Transformer = struct
    open M.LetSyntax

    let lift_rewrite rewrite rule ctxt target =
      let result = rewrite rule ctxt target in
      let+ _ = M.put true in
      result

    let wrap_rw rw self rule ctxt target =
      let* applied = M.get in
      if applied then M.return target else rw self rule ctxt target

    let wrap_rewrite rewrite rule ctxt target =
      let result, applied = M.run (rewrite rule ctxt target) false in
      if applied then result else raise Rewrite_failure
  end
end)
