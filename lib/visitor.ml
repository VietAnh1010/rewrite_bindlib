open Bindlib
open Syntax
open Constructors

class virtual ['self] abstract_map_visitor =
  object (self : 'self)
    method visit_term env t =
      match t with
      | TVar x -> self#visit_TVar env x
      | TSymbol s -> self#visit_TSymbol env s
      | TUnit -> self#visit_TUnit env
      | TBool b -> self#visit_TBool env b
      | TInt i -> self#visit_TInt env i
      | TPair (t1, t2) -> self#visit_TPair env t1 t2
      | TFun b -> self#visit_TFun env b
      | TMetavar mv -> self#visit_TMetavar env mv

    method visit_TVar _ x = TVar x
    method visit_TSymbol _ s = TSymbol s
    method visit_TUnit _ = TUnit
    method visit_TBool _ b = TBool b
    method visit_TInt _ i = TInt i

    method visit_TPair env t1 t2 =
      let t1 = self#visit_term env t1 in
      let t2 = self#visit_term env t2 in
      TPair (t1, t2)

    method visit_TFun env b =
      let b = self#visit_staged_spec_binder env b in
      TFun b

    method visit_TMetavar _ mv = TMetavar mv

    method visit_state env st =
      match st with
      | StState -> self#visit_StState env
      | StMetavar mv -> self#visit_StMetavar env mv

    method visit_StState _ = StState
    method visit_StMetavar _ mv = StMetavar mv

    method visit_staged_spec env s =
      match s with
      | Return t -> self#visit_Return env t
      | Ensures st -> self#visit_Ensures env st
      | Sequence (s1, s2) -> self#visit_Sequence env s1 s2
      | Bind (s, b) -> self#visit_Bind env s b
      | Apply (f, t) -> self#visit_Apply env f t
      | Disjunct (s1, s2) -> self#visit_Disjunct env s1 s2
      | Exists b -> self#visit_Exists env b
      | Shift b -> self#visit_Shift env b
      | Reset s -> self#visit_Reset env s
      | Dollar (s, k) -> self#visit_Dollar env s k
      | SMetavar mv -> self#visit_SMetavar env mv

    method visit_Return env t =
      let t = self#visit_term env t in
      Return t

    method visit_Ensures env st =
      let st = self#visit_state env st in
      Ensures st

    method visit_Sequence env s1 s2 =
      let s1 = self#visit_staged_spec env s1 in
      let s2 = self#visit_staged_spec env s2 in
      Sequence (s1, s2)

    method visit_Bind env s b =
      let s = self#visit_staged_spec env s in
      let b = self#visit_staged_spec_binder env b in
      Bind (s, b)

    method visit_Apply env f t =
      let f = self#visit_term env f in
      let t = self#visit_term env t in
      Apply (f, t)

    method visit_Disjunct env s1 s2 =
      let s1 = self#visit_staged_spec env s1 in
      let s2 = self#visit_staged_spec env s2 in
      Disjunct (s1, s2)

    method visit_Exists env b =
      let b = self#visit_staged_spec_binder env b in
      Exists b

    method visit_Shift env b =
      let b = self#visit_staged_spec_binder env b in
      Shift b

    method visit_Reset env s =
      let s = self#visit_staged_spec env s in
      Reset s

    method visit_Dollar env s k =
      let s = self#visit_staged_spec env s in
      let k = self#visit_staged_spec_binder env k in
      Dollar (s, k)

    method visit_SMetavar _ mv = SMetavar mv

    method visit_staged_spec_binder env b =
      match b with
      | Ignore s -> self#visit_Ignore env s
      | Binder b -> self#visit_Binder env b
      | SBMetavar mv -> self#visit_SBMetavar env mv

    method visit_Ignore env s =
      let s = self#visit_staged_spec env s in
      Ignore s

    method visit_Binder env b =
      let x, s = unbind b in
      let s = self#visit_staged_spec env s in
      let b = unbox (bind_var x (box_staged_spec s)) in
      Binder b

    method visit_SBMetavar _ mv = SBMetavar mv
  end
