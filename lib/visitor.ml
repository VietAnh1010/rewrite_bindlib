open Bindlib
open Syntax
open Constructors

class virtual ['self] abstract_map_visitor =
  object (self : 'self)
    method visit_term t =
      match t with
      | TVar x -> self#visit_TVar x
      | TSymbol s -> self#visit_TSymbol s
      | TUnit -> self#visit_TUnit
      | TBool b -> self#visit_TBool b
      | TInt i -> self#visit_TInt i
      | TPair (t1, t2) -> self#visit_TPair t1 t2
      | TFun b -> self#visit_TFun b
      | TMetavar mv -> self#visit_TMetavar mv

    method visit_TVar x = TVar x
    method visit_TSymbol s = TSymbol s
    method visit_TUnit = TUnit
    method visit_TBool b = TBool b
    method visit_TInt i = TInt i

    method visit_TPair t1 t2 =
      let t1 = self#visit_term t1 in
      let t2 = self#visit_term t2 in
      TPair (t1, t2)

    method visit_TFun b =
      let b = self#visit_staged_spec_binder b in
      TFun b

    method visit_TMetavar mv = TMetavar mv

    method visit_state st =
      match st with
      | StState -> self#visit_StState
      | StMetavar mv -> self#visit_StMetavar mv

    method visit_StState = StState
    method visit_StMetavar mv = StMetavar mv

    method visit_staged_spec s =
      match s with
      | Return t -> self#visit_Return t
      | Ensures st -> self#visit_Ensures st
      | Sequence (s1, s2) -> self#visit_Sequence s1 s2
      | Bind (s, b) -> self#visit_Bind s b
      | Apply (f, t) -> self#visit_Apply f t
      | Disjunct (s1, s2) -> self#visit_Disjunct s1 s2
      | Exists b -> self#visit_Exists b
      | Shift b -> self#visit_Shift b
      | Reset s -> self#visit_Reset s
      | Dollar (s, k) -> self#visit_Dollar s k
      | SMetavar mv -> self#visit_SMetavar mv

    method visit_Return t =
      let t = self#visit_term t in
      Return t

    method visit_Ensures st =
      let st = self#visit_state st in
      Ensures st

    method visit_Sequence s1 s2 =
      let s1 = self#visit_staged_spec s1 in
      let s2 = self#visit_staged_spec s2 in
      Sequence (s1, s2)

    method visit_Bind s b =
      let s = self#visit_staged_spec s in
      let b = self#visit_staged_spec_binder b in
      Bind (s, b)

    method visit_Apply f t =
      let f = self#visit_term f in
      let t = self#visit_term t in
      Apply (f, t)

    method visit_Disjunct s1 s2 =
      let s1 = self#visit_staged_spec s1 in
      let s2 = self#visit_staged_spec s2 in
      Disjunct (s1, s2)

    method visit_Exists b =
      let b = self#visit_staged_spec_binder b in
      Exists b

    method visit_Shift b =
      let b = self#visit_staged_spec_binder b in
      Shift b

    method visit_Reset s =
      let s = self#visit_staged_spec s in
      Reset s

    method visit_Dollar s k =
      let s = self#visit_staged_spec s in
      let k = self#visit_staged_spec_binder k in
      Dollar (s, k)

    method visit_SMetavar mv = SMetavar mv

    method visit_staged_spec_binder b =
      match b with
      | Ignore s -> self#visit_Ignore s
      | Binder b -> self#visit_Binder b
      | SBMetavar mv -> self#visit_SBMetavar mv

    method visit_Ignore s =
      let s = self#visit_staged_spec s in
      Ignore s

    method visit_Binder b =
      let x, s = unbind b in
      let s = self#visit_staged_spec s in
      let b = unbox (bind_var x (box_staged_spec s)) in
      Binder b

    method visit_SBMetavar mv = SBMetavar mv
  end
