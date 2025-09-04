(* an evaluator for staged_spec *)

open Syntax
open Bindlib

let rec simpl_term (t : term) : term =
  match t with
  | TVar _ ->
      t
  | TUnit ->
      t
  | TBool _ ->
      t
  | TInt _ ->
      t
  | TFun b ->
      let b = simpl_staged_spec_binder b in
      TFun b
  | TMetavar _ ->
      t

and simpl_state (st : state) : state =
  st

and simpl_staged_spec (s : staged_spec) : staged_spec =
  match s with
  | Return t ->
      Return (simpl_term t)
  | Ensures st ->
      Ensures (simpl_state st)
  | Sequence (s1, s2) ->
      let s1 = simpl_staged_spec s1 in
      let s2 = simpl_staged_spec s2 in
      begin
        match s1 with
        | Return _ -> s2
        | _ -> Sequence (s1, s2)
      end
  | Bind (s, b) ->
      let s = simpl_staged_spec s in
      let b = simpl_staged_spec_binder b in
      begin
        match s, b with
        | Return t, Binder b -> simpl_staged_spec (subst b t)
        | _ -> Bind (s, b)
      end
  | Apply (f, t) ->
      let f = simpl_term f in
      let t = simpl_term t in
      begin
        match f with
        | TFun (Binder b) -> simpl_staged_spec (subst b t)
        | _ -> Apply (f, t)
      end
  | Disjunct (s1, s2) ->
      let s1 = simpl_staged_spec s1 in
      let s2 = simpl_staged_spec s2 in
      Disjunct (s1, s2)
  | Exists b ->
      let b = simpl_staged_spec_binder b in
      Exists b
  | Shift b ->
      let b = simpl_staged_spec_binder b in
      Shift b
  | Reset s ->
      let s = simpl_staged_spec s in
      Reset s
  | Dollar (s, cont) ->
      let s = simpl_staged_spec s in
      let cont = simpl_staged_spec_binder cont in
      Dollar (s, cont)
  | SMetavar _ ->
      s

and simpl_staged_spec_binder (b : staged_spec_binder) : staged_spec_binder =
  match b with
  | Binder b ->
      let x, s = unbind b in
      let b = unbox (bind_var x (Constructors.box_staged_spec (simpl_staged_spec s))) in
      Binder b
  | SBMetavar _ ->
      b
