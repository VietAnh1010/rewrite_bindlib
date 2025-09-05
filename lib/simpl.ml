(* an evaluator for staged_spec *)

open Syntax
open Bindlib
open Binders
open Constructors

let identity_cont =
  let x = new_tvar "x" in
  unbox (mk_binder (bind_var x (mk_return (mk_tvar x))))

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
  | TPair (t1, t2) ->
      let t1 = simpl_term t1 in
      let t2 = simpl_term t2 in
      TPair (t1, t2)
  | TFun b ->
      let b = simpl_staged_spec_binder b in
      TFun b
  | TMetavar _ ->
      assert false

and simpl_state (st : state) : state =
  st

and simpl_staged_spec (s : staged_spec) : staged_spec =
  (* Format.printf "[simpl_staged_spec] s := %s\n" (Pretty.string_of_staged_spec s); *)
  match s with
  | Return t ->
      let t = simpl_term t in
      Return t
  | Ensures st ->
      let st = simpl_state st in
      Ensures st
  | Sequence (s1, s2) ->
      simpl_staged_spec_cont ~delimited:false s1 (simpl_staged_spec_binder (Ignore s2))
  | Bind (s, b) ->
      simpl_staged_spec_cont ~delimited:false s (simpl_staged_spec_binder b)
      (* let s = simpl_staged_spec s in
      let b = simpl_staged_spec_binder b in
      begin
        match s with
        | Return t -> simpl_staged_spec (subst_binder b t)
        | _ -> Bind (s, b)
      end *)
  | Apply (f, t) ->
      let f = simpl_term f in
      let t = simpl_term t in
      begin
        match f with
        | TFun b -> simpl_staged_spec (subst_binder b t)
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
      simpl_staged_spec_cont ~delimited:true s identity_cont
  | Dollar (s, cont) ->
      simpl_staged_spec_cont ~delimited:true s cont
  | SMetavar _ ->
      assert false

and simpl_staged_spec_binder (b : staged_spec_binder) : staged_spec_binder =
  match b with
  | Ignore s ->
      let s = simpl_staged_spec s in
      Ignore s
  | Binder b ->
      let x, s = unbind b in
      let b = unbox (bind_var x (box_staged_spec (simpl_staged_spec s))) in
      Binder b
  | SBMetavar _ ->
      assert false

and simpl_staged_spec_cont ~(delimited : bool) (s : staged_spec) (cont : staged_spec_binder) : staged_spec =
  (* Format.printf "[simpl_staged_spec_cont] s := %s | cont := %s\n"
    (Pretty.string_of_staged_spec s)
    (Pretty.string_of_staged_spec_binder cont); *)
  match s with
  | Return t ->
      simpl_staged_spec (subst_binder cont t)
  | Ensures st ->
      let st = simpl_state st in
      let cont = simpl_staged_spec (subst_binder cont TUnit) in
      Sequence (Ensures st, cont)
  | Sequence (s1, s2) ->
      simpl_staged_spec_cont ~delimited s1 (simpl_staged_spec_binder_cont ~delimited (Ignore s2) cont)
  | Bind (s, b) ->
      simpl_staged_spec_cont ~delimited s (simpl_staged_spec_binder_cont ~delimited b cont)
  | Apply (f, t) ->
      let f = simpl_term f in
      let t = simpl_term t in
      begin
        match f with
        | TFun b -> simpl_staged_spec_cont ~delimited (subst_binder b t) cont
        | _ -> prepend_binder ~delimited cont (Apply (f, t))
      end
  | Disjunct (s1, s2) ->
      let s1 = simpl_staged_spec_cont ~delimited s1 cont in
      let s2 = simpl_staged_spec_cont ~delimited s2 cont in
      Disjunct (s1, s2)
  | Exists b ->
      let b = simpl_staged_spec_binder_cont ~delimited b cont in
      Exists b
  | Shift b ->
      if delimited then
        simpl_staged_spec_cont ~delimited (subst_binder b (TFun cont)) identity_cont
      else
        let b = simpl_staged_spec_binder b in
        prepend_binder ~delimited cont (Shift b)
  | Reset s ->
      simpl_staged_spec_cont ~delimited (simpl_staged_spec_cont ~delimited:true s identity_cont) cont
  | Dollar (s, k) ->
      simpl_staged_spec_cont ~delimited (simpl_staged_spec_cont ~delimited:true s k) cont
  | SMetavar _ ->
      assert false

and simpl_staged_spec_binder_cont ~(delimited : bool) (b : staged_spec_binder) (cont : staged_spec_binder) : staged_spec_binder =
  match b with
  | Ignore s ->
      let s = simpl_staged_spec_cont ~delimited s cont in
      Ignore s
  | Binder b ->
      let x, s = unbind b in
      let b = unbox (bind_var x (box_staged_spec (simpl_staged_spec_cont ~delimited s cont))) in
      Binder b
  | SBMetavar _ ->
      assert false
