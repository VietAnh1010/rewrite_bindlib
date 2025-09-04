open Bindlib

type meta =
  | Meta

type term =
  | TVar of term var
  | TUnit
  | TBool of bool
  | TInt of int
  | TLambda of staged_spec_binder
  | TMetavar of meta

and state =
  | STState
  | STMetavar of meta

and staged_spec =
  | Return of term
  | Ensures of state
  | Bind of staged_spec * staged_spec_binder
  | Apply of term * term
  | Disjunct of staged_spec * staged_spec
  | Exists of staged_spec_binder
  (* | Forall of (term, staged_spec) binder *)
  | Shift of staged_spec_binder
  | Reset of staged_spec
  | Dollar of staged_spec * staged_spec_binder
  | SMetavar of meta

and staged_spec_binder =
  | Binder of (term, staged_spec) binder
  | SBMetavar of meta

module Constructors = struct
  let new_tvar = new_var (fun v -> TVar v)

  let mk_tvar = box_var
  let mk_tunit = box TUnit
  let mk_tbool = box_apply (fun b -> TBool b)
  let mk_tint = box_apply (fun i -> TInt i)
  let mk_tlambda = box_apply (fun b -> TLambda b)
  let mk_tmetavar = box_apply (fun m -> TMetavar m)

  let mk_state = box STState
  let mk_stmetavar = box_apply (fun m -> STMetavar m)

  let mk_meta = box Meta

  let mk_return = box_apply (fun t -> Return t)
  let mk_ensures = box_apply (fun st -> Ensures st)
  let mk_bind = box_apply2 (fun s b -> Bind (s, b))
  let mk_apply = box_apply2 (fun f t -> Apply (f, t))
  let mk_disjunct = box_apply2 (fun s1 s2 -> Disjunct (s1, s2))
  let mk_exists = box_apply (fun b -> Exists b)
  (* let forall = box_apply (fun b -> Forall b) *)
  let mk_shift = box_apply (fun b -> Shift b)
  let mk_reset = box_apply (fun s -> Reset s)
  let mk_dollar = box_apply2 (fun s cont -> Dollar (s, cont))
  let mk_smetavar = box_apply (fun m -> SMetavar m)

  let mk_binder = box_apply (fun b -> Binder b)
  let mk_sbmetavar = box_apply (fun m -> SBMetavar m)

  let box_meta = function
    | Meta -> mk_meta

  let rec box_term = function
    | TVar x -> mk_tvar x
    | TUnit -> mk_tunit
    | TBool b -> mk_tbool (box b)
    | TInt i -> mk_tint (box i)
    | TLambda b -> mk_tlambda (box_staged_spec_binder b)
    | TMetavar m -> mk_tmetavar (box_meta m)

  and box_state = function
    | STState -> mk_state
    | STMetavar m -> mk_stmetavar (box_meta m)

  and box_staged_spec = function
    | Return t -> mk_return (box_term t)
    | Ensures st -> mk_ensures (box_state st)
    | Bind (s, b) -> mk_bind (box_staged_spec s) (box_staged_spec_binder b)
    | Apply (f, t) -> mk_apply (box_term f) (box_term t)
    | Disjunct (s1, s2) -> mk_disjunct (box_staged_spec s1) (box_staged_spec s2)
    | Exists b -> mk_exists (box_staged_spec_binder b)
    | Shift b -> mk_shift (box_staged_spec_binder b)
    | Reset s -> mk_reset (box_staged_spec s)
    | Dollar (s, cont) -> mk_dollar (box_staged_spec s) (box_staged_spec_binder cont)
    | SMetavar m -> mk_smetavar (box_meta m)

  and box_staged_spec_binder = function
    | Binder b -> mk_binder (box_binder box_staged_spec b)
    | SBMetavar m -> mk_sbmetavar (box_meta m)
end

module Examples = struct
  open Constructors

  let ex1_box =
    let f = new_tvar "f" in
    let v = new_tvar "v" in
    mk_bind
      (mk_return mk_tunit)
      (mk_binder
        (bind_var f
          (mk_bind
            (mk_return mk_tunit)
            (mk_binder
              (bind_var v
              (mk_apply (mk_tvar f) (mk_tvar v)))))))

  let ex1 = unbox ex1_box
end
