open Bindlib

type meta =
  | Meta

type term =
  | TVar of term var
  | TTerm
  | TMetavar of meta

type state =
  | State

and staged_spec =
  | Return of term
  | Ensures of state
  | Bind of staged_spec * (term, staged_spec) binder
  | Apply of term * term
  | Disjunct of staged_spec * staged_spec
  | Exists of (term, staged_spec) binder
  (* | Forall of (term, staged_spec) binder *)
  | Reset of staged_spec * (term, staged_spec) binder
  | Shift of (term, staged_spec) binder
  (* | StagedVar of staged_spec var *)
  | SMetavar of meta

module Constructors = struct
  let new_tvar = new_var (fun v -> TVar v)

  let mk_tvar = box_var
  let mk_tterm = box TTerm
  let mk_tmetavar = box_apply (fun m -> TMetavar m)

  let mk_state = box State

  let mk_meta = box Meta

  let mk_return = box_apply (fun t -> Return t)
  let mk_ensures = box_apply (fun st -> Ensures st)
  let mk_bind = box_apply2 (fun s b -> Bind (s, b))
  let mk_apply = box_apply2 (fun f t -> Apply (f, t))
  let mk_disjunct = box_apply2 (fun s1 s2 -> Disjunct (s1, s2))
  let mk_exists = box_apply (fun b -> Exists b)
  (* let forall = box_apply (fun b -> Forall b) *)
  let mk_reset = box_apply2 (fun s cont -> Reset (s, cont))
  let mk_shift = box_apply (fun b -> Shift b)
  let mk_smetavar = box_apply (fun m -> SMetavar m)

  let box_meta = function
    | Meta -> mk_meta

  let box_term = function
    | TVar x -> mk_tvar x
    | TTerm -> mk_tterm
    | TMetavar m -> mk_tmetavar (box_meta m)

  let box_state = function
    | State -> mk_state

  let rec box_staged_spec = function
    | Return t -> mk_return (box_term t)
    | Ensures st -> mk_ensures (box_state st)
    | Bind (s, b) -> mk_bind (box_staged_spec s) (box_binder box_staged_spec b)
    | Apply (f, t) -> mk_apply (box_term f) (box_term t)
    | Disjunct (s1, s2) -> mk_disjunct (box_staged_spec s1) (box_staged_spec s2)
    | Exists b -> mk_exists (box_binder box_staged_spec b)
    | Reset (s, cont) -> mk_reset (box_staged_spec s) (box_binder box_staged_spec cont)
    | Shift b -> mk_shift (box_binder box_staged_spec b)
    | SMetavar m -> mk_smetavar (box_meta m)
end

module Examples = struct
  open Constructors

  (* representation of ret t; \f. ret t; \v. apply f(v) *)
  let ex1_box =
    let f = new_tvar "f" in
    let v = new_tvar "v" in
    mk_bind
      (mk_return mk_tterm)
      (bind_var f
        (mk_bind
          (mk_return mk_tterm)
          (bind_var v
            (mk_apply (mk_tvar f) (mk_tvar v)))))

  let ex1 = unbox ex1_box
end
