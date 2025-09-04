open Bindlib

type meta =
  | Meta

type term =
  | TVar of term var
  | TUnit
  | TBool of bool
  | TInt of int
  | TPair of term * term
  | TFun of staged_spec_binder
  | TMetavar of meta

and state =
  | STState
  | STMetavar of meta

and staged_spec =
  | Return of term
  | Ensures of state
  | Sequence of staged_spec * staged_spec
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
  let mk_tpair = box_apply2 (fun t1 t2 -> TPair (t1, t2))
  let mk_tfun = box_apply (fun b -> TFun b)
  let mk_tmetavar = box_apply (fun m -> TMetavar m)

  let mk_ststate = box STState
  let mk_stmetavar = box_apply (fun m -> STMetavar m)

  let mk_meta = box Meta

  let mk_return = box_apply (fun t -> Return t)
  let mk_ensures = box_apply (fun st -> Ensures st)
  let mk_sequence = box_apply2 (fun s1 s2 -> Sequence (s1, s2))
  let mk_bind = box_apply2 (fun s b -> Bind (s, b))
  let mk_apply = box_apply2 (fun f t -> Apply (f, t))
  let mk_disjunct = box_apply2 (fun s1 s2 -> Disjunct (s1, s2))
  let mk_exists = box_apply (fun b -> Exists b)
  (* let forall = box_apply (fun b -> Forall b) *)
  let mk_shift = box_apply (fun b -> Shift b)
  let mk_reset = box_apply (fun s -> Reset s)
  let mk_dollar = box_apply2 (fun s k -> Dollar (s, k))
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
    | TPair (t1, t2) -> mk_tpair (box_term t1) (box_term t2)
    | TFun b -> mk_tfun (box_staged_spec_binder b)
    | TMetavar m -> mk_tmetavar (box_meta m)

  and box_state = function
    | STState -> mk_ststate
    | STMetavar m -> mk_stmetavar (box_meta m)

  and box_staged_spec = function
    | Return t -> mk_return (box_term t)
    | Ensures st -> mk_ensures (box_state st)
    | Sequence (s1, s2) -> mk_sequence (box_staged_spec s1) (box_staged_spec s2)
    | Bind (s, b) -> mk_bind (box_staged_spec s) (box_staged_spec_binder b)
    | Apply (f, t) -> mk_apply (box_term f) (box_term t)
    | Disjunct (s1, s2) -> mk_disjunct (box_staged_spec s1) (box_staged_spec s2)
    | Exists b -> mk_exists (box_staged_spec_binder b)
    | Shift b -> mk_shift (box_staged_spec_binder b)
    | Reset s -> mk_reset (box_staged_spec s)
    | Dollar (s, k) -> mk_dollar (box_staged_spec s) (box_staged_spec_binder k)
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
            (mk_binder (bind_var v (mk_apply (mk_tvar f) (mk_tvar v)))))))

  let ex1 = unbox ex1_box

  let ex2_box =
    let x = new_tvar "x" in
    let f = new_tvar "f" in
    let v = new_tvar "v" in
    mk_bind
      (mk_return (mk_tfun (mk_binder (bind_var x (mk_return (mk_tvar x))))))
      (mk_binder
        (bind_var f
          (mk_bind
            (mk_return (mk_tint (box 1)))
            (mk_binder (bind_var v (mk_apply (mk_tvar f) (mk_tvar v)))))))

  let ex2 = unbox ex2_box

  let ex3_box =
    let x = new_tvar "x" in
    let k = new_tvar "k" in
    mk_reset
      (mk_sequence
        (mk_ensures (mk_ststate))
        (mk_bind
          (mk_shift (mk_binder (bind_var k (mk_return (mk_tvar k)))))
          (mk_binder (bind_var x (mk_return (mk_tint (box 10)))))))

  let ex3 = unbox ex3_box

  let ex4_box =
    let i = new_tvar "i" in
    let x = new_tvar "x" in
    let k = new_tvar "k" in
    mk_reset
      (mk_exists
        (mk_binder
          (bind_var i
            (mk_bind
              (mk_shift (mk_binder (bind_var k (mk_return (mk_tvar k)))))
              (mk_binder (bind_var x (mk_return (mk_tvar i))))))))

  let ex4 = unbox ex4_box

  let ex5_box =
    let f = new_tvar "f" in
    let k = new_tvar "k" in
    let x = new_tvar "x" in
    let y = new_tvar "y" in
    mk_bind
      (mk_reset
        (mk_bind
          (mk_shift (mk_binder (bind_var k (mk_return (mk_tvar k)))))
          (mk_binder
            (bind_var x
              (mk_bind
                (mk_shift (mk_binder (bind_var k (mk_return (mk_tvar k)))))
                (mk_binder
                  (bind_var y
                    (mk_return (mk_tpair (mk_tvar x) (mk_tvar y))))))))))
      (mk_binder
        (bind_var f
          (mk_bind
            (mk_apply (mk_tvar f) (mk_tint (box 10)))
            (mk_binder
              (bind_var f
                (mk_apply (mk_tvar f) (mk_tint (box 3))))))))

  let ex5 = unbox ex5_box

  let ex6_box =
    let k = new_tvar "k" in
    let x = new_tvar "x" in
    let y = new_tvar "y" in
    let f = new_tvar "f" in
    mk_reset
      (mk_bind
        (mk_shift (mk_binder (bind_var k (mk_apply (mk_tvar k) (mk_tint (box 10))))))
        (mk_binder
          (bind_var x
            (mk_bind
              (mk_shift (mk_binder (bind_var k (mk_return (mk_tvar k)))))
              (mk_binder
                (bind_var y
                  (mk_sequence
                    (mk_sequence
                      (mk_ensures mk_ststate)
                      (mk_apply (mk_tvar f) mk_tunit))
                    (mk_return (mk_tpair (mk_tvar x) (mk_tbool (box true)))))))))))

  let ex6 = unbox ex6_box

  let ex7_box =
    let k = new_tvar "k" in
    mk_shift
      (mk_binder
        (bind_var k
          (mk_sequence
            (mk_return (mk_tbool (box true)))
            (mk_apply (mk_tvar k) mk_tunit))))

  let ex7 = unbox ex7_box

  let ex8_box =
    mk_sequence
      (mk_sequence
        (mk_ensures mk_ststate)
        (mk_ensures mk_ststate))
      (mk_return (mk_tint (box 10)))

  let ex8 = unbox ex8_box
end

module Binders = struct
  open Constructors

  let subst_binder (b : staged_spec_binder) (t : term) : staged_spec =
    match b with
    | Binder b -> subst b t
    | SBMetavar _ -> assert false

  let ignored_var = new_tvar "_"

  let mk_ignored_binder (s : staged_spec) : staged_spec_binder =
    unbox (mk_binder (bind_var ignored_var (box_staged_spec s)))
end
