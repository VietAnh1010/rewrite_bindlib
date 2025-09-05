open Bindlib
open Syntax
open Constructors

module Vars = struct
  let f = new_tvar "f"
  let v = new_tvar "v"
  let x = new_tvar "x"
  let y = new_tvar "y"
  let i = new_tvar "i"
  let k = new_tvar "k"
  let g = new_tvar "g"
end

open Vars

let ex1_box =
  mk_bind
    (mk_return (mk_tvar k))
    (mk_binder
       (bind_var f
          (mk_bind (mk_return mk_tunit)
             (mk_binder (bind_var v (mk_apply (mk_tvar f) (mk_tvar v)))))))

let ex1 = unbox ex1_box

let ex2_box =
  mk_bind
    (mk_return (mk_tfun (mk_binder (bind_var x (mk_return (mk_tvar x))))))
    (mk_binder
       (bind_var f
          (mk_bind
             (mk_return (mk_tint 1))
             (mk_binder (bind_var v (mk_apply (mk_tvar f) (mk_tvar v)))))))

let ex2 = unbox ex2_box

let ex3_box =
  mk_reset
    (mk_sequence (mk_ensures mk_ststate)
       (mk_bind
          (mk_shift (mk_binder (bind_var k (mk_return (mk_tvar k)))))
          (mk_binder (bind_var x (mk_return (mk_tint 10))))))

let ex3 = unbox ex3_box

let ex4_box =
  mk_reset
    (mk_exists
       (mk_binder
          (bind_var i
             (mk_bind
                (mk_shift (mk_binder (bind_var k (mk_return (mk_tvar k)))))
                (mk_binder (bind_var x (mk_return (mk_tvar i))))))))

let ex4 = unbox ex4_box

let ex5_box =
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
             (mk_apply (mk_tvar f) (mk_tint 10))
             (mk_binder (bind_var f (mk_apply (mk_tvar f) (mk_tint 3)))))))

let ex5 = unbox ex5_box

let ex6_box =
  mk_reset
    (mk_bind
       (mk_shift
          (mk_binder (bind_var k (mk_apply (mk_tvar k) (mk_tint 10)))))
       (mk_binder
          (bind_var x
             (mk_bind
                (mk_shift (mk_binder (bind_var k (mk_return (mk_tvar k)))))
                (mk_binder
                   (bind_var y
                      (mk_sequence
                         (mk_sequence (mk_ensures mk_ststate)
                            (mk_apply (mk_tvar f) mk_tunit))
                         (mk_return
                            (mk_tpair (mk_tvar x) (mk_tbool true))))))))))

let ex6 = unbox ex6_box

let ex7_box =
  mk_shift
    (mk_binder
       (bind_var k
          (mk_sequence
             (mk_return (mk_tbool true))
             (mk_apply (mk_tvar k) mk_tunit))))

let ex7 = unbox ex7_box

let ex8_box =
  mk_sequence
    (mk_sequence (mk_ensures mk_ststate) (mk_ensures mk_ststate))
    (mk_return (mk_tint 10))

let ex8 = unbox ex8_box
let ex9_box = mk_sequence ex7_box (mk_return (mk_tint 10))
let ex9 = unbox ex9_box

let ex10_box =
  mk_bind
    (mk_apply (mk_tvar f) mk_tunit)
    (mk_binder
       (bind_var x
          (mk_exists
             (mk_binder
                (bind_var y (mk_return (mk_tpair (mk_tvar x) (mk_tvar y))))))))

let ex10 = unbox ex10_box

let ex11_box =
  mk_bind
    (mk_apply (mk_tvar f) mk_tunit)
    (mk_binder
       (bind_var x
          (mk_disjunct
             (mk_return (mk_tint 10))
             (mk_return (mk_tint 42)))))

let ex11 = unbox ex11_box

let ex12_box =
  mk_bind
    (mk_disjunct
       (mk_sequence (mk_ensures mk_ststate) (mk_return (mk_tint 10)))
       (mk_return (mk_tint 42)))
    (mk_binder (bind_var x (mk_apply (mk_tvar f) (mk_tvar x))))

let ex12 = unbox ex12_box

let ex13_box =
  mk_bind
    (mk_bind
      (mk_apply (mk_tvar f) (mk_tunit))
      (mk_binder (bind_var x (mk_apply (mk_tvar k) (mk_tint 1)))))
    (mk_binder (bind_var y (mk_apply (mk_tvar g) (mk_tvar y))))

let ex13 = unbox ex13_box
