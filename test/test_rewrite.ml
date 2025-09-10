open Bindlib
open Rewrite_bindlib
open Syntax
open Pretty
open Rewrite
open Constructors
open Vars
open Metavars

let ex1_lhs_box = mk_bind (mk_smetavar s') (mk_sbmetavar b')
let ex1_lhs = unbox ex1_lhs_box

let ex1_rhs_box =
  mk_sequence (mk_smetavar s') (mk_apply (mk_tfun (mk_sbmetavar b')) mk_tunit)

let ex1_rhs = unbox ex1_rhs_box
let ex1_rule = {lhs = ex1_lhs; rhs = Static ex1_rhs}

let ex1_target_box =
  mk_bind (mk_ensures mk_ststate)
    (mk_binder (bind_var x (mk_return (mk_tpair (mk_tvar x) (mk_tbool true)))))

let ex1_target = unbox ex1_target_box

let ex2_lhs_box =
  mk_sequence (mk_sequence (mk_smetavar s') (mk_smetavar t')) (mk_smetavar u')

let ex2_lhs = unbox ex2_lhs_box

let ex2_rhs_box =
  mk_sequence (mk_smetavar s') (mk_sequence (mk_smetavar t') (mk_smetavar u'))

let ex2_rhs = unbox ex2_rhs_box
let ex2_rule = {lhs = ex2_lhs; rhs = Static ex2_rhs}

let ex2_target_box =
  mk_sequence
    (mk_sequence
       (mk_sequence
          (mk_sequence (mk_return (mk_tint 1)) (mk_return (mk_tint 2)))
          (mk_return (mk_tint 3)))
       (mk_return (mk_tint 4)))
    (mk_return (mk_tint 5))

let ex2_target = unbox ex2_target_box
let ex3_rule = ex2_rule

let ex3_target_box =
  mk_bind
    (mk_reset (mk_return (mk_tint 10)))
    (mk_binder
       (bind_var x
          (mk_sequence
             (mk_sequence (mk_return (mk_tint 2)) (mk_return (mk_tint 3)))
             (mk_return (mk_tint 4)))))

let ex3_target = unbox ex3_target_box
let ex4_lhs_box = mk_sequence (mk_ensures mk_ststate) (mk_smetavar s')
let ex4_lhs = unbox ex4_lhs_box
let ex4_rhs_box = mk_ensures mk_ststate
let ex4_rhs = unbox ex4_rhs_box
let ex4_rule = {lhs = ex4_lhs; rhs = Static ex4_rhs}

let ex4_target_box =
  mk_sequence
    (mk_sequence
       (mk_sequence
          (mk_sequence (mk_ensures mk_ststate) (mk_return (mk_tint 1)))
          (mk_return (mk_tint 2)))
       (mk_return (mk_tint 3)))
    (mk_return (mk_tint 4))

let ex4_target = unbox ex4_target_box

let%expect_test "RewriteAll.rewrite_staged_spec (static)" =
  let open RewriteAll in
  let open StagedSpec in
  let test_rewrite_staged_spec rule target =
    let result = rewrite_staged_spec rule () target in
    Format.printf
      {|
      { %s }
      { %s }
      >>> rewrite_staged_spec >>>
      %s
      |}
      (string_of_rule string_of_staged_spec rule)
      (string_of_staged_spec target)
      (string_of_staged_spec result)
  in
  let () =
    test_rewrite_staged_spec ex1_rule ex1_target;
    [%expect
      {|
      { {lhs = (?s; ?b); rhs = (?s; (\?b) ())} }
      { (ensures <ststate>; x. return (x, true)) }
      >>> rewrite_staged_spec >>>
      (ensures <ststate>; (\x. return (x, true)) ())
      |}]
  in
  let () =
    test_rewrite_staged_spec ex2_rule ex2_target;
    [%expect
      {|
      { {lhs = ((?s; ?t); ?u); rhs = (?s; (?t; ?u))} }
      { ((((return 1; return 2); return 3); return 4); return 5) }
      >>> rewrite_staged_spec >>>
      (return 1; (return 2; (return 3; (return 4; return 5))))
      |}]
  in
  let () =
    test_rewrite_staged_spec ex3_rule ex3_target;
    [%expect
      {|
      { {lhs = ((?s; ?t); ?u); rhs = (?s; (?t; ?u))} }
      { (reset (return 10); x. ((return 2; return 3); return 4)) }
      >>> rewrite_staged_spec >>>
      (reset (return 10); x. (return 2; (return 3; return 4)))
      |}]
  in
  let () =
    test_rewrite_staged_spec ex4_rule ex4_target;
    [%expect
      {|
      { {lhs = (ensures <ststate>; ?s); rhs = ensures <ststate>} }
      { ((((ensures <ststate>; return 1); return 2); return 3); return 4) }
      >>> rewrite_staged_spec >>>
      ensures <ststate>
      |}]
  in
  ()

let%expect_test "RewriteFirst.rewrite_staged_spec (static)" =
  let open RewriteFirst in
  let open StagedSpec in
  let test_rewrite_staged_spec rule target =
    let result = rewrite_staged_spec rule () target in
    Format.printf
      {|
      { %s }
      { %s }
      >>> rewrite_staged_spec >>>
      %s
      |}
      (string_of_rule string_of_staged_spec rule)
      (string_of_staged_spec target)
      (string_of_staged_spec result)
  in
  let () =
    test_rewrite_staged_spec ex1_rule ex1_target;
    [%expect
      {|
      { {lhs = (?s; ?b); rhs = (?s; (\?b) ())} }
      { (ensures <ststate>; x. return (x, true)) }
      >>> rewrite_staged_spec >>>
      (ensures <ststate>; (\x. return (x, true)) ())
      |}]
  in
  let () =
    test_rewrite_staged_spec ex2_rule ex2_target;
    [%expect
      {|
      { {lhs = ((?s; ?t); ?u); rhs = (?s; (?t; ?u))} }
      { ((((return 1; return 2); return 3); return 4); return 5) }
      >>> rewrite_staged_spec >>>
      (((return 1; return 2); return 3); (return 4; return 5))
      |}]
  in
  let () =
    test_rewrite_staged_spec ex3_rule ex3_target;
    [%expect
      {|
      { {lhs = ((?s; ?t); ?u); rhs = (?s; (?t; ?u))} }
      { (reset (return 10); x. ((return 2; return 3); return 4)) }
      >>> rewrite_staged_spec >>>
      (reset (return 10); x. (return 2; (return 3; return 4)))
      |}]
  in
  let () =
    test_rewrite_staged_spec ex4_rule ex4_target;
    [%expect
      {|
      { {lhs = (ensures <ststate>; ?s); rhs = ensures <ststate>} }
      { ((((ensures <ststate>; return 1); return 2); return 3); return 4) }
      >>> rewrite_staged_spec >>>
      (((ensures <ststate>; return 2); return 3); return 4)
      |}]
  in
  ()
