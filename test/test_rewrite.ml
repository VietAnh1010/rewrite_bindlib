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
  mk_bind (mk_smetavar s')
    (mk_binder (bind_var r (mk_apply (mk_tfun (mk_sbmetavar b')) (mk_tvar r))))

let ex1_rhs = unbox ex1_rhs_box
let ex1_rule = {lhs = ex1_lhs; rhs = Static ex1_rhs}

let ex1_target_box =
  mk_bind
    (mk_return (mk_tint 1))
    (mk_binder (bind_var x (mk_return (mk_tpair (mk_tvar x) (mk_tbool true)))))

let ex1_target = unbox ex1_target_box

let%expect_test "rewrite_staged_spec with static rules" =
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
      { {lhs = (?s; ?b); rhs = (?s; r. (\?b) r)} }
      { (return 1; x. return (x, true)) }
      >>> rewrite_staged_spec >>>
      (return 1; r. (\x. return (x, true)) r)
      |}]
  in
  ()
