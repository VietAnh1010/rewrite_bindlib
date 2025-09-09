open Bindlib
open Rewrite_bindlib
open Syntax
open Constructors
open Pretty
open Metavars
open Subst
open Unify

let ex1_lhs_box = mk_sequence (mk_smetavar s') (mk_return (mk_tmetavar t'))

let ex1_rhs_box =
  mk_sequence
    (mk_apply (mk_tsymbol {s_name = "f"}) (mk_tint 10))
    (mk_return (mk_tint 69))

let ex1_lhs = unbox ex1_lhs_box
let ex1_rhs = unbox ex1_rhs_box

let%expect_test "unify_staged_spec" =
  let test_unify_staged_spec (s1 : staged_spec) (s2 : staged_spec) =
    let sigma = unify_staged_spec s1 s2 in
    Format.printf
      {|
      { %s }
      { %s }
      >>> unify_staged_spec >>>
      %s
      |}
      (string_of_staged_spec s1) (string_of_staged_spec s2)
      (string_of_subst sigma)
  in
  let () =
    test_unify_staged_spec ex1_lhs ex1_rhs;
    [%expect
      {|
      { (?s; return ?t) }
      { (f 10; return 69) }
      >>> unify_staged_spec >>>
      []
      |}]
  in
  ()
