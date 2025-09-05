open Bindlib
open Rewrite_bindlib
open Syntax
open Pretty
open Rewrite
open Constructors

let ex1_lhs_box =
  mk_sequence (mk_smetavar {m_name = "S"}) (mk_return (mk_tmetavar {m_name = "T"}))

let ex1_rhs_box =
  mk_sequence (mk_apply (mk_tsymbol {s_name = "f"}) (mk_tint 10)) (mk_return (mk_tint 69))

let ex1_lhs = unbox ex1_lhs_box
let ex1_rhs = unbox ex1_rhs_box

let%expect_test "unify_staged_spec" =
  let test_unify_staged_spec (s1 : staged_spec) (s2 : staged_spec) =
    Format.printf
      {|
        { %s }
        { %s }
        >>> unify_staged_spec >>>
        %s
      |}
      (string_of_staged_spec s1)
      (string_of_staged_spec s2)
      (Subst.to_string (unify_staged_spec s1 s2 Subst.empty))
  in
  let () =
    test_unify_staged_spec ex1_lhs ex1_rhs;
    [%expect{|
      { (?S; return ?T) }
      { (f 10; return 69) }
      >>> unify_staged_spec >>>
      []
      |}]
  in
  ()
