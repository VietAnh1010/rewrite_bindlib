open Rewrite_bindlib
open Syntax
open Pretty
open Simpl

let%expect_test "simpl_staged_spec" =
  let test_simpl_staged_spec (s : staged_spec) =
    Format.printf
      {|
        %s
        >>> simpl_staged_spec >>>
        %s
      |}
      (string_of_staged_spec s)
      (string_of_staged_spec (simpl_staged_spec s))
  in
  let open Examples in
  let () =
    test_simpl_staged_spec ex1;
    [%expect
      {|
      (return k; f. (return (); v. f v))
      >>> simpl_staged_spec >>>
      k ()
      |}]
  in
  let () =
    test_simpl_staged_spec ex2;
    [%expect
      {|
      (return (\x. return x); f. (return 1; v. f v))
      >>> simpl_staged_spec >>>
      return 1
      |}]
  in
  let () =
    test_simpl_staged_spec ex3;
    [%expect
      {|
      reset ((ensures <ststate>; ((shift k. return k); x. return 10)))
      >>> simpl_staged_spec >>>
      (ensures <ststate>; return (\x. return 10))
      |}]
  in
  let () =
    test_simpl_staged_spec ex4;
    [%expect
      {|
      reset ((exists i. ((shift k. return k); x. return i)))
      >>> simpl_staged_spec >>>
      (exists i. return (\x. return i))
      |}]
  in
  let () =
    test_simpl_staged_spec ex5;
    [%expect
      {|
      (reset (((shift k. return k); x. ((shift k. return k); y. return (x, y)))); f. (f 10; f1. f1 3))
      >>> simpl_staged_spec >>>
      return (10, 3)
      |}]
  in
  let () =
    test_simpl_staged_spec ex6;
    [%expect
      {|
      reset (((shift k. k 10); x. ((shift k. return k); y. ((ensures <ststate>; f ()); return (x, true)))))
      >>> simpl_staged_spec >>>
      return (\y. (ensures <ststate>; dollar (f (), _. return (10, true))))
      |}]
  in
  let () =
    test_simpl_staged_spec ex7;
    [%expect
      {|
      (shift k. (return true; k ()))
      >>> simpl_staged_spec >>>
      (shift k. k ())
      |}]
  in
  let () =
    test_simpl_staged_spec ex8;
    [%expect
      {|
      ((ensures <ststate>; ensures <ststate>); return 10)
      >>> simpl_staged_spec >>>
      (ensures <ststate>; (ensures <ststate>; return 10))
      |}]
  in
  let () =
    test_simpl_staged_spec ex9;
    [%expect
      {|
      ((shift k. (return true; k ())); return 10)
      >>> simpl_staged_spec >>>
      ((shift k. k ()); return 10)
      |}]
  in
  let () =
    test_simpl_staged_spec ex10;
    [%expect
      {|
      (f (); x. (exists y. return (x, y)))
      >>> simpl_staged_spec >>>
      (f (); x. (exists y. return (x, y)))
      |}]
  in
  let () =
    test_simpl_staged_spec ex11;
    [%expect
      {|
      (f (); x. (return 10 \/ return 42))
      >>> simpl_staged_spec >>>
      (f (); x. (return 10 \/ return 42))
      |}]
  in
  let () =
    test_simpl_staged_spec ex12;
    [%expect
      {|
      (((ensures <ststate>; return 10) \/ return 42); x. f x)
      >>> simpl_staged_spec >>>
      ((ensures <ststate>; f 10) \/ f 42)
      |}]
  in
  let () =
    test_simpl_staged_spec ex13;
    [%expect
      {|
      ((f (); x. k 1); y. g y)
      >>> simpl_staged_spec >>>
      (f (); x. (k 1; y. g y))
      |}]
  in
  ()
