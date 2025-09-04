open Rewrite_bindlib

let () =
  let open Syntax in
  let open Examples in
  let open Pretty in
  let open Simpl in
  print_endline (string_of_staged_spec (simpl_staged_spec ex2));
  print_endline (string_of_staged_spec (simpl_staged_spec ex3));
  print_endline (string_of_staged_spec (simpl_staged_spec ex4));
  print_endline (string_of_staged_spec ex6);
  print_endline (string_of_staged_spec (simpl_staged_spec ex6));
  print_endline (string_of_staged_spec ex7);
  print_endline (string_of_staged_spec (simpl_staged_spec ex7));
  print_endline (string_of_staged_spec (simpl_staged_spec ex8));
  print_endline (string_of_staged_spec (simpl_staged_spec_cont ex8 identity_cont));
