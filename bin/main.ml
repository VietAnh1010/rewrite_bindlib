open Rewrite_bindlib

let print_staged_spec s =
  let open Pretty in
  print_endline (string_of_staged_spec s)

let () =
  let open Examples in
  let open Simpl in
  (* print_staged_spec (simpl_staged_spec ex2);
  print_staged_spec (simpl_staged_spec ex3);
  print_staged_spec (simpl_staged_spec ex4);
  print_staged_spec ex6;
  print_staged_spec (simpl_staged_spec ex6);
  print_staged_spec ex7;
  print_staged_spec (simpl_staged_spec ex7);
  print_staged_spec (simpl_staged_spec ex8);
  print_staged_spec (simpl_staged_spec_cont ~delimited:false ex8 identity_cont);
  print_staged_spec (simpl_staged_spec ex9);
  print_staged_spec (simpl_staged_spec_cont ~delimited:true ex9 identity_cont); *)
  print_staged_spec (simpl_staged_spec ex10);
  print_staged_spec (simpl_staged_spec ex11);
  print_staged_spec (simpl_staged_spec ex12);
