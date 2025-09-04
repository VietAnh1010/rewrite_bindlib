open Rewrite_bindlib

let () =
  let open Syntax in
  let open Examples in
  let open Pretty in
  let open Simpl in
  print_endline (string_of_staged_spec (simpl_staged_spec ex2))
