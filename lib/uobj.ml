open Syntax
open Pretty
open Sort

type uobj =
  | UOTerm of term
  | UOState of state
  | UOStagedSpec of staged_spec
  | UOStagedSpecBinder of staged_spec_binder

let sort_of_uobj = function
  | UOTerm _ -> Term
  | UOState _ -> State
  | UOStagedSpec _ -> StagedSpec
  | UOStagedSpecBinder _ -> StagedSpecBinder

let string_of_uobj_sort uobj = string_of_sort (sort_of_uobj uobj)

let invalid_uobj_sort ~expected uobj =
  invalid_sort
    (Format.sprintf "expected sort %s, got %s" (string_of_sort expected)
       (string_of_uobj_sort uobj))

let uobj_of_term t = UOTerm t
let uobj_of_state st = UOState st
let uobj_of_staged_spec s = UOStagedSpec s
let uobj_of_staged_spec_binder b = UOStagedSpecBinder b

let term_of_uobj = function
  | UOTerm t -> t
  | uobj -> invalid_uobj_sort ~expected:Term uobj

let state_of_uobj = function
  | UOState st -> st
  | uobj -> invalid_uobj_sort ~expected:State uobj

let staged_spec_of_uobj = function
  | UOStagedSpec s -> s
  | uobj -> invalid_uobj_sort ~expected:StagedSpec uobj

let staged_spec_binder_of_uobj = function
  | UOStagedSpecBinder b -> b
  | uobj -> invalid_uobj_sort ~expected:StagedSpecBinder uobj
