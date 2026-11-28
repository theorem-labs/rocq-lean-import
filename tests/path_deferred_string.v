From LeanImport Require Import Lean.

(* V9b: two exports on the new path, on either side of Lean 4.26.0, where a literal is translated with
   String.mk before 4.26.0 and String.ofList from 4.26.0 on. dumps/lean434/string_deferred_4250.ndjson
   (Lean 4.25.0) declares RLI425.plit.{u} (α : Sort u) : String := "aé∀𝔸"; the import declares its instance
   at the universes that are not Prop, RLI425_plit, and leaves the one at Prop for the first entry that
   asks for it. dumps/lean434/string_deferred_4260.ndjson (Lean 4.26.0) declares String.ofList as an axiom,
   so a term built with it is convertible only with itself, and RLI426.pair := [RLI425.plit.{0} _, "b"],
   whose value first asks for that instance, RLI425_plit_inst1, and then holds its own literal "b".
   RLI426.pair_eq states by rfl that the instance holds String.mk, as its 4.25.0 export says, and that "b"
   is String.ofList, as the 4.26.0 export says. tests/path_deferred_string.expect checks the logs and the
   printed terms. *)
Set Lean Error Mode "Fail".
Redirect "path_deferred_string_4250.log" Lean Import "../dumps/lean434/string_deferred_4250.ndjson".
(* Before its fix (ci/build-9.2-cut.sh --revert-fix), the instance of RLI425.plit that this second import asks
   for gets the 4.26.0 constructor, and the kernel refuses RLI426.pair_eq, whose statement holds the unqualified
   String_mk of this file's first import: *)
(* r5 error: RLI426_pair = List_cons_inst1 String (String_mk *)
Redirect "path_deferred_string_4260.log" Lean Import "../dumps/lean434/string_deferred_4260.ndjson".

Check RLI426_pair_eq.
Redirect "path_deferred_string_plit.log" Print RLI425_plit.
Redirect "path_deferred_string_plit_inst1.log" Print RLI425_plit_inst1.
Redirect "path_deferred_string_pair.log" Print RLI426_pair.
