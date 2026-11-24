From LeanImport Require Import Lean.

Set Lean Error Mode "Fail".

(* From Lean 4.26.0 on the kernel unfolds a string literal to String.ofList
   of its characters: an export of that version that declares no String.ofList
   is refused at its first literal, RLI425.lit. *)
Redirect "string_literal_mk_4260.log" Fail Lean Import "../dumps/lean434/string_mk_4260.ndjson".

(* Lean 4.17.0 to 4.25.x unfold it to String.mk: an export of Lean 4.25.0 that
   declares String.mk and no String.ofList imports, and its theorem
   RLI425.lit_eq, which states by rfl that the literal of RLI425.lit is the
   String.mk term of its code points, is accepted. *)
Lean Import "../dumps/lean434/string_mk_4250.ndjson".

Check RLI425_lit_eq.
