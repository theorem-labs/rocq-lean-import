From LeanImport Require Import Lean.

(* T12b, the prefix reader: the import of dumps/lean434/parse_untagged.ndjson from line 144 reads lines 1 to
   143 for their names, levels and expressions only, and declares the axioms of lines 144 to 146
   (tests/parse_untagged.v reads every line with the normal reader). The prefix reader refuses the name,
   level and expression records of lines 132, 135 and 138, which carry only their next id, as the normal
   reader does: each keeps its own id, the record of its kind at the next id is read and the record that
   uses the refused id is refused with that id named. tests/parse_untagged_prefix.expect checks the log. *)
Set Lean Error Mode "Skip".
Redirect "parse_untagged_prefix.log" Lean Import "../dumps/lean434/parse_untagged.ndjson" 144.
(* Before its fix (ci/build-9.2-cut.sh --revert-fix), this prefix import, which announces no entry before line
   144, refuses the name of line 133 as out of sequence, so the axiom of line 144 is refused and RLIUntaggedName
   is not declared: *)
(* r5 log lacks: "parse_untagged_prefix.log" line 131: RLI434T.fast *)
(* r5 log: "parse_untagged_prefix.log" NDJSON parse error at line 133: name id 33 is not the next expected id 32 *)

(* r5 error: The reference RLIUntaggedName was not found *)
Check RLIUntaggedName.
Check RLIUntaggedLevel.
Check RLIUntaggedExpr.
