From LeanImport Require Import Lean.

(* T12b, a record with its next id and no payload tag, read by the normal reader (tests/parse_untagged_prefix.v
   reads the same lines with the prefix reader). dumps/lean434/parse_untagged.ndjson has, after the lines of
   timeout.ndjson it starts with, a name, a level and an expression record that carry only their next id
   ("in" at line 132, "il" at line 135, "ie" at line 138). Each is refused and reserves its own id and no
   other: the record of its kind at the next id (lines 133, 136 and 139) is read, and the record that uses
   the refused id (lines 134, 137 and 140) is refused with that id named. The names of lines 142 and 143 are
   read at the next name ids after the three cases, and each axiom of lines 144 to 146 uses the record that
   follows one case. tests/parse_untagged.expect checks the log. *)
Set Lean Error Mode "Skip".
Redirect "parse_untagged.log" Lean Import "../dumps/lean434/parse_untagged.ndjson".

Check RLIUntaggedName.
Check RLIUntaggedLevel.
Check RLIUntaggedExpr.
