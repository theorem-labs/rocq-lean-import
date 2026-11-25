From LeanImport Require Import Lean.

(* T12b, a record whose id is not clear: dumps/lean434/parse_unclear_id.ndjson has, after the lines of
   timeout.ndjson it starts with, a name record with its id field twice (line 132), a level record with a
   second id field (line 134) and an expression record with its id field twice (line 136), each followed by
   a valid record of its kind at the next id (lines 133, 135 and 137). Then come records with no payload tag
   whose id is out of sequence, not an integer, or given by two fields (lines 138 to 141), tagged records
   whose id is not an integer or out of sequence (lines 142 to 145) and a record with no id (line 146). None
   of them reserves an id: the name, level and expression records of lines 147 to 149 are read at the next
   ids, and the axioms of lines 150 and 151 use the records that follow the refused ones. The records with no
   payload tag keep the refusal "unsupported NDJSON record". tests/parse_unclear_id.expect checks the log. *)
Set Lean Error Mode "Skip".
Redirect "parse_unclear_id.log" Lean Import "../dumps/lean434/parse_unclear_id.ndjson".

Check RLIUnclear.
Check RLIUnclearNext.
