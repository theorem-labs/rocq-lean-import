From LeanImport Require Import Lean.

(* An importer that does not know the option Lean Entry Timeout fails at the
   Set below, instead of only warning and importing with no limit. *)
Set Warnings "+unknown-option".
Set Lean Entry Timeout 1.

(* T12, T13: a line the NDJSON parser cannot read is refused like an entry
   that cannot be declared, under the Error Mode: Skip refuses it and goes on
   with the next line, Stop ends the import and succeeds, Fail ends it and
   fails. Each case runs from a fresh import state. *)
Unset Lean Entry Timeout.
Set Lean Error Mode "Skip".
Redirect "entry_timeout_parse_mutual.log" Succeed Lean Import "../dumps/lean434/parse_mutual.ndjson".
Redirect "entry_timeout_parse_id.log" Succeed Lean Import "../dumps/lean434/parse_id.ndjson".
Redirect "entry_timeout_parse_no_meta.log" Succeed Lean Import "../dumps/lean434/parse_no_meta.ndjson".
Redirect "entry_timeout_parse_bad_format.log" Succeed Lean Import "../dumps/lean434/parse_bad_format.ndjson".
Redirect "entry_timeout_parse_truncated.log" Succeed Lean Import "../dumps/lean434/parse_truncated.ndjson".
Redirect "entry_timeout_parse_empty.log" Succeed Lean Import "../dumps/lean434/parse_empty.ndjson".
Redirect "entry_timeout_parse_messages.log" Succeed Lean Import "../dumps/lean434/parse_messages.ndjson".
(* A line before the first line to import (the 134 below) is read for its
   names, levels and expressions only, and is refused like any other line:
   lines 132 and 133 of parse_id.ndjson are, and the import goes on. *)
Redirect "entry_timeout_parse_prefix.log" Succeed Lean Import "../dumps/lean434/parse_id.ndjson" 134.

Set Lean Error Mode "Stop".
Redirect "entry_timeout_parse_stop_mutual.log" Succeed Lean Import "../dumps/lean434/parse_mutual.ndjson".
Redirect "entry_timeout_parse_stop_id.log" Succeed Lean Import "../dumps/lean434/parse_id.ndjson".
Redirect "entry_timeout_parse_stop_no_meta.log" Succeed Lean Import "../dumps/lean434/parse_no_meta.ndjson".
Redirect "entry_timeout_parse_stop_bad_format.log" Succeed Lean Import "../dumps/lean434/parse_bad_format.ndjson".
Redirect "entry_timeout_parse_stop_truncated.log" Succeed Lean Import "../dumps/lean434/parse_truncated.ndjson".

Set Lean Error Mode "Fail".
Redirect "entry_timeout_parse_fail_mutual.log" Fail Lean Import "../dumps/lean434/parse_mutual.ndjson".
Redirect "entry_timeout_parse_fail_id.log" Fail Lean Import "../dumps/lean434/parse_id.ndjson".
Redirect "entry_timeout_parse_fail_no_meta.log" Fail Lean Import "../dumps/lean434/parse_no_meta.ndjson".
Redirect "entry_timeout_parse_fail_bad_format.log" Fail Lean Import "../dumps/lean434/parse_bad_format.ndjson".
Redirect "entry_timeout_parse_fail_truncated.log" Fail Lean Import "../dumps/lean434/parse_truncated.ndjson".
