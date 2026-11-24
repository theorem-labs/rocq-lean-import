From LeanImport Require Import Lean.

Set Warnings "+unknown-option".
Set Lean Entry Timeout 1.

(* T6, T11: an unsupported option fails at the first Set above. *)
Redirect "entry_timeout_zero.log" Fail Set Lean Entry Timeout 0.
Redirect "entry_timeout_negative.log" Fail Set Lean Entry Timeout -1.

(* T15, T2: a small entry imports with the largest test value. *)
Set Lean Entry Timeout 1073741824.
Redirect "entry_timeout_large.log" Succeed Lean Import "../dumps/lean434/timeout.ndjson" 1 132.

(* T1, T14: clearing the limit permits the smaller decide proof. *)
Set Lean Entry Timeout 1.
Unset Lean Entry Timeout.
Redirect "entry_timeout_unset.log" Succeed Timeout 60 Lean Import "../dumps/lean434/timeout.ndjson" 1 2196.

(* T8: the surrounding command limit is shorter than the entry limit. *)
Set Lean Entry Timeout 10.
Set Lean Error Mode "Skip".
Redirect "entry_timeout_outer.log" Fail Timeout 1 Lean Import "../dumps/lean434/timeout_cases.ndjson".

(* T4: Stop leaves the events after the timed entry unread. *)
Set Lean Entry Timeout 1.
Set Lean Error Mode "Stop".
Redirect "entry_timeout_stop.log" Succeed Timeout 20 Lean Import "../dumps/lean434/timeout_cases.ndjson".

(* T5: Fail propagates the refusal as the command error. *)
Set Lean Error Mode "Fail".
Redirect "entry_timeout_fail.log" Fail Timeout 20 Lean Import "../dumps/lean434/timeout_cases.ndjson".

(* T3, T7, T9, T16: the line limit does not limit entry declaration. *)
Set Lean Error Mode "Skip".
Set Lean Line Timeout 5.
Redirect "entry_timeout_skip.log" Timeout 20 Lean Import "../dumps/lean434/timeout_cases.ndjson".
Check RLI434T_fast.
Fail Check RLI434T_slower_sum.
Check RLI434T_after_slow.
Fail Check RLI434T_needs_slower.
