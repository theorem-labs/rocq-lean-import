From LeanImport Require Import Lean.

(* An importer that does not know the option Lean Entry Timeout fails at the
   Set below, instead of only warning and importing with no limit. *)
Set Warnings "+unknown-option".
Set Lean Entry Timeout 1.

(* T6, T11: the limit must be a positive number of seconds: 0 and -1 are
   refused. *)
Redirect "entry_timeout_zero.log" Fail Set Lean Entry Timeout 0.
Redirect "entry_timeout_negative.log" Fail Set Lean Entry Timeout -1.

(* T15, T2: the largest value tested, 2^30 s, is accepted, and a small entry
   imports under it. *)
Set Lean Entry Timeout 1073741824.
Redirect "entry_timeout_large.log" Succeed Lean Import "../dumps/lean434/timeout.ndjson" 1 132.

(* T1, T14: Unset removes the limit. The decide proof slow_sum takes
   more than 1 s. On the Rocq 9.2 cut it took 49.3 s and 59.8 s at
   an 8 MiB stack in two trials, and more than 60 s in another.
   The outer timeout gives the proof time to finish and still bounds
   the test if the import does not finish. *)
Set Lean Entry Timeout 1.
Unset Lean Entry Timeout.
Redirect "entry_timeout_unset.log" Succeed Timeout 300 Lean Import "../dumps/lean434/timeout.ndjson" 1 2196.

(* T8: an outer Timeout shorter than the entry limit fires first: the command
   ends in Timeout!, and no entry is refused for the entry limit. *)
Set Lean Entry Timeout 10.
Set Lean Error Mode "Skip".
Redirect "entry_timeout_outer.log" Fail Timeout 5 Lean Import "../dumps/lean434/timeout_cases.ndjson".

(* T4: in Stop mode the import ends at the entry that runs out of time, and
   succeeds; the entries after it are not read. *)
Set Lean Entry Timeout 1.
Set Lean Error Mode "Stop".
Redirect "entry_timeout_stop.log" Succeed Timeout 20 Lean Import "../dumps/lean434/timeout_cases.ndjson".

(* T5: in Fail mode the refusal of that entry is the error of the command. *)
Set Lean Error Mode "Fail".
Redirect "entry_timeout_fail.log" Fail Timeout 20 Lean Import "../dumps/lean434/timeout_cases.ndjson".

(* T3, T7, T9, T16: in Skip mode the entry that runs out of time and the entry
   that uses it are refused, and the import goes on; the line limit does not
   bound declaring an entry. *)
Set Lean Error Mode "Skip".
Set Lean Line Timeout 5.
Redirect "entry_timeout_skip.log" Timeout 20 Lean Import "../dumps/lean434/timeout_cases.ndjson".
Check RLI434T_fast.
Fail Check RLI434T_slower_sum.
Check RLI434T_after_slow.
Fail Check RLI434T_needs_slower.

(* The limit also bounds the kernel's check of an inductive type: a field of
   RLI434T.SlowBox's constructor has a type that applies a function to the
   decide proof of slow_sum, and checking that application takes more than
   1 s. The entry is refused when its limit runs out there, and the type is not
   declared again without a limit. *)
Set Lean Error Mode "Fail".
Redirect "entry_timeout_inductive.log" Fail Timeout 120 Lean Import "../dumps/lean434/timeout_inductive.ndjson".
