From LeanImport Require Import Lean.

(* Lean Entry Memory Limit, in GiB: a limit on how much declaring one entry grows the major heap above its size
   at the entry's start. dumps/lean434/memory_twice.ndjson holds the records of bigint.ndjson up to the decide
   proof RLI434.boundedVal._proof_1 (line 2491), the same proof again as RLI434.boundedVal._proof_2 (line 2493)
   and a small definition, RLI434.small (line 2495, a copy of id). In one 30 s trial on Rocq 07e45e36 and
   OCaml 4.14.2, checking the first proof grew the major heap by 8151 MiB from 124 MiB (about 270 MiB/s).
   Each entry before it grew the heap by less than 50 MiB. *)

(* M12: an importer that does not know the option fails at the Set below, instead of only warning and importing
   with no limit. *)
Set Warnings "+unknown-option".
Set Lean Entry Memory Limit 1.

(* M6: the limit must be a positive number of GiB: 0 and -1 are refused. *)
Redirect "entry_memory_zero.log" Fail Set Lean Entry Memory Limit 0.
Redirect "entry_memory_negative.log" Fail Set Lean Entry Memory Limit -1.

(* M2, M7: under a limit of 1 GiB, every entry before the proof imports, RLI434.big_ok and RLI434.big_fields
   among them (each under 50 MiB). *)
Set Lean Error Mode "Fail".
Redirect "entry_memory_under.log" Lean Import "../dumps/lean434/memory_twice.ndjson" 1 2491.
Check RLI434_big_ok.
Check RLI434_big_fields.

(* M5: in Fail mode the proof's refusal is the error of the command. *)
Redirect "entry_memory_fail.log" Fail Lean Import "../dumps/lean434/memory_twice.ndjson".

(* M4: in Stop mode the import ends at the proof, and succeeds; the entries after it are not read. *)
Set Lean Error Mode "Stop".
Redirect "entry_memory_stop.log" Lean Import "../dumps/lean434/memory_twice.ndjson".
Fail Check RLI434_boundedVal__proof_1.
Fail Check RLI434_small.

(* M3, M7, M8, M11: in Skip mode both proofs are stopped and refused at the limit, their state is undone, and
   the small entry after them imports. Each refusal gives the major heap at the entry's start: the heap is
   compacted after the first stop, so the second proof starts within 768 MiB of the first one's start; without
   the compaction it would start more than 1 GiB above it (tests/entry_memory.expect). *)
Set Lean Error Mode "Skip".
Redirect "entry_memory_skip.log" Lean Import "../dumps/lean434/memory_twice.ndjson".
Fail Check RLI434_boundedVal__proof_1.
Fail Check RLI434_boundedVal__proof_2.
Check RLI434_small.

(* M10: with both limits, the limit reached first refuses the entry: here the memory limit, in about 5 s. *)
Set Lean Entry Timeout 120.
Redirect "entry_memory_first.log" Lean Import "../dumps/lean434/memory_twice.ndjson" 1 2492.

(* M10: here the time limit, with the memory limit at 2^40 GiB, which in words does not fit an OCaml integer. *)
Set Lean Entry Memory Limit 1099511627776.
Set Lean Entry Timeout 2.
Redirect "entry_memory_time_first.log" Lean Import "../dumps/lean434/memory_twice.ndjson" 1 2492.

(* M13, M1: Unset removes the memory limit: each proof runs to the time limit, 10 s, growing the heap by more
   than 1 GiB. The heap is compacted after a timed-out entry too: the second proof starts within 768 MiB of the
   first one's start. *)
Set Lean Entry Memory Limit 1.
Unset Lean Entry Memory Limit.
Set Lean Entry Timeout 10.
Redirect "entry_memory_unset.log" Lean Import "../dumps/lean434/memory_twice.ndjson" 1 2494.

(* M9: an outer Timeout shorter than both limits fires first: the command ends in Timeout!, and the entry is not
   refused for the memory limit. *)
Set Lean Entry Memory Limit 8.
Unset Lean Entry Timeout.
Redirect "entry_memory_outer.log" Fail Timeout 8 Lean Import "../dumps/lean434/memory_twice.ndjson" 1 2492.
