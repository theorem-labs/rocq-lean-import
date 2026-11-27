From LeanImport Require Import Lean.

(* The transport pass's walk of an entry's value takes a literal of the importer's form whole (README, "Transport
   of proof arguments across Nat literals"): a literal holds no transport site, so the walk returns it as it is for
   a step and a lookup, not for its chain of Nat_succ at each place. dumps/lean434/walk.ndjson is exported from
   dumps/lean434/src/RLI434Walk.lean; each theorem proves 2 ^ 40 = 2 ^ 40 from h : 2 ^ 39 + 2 ^ 39 = 2 ^ 40 as
   (fun _ => h) l, so the pass casts the redex along a generated lemma, which the kernel checks through Rocq's
   binary N; left to the kernel, the Nat pair outlasts the 10 s limit below. The list l is in the value only.
   - walk_lits (line 767): l holds 1024 and 4096 in turn, 400 times each, each written OfNat.ofNat Nat n
     (instOfNatNat n): 4,096,000 unary levels as a tree. The walk takes each literal whole: the entry's own part
     needs 31,435 steps, its argument 7,471, and the pair is cast. The src/ of the fix's parent walks every chain at
     every place and stops at the entry's own part (more than 1000000 steps); the kernel's check of Lean's value
     then outlasts the limit.
   - walk_limit (line 796): the same with 160 times each: its own part, the walk's, needs 16,838 steps, its argument
     6,091 (the lemma of walk_lits read from the cache). At 16,837 the pass stops at the entry's own part; at
     16,838 it casts.
   - walk_open (line 1403): l holds x under 600 Nat.succ, a run of Nat_succ that is no literal (its base is the
     entry's variable x), walked in one loop: the entry's own part needs 2,818 steps, its argument 6,091. At 6,090
     the pass stops at the argument, at 6,091 and at the default it casts; a walk that asked each suffix of the run
     whether it is a literal would pay a step per level of each suffix, and stop at 6,091.
   Each limit row runs under Succeed, which undoes the import, so that the next row imports the same entry again.
   tests/transport_walk.expect checks the logs. *)
Set Warnings "+unknown-option".
Set Lean Error Mode "Skip".
Set Lean Entry Timeout 10.
Redirect "transport_walk_lib.log" Lean Import "../dumps/lean434/walk.ndjson" 1 767.
Redirect "transport_walk_lits.log" Lean Import "../dumps/lean434/walk.ndjson" 767 768.

Set Lean Transport Step Budget 16837.
Redirect "transport_walk_limit_stop.log" Succeed Lean Import "../dumps/lean434/walk.ndjson" 796 797.
Set Lean Transport Step Budget 16838.
Redirect "transport_walk_limit_part.log" Succeed Lean Import "../dumps/lean434/walk.ndjson" 796 797.
Set Lean Transport Step Budget 6090.
Redirect "transport_walk_open_stop.log" Succeed Lean Import "../dumps/lean434/walk.ndjson" 1403 1404.
Set Lean Transport Step Budget 6091.
Redirect "transport_walk_open_part.log" Succeed Lean Import "../dumps/lean434/walk.ndjson" 1403 1404.
Unset Lean Transport Step Budget.
Redirect "transport_walk_open.log" Lean Import "../dumps/lean434/walk.ndjson" 1403 1404.

Check RLI434Wk_walk_lits.
Check RLI434Wk_walk_open.
