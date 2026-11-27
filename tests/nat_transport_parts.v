From LeanImport Require Import Lean.

(* The step budget of each part of an entry (README, "Lean Transport Step Budget"): N steps for the entry's own
   scans and walks, and N for each argument the pass looks at; over a part's N the pass stops and the entry's own
   value goes to the kernel. dumps/lean434/fin_parts.ndjson is dumps/lean434/utf8size_one.ndjson with one theorem
   added after it, RLI434Fin.many127_1 : forall v : UInt32, v <= UInt32.ofNatLT 127 _ -> v <= (127 : UInt32)
   := fun v h => h (export line 11275).
  - Char.utf8Size_eq_one_iff (export line 11238): its own part needs 25,787 steps, its largest of 60 arguments
    29,624, and all its parts together 310,442, more than 10 N for N below 31,045. At N = 31,046 and 31,045 the
    pass completes; at 31,044 it stops for the total (more than 310,440 steps in total), and at 29,623 at that
    argument; the kernel's own conversion then takes far longer than the 10 s limit below (about 1,100 s on the
    Rocq 9.2 cut).
  - RLI434Fin.many127_1: its own part needs 747 steps, and its largest argument 7,449. At N = 7,450 and 7,449 the
    pass completes; at 7,448 it stops at that argument, and the kernel times out as above.
   - The total for all the parts of an entry is 10 N, or the largest integer when 10 N is larger (max_int, 2 ^ 62 - 1
     on 64 bits): at N = max_int / 10 - 1, max_int / 10 and max_int / 10 + 1 (461168601842738789, ...790, ...791),
     where 10 N first exceeds max_int, and at N = max_int itself (4611686018427387903), many127_1 is transported.
   - N = 1, the smallest budget, is accepted, and the pass stops at its second step.
   Each row but the last of each entry runs under Succeed, which undoes the import, so that the next row imports
   the same entry again. An importer without the option fails at the Set below.
   tests/nat_transport_parts.expect checks the logs. *)
Set Warnings "+unknown-option".
Set Lean Transport Step Budget 1000000.
Set Lean Error Mode "Skip".
Set Lean Entry Timeout 10.
Redirect "nat_transport_parts_base.log" Lean Import "../dumps/lean434/fin_parts.ndjson" 1 11238.

Set Lean Transport Step Budget 31046.
Redirect "nat_transport_parts_entry_31046.log" Succeed Lean Import "../dumps/lean434/fin_parts.ndjson" 11238 11239.
Set Lean Transport Step Budget 31045.
Redirect "nat_transport_parts_entry_31045.log" Succeed Lean Import "../dumps/lean434/fin_parts.ndjson" 11238 11239.
Set Lean Transport Step Budget 31044.
Redirect "nat_transport_parts_entry_31044.log" Succeed Lean Import "../dumps/lean434/fin_parts.ndjson" 11238 11239.
Set Lean Transport Step Budget 29623.
Redirect "nat_transport_parts_entry_29623.log" Lean Import "../dumps/lean434/fin_parts.ndjson" 11238 11239.
Fail Check Char_utf8Size_eq_one_iff.

Set Lean Transport Step Budget 7450.
Redirect "nat_transport_parts_arg_7450.log" Succeed Lean Import "../dumps/lean434/fin_parts.ndjson" 11239.
Set Lean Transport Step Budget 7449.
Redirect "nat_transport_parts_arg_7449.log" Succeed Lean Import "../dumps/lean434/fin_parts.ndjson" 11239.
Set Lean Transport Step Budget 461168601842738789.
Redirect "nat_transport_parts_max_m1.log" Succeed Lean Import "../dumps/lean434/fin_parts.ndjson" 11239.
Set Lean Transport Step Budget 461168601842738790.
Redirect "nat_transport_parts_max.log" Succeed Lean Import "../dumps/lean434/fin_parts.ndjson" 11239.
Set Lean Transport Step Budget 461168601842738791.
Redirect "nat_transport_parts_max_p1.log" Succeed Lean Import "../dumps/lean434/fin_parts.ndjson" 11239.
Set Lean Transport Step Budget 4611686018427387903.
Redirect "nat_transport_parts_max_int.log" Succeed Lean Import "../dumps/lean434/fin_parts.ndjson" 11239.
Set Lean Transport Step Budget 1.
Redirect "nat_transport_parts_one.log" Succeed Lean Import "../dumps/lean434/fin_parts.ndjson" 11239.
Set Lean Transport Step Budget 7448.
Redirect "nat_transport_parts_arg_7448.log" Lean Import "../dumps/lean434/fin_parts.ndjson" 11239.
Fail Check RLI434Fin_many127_1.
