From LeanImport Require Import Lean.

(* The nesting limit 10000 of the detector and of the relevant pass (README, "Transport of proof arguments across
   Nat literals", the item on relevant positions). dumps/lean434/relcast_depth.ndjson is the export of
   dumps/lean434/src/RLI434RelDepth.lean with copies of useNest and dNest and theorems built from rel_depth's value
   appended (its row in dumps/lean434/README.md). In each copy the relevant argument dNest x has the type
   Decidable (x <= id (... (id (wk 3 lw3)))) where useNest expects Decidable (x <= id (... (id (mkW 3)))), each side
   a nest of k applications of @id W, k = 9989, 9990 and 9991.
   - detect_depth_k (lines 30357, 50362 and 70369): that argument is the entry's only relevant site, after the
     literal 65536, which makes the pass run at the entry, so the detector descends the nest. At 9989 and 9990 the
     relevant pass casts the argument. At 9991 the detector stops at the limit and no relevant pass runs; neither
     the detector's stop nor a cast result is logged for the entry.
   - rel_depth_k (lines 90367, 110367 and 130369): a shallow relevant site comes first, where the detector stops,
     so only the relevant pass descends the nest. At 9989 and 9990 it casts both sites. At 9991 it stops at the
     limit, logs that, and casts no relevant argument.
   Each cast uses the lemma RLI434RD_rel_depth__rel_eq_1 of the template's rel_depth (line 10354, in the first
   import). tests/relcast_depth.expect checks the logs. *)
Set Warnings "+unknown-option".
Set Lean Error Mode "Skip".
Set Lean Entry Timeout 10.
Redirect "relcast_depth_lib.log" Lean Import "../dumps/lean434/relcast_depth.ndjson" 1 10355.
Redirect "relcast_detect_depth_9989.log" Lean Import "../dumps/lean434/relcast_depth.ndjson" 10355 30358.
Redirect "relcast_detect_depth_9990.log" Lean Import "../dumps/lean434/relcast_depth.ndjson" 30358 50363.
Redirect "relcast_detect_depth_9991.log" Lean Import "../dumps/lean434/relcast_depth.ndjson" 50363 70370.
Redirect "relcast_rel_depth_9989.log" Lean Import "../dumps/lean434/relcast_depth.ndjson" 70370 90368.
Redirect "relcast_rel_depth_9990.log" Lean Import "../dumps/lean434/relcast_depth.ndjson" 90368 110368.
Redirect "relcast_rel_depth_9991.log" Lean Import "../dumps/lean434/relcast_depth.ndjson" 110368 130370.
