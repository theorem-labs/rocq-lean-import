From LeanImport Require Import Lean.

(* An entry whose expressions use a universe name that its levelParams do not declare is refused with an error
   that names the universe and the entry's universe parameters (to_universe in src/lean.ml), and in Skip mode the
   import goes on with the next entry. dumps/lean434/univ_undeclared.ndjson (dumps/lean434/README.md) adds to the
   Nat and Eq of pow.ndjson:
   - line 111, RLIU.refl_u, a theorem with no universe parameters whose proof is Eq.refl at the universe u, in a
     constant's universe instance;
   - line 116, RLIU.refl_one, the same theorem with Eq.refl at the universe 1: it is well formed;
   - line 120, RLIU.sort_u_1, a definition with the universe parameter u whose type is (α : Sort u_1) → Nat, a
     sort;
   - line 128, RLIU.Box, an inductive type with no universe parameters whose constructor has a field in Sort v.
   tests/univ_undeclared.expect checks the log. *)
Set Lean Error Mode "Skip".
(* Before its fix (ci/build-9.2-cut.sh --revert-fix), the lookup of an undeclared universe failed an assertion of
   Rocq's maps: each planted entry was refused with this anomaly, on the line right after its refusal header, and
   tests/univ_undeclared.expect refuses that line after the compile: *)
(* r5 assertion: "univ_undeclared.log" Anomaly "File "clib/cMap.ml", line 145, characters 16-22: Assertion failed." *)
(* r5 log: "univ_undeclared.log" Anomaly "File "clib/cMap.ml", line 145, characters 16-22: Assertion failed." *)
(* planted: RLIU.refl_u *)
(* planted: RLIU.sort_u_1 *)
(* planted: RLIU.Box *)
Redirect "univ_undeclared.log" Lean Import "../dumps/lean434/univ_undeclared.ndjson".

(* The well-formed entry is declared; the refused ones are not. *)
Check RLIU_refl_one.
Fail Check RLIU_refl_u.
Fail Check RLIU_sort_u_1.
Fail Check RLIU_Box.
