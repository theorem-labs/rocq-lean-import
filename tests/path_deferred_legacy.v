From LeanImport Require Import Lean.

(* V9a: an export on the legacy path saves an entry that a later export on the new path first declares.
   dumps/lean434/pow_body_4169.ndjson (Lean 4.16.9: the legacy path) is imported with Lean Lazy
   Instantiation, which saves its entries and leaves them undeclared (only Nat, which the types of its
   inductive types name, is bound to the predeclared Nat); its Nat.pow returns zero. Then
   dumps/lean434/legacy_deferred_4250.ndjson (Lean 4.25.0: the new path) declares RLIV.mix, whose value asks
   for Nat.pow first and then holds the string literal "b". Nat.pow is declared on the path of the export
   that gave it: the legacy path binds it to the predeclared Nat_pow of src/Lean.v, which computes 2 ^ 3 = 8
   (on the new path it would be the export's, which gives 0). Back in RLIV.mix, "b" is translated on the
   new path of its own export: String.mk applied to Char.ofNat 98. RLIV.mix_eq states both by rfl.
   tests/path_deferred_legacy.expect checks the logs. *)
Set Lean Error Mode "Fail".
Set Lean Lazy Instantiation.
Redirect "path_deferred_legacy_saved.log" Lean Import "../dumps/lean434/pow_body_4169.ndjson".
Unset Lean Lazy Instantiation.
Redirect "path_deferred_legacy.log" Lean Import "../dumps/lean434/legacy_deferred_4250.ndjson".

Check RLIV_mix_eq.
Redirect "path_deferred_legacy_pow.log" Locate Nat_pow.
Redirect "path_deferred_legacy_mix.log" Print RLIV_mix.
