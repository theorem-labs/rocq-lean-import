(* P10 on the legacy path, in a session where UInt32 has only its pre-4.17 registration: this file loads the
   importer without src/Lean.v, and registers lean.Fin and lean.UInt32.legacy only (not lean.UInt32).
   dumps/lean434/uint32_legacy_only.ndjson (Lean 4.16.9) declares Fin, then UInt32 with a Fin field twice
   (lines 13 and 14), then RLIP.x := UInt32.mk Fin.mk. The second UInt32 entry is declared again, as any
   repeated UInt32 or Char entry of the legacy path is (tests/uint32_dispatch.v), whatever the registrations:
   it binds lean.UInt32.legacy from its Fin field, and it is not skipped as a duplicate. Its eliminators exist
   from the first entry, so Error Mode Skip skips them ("Skipping scheme"), as in tests/uint32_dispatch.v.
   tests/uint32_legacy_only.expect checks the log. *)
Declare ML Module "coq-lean-import.plugin".

Set Universe Polymorphism.
Set Primitive Projections.

Inductive Fin@{} : Set := Fin_mk.
Register Fin as lean.Fin.

Record UInt32_legacy@{} : Set := UInt32_legacy_mk { val0 : Fin }.
Register UInt32_legacy as lean.UInt32.legacy.

Set Lean Error Mode "Skip".
Redirect "uint32_legacy_only.log" Lean Import "../dumps/lean434/uint32_legacy_only.ndjson".

Check RLIP_x : UInt32_legacy.
