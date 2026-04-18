From LeanImport Require Import Lean ULiftCumulativeRegistration.

(* Regression test for ULift cumul functions.

   The dump [ulift_proper] exports a Lean [useUp.{u} (α : Type u) (x : α) :
   ULift.{u, u} α := ULift.up.{u, u} α x] which forces the plugin to apply
   [ULift_up_cumul] to an α whose Lean-exported sort is [Sort (u+1)].  Before
   the 4-universe rewrite of [ULiftCumulativeRegistration] (and the matching
   [algs] in lean.ml), this crashed with a universe mismatch / kernel
   assertion because the cumul refs were instantiated at [{u, u}] but
   expected α at [Type@{u+1}]. *)
Redirect "ulift_proper.log" Lean Import "../dumps/ulift_proper".

Set Printing Universes.
Check Scratch_useUp.
Print Scratch_useUp.

(* Applying the imported [useUp] to a concrete type and term must now succeed. *)
Check Scratch_useUp Nat Nat_zero.

(* Pointwise convertibility: Scratch_useUp α x reduces to x because
   ULift_up_cumul is the identity. *)
Check fun (α : Type) (x : α) =>
        eq_refl (Scratch_useUp α x) : Scratch_useUp α x = x.
