import Init

/- The template of the nesting fixtures of the relevant path (tests/relcast_depth.v; README, "Transport of proof
   arguments across Nat literals", the item on relevant positions): `useNest`'s relevant argument has a declared
   domain that holds the W pair (`mkW 3` against `wk 3 lw3`) under a nest of `@id W`, two applications deep here.
   dumps/lean434/relcast_depth.ndjson is this module's export with copies appended whose nests have 9989 to 9991
   applications (its row in dumps/lean434/README.md). -/
namespace RLI434RD

set_option maxRecDepth 100000

structure W where
  val : Fin 5
def wk (n : Nat) (h : n < 5) : W := ⟨⟨n, h⟩⟩
def mkW (n : Nat) : W := ⟨⟨n % 5, Nat.mod_lt _ (by decide)⟩⟩
instance : LE W := ⟨fun a b => a.val.val ≤ b.val.val⟩
instance decLeW (a b : W) : Decidable (a ≤ b) := Nat.decLe a.val.val b.val.val
theorem lw3 : 3 < 5 := by decide
axiom useNest (x : W) (_ : Decidable (x ≤ @id W (@id W (mkW 3)))) : Nat
axiom dNest (x : W) : Decidable (x ≤ @id W (@id W (wk 3 lw3)))
/- B-detect-depth: the nest in the domain of the only relevant site. -/
theorem detect_depth (x : W) : True := (fun (_ : Nat) => True.intro) (useNest x (dNest x))
/- B-depth: a shallow relevant site first (the detector stops there), then the nest. -/
theorem rel_depth (x : W) : True :=
  (fun (_ : Nat) (_ : Nat) => True.intro) (@ite Nat (x ≤ mkW 3) (decLeW x (wk 3 lw3)) 1 2) (useNest x (dNest x))

end RLI434RD
