/- A nest of projections on both sides of a Fin pair (idA N against idB N; tests/fin_transport_nest.v). The nest itself is planted in
   dumps/lean434/fin_nest.ndjson (its row in dumps/lean434/README.md). -/

namespace RLI434N

structure W (α : Type) where
  w : α

def idA (x : UInt32) : UInt32 := x
def idB (x : UInt32) : UInt32 := x

theorem cast_127 (v : UInt32) (h : v ≤ UInt32.ofNatLT 127 (by decide)) : v ≤ 127 := h

theorem pair (v : UInt32) (h1 : v ≤ 127) (h2 : v ≤ idA 127) : v ≤ 127 ∧ v ≤ idA 127 := ⟨h1, h2⟩

end RLI434N
