import Init

/- Two Fin values that differ, at a place the kernel does not need to convert (`f` ignores its argument),
   beside a Nat hole at 5000 in the same proof argument: the Fin pair gets no lemma, and the Nat hole is still
   cast. The values are UInt8s, whose conversion the kernel does at once. -/
namespace RLI434V

def f (_ : UInt8) : Prop := True
def c3 : UInt8 := 3
def c4 : UInt8 := 4

theorem values_differ (h : f c3 ∧ 2500 + 2500 = 5000) : f c4 ∧ 5000 = 5000 := h

end RLI434V
