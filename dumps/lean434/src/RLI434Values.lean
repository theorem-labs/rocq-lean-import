import Init

/- Two Fin values that differ, at a place the kernel does not need to convert (`f` ignores its argument),
   beside a Nat hole in the same proof argument: the Fin pair gets no lemma, and the Nat hole is still cast.
   The Fin values are UInt8s, whose conversion the kernel does at once. The Nat pair is 2 ^ 39 + 2 ^ 39 against
   2 ^ 40: its lemma is checked through Rocq's binary `N` at once, while Rocq's kernel converts the two sides on
   the unary Nat, one successor at a time, far longer than any short entry limit. -/
namespace RLI434V

def f (_ : UInt8) : Prop := True
def c3 : UInt8 := 3
def c4 : UInt8 := 4

theorem values_differ (h : f c3 ∧ 549755813888 + 549755813888 = 1099511627776) :
    f c4 ∧ 1099511627776 = 1099511627776 := h

end RLI434V
