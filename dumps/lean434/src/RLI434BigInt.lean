namespace RLI434
structure Bounds where
  lo : Int
  hi : Int
def big : Bounds := ⟨-134217728, 18446744073709551616⟩
theorem big_ok : big.lo < big.hi := by decide
theorem big_fields : ({ lo := -(-big.lo), hi := big.hi + 0 } : Bounds) = big := rfl
def boundedVal : {x : Int // 0 ≤ x ∧ x < 18446744073709551616} := ⟨4294967296, by decide⟩
theorem boundedVal_val : boundedVal.val = 4294967296 := rfl
theorem omega_big (x : Int) (h : x < 1099511627776) : x < 2199023255552 := by omega
def window : {p : Int × Int // p.1 + 134217728 ≤ p.2} := ⟨(4294967296, 8589934592), by decide⟩
end RLI434
