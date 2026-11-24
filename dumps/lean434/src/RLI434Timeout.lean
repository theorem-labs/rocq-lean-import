namespace RLI434T
def fast : Nat := 3
def sumTo : Nat → Nat
  | 0 => 0
  | n + 1 => (n + 1) + sumTo n
set_option maxRecDepth 100000 in
theorem slow_sum : sumTo 400 = 80200 := by decide
set_option maxRecDepth 1000000 in
theorem slower_sum : sumTo 1500 = 1125750 := by decide
theorem after_slow : fast = 3 := rfl
theorem needs_slow : sumTo 400 = 80200 := slow_sum
theorem needs_slower : sumTo 1500 = 1125750 := slower_sum
end RLI434T
