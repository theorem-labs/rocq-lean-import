namespace RLI434
def half (n : Nat) (_h : n % 2 = 0 := by decide) : Nat := n / 2
theorem half_four : half 4 = 2 := rfl
end RLI434
