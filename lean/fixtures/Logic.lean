namespace Scratch

theorem and_comm (p q : Prop) : p ∧ q -> q ∧ p := by
  intro h
  exact And.intro h.right h.left

end Scratch
