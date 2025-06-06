import Mathlib.Data.Real.Basic

theorem solve_system (a b : ℝ) (h₁ : 3 * a + 2 * b = 5) (h₂ : a + b = 2) : a = 1 ∧ b = 1 := by
  have h₃ : 3 * a + 2 * b = 3 * (a + b) - a := by ring
  rw [h₂] at h₃
  have h₄ : 5 = 6 - a := by linarith
  have h₅ : a = 1 := by linarith
  have h₆ : b = 1 := by linarith
  exact ⟨h₅, h₆⟩