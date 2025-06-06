import Mathlib.Data.Real.Basic

theorem solve_system (s t : ℝ) (h₁ : s = 9 - 2 * t) (h₂ : t = 3 * s + 1) : s = 1 ∧ t = 4 := by
  have : s = 9 - 2 * (3 * s + 1) := by rw [h₂]
  ring_nf at this
  linarith
  have : t = 4 := by linarith
  exact ⟨this, h₂ ▸ by linarith⟩