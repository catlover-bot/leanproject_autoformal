import Mathlib.Data.Real.Basic

theorem solve_system (a b : ℝ) (h1 : 3 * a + 2 * b = 5) (h2 : a + b = 2) : a = 1 ∧ b = 1 := by
  have h3 : b = 2 - a := by
    linarith
  rw [h3] at h1
  linarith
  use 1, 1
  linarith