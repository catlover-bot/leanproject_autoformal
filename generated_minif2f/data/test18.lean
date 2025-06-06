import Mathlib.Data.Real.Basic

theorem expression_evaluation (a b : ℝ) (h₀ : a = -1) (h₁ : b = 5) : -a - b^2 + 3 * (a * b) = -39 := by
  rw [h₀, h₁]
  norm_num