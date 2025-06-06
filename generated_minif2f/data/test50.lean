import Mathlib.Data.Real.Basic

theorem function_value_at_one (f : ℝ → ℝ) (h₀ : ∀ x, f x = 5 * x + 4) : f 1 = 9 :=
by
  rw [h₀ 1]
  linarith