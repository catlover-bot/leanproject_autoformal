import Mathlib.Data.Int.Basic

theorem expression_evaluates_to_11 (x : ℤ) (h₀ : x = 4) : 
  (3 * x - 2) * (4 * x + 1) - (3 * x - 2) * (4 * x) + 1 = 11 := 
by
  rw [h₀]
  norm_num