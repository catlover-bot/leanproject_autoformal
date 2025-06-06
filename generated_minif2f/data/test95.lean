import Mathlib.Data.Real.Basic

open Real

theorem solve_equation (x : ℝ) (h₁ : x ≠ -1) (h₂ : (x - 9) / (x + 1) = 2) : x = -11 :=
by
  have h₃ : x - 9 = 2 * (x + 1) := by
    rw [← h₂, mul_div_cancel' _ (ne_of_gt (by norm_num : (2 : ℝ) ≠ 0))]
  linarith