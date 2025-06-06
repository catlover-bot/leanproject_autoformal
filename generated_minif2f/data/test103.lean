import Mathlib.Data.Real.Basic
import Mathlib.Tactic

theorem solve_for_y (y : ℝ) (h₀ : 0 ≤ 19 + 3 * y) (h₁ : real.sqrt (19 + 3 * y) = 7) : y = 10 := by
  rw [real.sqrt_eq_iff_sq_eq h₀] at h₁
  norm_num at h₁
  nlinarith at h₁
  exact h₁