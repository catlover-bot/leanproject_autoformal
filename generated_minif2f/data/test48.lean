import Mathlib.Data.Real.Basic

theorem inequality_for_all_real (a : ℝ) : a * (2 - a) ≤ 1 := by
  have h : a * (2 - a) = 1 - (a - 1)^2 := by
    ring
  rw [h]
  apply sub_nonneg.mpr
  apply pow_two_nonneg