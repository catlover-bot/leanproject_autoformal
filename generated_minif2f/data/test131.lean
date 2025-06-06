import Mathlib.Data.Real.Basic

theorem unit_circle_inequality (a b : ℝ) (h : a^2 + b^2 = 1) : a * b + (a - b) ≤ 1 := by
  have h1 : (a - b)^2 ≥ 0 := by
    apply sq_nonneg
  have h2 : (a - b)^2 = a^2 - 2 * a * b + b^2 := by
    ring
  rw [h2, h] at h1
  have h3 : 1 - 2 * a * b ≥ 0 := by
    linarith
  linarith