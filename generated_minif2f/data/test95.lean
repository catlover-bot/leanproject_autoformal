import Mathlib.Data.Real.Basic

theorem solve_for_x (x : ℝ) (hx : x ≠ -1) (h : (x - 9) / (x + 1) = 2) : x = -11 := by
  have h' : (x - 9) = 2 * (x + 1) := by rwa [div_eq_iff (by linarith)] at h
  linarith