import Mathlib.Data.Real.Basic

lemma solve_for_y (y : ℝ) : y + 6 + y = 2 * 12 → y = 9 := by
  intro h
  linarith