import Mathlib.Data.Real.Basic

theorem solve_for_x (x : ℝ) : 5 + 500 / 100 * 10 = 110 / 100 * x → x = 50 := by
  intro h
  have h1 : 5 + 500 / 100 * 10 = 55 := by norm_num
  rw [h1] at h
  have h2 : 110 / 100 = 1.1 := by norm_num
  rw [h2] at h
  linarith