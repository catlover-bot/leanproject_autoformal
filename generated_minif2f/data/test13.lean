import Mathlib.Data.Real.Basic

open Real

theorem solve_fraction (x : ℝ) : 2 + 1 / (1 + 1 / (2 + 2 / (3 + x))) = 144 / 53 → x = 3 / 4 := by
  intro h
  have h1 : 3 + 3 / 4 = 15 / 4 := by norm_num
  have h2 : 2 + 2 / (3 + 3 / 4) = 2 + 2 / (15 / 4) := by rw [h1]
  have h3 : 2 + 2 / (15 / 4) = 2 + 8 / 15 := by norm_num
  have h4 : 1 + 1 / (2 + 8 / 15) = 1 + 1 / (38 / 15) := by norm_num
  have h5 : 1 + 1 / (38 / 15) = 1 + 15 / 38 := by norm_num
  have h6 : 2 + 1 / (1 + 15 / 38) = 2 + 38 / 53 := by norm_num
  have h7 : 2 + 38 / 53 = 144 / 53 := by norm_num
  rw [h6] at h
  exact (eq_of_add_eq_add_right h7).mp h