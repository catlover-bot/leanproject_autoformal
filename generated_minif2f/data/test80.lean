import Mathlib.Data.Int.Basic

theorem abs_expression : abs (((3491 - 60) * (3491 + 60) - 3491^2) : ℤ) = 3600 := by
  have h : (3491 - 60) * (3491 + 60) = 3491^2 - 60^2 := by
    ring
  rw [h]
  rw [Int.sub_sub, Int.sub_self, Int.zero_sub]
  have : 60^2 = 3600 := by norm_num
  rw [this]
  exact abs_neg 3600