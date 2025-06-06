import Mathlib.Data.Real.Basic

open Real

theorem log_div_log_eq_three : log 27 / log 3 = 3 := by
  rw [log_div_log]
  have h : 27 = 3 ^ 3 := by norm_num
  rw [h]
  apply logb_rpow
  norm_num
  norm_num