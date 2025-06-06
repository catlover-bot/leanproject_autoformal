import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Real

theorem log_div_log_eq : log 27 / log 3 = 3 :=
by
  have h : log 27 = log (3 ^ 3) := by rw [pow_succ, pow_succ, pow_one]
  rw [h, log_pow, mul_div_cancel_left]
  exact ne_of_gt (log_pos (by norm_num))