import Mathlib.Data.Real.Basic
import Mathlib.Algebra.GroupPower.Basic

open Real

theorem log_expression : 
  (log 80 / log 2) / (log 2 / log 40) - (log 160 / log 2) / (log 2 / log 20) = 2 :=
by
  have h1 : log 80 = log (2^4 * 5) := by rw [←log_mul (by norm_num : 0 < 16) (by norm_num : 0 < 5), log_pow, log_two]
  have h2 : log 160 = log (2^5 * 5) := by rw [←log_mul (by norm_num : 0 < 32) (by norm_num : 0 < 5), log_pow, log_two]
  have h3 : log 40 = log (2^3 * 5) := by rw [←log_mul (by norm_num : 0 < 8) (by norm_num : 0 < 5), log_pow, log_two]
  have h4 : log 20 = log (2^2 * 5) := by rw [←log_mul (by norm_num : 0 < 4) (by norm_num : 0 < 5), log_pow, log_two]
  rw [h1, h2, h3, h4]
  field_simp [log_pos (by norm_num : 1 < 2), log_pos (by norm_num : 1 < 5)]
  ring_nf
  norm_num