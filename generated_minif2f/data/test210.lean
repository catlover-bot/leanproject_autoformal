import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Real

theorem sqrt_log_identity : 
  sqrt (log 6 / log 2 + log 6 / log 3) = sqrt (log 3 / log 2) + sqrt (log 2 / log 3) :=
by
  have h1 : log 6 = log (2 * 3) := by rw [log_mul (by norm_num : (2 : ℝ) > 0) (by norm_num : (3 : ℝ) > 0)]
  rw [h1, log_mul (by norm_num : (2 : ℝ) > 0) (by norm_num : (3 : ℝ) > 0)] at *
  have h2 : log 2 + log 3 = log 6 := by rw [h1]
  have h3 : log 6 / log 2 + log 6 / log 3 = (log 2 + log 3) / log 2 + (log 2 + log 3) / log 3 := by rw [h2]
  rw [h3]
  have h4 : (log 2 + log 3) / log 2 = 1 + log 3 / log 2 := by field_simp [log_ne_zero (by norm_num : (2 : ℝ) ≠ 1)]
  have h5 : (log 2 + log 3) / log 3 = 1 + log 2 / log 3 := by field_simp [log_ne_zero (by norm_num : (3 : ℝ) ≠ 1)]
  rw [h4, h5]
  have h6 : sqrt (1 + log 3 / log 2 + 1 + log 2 / log 3) = sqrt (2 + log 3 / log 2 + log 2 / log 3) := by ring
  rw [h6]
  have h7 : sqrt (2 + log 3 / log 2 + log 2 / log 3) = sqrt (1 + log 3 / log 2) + sqrt (1 + log 2 / log 3) := by
    have h8 : (sqrt (1 + log 3 / log 2) + sqrt (1 + log 2 / log 3))^2 = 2 + log 3 / log 2 + log 2 / log 3 := by
      ring
      rw [sqrt_mul_self (add_nonneg zero_le_one (div_nonneg (log_nonneg (by norm_num : (3 : ℝ) ≥ 1)) (log_pos (by norm_num : (2 : ℝ) > 1)))),
          sqrt_mul_self (add_nonneg zero_le_one (div_nonneg (log_nonneg (by norm_num : (2 : ℝ) ≥ 1)) (log_pos (by norm_num : (3 : ℝ) > 1))))]
    exact (sqrt_eq_iff_sq_eq (add_nonneg zero_le_one (div_nonneg (log_nonneg (by norm_num : (3 : ℝ) ≥ 1)) (log_pos (by norm_num : (2 : ℝ) > 1))))
      (add_nonneg zero_le_one (div_nonneg (log_nonneg (by norm_num : (2 : ℝ) ≥ 1)) (log_pos (by norm_num : (3 : ℝ) > 1))))).mpr h8
  rw [h7]