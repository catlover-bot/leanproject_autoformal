import Mathlib.Data.Real.Basic
import Mathlib.Algebra.GroupPower.Basic

open Real

theorem sum_of_a_b (a b : ℝ) (h : a^2 * b^3 = 32 / 27 ∧ a / b^3 = 27 / 4) : a + b = 8 / 3 := by
  have h1 : a = (27 / 4) * b^3 := by
    rw [div_eq_iff] at h.2
    exact h.2
    exact pow_ne_zero 3 (ne_of_gt (by norm_num : (4 : ℝ) > 0))
  
  rw [h1] at h
  have h2 : ((27 / 4) * b^3)^2 * b^3 = 32 / 27 := h.1
  rw [mul_pow, pow_mul, pow_succ, pow_succ, mul_assoc] at h2
  have h3 : (729 / 16) * b^9 = 32 / 27 := h2
  have h4 : b^9 = (32 / 27) * (16 / 729) := by
    rw [←div_eq_iff] at h3
    exact h3
    exact ne_of_gt (by norm_num : (729 : ℝ) > 0)
  
  have h5 : b^9 = 512 / 19683 := by
    norm_num at h4
    exact h4
  
  have h6 : b = (512 / 19683)^(1/9) := by
    rw [←Real.rpow_nat_cast, Real.rpow_eq_rpow_iff] at h5
    exact h5
    exact ne_of_gt (by norm_num : (19683 : ℝ) > 0)
    exact ne_of_gt (by norm_num : (512 : ℝ) > 0)
  
  have h7 : a = (27 / 4) * ((512 / 19683)^(1/9))^3 := by
    rw [h1, h6]
  
  have h8 : a = 3 / 2 := by
    rw [h7]
    norm_num
    rw [Real.rpow_nat_cast]
    norm_num
  
  have h9 : b = 5 / 6 := by
    rw [h6]
    norm_num
    rw [Real.rpow_nat_cast]
    norm_num
  
  rw [h8, h9]
  norm_num
  done