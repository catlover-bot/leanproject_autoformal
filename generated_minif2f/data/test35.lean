import Mathlib.Data.Real.Basic

theorem div_eq_implies_eq (x : ℝ) : x / 50 = 40 → x = 2000 := by
  intro h
  have h1 : x = 40 * 50 := by
    rw [← mul_div_cancel x (by norm_num : (50 : ℝ) ≠ 0)]
    rw [h]
  norm_num at h1
  exact h1