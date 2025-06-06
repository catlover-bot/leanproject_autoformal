import Mathlib.Data.Real.Basic

theorem ratio_of_equations (x y z : ℝ) (hx : x ≠ 0) (h1 : 2 * x = 5 * y) (h2 : 7 * y = 10 * z) : z / x = 7 / 25 := by
  have h3 : y = (2 / 5) * x := by
    rw [← mul_right_inj' (show 5 ≠ 0 by norm_num), mul_assoc, ← h1, mul_div_cancel' _ (show 2 ≠ 0 by norm_num)]
  have h4 : z = (7 / 10) * y := by
    rw [← mul_right_inj' (show 10 ≠ 0 by norm_num), mul_assoc, ← h2, mul_div_cancel' _ (show 7 ≠ 0 by norm_num)]
  rw [h3, h4]
  field_simp [hx]
  ring_nf
  norm_num