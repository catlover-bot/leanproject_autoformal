import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Nnreal

open Real

theorem nnreal_sqrt_product (x y : ℝ≥0) (h1 : (x + y) / 2 = 7) (h2 : sqrt (x * y) = sqrt 19) : x^2 * y^2 = 158 := by
  have h3 : x * y = 19 := by
    rw [sqrt_eq_iff_sq_eq] at h2
    exact h2.1
    apply mul_nonneg; exact x.2; exact y.2
  have h4 : x + y = 14 := by
    linarith
  have h5 : (x - y)^2 = (x + y)^2 - 4 * x * y := by
    ring
  have h6 : (x - y)^2 = 196 - 76 := by
    rw [h4, h3]
    norm_num
  have h7 : (x - y)^2 = 120 := by
    norm_num at h6
    exact h6
  have h8 : x^2 + y^2 = 196 - 2 * 19 := by
    rw [←h4, h3]
    ring
  have h9 : x^2 + y^2 = 158 := by
    norm_num at h8
    exact h8
  have h10 : (x^2 + y^2)^2 = (x^2 - y^2)^2 + 4 * x^2 * y^2 := by
    ring
  have h11 : (x^2 - y^2)^2 = 120 * 76 := by
    rw [h7, h3]
    norm_num
  have h12 : (x^2 + y^2)^2 = 158^2 := by
    rw [h9]
    norm_num
  have h13 : 158^2 = 120 * 76 + 4 * x^2 * y^2 := by
    rw [h10, h11]
    exact h12
  have h14 : 158^2 - 120 * 76 = 4 * x^2 * y^2 := by
    linarith
  have h15 : 158 = 2 * x * y := by
    rw [h3]
    norm_num
  have h16 : x^2 * y^2 = 158 := by
    linarith
  exact h16