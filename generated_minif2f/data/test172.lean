import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Nnreal

open Real

lemma sqrt_mul_sqrt (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : sqrt a * sqrt b = sqrt (a * b) :=
  by rw [sqrt_mul ha hb]

theorem sqrt_product_identity (x : ℝ≥0) : 
  sqrt (60 * x) * sqrt (12 * x) * sqrt (63 * x) = 36 * x * sqrt (35 * x) :=
begin
  have hx : 0 ≤ (x : ℝ) := x.2,
  have h60x : 0 ≤ 60 * (x : ℝ) := mul_nonneg (by norm_num) hx,
  have h12x : 0 ≤ 12 * (x : ℝ) := mul_nonneg (by norm_num) hx,
  have h63x : 0 ≤ 63 * (x : ℝ) := mul_nonneg (by norm_num) hx,
  have h35x : 0 ≤ 35 * (x : ℝ) := mul_nonneg (by norm_num) hx,
  rw [sqrt_mul_sqrt (60 * x) (12 * x) h60x h12x, sqrt_mul_sqrt (720 * x^2) (63 * x) (mul_nonneg h60x h12x) h63x],
  rw [mul_assoc, mul_assoc, mul_comm (sqrt (720 * x^2)), ←mul_assoc, sqrt_mul_sqrt (720 * x^2 * 63 * x) (35 * x) (mul_nonneg (mul_nonneg (by norm_num) hx) hx) h35x],
  rw [mul_assoc, mul_assoc, mul_comm (720 * x^2), ←mul_assoc, mul_assoc (720 * x^2), mul_comm (63 * x), ←mul_assoc, mul_assoc (720 * x^2 * 63 * x)],
  rw [mul_comm (720 * x^2 * 63 * x), ←mul_assoc, mul_assoc (720 * x^2 * 63 * x), mul_comm (35 * x), ←mul_assoc],
  rw [sqrt_mul_sqrt (720 * x^2 * 63 * x * 35 * x) 1 (mul_nonneg (mul_nonneg (by norm_num) hx) hx) zero_le_one],
  rw [mul_one, sqrt_mul_self (mul_nonneg (by norm_num) hx)],
  norm_num,
end