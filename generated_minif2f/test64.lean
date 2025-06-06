import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.NNReal

open NNReal

theorem nnreal_problem (a b : ℝ≥0) :
  0 < a ∧ 0 < b ∧ (a^2 = 6 * b) ∧ (a^2 = 54 / b) → a = 3 * sqrt 2 :=
begin
  rintro ⟨ha, hb, h1, h2⟩,
  have h3 : 6 * b = 54 / b, from h1.trans h2.symm,
  have h4 : 6 * b * b = 54, by rwa [← mul_div_assoc, mul_comm, mul_div_cancel' _ (ne_of_gt hb)],
  have h5 : b^2 = 9, by rwa [mul_comm, mul_eq_iff_eq_div, div_eq_iff (ne_of_gt hb), mul_comm] at h4,
  have hb' : b = 3, from (pow_eq_pow_iff (by norm_num) (by norm_num)).1 h5,
  rw [hb', mul_comm] at h1,
  have h6 : a^2 = 18, by rwa [mul_comm, mul_eq_iff_eq_div, div_eq_iff (ne_of_gt hb), mul_comm] at h1,
  have ha' : a = 3 * sqrt 2, from (pow_eq_pow_iff (by norm_num) (by norm_num)).1 h6,
  exact ha',
end