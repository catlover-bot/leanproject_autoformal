import Mathlib.Algebra.Order.ArithmeticMean
import Mathlib.Data.Real.Basic

open Real

theorem am_gm_inequality_example (a b c d : ℝ) (h : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d) :
  a^2 / b + b^2 / c + c^2 / d + d^2 / a ≥ a + b + c + d :=
begin
  have h1 : a^2 / b + b ≥ 2 * a := by
    apply (AM_GM2_weighted (a^2 / b) b 1 1 (by linarith [h.1, h.2.1])).1,
    rw [add_div, one_div_one, one_div_one, add_comm],
    exact div_nonneg (sq_nonneg a) (le_of_lt h.2.1),
    exact le_of_lt h.2.1,
    rw [add_comm, mul_one, mul_one, div_mul_cancel _ (ne_of_gt h.2.1)],
    exact le_of_lt h.1,
  have h2 : b^2 / c + c ≥ 2 * b := by
    apply (AM_GM2_weighted (b^2 / c) c 1 1 (by linarith [h.2.1, h.2.2.1])).1,
    rw [add_div, one_div_one, one_div_one, add_comm],
    exact div_nonneg (sq_nonneg b) (le_of_lt h.2.2.1),
    exact le_of_lt h.2.2.1,
    rw [add_comm, mul_one, mul_one, div_mul_cancel _ (ne_of_gt h.2.2.1)],
    exact le_of_lt h.2.1,
  have h3 : c^2 / d + d ≥ 2 * c := by
    apply (AM_GM2_weighted (c^2 / d) d 1 1 (by linarith [h.2.2.1, h.2.2.2])).1,
    rw [add_div, one_div_one, one_div_one, add_comm],
    exact div_nonneg (sq_nonneg c) (le_of_lt h.2.2.2),
    exact le_of_lt h.2.2.2,
    rw [add_comm, mul_one, mul_one, div_mul_cancel _ (ne_of_gt h.2.2.2)],
    exact le_of_lt h.2.2.1,
  have h4 : d^2 / a + a ≥ 2 * d := by
    apply (AM_GM2_weighted (d^2 / a) a 1 1 (by linarith [h.2.2.2, h.1])).1,
    rw [add_div, one_div_one, one_div_one, add_comm],
    exact div_nonneg (sq_nonneg d) (le_of_lt h.1),
    exact le_of_lt h.1,
    rw [add_comm, mul_one, mul_one, div_mul_cancel _ (ne_of_gt h.1)],
    exact le_of_lt h.2.2.2,
  linarith,
end