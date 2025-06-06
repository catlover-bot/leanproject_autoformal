```lean
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt

open Real

theorem sqrt_log_sum_eq_sqrt_sum_log :
  sqrt (log 6 / log 2 + log 6 / log 3) = sqrt (log 3 / log 2) + sqrt (log 2 / log 3) :=
begin
  -- Simplify the left-hand side using properties of logarithms
  have h1 : log 6 / log 2 = log 2 / log 2 + log 3 / log 2,
  { rw [log_mul (by norm_num : (2 : ℝ) > 0) (by norm_num : (3 : ℝ) > 0), add_div],
    simp, },
  have h2 : log 6 / log 3 = log 2 / log 3 + log 3 / log 3,
  { rw [log_mul (by norm_num : (2 : ℝ) > 0) (by norm_num : (3 : ℝ) > 0), add_div],
    simp, },
  rw [h1, h2],
  -- Combine terms
  have h3 : log 6 / log 2 + log 6 / log 3 = (log 2 / log 2 + log 3 / log 2) + (log 2 / log 3 + log 3 / log 3),
  { rw [add_assoc, add_assoc], },
  rw h3,
  -- Simplify using properties of logarithms
  have h4 : log 2 / log 2 = 1, { rw div_self (log_pos (by norm_num : (2 : ℝ) > 0)).ne' },
  have h5 : log 3 / log 3 = 1, { rw div_self (log_pos (by norm_num : (3 : ℝ) > 0)).ne' },
  rw [h4, h5],
  -- Simplify the square root
  have h6 : sqrt (1 + log 3 / log 2 + log 2 / log 3 + 1) = sqrt (log 3 / log 2 + log 2 / log 3 + 2),
  { ring, },
  rw h6,
  -- Use the identity for square roots
  have h7 : sqrt (log 3 / log 2 + log 2 / log 3 + 2) = sqrt (log 3 / log 2) + sqrt (log 2 / log 3),
  { rw [sqrt_add, sqrt_mul_self, sqrt_mul_self],
    { ring, },
    { apply add_nonneg,
      { apply div_nonneg (log_nonneg (by norm_num : (3 : ℝ) ≥ 1)) (log_pos (by norm_num : (2 : ℝ) > 0)).le, },
      { apply div_nonneg (log_nonneg (by norm_num : (2 : ℝ) ≥ 1)) (log_pos (by norm_num : (3 : ℝ) > 0)).le, }, },
    { apply add_nonneg,
      { apply div_nonneg (log_nonneg (by norm_num : (3 : ℝ) ≥ 1)) (log_pos (by norm_num : (2 : ℝ) > 0)).le, },
      { apply div_nonneg (log_nonneg (by norm_num : (2 : ℝ) ≥ 1)) (log_pos (by norm_num : (3 : ℝ) > 0)).le, }, }, },
  rw h7,
end
```