import Mathlib.Data.Real.Basic

theorem pow_div_eq : (2^2014 + 2^2012) / (2^2014 - 2^2012) = (5:ℝ) / 3 := by
  have h1 : (2^2014 : ℝ) = (2^2012 : ℝ) * 2 := by norm_num
  have h2 : (2^2012 : ℝ) ≠ 0 := by norm_num
  calc
    (2^2014 + 2^2012) / (2^2014 - 2^2012)
        = ((2^2012 * 2) + 2^2012) / ((2^2012 * 2) - 2^2012) := by rw [h1]
    _ = (2^2012 * (2 + 1)) / (2^2012 * (2 - 1)) := by ring
    _ = (2 + 1) / (2 - 1) := by rw [mul_div_mul_left _ _ h2]
    _ = 3 / 1 := by norm_num
    _ = 5 / 3 := by norm_num