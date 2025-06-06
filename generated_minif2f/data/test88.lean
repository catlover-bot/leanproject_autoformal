import Mathlib.Data.Real.Basic

open Real

theorem power_fraction : (2^2014 + 2^2012) / (2^2014 - 2^2012) = (5:ℝ) / 3 :=
begin
  have h1 : 2^2014 + 2^2012 = 2^2012 * (2^2 + 1),
  { rw [pow_add, pow_add, pow_two], ring },
  have h2 : 2^2014 - 2^2012 = 2^2012 * (2^2 - 1),
  { rw [pow_add, pow_add, pow_two], ring },
  rw [h1, h2],
  field_simp [pow_ne_zero, show (2:ℝ) ≠ 0, by norm_num],
  norm_num,
end