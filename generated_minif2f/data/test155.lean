import Mathlib.Data.Real.Basic

open Real

theorem quadratic_inequality : ∀ (x : ℝ), x^2 - 14 * x + 3 ≥ 7^2 - 14 * 7 + 3 :=
begin
  intro x,
  have h : ∀ (x : ℝ), x^2 - 14 * x + 3 = (x - 7)^2 - 46,
  { intro x,
    ring },
  rw h,
  have h7 : (7 - 7)^2 - 46 = -46,
  { norm_num },
  rw h7,
  have h_nonneg : ∀ (x : ℝ), (x - 7)^2 ≥ 0,
  { intro x,
    apply pow_two_nonneg },
  linarith,
end