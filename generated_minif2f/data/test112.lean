import Mathlib.Data.Real.Basic
import Mathlib.Data.Int.Basic

open Int

theorem polynomial_factorization (a b : ℤ) :
  (∀ x : ℝ, 10 * x^2 - x - 24 = (a * x - 8) * (b * x + 3)) → a + b = 12 :=
begin
  intro h,
  specialize h 0,
  have h0 : 10 * 0^2 - 0 - 24 = (a * 0 - 8) * (b * 0 + 3), by exact h,
  norm_num at h0,
  have h1 : 10 * 1^2 - 1 - 24 = (a * 1 - 8) * (b * 1 + 3), by exact h 1,
  norm_num at h1,
  have h2 : 10 * 2^2 - 2 - 24 = (a * 2 - 8) * (b * 2 + 3), by exact h 2,
  norm_num at h2,
  linarith,
end