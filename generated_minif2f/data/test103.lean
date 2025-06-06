import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field

open Real

theorem solve_for_y (y : ℝ) (h1 : 0 ≤ 19 + 3 * y) (h2 : sqrt (19 + 3 * y) = 7) : y = 10 :=
begin
  have h3 : 19 + 3 * y = 49,
  { rw [←h2, sqrt_eq_iff_sq_eq],
    { norm_num },
    { exact h1 } },
  linarith,
end