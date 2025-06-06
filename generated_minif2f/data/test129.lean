import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open Real

theorem solve_for_a (a : ℝ) :
  sqrt (4 + sqrt (16 + 16 * a)) + sqrt (1 + sqrt (1 + a)) = 6 → a = 8 :=
begin
  intro h,
  have h1 : sqrt (4 + sqrt (16 + 16 * a)) = 6 - sqrt (1 + sqrt (1 + a)), from
    eq_sub_of_add_eq h,
  have h2 : (sqrt (4 + sqrt (16 + 16 * a)))^2 = (6 - sqrt (1 + sqrt (1 + a)))^2, by rw h1,
  rw [sq_sqrt, sq_sub, sq_sqrt, sq_sqrt] at h2,
  { linarith },
  { linarith [sqrt_nonneg (16 + 16 * a)] },
  { linarith [sqrt_nonneg (1 + a)] },
  { linarith [sqrt_nonneg (1 + a)] },
end