import Mathlib.Data.Real.Basic
import Mathlib.Data.Int.Basic

open Int

theorem floor_sum_eq_3702 : ∀ (n : ℝ), (n = 1 / 3) → (floor (10 * n) + floor (100 * n) + floor (1000 * n) + floor (10000 * n) = 3702) :=
begin
  intro n,
  intro h,
  rw h,
  have h1 : 10 * (1 / 3) = 10 / 3 := by norm_num,
  have h2 : 100 * (1 / 3) = 100 / 3 := by norm_num,
  have h3 : 1000 * (1 / 3) = 1000 / 3 := by norm_num,
  have h4 : 10000 * (1 / 3) = 10000 / 3 := by norm_num,
  rw [h1, h2, h3, h4],
  have f1 : floor (10 / 3) = 3 := by norm_num,
  have f2 : floor (100 / 3) = 33 := by norm_num,
  have f3 : floor (1000 / 3) = 333 := by norm_num,
  have f4 : floor (10000 / 3) = 3333 := by norm_num,
  rw [f1, f2, f3, f4],
  norm_num,
end