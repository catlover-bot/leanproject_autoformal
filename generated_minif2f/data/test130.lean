import Mathlib.Data.Real.Basic
import Mathlib.Data.Int.Basic

open Int

theorem floor_sum_of_thirds :
  ∀ (n : ℝ), (n = 1 / 3) → (floor (10 * n) + floor (100 * n) + floor (1000 * n) + floor (10000 * n) = 3702) :=
begin
  intros n hn,
  rw hn,
  have h1 : floor (10 * (1 / 3)) = 3,
  { norm_num },
  have h2 : floor (100 * (1 / 3)) = 33,
  { norm_num },
  have h3 : floor (1000 * (1 / 3)) = 333,
  { norm_num },
  have h4 : floor (10000 * (1 / 3)) = 3333,
  { norm_num },
  rw [h1, h2, h3, h4],
  norm_num,
end