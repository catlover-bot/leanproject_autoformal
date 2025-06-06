import Mathlib.Data.Real.Basic

theorem inequality_holds_for_all_x : ∀ (x : ℝ), x^2 - 14 * x + 3 ≥ 7^2 - 14 * 7 + 3 :=
begin
  intro x,
  have h : 7^2 - 14 * 7 + 3 = -46,
  { norm_num },
  rw h,
  have h2 : x^2 - 14 * x + 3 + 46 = (x - 7)^2,
  { ring },
  rw ← h2,
  apply add_nonneg,
  { exact pow_two_nonneg (x - 7) },
  { norm_num }
end