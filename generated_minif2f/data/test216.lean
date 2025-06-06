import Mathlib.Data.Real.Basic

theorem solve_for_y : ∀ (y : ℝ), y + 6 + y = 2 * 12 → y = 9 :=
begin
  intro y,
  intro h,
  linarith,
end