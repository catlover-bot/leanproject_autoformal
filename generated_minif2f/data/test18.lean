import Mathlib.Data.Real.Basic

theorem problem_statement : ∀ (a b : ℝ), a = -1 → b = 5 → -a - b^2 + 3 * (a * b) = -39 :=
begin
  intros a b ha hb,
  rw [ha, hb],
  norm_num,
end