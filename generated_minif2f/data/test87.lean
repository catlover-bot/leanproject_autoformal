import Mathlib.Data.Real.Basic

open Real

theorem solve_for_x : ∀ (x y : ℝ), (x + y = 25) → (x - y = 11) → x = 18 :=
begin
  intros x y h1 h2,
  linarith,
end