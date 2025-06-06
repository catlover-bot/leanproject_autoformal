import Mathlib.Data.Real.Basic

theorem function_composition_example :
  ∀ (f g : ℝ → ℝ), (∀ x, f x = 2 * x - 3) → (∀ x, g x = x + 1) → g (f 5 - 1) = 7 :=
begin
  intros f g hf hg,
  rw [hf, hg],
  norm_num,
end