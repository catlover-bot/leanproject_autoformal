import Mathlib.Data.Real.Basic

open Real

theorem fg_evaluation : ∀ (f g : ℝ → ℝ), (∀ x, f x = x + 1) → (∀ x, g x = x^2 + 3) → f (g 2) = 8 :=
begin
  intros f g hf hg,
  have h1 : g 2 = 2^2 + 3, from hg 2,
  norm_num at h1,
  have h2 : f 7 = 7 + 1, from hf 7,
  norm_num at h2,
  rw h1,
  exact h2,
end