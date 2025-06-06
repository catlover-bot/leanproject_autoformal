import Mathlib.Data.Real.Basic

open Real

theorem problem (f g : ℝ → ℝ) :
  (∀ x, f x = 2 * x - 3) → (∀ x, g x = x + 1) → g (f 5 - 1) = 7 :=
begin
  intros hf hg,
  have h1 : f 5 = 2 * 5 - 3 := hf 5,
  have h2 : f 5 - 1 = 2 * 5 - 3 - 1,
  { rw h1 },
  norm_num at h2,
  have h3 : g 6 = 6 + 1 := hg 6,
  rw h2 at h3,
  exact h3,
end