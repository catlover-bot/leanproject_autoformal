import Mathlib.Data.Real.Basic

theorem fg_eight (f g : ℝ → ℝ) (hf : ∀ x, f x = x + 1) (hg : ∀ x, g x = x^2 + 3) : f (g 2) = 8 := by
  rw [hg, hf]
  norm_num