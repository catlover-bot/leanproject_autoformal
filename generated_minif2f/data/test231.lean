import Mathlib.Data.Real.Basic

theorem mathd_algebra_139
(s : ℝ → ℝ → ℝ)
(h₀ : ∀ x≠0, ∀y≠0, s x y = (1/y - 1/x) / (x-y)) :
s 3 11 = 1/33 :=
by
  have h₁ : s 3 11 = (1/11 - 1/3) / (3 - 11) := h₀ 3 (by norm_num) 11 (by norm_num)
  rw [h₁]
  norm_num