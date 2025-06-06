import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Real.Basic

theorem mathd_algebra_148
(c : ℝ)
(f : ℝ → ℝ)
(h₀ : ∀ x, f x = c * x^3 - 9 * x + 3)
(h₁ : f 2 = 9) :
c = 3 :=
by
  have h₂ : f 2 = c * 2^3 - 9 * 2 + 3 := h₀ 2
  rw [h₂] at h₁
  norm_num at h₁
  linarith