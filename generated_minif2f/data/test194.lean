import Mathlib.Data.Real.Basic

theorem mathd_algebra_270
  (f : ℝ → ℝ)
  (h₀ : ∀ x ≠ -2, f x = 1 / (x + 2)) :
  f (f 1) = 3 / 7 :=
by
  have h₁ : f 1 = 1 / (1 + 2) := h₀ 1 (by norm_num)
  have h₂ : f 1 = 1 / 3 := by norm_num
  rw [h₂] at h₁
  have h₃ : f (1 / 3) = 1 / ((1 / 3) + 2) := h₀ (1 / 3) (by norm_num)
  have h₄ : (1 / 3) + 2 = 7 / 3 := by norm_num
  rw [h₄] at h₃
  have h₅ : 1 / (7 / 3) = 3 / 7 := by norm_num
  rw [h₅] at h₃
  exact h₃