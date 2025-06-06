import Mathlib.Data.Real.Basic
import Mathlib.Tactic

theorem aime_1988_p8
  (f : ℕ → ℕ → ℝ)
  (h₀ : ∀ x, 0 < x → f x x = x)
  (h₁ : ∀ x y, (0 < x ∧ 0 < y) → f x y = f y x)
  (h₂ : ∀ x y, (0 < x ∧ 0 < y) → (↑x + ↑y) * f x y = y * (f x (x + y))) :
  f 14 52 = 364 :=
by
  have h₃ : ∀ x y, (0 < x ∧ 0 < y) → f x y = x * y / (x + y) := by
    intros x y hxy
    have h₄ := h₂ x y hxy
    rw [h₀ x hxy.1] at h₄
    field_simp at h₄
    exact h₄
  have h₅ : f 14 52 = 14 * 52 / (14 + 52) := h₃ 14 52 ⟨by norm_num, by norm_num⟩
  norm_num at h₅
  exact h₅