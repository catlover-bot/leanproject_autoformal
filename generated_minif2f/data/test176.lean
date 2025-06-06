import Mathlib.Data.Real.Basic

theorem aime_1988_p8
  (f : ℕ → ℕ → ℝ)
  (h₀ : ∀ x, 0 < x → f x x = x)
  (h₁ : ∀ x y, (0 < x ∧ 0 < y) → f x y = f y x)
  (h₂ : ∀ x y, (0 < x ∧ 0 < y) → (↑x + ↑y) * f x y = y * (f x (x + y))) :
  f 14 52 = 364 :=
begin
  have h₃ : ∀ x y, (0 < x ∧ 0 < y) → f x y = y * x / (x + y),
  { intros x y hxy,
    have h₄ := h₂ x y hxy,
    rw [h₀ x hxy.1] at h₄,
    field_simp [hxy.1, hxy.2] at h₄,
    exact h₄.symm },
  have h₅ : f 14 52 = 52 * 14 / (14 + 52),
  { apply h₃,
    exact ⟨by norm_num, by norm_num⟩ },
  norm_num at h₅,
  exact h₅,
end