import Mathlib.Data.Real.Basic

theorem real_function_equality
  (a b : ℝ) (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = a * x^4 - b * x^2 + x + 5)
  (h₁ : f (-3) = 2) : f 3 = 8 :=
by
  have h₂ : a * (-3)^4 - b * (-3)^2 + (-3) + 5 = 2 := by
    rw [h₀ (-3)]
    exact h₁
  simp at h₂
  have h₃ : 81 * a - 9 * b = 0 := by linarith
  have h₄ : a * 3^4 - b * 3^2 + 3 + 5 = 8 := by
    rw [h₀ 3]
    simp
    linarith [h₃]
  exact h₄