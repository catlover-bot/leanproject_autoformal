import Mathlib.Data.Real.Basic

theorem imo_1964_p2
  (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : c < a + b)
  (h₂ : b < a + c)
  (h₃ : a < b + c) :
  a^2 * (b + c - a) + b^2 * (c + a - b) + c^2 * (a + b - c) ≤ 3 * a * b * c :=
by
  have h₄ : a + b - c > 0 := by linarith
  have h₅ : b + c - a > 0 := by linarith
  have h₆ : c + a - b > 0 := by linarith
  have h₇ : a^2 * (b + c - a) ≤ a^2 * (b + c - a) := le_refl _
  have h₈ : b^2 * (c + a - b) ≤ b^2 * (c + a - b) := le_refl _
  have h₉ : c^2 * (a + b - c) ≤ c^2 * (a + b - c) := le_refl _
  have h₁₀ : a^2 * (b + c - a) + b^2 * (c + a - b) + c^2 * (a + b - c) ≤ a^2 * (b + c - a) + b^2 * (c + a - b) + c^2 * (a + b - c) := by linarith
  have h₁₁ : a^2 * (b + c - a) + b^2 * (c + a - b) + c^2 * (a + b - c) ≤ a^2 * (b + c - a) + b^2 * (c + a - b) + c^2 * (a + b - c) := by linarith
  have h₁₂ : a^2 * (b + c - a) + b^2 * (c + a - b) + c^2 * (a + b - c) ≤ 3 * a * b * c := by
    linarith [h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁]
  exact h₁₂