import Mathlib.Data.Nat.Basic

theorem mathd_numbertheory_430
(a b c : ℕ)
(h₀ : 1 ≤ a ∧ a ≤ 9)
(h₁ : 1 ≤ b ∧ b ≤ 9)
(h₂ : 1 ≤ c ∧ c ≤ 9)
(h₃ : a ≠ b)
(h₄ : a ≠ c)
(h₅ : b ≠ c)
(h₆ : a + b = c)
(h₇ : 10 * a + a - b = 2 * c)
(h₈ : c * b = 10 * a + a + a) :
a + b + c = 8 :=
begin
  have h₉ : c = a + b, from h₆,
  have h₁₀ : 11 * a - b = 2 * c, from h₇,
  rw [h₉] at h₁₀,
  have h₁₁ : 11 * a - b = 2 * (a + b), from h₁₀,
  linarith,
  have h₁₂ : c * b = 12 * a, from h₈,
  rw [h₉] at h₁₂,
  have h₁₃ : (a + b) * b = 12 * a, from h₁₂,
  have h₁₄ : a + b + c = 2 * a + 2 * b, from by linarith,
  have h₁₅ : 2 * a + 2 * b = 8, from by linarith,
  exact h₁₅,
end