import Mathlib.Data.Nat.Prime
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

theorem imo_2001_p6
  (a b c d : ℕ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d)
  (h₁ : d < c)
  (h₂ : c < b)
  (h₃ : b < a)
  (h₄ : a * c + b * d = (b + d + a - c) * (b + d - a + c)) :
  ¬ Nat.Prime (a * b + c * d) :=
begin
  have h₅ : a * c + b * d = (b + d + a - c) * (b + d - a + c), from h₄,
  have h₆ : a * b + c * d = (a * c + b * d) - (a * c - a * b - c * d + b * d),
  { ring },
  rw h₅ at h₆,
  have h₇ : a * b + c * d = (b + d + a - c) * (b + d - a + c) - (a * c - a * b - c * d + b * d),
  { exact h₆ },
  have h₈ : a * c - a * b - c * d + b * d = (a - b) * (c - d),
  { ring },
  rw h₈ at h₇,
  have h₉ : a * b + c * d = (b + d + a - c) * (b + d - a + c) - (a - b) * (c - d),
  { exact h₇ },
  have h₁₀ : (b + d + a - c) * (b + d - a + c) > (a - b) * (c - d),
  { linarith },
  have h₁₁ : a * b + c * d = (b + d + a - c) * (b + d - a + c) - (a - b) * (c - d),
  { exact h₉ },
  have h₁₂ : (b + d + a - c) * (b + d - a + c) > (a - b) * (c - d),
  { exact h₁₀ },
  have h₁₃ : a * b + c * d > 1,
  { linarith },
  intro h_prime,
  have h₁₄ : a * b + c * d = 1 ∨ a * b + c * d = (b + d + a - c) * (b + d - a + c),
  { exact Nat.Prime.eq_one_or_self_of_dvd h_prime (dvd_refl _) },
  cases h₁₄,
  { linarith },
  { have h₁₅ : (b + d + a - c) * (b + d - a + c) = a * b + c * d,
    { exact h₁₄ },
    rw h₁₅ at h₁₁,
    have h₁₆ : (a - b) * (c - d) = 0,
    { linarith },
    have h₁₇ : a - b = 0 ∨ c - d = 0,
    { exact Nat.eq_zero_or_eq_zero_of_mul_eq_zero h₁₆ },
    cases h₁₇,
    { linarith },
    { linarith } }
end