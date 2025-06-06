import Mathlib.Data.Nat.Prime
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace IMO2001P6

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
  have h₆ : a * b + c * d = (a * c + b * d) - (a * c - b * d), by ring,
  rw [h₅] at h₆,
  have h₇ : a * c - b * d = (a - b) * (c - d), by ring,
  rw [h₇] at h₆,
  have h₈ : a * b + c * d = (b + d + a - c) * (b + d - a + c) - (a - b) * (c - d), from h₆,
  have h₉ : (b + d + a - c) * (b + d - a + c) - (a - b) * (c - d) = (b + d)^2 - (a - c)^2, by ring,
  rw [h₉] at h₈,
  have h₁₀ : a * b + c * d = (b + d)^2 - (a - c)^2, from h₈,
  have h₁₁ : (b + d)^2 - (a - c)^2 = (b + d - (a - c)) * (b + d + (a - c)), by ring,
  rw [h₁₁] at h₁₀,
  have h₁₂ : b + d - (a - c) = 2 * b, by linarith,
  have h₁₃ : b + d + (a - c) = 2 * d, by linarith,
  rw [h₁₂, h₁₃] at h₁₀,
  have h₁₄ : a * b + c * d = 2 * b * 2 * d, from h₁₀,
  have h₁₅ : a * b + c * d = 4 * b * d, by ring,
  rw [h₁₅] at h₁₄,
  have h₁₆ : 4 * b * d = 2 * 2 * b * d, by ring,
  rw [h₁₆] at h₁₄,
  have h₁₇ : ¬ Nat.Prime (4 * b * d), from Nat.not_prime_mul,
  exact h₁₇,
end

end IMO2001P6