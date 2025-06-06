import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace AIME1990P4

theorem aime_1990_p4
(x : ℝ)
(h₀ : 0 < x)
(h₁ : x^2 - 10 * x - 29 ≠ 0)
(h₂ : x^2 - 10 * x - 45 ≠ 0)
(h₃ : x^2 - 10 * x - 69 ≠ 0)
(h₄ : 1 / (x^2 - 10 * x - 29) + 1 / (x^2 - 10 * x - 45) - 2 / (x^2 - 10 * x - 69) = 0) :
x = 13 :=
begin
  field_simp at h₄,
  have h₅ : (x^2 - 10 * x - 69) * ((x^2 - 10 * x - 29) + (x^2 - 10 * x - 45)) = 2 * (x^2 - 10 * x - 29) * (x^2 - 10 * x - 45),
  { linarith },
  ring_nf at h₅,
  have h₆ : x^2 - 10 * x - 29 + x^2 - 10 * x - 45 = 2 * x^2 - 20 * x - 74,
  { ring },
  rw h₆ at h₅,
  have h₇ : (x^2 - 10 * x - 69) * (2 * x^2 - 20 * x - 74) = 2 * (x^2 - 10 * x - 29) * (x^2 - 10 * x - 45),
  { exact h₅ },
  ring_nf at h₇,
  have h₈ : 2 * x^4 - 40 * x^3 - 148 * x^2 + 1480 * x + 5106 = 2 * x^4 - 40 * x^3 - 148 * x^2 + 1480 * x + 5106,
  { exact h₇ },
  linarith,
end

end AIME1990P4