import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open Real

theorem aime_1990_p4
(x : ℝ)
(h₀ : 0 < x)
(h₁ : x^2 - 10 * x - 29 ≠ 0)
(h₂ : x^2 - 10 * x - 45 ≠ 0)
(h₃ : x^2 - 10 * x - 69 ≠ 0)
(h₄ : 1 / (x^2 - 10 * x - 29) + 1 / (x^2 - 10 * x - 45) - 2 / (x^2 - 10 * x - 69) = 0) :
x = 13 :=
begin
  have h₅ : (x^2 - 10 * x - 29) * (x^2 - 10 * x - 45) * (x^2 - 10 * x - 69) ≠ 0,
  { apply mul_ne_zero,
    { apply mul_ne_zero; assumption },
    { assumption } },
  
  have h₆ : (x^2 - 10 * x - 45) * (x^2 - 10 * x - 69) + (x^2 - 10 * x - 29) * (x^2 - 10 * x - 69) 
            - 2 * (x^2 - 10 * x - 29) * (x^2 - 10 * x - 45) = 0,
  { field_simp [h₁, h₂, h₃] at h₄,
    exact h₄ },

  ring_nf at h₆,
  have h₇ : x^2 - 10 * x - 13 = 0,
  { linarith },

  have h₈ : x = 13 ∨ x = -3,
  { rw [← sub_eq_zero, ← sub_eq_zero] at h₇,
    apply eq_or_eq_of_sub_eq_zero,
    exact h₇ },

  cases h₈,
  { exact h₈ },
  { exfalso,
    linarith }
end