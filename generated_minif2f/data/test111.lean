import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

open Real

theorem AM_GM_inequality_variant (a b : ℝ) (h₀ : 0 < a ∧ 0 < b) (h₁ : b ≤ a) :
  (a + b) / 2 - sqrt (a * b) ≤ (a - b)^2 / (8 * b) :=
begin
  have h₂ : 0 < b := h₀.2,
  have h₃ : 0 < a := h₀.1,
  have h₄ : 0 < a * b := mul_pos h₃ h₂,
  have h₅ : 0 < 8 * b := mul_pos (by norm_num) h₂,
  have h₆ : 0 ≤ (sqrt a - sqrt b)^2,
  { apply pow_two_nonneg, },
  have h₇ : (a + b) / 2 - sqrt (a * b) = ((sqrt a - sqrt b)^2) / 2,
  { field_simp [sqrt_mul h₃ h₂],
    ring_nf,
    rw [← sqrt_mul h₄, mul_self_sqrt (le_of_lt h₄)],
    ring, },
  rw [h₇],
  apply div_le_div_of_le h₅,
  rw [mul_comm, ← mul_assoc],
  apply mul_le_mul_of_nonneg_left h₆,
  norm_num,
end