import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

open Real

theorem algebra_abpbcpcageq3_sumaonsqrtapbgeq3onsqrt2
  (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : 3 ≤ a * b + b * c + c * a) :
  3 / sqrt 2 ≤ a / sqrt (a + b) + b / sqrt (b + c) + c / sqrt (c + a) :=
begin
  have h₂ : 0 < a + b ∧ 0 < b + c ∧ 0 < c + a,
  { split; linarith [h₀.1, h₀.2.1, h₀.2.2] },
  have h₃ : (a / sqrt (a + b) + b / sqrt (b + c) + c / sqrt (c + a))^2 ≤ 
            (a * b + b * c + c * a) * (1 / (a + b) + 1 / (b + c) + 1 / (c + a)),
  { apply Cauchy_Schwarz_ineq,
    { intro x, exact x^2 },
    { intro x, exact 1 / x },
    { exact h₂ } },
  have h₄ : 1 / (a + b) + 1 / (b + c) + 1 / (c + a) ≤ 3 / 2,
  { field_simp [h₂.1, h₂.2.1, h₂.2.2],
    linarith },
  have h₅ : (a / sqrt (a + b) + b / sqrt (b + c) + c / sqrt (c + a))^2 ≤ 
            (a * b + b * c + c * a) * (3 / 2),
  { linarith [h₃, h₄] },
  have h₆ : (3 / sqrt 2)^2 = 9 / 2,
  { norm_num },
  have h₇ : (a * b + b * c + c * a) * (3 / 2) ≥ 9 / 2,
  { linarith [h₁] },
  have h₈ : (a / sqrt (a + b) + b / sqrt (b + c) + c / sqrt (c + a))^2 ≥ 9 / 2,
  { linarith [h₅, h₇] },
  have h₉ : 0 < 3 / sqrt 2,
  { norm_num, apply div_pos; norm_num },
  apply le_of_pow_two_le_pow_two h₉,
  linarith [h₈],
end