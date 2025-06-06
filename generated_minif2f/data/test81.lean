import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Real

theorem algebra_abpbcpcageq3_sumaonsqrtapbgeq3onsqrt2
  (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : 3 ≤ a * b + b * c + c * a) :
  3 / sqrt 2 ≤ a / sqrt (a + b) + b / sqrt (b + c) + c / sqrt (c + a) :=
begin
  have h₂ : 0 < a + b ∧ 0 < b + c ∧ 0 < c + a,
  { split; linarith [h₀.1, h₀.2.1, h₀.2.2] },
  have h₃ : 0 < sqrt (a + b) ∧ 0 < sqrt (b + c) ∧ 0 < sqrt (c + a),
  { split; apply sqrt_pos.mpr; linarith [h₂.1, h₂.2.1, h₂.2.2] },
  have h₄ : (a / sqrt (a + b))^2 + (b / sqrt (b + c))^2 + (c / sqrt (c + a))^2
            = (a^2 / (a + b)) + (b^2 / (b + c)) + (c^2 / (c + a)),
  { ring },
  have h₅ : (a^2 / (a + b)) + (b^2 / (b + c)) + (c^2 / (c + a)) ≥ 3 / 2,
  { linarith [h₁, h₂.1, h₂.2.1, h₂.2.2] },
  have h₆ : (a / sqrt (a + b))^2 + (b / sqrt (b + c))^2 + (c / sqrt (c + a))^2 ≥ 3 / 2,
  { rw h₄, exact h₅ },
  have h₇ : a / sqrt (a + b) + b / sqrt (b + c) + c / sqrt (c + a) ≥ sqrt (3 / 2),
  { apply sqrt_sum_squares_ge_sum_sqrt, exact h₆, exact h₃ },
  have h₈ : sqrt (3 / 2) = 3 / sqrt 2,
  { rw [sqrt_div, sqrt_mul, sqrt_sqrt, sqrt_sqrt]; norm_num },
  rw h₈ at h₇,
  exact h₇,
end