import Mathlib.Algebra.Order.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Real

theorem imo_1983_p6
  (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : c < a + b)
  (h₂ : b < a + c)
  (h₃ : a < b + c) :
  0 ≤ a^2 * b * (a - b) + b^2 * c * (b - c) + c^2 * a * (c - a) :=
begin
  have h₄ : a^2 * b * (a - b) + b^2 * c * (b - c) + c^2 * a * (c - a) =
            1/2 * ((a - b)^2 * a * b + (b - c)^2 * b * c + (c - a)^2 * c * a),
  { ring },
  rw h₄,
  apply add_nonneg,
  { apply add_nonneg,
    { apply mul_nonneg,
      { apply mul_nonneg,
        { apply pow_two_nonneg },
        { exact h₀.1.le } },
      { exact pow_two_nonneg (a - b) } },
    { apply mul_nonneg,
      { apply mul_nonneg,
        { apply pow_two_nonneg },
        { exact h₀.2.1.le } },
      { exact pow_two_nonneg (b - c) } } },
  { apply mul_nonneg,
    { apply mul_nonneg,
      { apply pow_two_nonneg },
      { exact h₀.2.2.le } },
    { exact pow_two_nonneg (c - a) } }
end