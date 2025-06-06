import Mathlib.Data.Real.Basic

namespace AMC12B2002P19

theorem amc12b_2002_p19
  (a b c: ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : a * (b + c) = 152)
  (h₂ : b * (c + a) = 162)
  (h₃ : c * (a + b) = 170) :
  a * b * c = 720 :=
begin
  have h₄ : a * b + a * c = 152 := h₁,
  have h₅ : b * c + a * b = 162 := h₂,
  have h₆ : c * a + b * c = 170 := h₃,
  have h₇ : (a * b + a * c) + (b * c + a * b) + (c * a + b * c) = 152 + 162 + 170,
  { ring, },
  have h₈ : 2 * (a * b + b * c + c * a) = 484 := by linarith,
  have h₉ : a * b + b * c + c * a = 242 := by linarith,
  have h₁₀ : (a + b + c) ^ 2 = a^2 + b^2 + c^2 + 2 * (a * b + b * c + c * a),
  { ring, },
  have h₁₁ : (a + b + c) ^ 2 = a^2 + b^2 + c^2 + 484 := by rw [h₁₀, h₈],
  have h₁₂ : (a + b + c) ^ 2 = (a + b + c) * (a + b + c) := by ring,
  have h₁₃ : a * b * c = (a + b + c) * (a * b + b * c + c * a) - (a * b + a * c + b * c) * (a + b + c) + a * b * c,
  { ring, },
  have h₁₄ : a * b * c = (a + b + c) * 242 - 484 * (a + b + c) + a * b * c := by rw [h₉, h₁₃],
  have h₁₅ : a * b * c = 720 := by linarith,
  exact h₁₅,
end

end AMC12B2002P19