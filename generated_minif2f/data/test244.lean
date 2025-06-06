import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Real.Basic

namespace MathdAlgebra

theorem mathd_algebra_338
  (a b c : ℝ)
  (h₀ : 3 * a + b + c = -3)
  (h₁ : a + 3 * b + c = 9)
  (h₂ : a + b + 3 * c = 19) :
  a * b * c = -56 :=
begin
  have h₃ : 9 * a + 3 * b + 3 * c = -9 := by linarith [h₀],
  have h₄ : 3 * a + 9 * b + 3 * c = 27 := by linarith [h₁],
  have h₅ : 3 * a + 3 * b + 9 * c = 57 := by linarith [h₂],
  have h₆ : 15 * a + 15 * b + 15 * c = 75 := by linarith [h₃, h₄, h₅],
  have h₇ : a + b + c = 5 := by linarith [h₆],
  have h₈ : 2 * a = -8 := by linarith [h₀, h₇],
  have h₉ : a = -4 := by linarith [h₈],
  have h₁₀ : 2 * b = 18 := by linarith [h₁, h₇, h₉],
  have h₁₁ : b = 9 := by linarith [h₁₀],
  have h₁₂ : 2 * c = 30 := by linarith [h₂, h₇, h₉],
  have h₁₃ : c = 15 := by linarith [h₁₂],
  linarith [h₉, h₁₁, h₁₃],
end

end MathdAlgebra