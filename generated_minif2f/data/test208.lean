import Mathlib.Algebra.GroupPower.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace AIME1990P15

theorem aime_1990_p15
  (a b x y : ℝ)
  (h₀ : a * x + b * y = 3)
  (h₁ : a * x^2 + b * y^2 = 7)
  (h₂ : a * x^3 + b * y^3 = 16)
  (h₃ : a * x^4 + b * y^4 = 42) :
  a * x^5 + b * y^5 = 20 :=
begin
  have h₄ : a * x^5 + b * y^5 = (a * x^4 + b * y^4) * (a * x + b * y) - (a * x^3 + b * y^3) * (a * x^2 + b * y^2),
  { ring },
  rw [h₀, h₁, h₂, h₃] at h₄,
  norm_num at h₄,
  exact h₄,
end

end AIME1990P15