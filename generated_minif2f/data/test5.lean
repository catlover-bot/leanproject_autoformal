import Mathlib.Algebra.GroupPower.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

theorem mathd_algebra_141
(a b : ℝ)
(h₁ : (a * b) = 180)
(h₂ : 2 * (a + b) = 54) :
(a^2 + b^2) = 369 :=
begin
  have h₃ : a + b = 27, from (eq_div_of_mul_eq (by norm_num) h₂).symm,
  have h₄ : (a + b)^2 = a^2 + 2 * a * b + b^2, by ring,
  have h₅ : 27^2 = a^2 + 2 * a * b + b^2, from h₃ ▸ h₄,
  have h₆ : 729 = a^2 + 2 * 180 + b^2, from h₅ ▸ h₁,
  linarith,
end