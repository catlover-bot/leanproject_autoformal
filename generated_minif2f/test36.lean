import Mathlib.Algebra.GroupPower.Basic
import Mathlib.Tactic.Ring

lemma polynomial_identity : ∀ (x : ℝ), (x + 1)^2 * x = x^3 + 2 * x^2 + x :=
begin
  intro x,
  ring,
end