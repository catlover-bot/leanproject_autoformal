import Mathlib.Algebra.GroupPower.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

theorem mathd_algebra_141
(a b : ℝ)
(h₁ : (a * b) = 180)
(h₂ : 2 * (a + b) = 54) :
(a^2 + b^2) = 369 :=
by
  have h₃ : a + b = 27 := by linarith
  calc
    a^2 + b^2 = (a + b)^2 - 2 * a * b := by ring
    _ = 27^2 - 2 * 180 := by rw [h₃, h₁]
    _ = 729 - 360 := by norm_num
    _ = 369 := by norm_num