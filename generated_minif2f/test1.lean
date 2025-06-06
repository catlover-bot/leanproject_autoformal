import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

theorem mathd_algebra_478
(b h v : ℝ)
(h₀ : 0 < b ∧ 0 < h ∧ 0 < v)
(h₁ : v = 1 / 3 * (b * h))
(h₂ : b = 30)
(h₃ : h = 13 / 2) :
v = 65 :=
by
  rw [h₂, h₃] at h₁
  have : v = 1 / 3 * (30 * (13 / 2)) := h₁
  norm_num at this
  exact this